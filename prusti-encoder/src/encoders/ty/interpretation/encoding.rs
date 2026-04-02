use crate::encoders::{
    MirBuiltinEnc, Pure, TyUsePureEnc,
    mir_builtin::IntEncoding,
    ty::{
        RustTyDecomposition, UseTyDatas,
        interpretation::bitvec::{BitVecDomain, BitVecEnc},
        pure::{TyPurePrimData, TyPurePrimDataKind},
    },
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CSnap, CastType as _, ExprGenData, TypeData};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct EncodedTy<'tcx> {
    pub ty: ty::Ty<'tcx>,
    pub encoding: IntEncoding,
}

pub(crate) enum Encoded<'vir> {
    Native {
        ty: &'vir crate::encoders::ty::TyData<'vir, UseTyDatas<Pure>>,
    },
    BitVec {
        domain: &'vir BitVecDomain<'vir>,
    },
}

impl<'vir> Encoded<'vir> {
    pub fn from_encoded_ty<E: TaskEncoder>(
        t: EncodedTy<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<Self, EncodeFullError<'vir, E>> {
        match t.encoding {
            IntEncoding::Native => {
                let ty_task = RustTyDecomposition::from_prim_ty(t.ty);
                let e_ty = deps.require_dep::<TyUsePureEnc>(ty_task)?;
                Ok(Encoded::Native { ty: e_ty })
            }
            IntEncoding::BitVec => {
                let bit_vec_size = match t.ty.kind() {
                    ty::TyKind::Int(kind) => (*kind).into(),
                    ty::TyKind::Uint(kind) => (*kind).into(),
                    k => todo!("not int {k:?}"),
                };
                let bit_vec = deps.require_dep::<BitVecEnc>(bit_vec_size)?;
                Ok(Encoded::BitVec {
                    domain: vcx.alloc(bit_vec),
                })
            }
        }
    }

    pub fn snapshot_type(&self) -> &'vir TypeData<'vir, CSnap> {
        match self {
            Encoded::Native { ty } => ty.snapshot.downcast_ty(),
            Encoded::BitVec { domain } => (domain.domain)(),
        }
    }

    pub fn expect_primitive(&self, vcx: &'vir vir::VirCtxt<'vir>) -> &TyPurePrimData<'vir> {
        match self {
            Encoded::Native { ty } => ty.expect_primitive(),
            Encoded::BitVec { domain } => {
                // TODO:
                // taken from encoders::ty::kinds::primitive::ty_pure, where ty_kind is
                // TyKind::Float
                // Why is this type TYPE_INT?
                let prim_type: vir::TypePrim<'vir> = vir::TYPE_INT.upcast_ty();
                let cons_ident = domain.from_int;
                vcx.alloc(TyPurePrimData {
                    prim_type,
                    prim_to_snap: cons_ident,
                    kind: TyPurePrimDataKind::BitVec(domain),
                })
            }
        }
    }

    /// translates encoding of `e` from `self` into the encoding `encoding`
    pub fn encode<A, B>(
        &self,
        encoding: Self,
        e: &'vir ExprGenData<'vir, A, B, CSnap>,
    ) -> &'vir ExprGenData<'vir, A, B, CSnap> {
        match (self, encoding) {
            (Encoded::Native { .. }, Encoded::Native { .. })
            | (Encoded::BitVec { .. }, Encoded::BitVec { .. }) => e,
            (Encoded::Native { ty }, Encoded::BitVec { domain }) => {
                let native = ty.expect_native();
                (domain.from_int.call())((native.snap_to_prim.call())(e))
            }
            (Encoded::BitVec { domain }, Encoded::Native { ty }) => {
                let prim = ty.expect_primitive();
                (prim.prim_to_snap.call())((domain.to_int.call())(e))
            }
        }
    }
}

impl<'vir> EncodedTy<'vir> {
    pub fn new(ty: ty::Ty<'vir>, hint: IntEncoding) -> Self {
        Self { ty, encoding: hint }
    }

    /// ensures that `e` is in the right encoding for `self`, assuming it's currently native
    pub fn cons<A, B, E: TaskEncoder>(
        &self,
        e: &'vir ExprGenData<'vir, A, B, CSnap>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<&'vir ExprGenData<'vir, A, B, CSnap>, EncodeFullError<'vir, E>> {
        match self.encoding {
            IntEncoding::Native => Ok(e),
            IntEncoding::BitVec => {
                let t_src = Encoded::from_encoded_ty(
                    EncodedTy::new(self.ty, IntEncoding::Native),
                    vcx,
                    deps,
                )?;
                let t_dst = Encoded::from_encoded_ty(
                    EncodedTy::new(self.ty, IntEncoding::BitVec),
                    vcx,
                    deps,
                )?;
                Ok(t_src.encode(t_dst, e))
            }
        }
    }
}
