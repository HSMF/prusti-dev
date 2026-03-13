use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, VirCtxt};

use crate::encoders::ty::{
    interpretation::bitvec::BitVecEnc,
    pure::{DomainBuilder, TyPureEnc, TyPureIntegerData, TyPurePrimDataNative},
};

pub(crate) enum MaybeSigned {
    Signed(ty::IntTy),
    Unsigned(ty::UintTy),
}

impl<'a> From<MaybeSigned> for ty::TyKind<'a> {
    fn from(value: MaybeSigned) -> Self {
        match value {
            MaybeSigned::Signed(int) => ty::TyKind::Int(int),
            MaybeSigned::Unsigned(uint) => ty::TyKind::Uint(uint),
        }
    }
}

pub(crate) fn ty_pure_integer<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, crate::encoders::ty::TyEnc<crate::encoders::Pure>>,
    builder: &mut DomainBuilder<'vir>,
    int: MaybeSigned,
    cons_ident: vir::FunctionIdn<'vir, vir::Prim, vir::CSnap>,
) -> Result<TyPureIntegerData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let bit_vec_size = match int {
        MaybeSigned::Signed(i) => i.into(),
        MaybeSigned::Unsigned(u) => u.into(),
    };
    let ty_kind: ty::TyKind = int.into();
    let prim_type = vir::TYPE_INT.upcast_ty();
    let min = builder.vcx.get_min_int(&ty_kind);
    let max = builder.vcx.get_max_int(&ty_kind);
    let value_ident = builder.function("value", builder.self_type(), prim_type);
    builder.axiom("bounds", vir::expr! {
                        forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= (([value_ident](s)) as Int)) && ((([value_ident](s)) as Int) <= ([max]))
                    });
    builder.axiom(
        "value",
        vir::expr! {
            forall value: [prim_type] :: {[cons_ident](value)}
                ((([min]) <= ((value) as Int)) && (((value) as Int) <= ([max])))
                    ==> (([value_ident]([cons_ident](value))) == (value))
        },
    );

    let native = TyPurePrimDataNative {
        snap_to_prim: value_ident,
    };

    let bit_vec = deps.require_dep::<BitVecEnc>(bit_vec_size)?;

    Ok(TyPureIntegerData {
        native,
        bit_vec: vcx.alloc(bit_vec),
    })
}
