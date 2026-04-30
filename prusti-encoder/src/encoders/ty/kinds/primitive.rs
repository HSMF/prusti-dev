use crate::encoders::ty::{
    RustPrimitive,
    impure::{PredicateBuilder, TyImpureEnc, TyImpurePrimitive},
    interpretation::{
        bitvec::{BitVecEnc, BitVecSize},
        float::ty_pure_float,
    },
    pure::{
        TyPureBuilder, TyPureEnc, TyPurePrimData, TyPurePrimDataBitVec, TyPurePrimDataKind,
        TyPurePrimDataNative, TyPurePrimitive,
    },
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, VirCtxt};

pub(crate) fn ty_pure<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    data: &RustPrimitive<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut TyPureBuilder<'vir>,
) -> Result<TyPurePrimitive<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data;
    let ty_kind = ty.kind();

    let prim_type: vir::TypePrim<'vir> = match ty_kind {
        ty::TyKind::Bool => vir::TYPE_BOOL.upcast_ty(),
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::TYPE_INT.upcast_ty(),
        ty::TyKind::Float(_) => vir::TYPE_INT.upcast_ty(),
        _ => unreachable!(),
    };

    match ty_kind {
        ty::TyKind::Float(float) => {
            let builder = builder.set_domain_builder();
            let cons_ident = builder.function("cons", prim_type, builder.self_type());
            let data = ty_pure_float(vcx, deps, builder, *float, cons_ident)?;
            Ok(TyPurePrimData {
                prim_type,
                prim_to_snap: cons_ident,
                kind: TyPurePrimDataKind::Float(vcx.alloc(data)),
            })
        }
        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
            let builder = builder.set_adt_builder();
            let bit_vec_size = match ty_kind {
                ty::TyKind::Int(kind) => (*kind).into(),
                ty::TyKind::Uint(kind) => (*kind).into(),
                ty::TyKind::Bool => BitVecSize::BitVec8,
                k => todo!("not int {k:?}"),
            };
            let bit_vec = deps.require_dep::<BitVecEnc>(bit_vec_size)?;
            let bit_vec_type = (bit_vec.domain)();
            let (cons_bv, destructor) = builder.constructor::<vir::CSnap>("", bit_vec_type, None);

            let int = vir::TYPE_INT.upcast_ty();
            let arg_decl = vcx.mk_local_decl("arg1", int);
            let arg = vcx.mk_local_ex(arg_decl);
            let cons_ident = builder.function(
                "cons_prim",
                int,
                builder.self_type(),
                (arg_decl,),
                &[],
                &[],
                Some(cons_bv((bit_vec.from_int)(arg))),
            );

            Ok(TyPurePrimData {
                prim_type,
                prim_to_snap: cons_ident,
                kind: TyPurePrimDataKind::BitVec(TyPurePrimDataBitVec {
                    bit_vec: vcx.alloc(bit_vec),
                    value: destructor.first().unwrap().downcast_ty(),
                    cons: vcx.alloc(cons_bv),
                }),
            })
        }
        _ => {
            let builder = builder.set_domain_builder();
            let cons_ident = builder.function("cons", prim_type, builder.self_type());
            let value_ident = builder.function("value", builder.self_type(), prim_type);

            builder.axiom("cons", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
            });

            builder.axiom("value", vir::expr! {
                        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
                    });

            Ok(TyPurePrimData {
                prim_type,
                prim_to_snap: cons_ident,
                kind: TyPurePrimDataKind::Native(TyPurePrimDataNative {
                    snap_to_prim: value_ident,
                }),
            })
        }
    }
}

pub(crate) fn ty_impure<'vir>(
    _data: &(&RustPrimitive<'vir>, &TyPurePrimitive<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpurePrimitive<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    // let ty = data.ty();
    // let ty_kind = ty.kind();

    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let prim_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate("", Some(vir::expr! { acc((ref_self).[prim_field]) }));

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [prim_field](ref_self) }));

    Ok(())
}
