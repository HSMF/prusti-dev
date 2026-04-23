use crate::encoders::ty::{
    RustPrimitive,
    impure::{PredicateBuilder, TyImpureEnc, TyImpurePrimitive},
    interpretation::{
        bitvec::{BitVecEnc, BitVecSize},
        float::ty_pure_float,
    },
    pure::{
        DomainBuilder, TyPureEnc, TyPurePrimData, TyPurePrimDataKind, TyPurePrimDataNative,
        TyPurePrimitive,
    },
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, VirCtxt};

pub(crate) fn ty_pure<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    data: &RustPrimitive<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<TyPurePrimitive<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data;
    let ty_kind = ty.kind();

    let prim_type: vir::TypePrim<'vir> = match ty_kind {
        ty::TyKind::Bool => vir::TYPE_BOOL.upcast_ty(),
        ty::TyKind::Char | ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::TYPE_INT.upcast_ty(),
        ty::TyKind::Float(_) => vir::TYPE_INT.upcast_ty(),
        _ => unreachable!(),
    };

    let cons_ident = builder.function("cons", prim_type, builder.self_type());

    let kind = match ty_kind {
        ty::TyKind::Float(float) => {
            let data = ty_pure_float(vcx, deps, builder, *float, cons_ident)?;
            TyPurePrimDataKind::Float(vcx.alloc(data))
        }
        _ => {
            let bit_vec_size = match ty_kind {
                ty::TyKind::Int(kind) => (*kind).into(),
                ty::TyKind::Uint(kind) => (*kind).into(),
                ty::TyKind::Bool => BitVecSize::BitVec8,
                k => todo!("not int {k:?}"),
            };

            let bit_vec = deps.require_dep::<BitVecEnc>(bit_vec_size)?;
            let bit_vec_type = (bit_vec.domain)();

            let value_ident = builder.function("value", builder.self_type(), prim_type);
            let snap_to_bitvec =
                builder.function("value_bitvec", builder.self_type(), bit_vec_type);
            let bitvec_to_snap = builder.function("cons_bitvec", bit_vec_type, builder.self_type());

            builder.axiom("cons", vir::expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
            });

            match ty_kind {
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => {
                    let min = builder.vcx.get_min_int(ty_kind);
                    let max = builder.vcx.get_max_int(ty_kind);
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
                    // bv.to_int(snap_to_bitvec(x)) == snap_to_prim(x)
                    builder.axiom(
                        "bitvec_value",
                        vir::expr! {
                            forall arg: [builder.self_type()] :: { [snap_to_bitvec](arg) }
                                ( [snap_to_bitvec](arg) ) == ( [bit_vec.from_int]( [value_ident](arg) ) )
                                // ( [bit_vec.to_int]([snap_to_bitvec](arg)) ) == ( [value_ident](arg) )
                                // (
                                //     [bit_vec.to_int]( [snap_to_bitvec](arg) )
                                //     == ([snap_to_prim](arg))
                                //     )
                        },
                    );
                    let bv_less = if matches!(ty_kind, ty::TyKind::Int(_)) {
                        bit_vec.less_eq_signed
                    } else {
                        bit_vec.less_eq_unsigned
                    };

                    let min: &vir::ExprGenData<'_, (), !, vir::Prim> = min.upcast_ty();
                    let max: &vir::ExprGenData<'_, (), !, vir::Prim> = max.upcast_ty();

                    builder.axiom(
                        "bitvec_cons",
                        vir::expr! {
                            forall value: [bit_vec_type] :: { [bitvec_to_snap](value) }
                            (
                                ([bv_less]( ([bit_vec.from_int]( min )), value ))
                                &&
                                ([bv_less]( value, ([bit_vec.from_int]( max )) ))
                            ) ==>
                                // (([bitvec_to_snap](value)) == ( [cons_ident]( [bit_vec.to_int](value) ) )
                                ( ( [snap_to_bitvec]( [bitvec_to_snap]( value ) ) ) == ( value ) )
                        },
                    );
                    builder.axiom(
                        "bounds_bv",
                        vir::expr! {
                            forall s: [builder.self_type()] :: { [snap_to_bitvec](s) }

                            ([bv_less]( ([bit_vec.from_int]( min )), ([snap_to_bitvec](s)) ))
                                &&
                            ([bv_less]( ([snap_to_bitvec](s)), ([bit_vec.from_int]( max )) ))
                        },
                    );
                    //  (forall s: s_Int_i64 ::
                    // { s_Int_i64_value_bitvec(s) }
                    // s_BitVec_64_bvsle(s_BitVec_64_from_int(-9223372036854775808), s_Int_i64_value_bitvec(s)) &&
                    // s_BitVec_64_bvsle(s_Int_i64_value_bitvec(s), s_BitVec_64_from_int(9223372036854775807)))
                }
                _ => {
                    builder.axiom("value", vir::expr! {
                        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
                    });
                }
            };
            TyPurePrimDataKind::Native(TyPurePrimDataNative {
                snap_to_prim: value_ident,
                snap_to_bitvec,
                bitvec_to_snap,
            })
        }
    };
    Ok(TyPurePrimData {
        prim_type,
        prim_to_snap: cons_ident,
        kind,
    })
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
