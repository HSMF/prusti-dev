use task_encoder::{OutputRefAny, TaskEncoder};
use vir::{
    Arity, BackendInterpretationPair, CastType, CompType, DomainFunctionData, DomainGenData,
    DomainIdnCSnap, FunctionIdn, Type, VirCtxt,
};

use crate::encoders::ty::{RustTy, pure::TyPureEnc};

#[derive(Eq, PartialEq, Hash, Debug, Clone, Copy)]
pub enum BitVecSize {
    BitVec8,
    BitVec16,
    BitVec32,
    BitVec64,
    BitVec128,
}

impl BitVecSize {
    fn from_int(i: u64) -> BitVecSize {
        match i {
            8 => Self::BitVec8,
            16 => Self::BitVec16,
            32 => Self::BitVec32,
            64 => Self::BitVec64,
            128 => Self::BitVec128,
            _ => panic!("illegal bit width {i}"),
        }
    }
}

impl From<prusti_rustc_interface::middle::ty::IntTy> for BitVecSize {
    fn from(value: prusti_rustc_interface::middle::ty::IntTy) -> Self {
        Self::from_int(
            value
                .bit_width()
                .unwrap_or((std::mem::size_of::<isize>() * 8) as u64),
        )
    }
}

impl From<prusti_rustc_interface::middle::ty::UintTy> for BitVecSize {
    fn from(value: prusti_rustc_interface::middle::ty::UintTy) -> Self {
        Self::from_int(
            value
                .bit_width()
                .unwrap_or((std::mem::size_of::<usize>() * 8) as u64),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct BitVecDomain<'vir> {
    pub domain: vir::DomainIdn<'vir, vir::CSnap>,
    pub from_int: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    pub to_int: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
    pub shl: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub shr: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bit_not: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub bit_or: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bit_and: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
}

#[derive(Debug, Clone, Copy)]
pub struct BitVecConversion<'vir> {
    pub from_int: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub to_int: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
}

impl OutputRefAny for BitVecConversion<'_> {}

pub struct BitVecEnc;

// TODO: can we really not use `DomainBuilder`?
struct Builder<'vir> {
    domain_name: &'static str,
    vcx: &'vir VirCtxt<'vir>,
    functions: Vec<&'vir DomainFunctionData<'vir>>,
}

impl<'vir> Builder<'vir> {
    // TODO: instead of returning the function data, push it into a internal (small) vec
    fn backend_func<A: Arity, T: CompType>(
        &mut self,
        name: &str,
        args: A::Tys<'vir>,
        ret: Type<'vir, T>,
        interpretation: &'static str,
    ) -> FunctionIdn<'vir, A, T> {
        let name = vir::vir_format!(self.vcx, "{}_{name}", self.domain_name);
        let ident = FunctionIdn::new(vir::ViperIdent::new(name), args, ret);
        let function = self
            .vcx
            .mk_domain_function(ident, false, Some(interpretation));
        self.functions.push(function);
        ident
    }
}

impl TaskEncoder for BitVecEnc {
    task_encoder::encoder_cache!(BitVecEnc);

    type TaskDescription<'vir> = BitVecSize;

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = BitVecDomain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in BitVecEnc::all_outputs_local_no_errors() {
            program.add_domain(output);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let domain_name = match *task_key {
                BitVecSize::BitVec8 => "s_BitVec_8",
                BitVecSize::BitVec16 => "s_BitVec_16",
                BitVecSize::BitVec32 => "s_BitVec_32",
                BitVecSize::BitVec64 => "s_BitVec_64",
                BitVecSize::BitVec128 => "s_BitVec_128",
            };

            let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name), 0);

            let self_type = domain_ident();

            let mut builder = Builder {
                domain_name,
                vcx,
                functions: vec![],
            };
            let from_int = builder.backend_func(
                "from_int",
                vir::TYPE_INT.upcast_ty(),
                self_type,
                match *task_key {
                    BitVecSize::BitVec8 => "(_ int2bv 8)",
                    BitVecSize::BitVec16 => "(_ int2bv 16)",
                    BitVecSize::BitVec32 => "(_ int2bv 32)",
                    BitVecSize::BitVec64 => "(_ int2bv 64)",
                    BitVecSize::BitVec128 => "(_ int2bv 128)",
                },
            );
            let to_int = builder.backend_func(
                "to_int",
                self_type,
                vir::TYPE_INT.upcast_ty(),
                match *task_key {
                    BitVecSize::BitVec8 => "(_ bv2int 8)",
                    BitVecSize::BitVec16 => "(_ bv2int 16)",
                    BitVecSize::BitVec32 => "(_ bv2int 32)",
                    BitVecSize::BitVec64 => "(_ bv2int 64)",
                    BitVecSize::BitVec128 => "(_ bv2int 128)",
                },
            );
            let shl = builder.backend_func("shl", (self_type, self_type), self_type, "bvshl");

            let shr = builder.backend_func("shr", (self_type, self_type), self_type, "bvlshr");
            let bit_or = builder.backend_func("bit_or", (self_type, self_type), self_type, "bvor");
            let bit_and =
                builder.backend_func("bit_and", (self_type, self_type), self_type, "bvand");

            let bit_not = builder.backend_func("bit_not", self_type, self_type, "bvnot");

            let functions = &builder.functions;

            macro_rules! backend_pair {
                ($size:literal) => {
                    Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: concat!("(_ BitVec ", stringify!($size), ")"),
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: concat!("bv", stringify!($size)),
                        }),
                    ]))
                };
            }

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(functions),
                match *task_key {
                    BitVecSize::BitVec8 => backend_pair!(8),
                    BitVecSize::BitVec16 => backend_pair!(16),
                    BitVecSize::BitVec32 => backend_pair!(32),
                    BitVecSize::BitVec64 => backend_pair!(64),
                    BitVecSize::BitVec128 => backend_pair!(128),
                },
            );

            deps.emit_output_ref(*task_key, ())?;
            Ok((
                domain_data,
                BitVecDomain {
                    domain: domain_ident,
                    from_int,
                    to_int,
                    shl,
                    shr,
                    bit_not,
                    bit_or,
                    bit_and,
                },
            ))
        })
    }
}

pub struct BitVecConversionEnc;

impl TaskEncoder for BitVecConversionEnc {
    task_encoder::encoder_cache!(BitVecConversionEnc);

    /// bitvec type, rust type
    type TaskDescription<'vir> = (BitVecSize, RustTy<'vir>);

    type TaskKey<'vir> = Self::TaskDescription<'vir>;

    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;

    type OutputRef<'vir> = BitVecConversion<'vir>;

    type EncodingError = !;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let pure = deps.require_dep::<TyPureEnc>(task_key.1)?;
        let bit_vec = deps.require_dep::<BitVecEnc>(task_key.0)?;

        vir::with_vcx(|vcx| {
            let to_prim = pure.expect_native().snap_to_prim;
            let from_prim = pure.expect_primitive().prim_to_snap;

            let bv2int = bit_vec.to_int;
            // let int2bv = bit_vec.from_int;

            let int_ty = (pure.domain)().downcast_ty::<vir::CSnap>();
            let bv_ty = (bit_vec.domain)();

            let (to_bv, to_bv_data) = {
                let name = vir::vir_format_identifier!(
                    vcx,
                    "{}_to_{}",
                    pure.domain.name(),
                    bit_vec.domain.name()
                );
                let to_bv = FunctionIdn::<vir::CSnap, _>::new(name, int_ty, bv_ty);
                let arg = vcx.mk_local_decl("arg", int_ty);
                let result = vcx.mk_result(bv_ty);
                // bv2int(to_bv(x)) = bv2int(int2bv(to_prim(arg))) = to_prim(arg)
                let post = vir::expr!(([to_prim](arg)) == ([bv2int](result)));
                (
                    to_bv,
                    vcx.mk_function::<_, _, _, vir::CSnap>(
                        to_bv,
                        (arg,),
                        &[],
                        vcx.alloc_slice(&[post]),
                        None,
                        None,
                    ),
                )
            };

            let (from_bv, from_bv_data) = {
                let name = vir::vir_format_identifier!(
                    vcx,
                    "{}_from_{}",
                    pure.domain.name(),
                    bit_vec.domain.name()
                );
                let from_bv = FunctionIdn::<vir::CSnap, _>::new(name, bv_ty, int_ty);
                let arg = vcx.mk_local_decl("arg", bv_ty);
                let val = vir::expr! {
                    [from_prim]([bv2int](arg))
                };
                (
                    from_bv,
                    vcx.mk_function(from_bv, (arg,), &[], &[], None, Some(val)),
                )
            };

            let conv = BitVecConversion {
                from_int: to_bv,
                to_int: from_bv,
            };
            deps.emit_output_ref(*task_key, conv)?;

            Ok((vec![to_bv_data, from_bv_data], ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in BitVecConversionEnc::all_outputs_local_no_errors()
            .iter()
            .flatten()
        {
            program.add_function(output);
        }
    }
}
