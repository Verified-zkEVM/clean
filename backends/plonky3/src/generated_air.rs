//! Generic Plonky3 AIR wrapper for programs extracted from Clean.
//!
//! Generated files provide only component widths and direct expression builders through
//! [`GeneratedAirSpec`]. Trace selectors, lookup registration, and Plonky3 trait plumbing live
//! here so they are implemented and reviewed once.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::lookup::{Direction as LookupDirection, Kind, Lookup};
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder,
    SymbolicExpression, SymbolicVariable,
};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::SymbolicAirBuilder;

/// Shape errors detected before proving or verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnsembleShapeError {
    NoComponents,
    ComponentCount {
        expected: usize,
        trace_heights: usize,
        active_rows: usize,
    },
    ActiveRowsExceedHeight {
        component: usize,
        active_rows: usize,
        trace_height: usize,
    },
    TraceCount {
        airs: usize,
        traces: usize,
    },
    TraceWidth {
        component: usize,
        expected: usize,
        actual: usize,
    },
    TraceHeight {
        component: usize,
        height: usize,
    },
    PublicValueCount {
        expected: usize,
        actual: usize,
    },
    ProofDegreeBits {
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
}

/// One generated symbolic channel interaction before Plonky3 allocates lookup columns.
pub struct GeneratedLookup<F: Field> {
    pub channel: String,
    pub message: Vec<SymbolicExpression<F>>,
    pub multiplicity: SymbolicExpression<F>,
    pub direction: LookupDirection,
}

/// Direct expressions emitted for one Clean ensemble.
pub trait GeneratedAirSpec: Clone + Sync {
    const PUBLIC_VALUES: usize;
    const WIDTHS: &'static [usize];

    fn constraints<AB>(component: usize, local: &[AB::Var]) -> Vec<AB::Expr>
    where
        AB: AirBuilderWithPublicValues,
        AB::F: Field + PrimeCharacteristicRing;

    fn lookups<F: Field>(
        component: usize,
        local: &[SymbolicVariable<F>],
        public_values: &[SymbolicVariable<F>],
        active: SymbolicExpression<F>,
    ) -> Vec<GeneratedLookup<F>>;
}

/// Plonky3 wrapper shared by every generated ensemble AIR.
#[derive(Clone, Debug)]
pub struct GeneratedAir<P> {
    component: usize,
    trace_height: usize,
    active_rows: usize,
    num_lookups: usize,
    _program: PhantomData<P>,
}

impl<P: GeneratedAirSpec> GeneratedAir<P> {
    pub fn all(
        trace_heights: &[usize],
        active_rows: &[usize],
    ) -> Result<Vec<Self>, EnsembleShapeError> {
        let expected = P::WIDTHS.len();
        if trace_heights.len() != expected || active_rows.len() != expected {
            return Err(EnsembleShapeError::ComponentCount {
                expected,
                trace_heights: trace_heights.len(),
                active_rows: active_rows.len(),
            });
        }
        trace_heights
            .iter()
            .copied()
            .zip(active_rows.iter().copied())
            .enumerate()
            .map(|(component, (trace_height, active_rows))| {
                if trace_height == 0 || !trace_height.is_power_of_two() {
                    return Err(EnsembleShapeError::TraceHeight {
                        component,
                        height: trace_height,
                    });
                }
                if active_rows > trace_height {
                    return Err(EnsembleShapeError::ActiveRowsExceedHeight {
                        component,
                        active_rows,
                        trace_height,
                    });
                }
                Ok(Self {
                    component,
                    trace_height,
                    active_rows,
                    num_lookups: 0,
                    _program: PhantomData,
                })
            })
            .collect()
    }
}

/// Static physical trace metadata expected by the verifier.
pub trait EnsembleAir {
    fn trace_height(&self) -> usize;
    fn public_value_count(&self) -> usize;
}

impl<P: GeneratedAirSpec> EnsembleAir for GeneratedAir<P> {
    fn trace_height(&self) -> usize {
        self.trace_height
    }

    fn public_value_count(&self) -> usize {
        P::PUBLIC_VALUES
    }
}

impl<F: Field, P: GeneratedAirSpec> BaseAir<F> for GeneratedAir<P> {
    fn width(&self) -> usize {
        P::WIDTHS[self.component]
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let mut selector = vec![F::ZERO; self.trace_height];
        selector[..self.active_rows].fill(F::ONE);
        Some(RowMajorMatrix::new(selector, 1))
    }
}

impl<AB, P> Air<AB> for GeneratedAir<P>
where
    AB: AirBuilderWithPublicValues,
    AB::F: Field + PrimeCharacteristicRing,
    P: GeneratedAirSpec,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main
            .row_slice(0)
            .expect("validated trace height is nonzero");
        let preprocessed = builder.preprocessed();
        let preprocessed_local = preprocessed
            .as_ref()
            .and_then(|matrix| matrix.row_slice(0))
            .expect("generated AIR always has an active-row selector");
        let active = Into::<AB::Expr>::into(preprocessed_local[0].clone());
        for constraint in P::constraints::<AB>(self.component, &local) {
            builder.assert_zero(active.clone() * constraint);
        }
    }

    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let symbolic = SymbolicAirBuilder::<AB::F>::new(
            1,
            BaseAir::<AB::F>::width(self),
            P::PUBLIC_VALUES,
            0,
            0,
        );
        let main = AirBuilder::main(&symbolic);
        let local = main
            .row_slice(0)
            .expect("validated trace height is nonzero");
        let preprocessed = AirBuilder::preprocessed(&symbolic);
        let preprocessed_local = preprocessed
            .as_ref()
            .and_then(|matrix| matrix.row_slice(0))
            .expect("generated AIR always has an active-row selector");
        let active = SymbolicExpression::<AB::F>::from(preprocessed_local[0]);
        let public_values = AirBuilderWithPublicValues::public_values(&symbolic);
        P::lookups(self.component, &local, public_values, active)
            .into_iter()
            .map(|lookup| {
                Air::<AB>::register_lookup(
                    self,
                    Kind::Global(lookup.channel),
                    &[(lookup.message, lookup.multiplicity, lookup.direction)],
                )
            })
            .collect()
    }

    fn add_lookup_columns(&mut self) -> Vec<usize> {
        let index = self.num_lookups;
        self.num_lookups += 1;
        vec![index]
    }
}
