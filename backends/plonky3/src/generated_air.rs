//! Generic Plonky3 AIR wrapper for programs extracted from Clean.
//!
//! Generated files provide only component widths and direct expression builders through
//! [`GeneratedAirSpec`]. Lookup registration and Plonky3 trait plumbing live here so they are
//! implemented and reviewed once.

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

use crate::witness_generation::{Interaction, WitnessField};

/// Shape errors detected before proving or verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnsembleShapeError {
    NoComponents,
    MetadataCount {
        metadata: &'static str,
        expected: usize,
        actual: usize,
    },
    ComponentCount {
        expected: usize,
        trace_heights: usize,
    },
    TraceCount {
        expected: usize,
        actual: usize,
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
    StatementTraceHeight {
        component: usize,
        expected: usize,
        actual: usize,
    },
    FixedTraceHeight {
        component: usize,
        expected: usize,
        actual: usize,
    },
    PublicValueCount {
        expected: usize,
        actual: usize,
    },
    ProofDegreeBits {
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    InteractionCountOverflow,
    InteractionCountBound {
        interactions: u128,
        field_order: u64,
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
    const FIXED_WIDTHS: &'static [usize];
    const FIXED_HEIGHTS: &'static [usize];
    const INTERACTIONS_PER_ROW: &'static [usize];
    const VERIFIER_INTERACTIONS: usize;

    fn fixed_trace<F: Field + PrimeCharacteristicRing>(
        component: usize,
    ) -> Option<RowMajorMatrix<F>>;

    fn constraints<AB>(component: usize, fixed: &[AB::Var], local: &[AB::Var]) -> Vec<AB::Expr>
    where
        AB: AirBuilderWithPublicValues,
        AB::F: Field + PrimeCharacteristicRing;

    fn lookups<F: Field>(
        component: usize,
        fixed: &[SymbolicVariable<F>],
        local: &[SymbolicVariable<F>],
    ) -> Vec<GeneratedLookup<F>>;

    fn verifier_interactions<F: WitnessField>(public_values: &[F]) -> Vec<Interaction<F>>;
}

/// Plonky3 wrapper shared by every generated ensemble AIR.
#[derive(Clone, Debug)]
pub struct GeneratedAir<P> {
    component: usize,
    num_lookups: usize,
    _program: PhantomData<P>,
}

/// A complete generated Clean statement with its AIR components in canonical order.
///
/// The component AIRs are private so callers cannot omit, duplicate, or reorder them. Construction
/// also establishes the interaction-count side condition required by Clean's channel semantics.
#[derive(Clone, Debug)]
pub struct GeneratedEnsemble<F, P> {
    airs: Vec<GeneratedAir<P>>,
    trace_heights: Vec<usize>,
    interaction_count: u128,
    _field: PhantomData<F>,
}

impl<F: WitnessField, P: GeneratedAirSpec> GeneratedEnsemble<F, P> {
    pub fn new(trace_heights: &[usize]) -> Result<Self, EnsembleShapeError> {
        let expected = P::WIDTHS.len();
        if expected == 0 {
            return Err(EnsembleShapeError::NoComponents);
        }
        for (metadata, actual) in [
            ("fixed widths", P::FIXED_WIDTHS.len()),
            ("fixed heights", P::FIXED_HEIGHTS.len()),
            ("interactions per row", P::INTERACTIONS_PER_ROW.len()),
        ] {
            if actual != expected {
                return Err(EnsembleShapeError::MetadataCount {
                    metadata,
                    expected,
                    actual,
                });
            }
        }
        if trace_heights.len() != expected {
            return Err(EnsembleShapeError::ComponentCount {
                expected,
                trace_heights: trace_heights.len(),
            });
        }
        let airs = trace_heights
            .iter()
            .copied()
            .enumerate()
            .map(|(component, trace_height)| {
                if trace_height == 0 || !trace_height.is_power_of_two() {
                    return Err(EnsembleShapeError::TraceHeight {
                        component,
                        height: trace_height,
                    });
                }
                let fixed_height = P::FIXED_HEIGHTS[component];
                if fixed_height != 0 && fixed_height != trace_height {
                    return Err(EnsembleShapeError::FixedTraceHeight {
                        component,
                        expected: fixed_height,
                        actual: trace_height,
                    });
                }
                Ok(GeneratedAir {
                    component,
                    num_lookups: 0,
                    _program: PhantomData,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let interactions = trace_heights
            .iter()
            .copied()
            .zip(P::INTERACTIONS_PER_ROW.iter().copied())
            .try_fold(
                P::VERIFIER_INTERACTIONS as u128,
                |total, (height, per_row)| {
                    let component = (height as u128)
                        .checked_mul(per_row as u128)
                        .ok_or(EnsembleShapeError::InteractionCountOverflow)?;
                    total
                        .checked_add(component)
                        .ok_or(EnsembleShapeError::InteractionCountOverflow)
                },
            )?;
        if interactions >= F::ORDER_U64 as u128 {
            return Err(EnsembleShapeError::InteractionCountBound {
                interactions,
                field_order: F::ORDER_U64,
            });
        }

        Ok(Self {
            airs,
            trace_heights: trace_heights.to_vec(),
            interaction_count: interactions,
            _field: PhantomData,
        })
    }

    pub fn trace_heights(&self) -> &[usize] {
        &self.trace_heights
    }

    pub fn component_count(&self) -> usize {
        self.airs.len()
    }

    pub fn interaction_count(&self) -> u128 {
        self.interaction_count
    }

    pub(crate) fn airs(&self) -> &[GeneratedAir<P>] {
        &self.airs
    }
}

impl<F: Field, P: GeneratedAirSpec> BaseAir<F> for GeneratedAir<P> {
    fn width(&self) -> usize {
        P::WIDTHS[self.component]
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        P::fixed_trace(self.component)
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
        let constraints = if P::FIXED_WIDTHS[self.component] == 0 {
            P::constraints::<AB>(self.component, &[], &local)
        } else {
            match builder.preprocessed() {
                Some(fixed) => {
                    let fixed_local = fixed
                        .row_slice(0)
                        .expect("validated fixed trace height is nonzero");
                    P::constraints::<AB>(self.component, &fixed_local, &local)
                }
                None => unreachable!("fixed component has no preprocessed trace"),
            }
        };
        for constraint in constraints {
            builder.assert_zero(constraint);
        }
    }

    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let symbolic = SymbolicAirBuilder::<AB::F>::new(
            P::FIXED_WIDTHS[self.component],
            BaseAir::<AB::F>::width(self),
            P::PUBLIC_VALUES,
            0,
            0,
        );
        let main = AirBuilder::main(&symbolic);
        let local = main
            .row_slice(0)
            .expect("validated trace height is nonzero");
        let lookups = if P::FIXED_WIDTHS[self.component] == 0 {
            P::lookups(self.component, &[], &local)
        } else {
            match AirBuilder::preprocessed(&symbolic) {
                Some(fixed) => {
                    let fixed_local = fixed
                        .row_slice(0)
                        .expect("validated fixed trace height is nonzero");
                    P::lookups(self.component, &fixed_local, &local)
                }
                None => unreachable!("fixed component has no symbolic preprocessed trace"),
            }
        };
        lookups
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
