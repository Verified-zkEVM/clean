//! Generic Plonky3 AIR wrapper for programs extracted from Clean.
//!
//! Generated files provide component shapes and direct expression builders through
//! [`GeneratedAirSpec`], usually implemented by [`crate::ensemble`]. Lookup registration and
//! Plonky3 trait plumbing live here.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::lookup::{Direction as LookupDirection, Kind, Lookup};
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder, SymbolicExpression,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::SymbolicAirBuilder;

use crate::witness_generation::{Interaction, WitnessField};

/// Shape errors detected before proving or verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnsembleShapeError {
    FieldOrder {
        expected: u64,
        actual: u64,
    },
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

/// Direct expressions emitted for one Clean ensemble.
///
/// Constraints and interactions read a complete row: the fixed columns at their input columns, and
/// the committed columns in the others. They are generic over the ring of values, so the same
/// generated functions run on field elements during witness generation and on symbolic expressions
/// here.
pub trait GeneratedAirSpec: Clone + Sync {
    /// Order of the field whose constants and arithmetic the generated code was printed for.
    const FIELD_ORDER: u64;
    const PUBLIC_VALUES: usize;
    /// Committed widths, without the fixed columns.
    const WIDTHS: &'static [usize];
    /// The input columns that are fixed columns, per component, in increasing order.
    const FIXED_COLUMNS: &'static [&'static [usize]];
    const FIXED_HEIGHTS: &'static [usize];
    const INTERACTIONS_PER_ROW: &'static [usize];
    const VERIFIER_INTERACTIONS: usize;

    /// The fixed-column values of one row of a component with fixed columns.
    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F>;

    fn constraints<E: PrimeCharacteristicRing + Clone>(component: usize, row: &[E]) -> Vec<E>;

    fn interactions<E: PrimeCharacteristicRing + Clone>(
        component: usize,
        row: &[E],
    ) -> Vec<Interaction<E>>;

    fn verifier_interactions<F: WitnessField>(public_values: &[F]) -> Vec<Interaction<F>>;
}

/// The complete row of a component: the values of the fixed columns at the input columns
/// `fixed_columns`, which are in increasing order, and the committed values in the other columns.
fn semantic_row<E>(
    fixed_columns: &[usize],
    fixed: impl IntoIterator<Item = E>,
    committed: impl IntoIterator<Item = E>,
) -> Vec<E> {
    let mut fixed_columns = fixed_columns.iter().peekable();
    let mut fixed = fixed.into_iter();
    let mut committed = committed.into_iter();
    let mut row = Vec::new();
    loop {
        let value = if fixed_columns.next_if(|&&column| column == row.len()).is_some() {
            fixed.next()
        } else {
            committed.next()
        };
        let Some(value) = value else {
            return row;
        };
        row.push(value);
    }
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
        if F::ORDER_U64 != P::FIELD_ORDER {
            return Err(EnsembleShapeError::FieldOrder {
                expected: P::FIELD_ORDER,
                actual: F::ORDER_U64,
            });
        }
        let expected = P::WIDTHS.len();
        if expected == 0 {
            return Err(EnsembleShapeError::NoComponents);
        }
        for (metadata, actual) in [
            ("fixed columns", P::FIXED_COLUMNS.len()),
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

impl<F: WitnessField, P: GeneratedAirSpec> BaseAir<F> for GeneratedAir<P> {
    fn width(&self) -> usize {
        P::WIDTHS[self.component]
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let width = P::FIXED_COLUMNS[self.component].len();
        if width == 0 {
            return None;
        }
        let height = P::FIXED_HEIGHTS[self.component];
        let mut values = Vec::with_capacity(height * width);
        for row in 0..height as u64 {
            values.extend(P::fixed_row::<F>(self.component, row));
        }
        Some(RowMajorMatrix::new(values, width))
    }
}

impl<AB, P> Air<AB> for GeneratedAir<P>
where
    AB: AirBuilderWithPublicValues,
    AB::F: WitnessField,
    P: GeneratedAirSpec,
{
    fn eval(&self, builder: &mut AB) {
        let fixed_columns = P::FIXED_COLUMNS[self.component];
        let mut fixed: Vec<AB::Expr> = Vec::new();
        if !fixed_columns.is_empty() {
            let preprocessed = builder
                .preprocessed()
                .expect("fixed component has no preprocessed trace");
            let fixed_local = preprocessed
                .row_slice(0)
                .expect("validated fixed trace height is nonzero");
            fixed.extend(fixed_local.iter().map(|value| value.clone().into()));
        }
        let main = builder.main();
        let local = main
            .row_slice(0)
            .expect("validated trace height is nonzero");
        let committed = local.iter().map(|value| value.clone().into());
        let row = semantic_row(fixed_columns, fixed, committed);
        for constraint in P::constraints(self.component, &row) {
            builder.assert_zero(constraint);
        }
    }

    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>
    where
        AB: PermutationAirBuilder + AirBuilderWithPublicValues,
    {
        self.num_lookups = 0;
        let fixed_columns = P::FIXED_COLUMNS[self.component];
        let symbolic = SymbolicAirBuilder::<AB::F>::new(
            fixed_columns.len(),
            BaseAir::<AB::F>::width(self),
            P::PUBLIC_VALUES,
            0,
            0,
        );
        let mut fixed: Vec<SymbolicExpression<AB::F>> = Vec::new();
        if !fixed_columns.is_empty() {
            let preprocessed = AirBuilder::preprocessed(&symbolic)
                .expect("fixed component has no symbolic preprocessed trace");
            let fixed_local = preprocessed
                .row_slice(0)
                .expect("validated fixed trace height is nonzero");
            fixed.extend(fixed_local.iter().map(|&value| value.into()));
        }
        let main = AirBuilder::main(&symbolic);
        let local = main
            .row_slice(0)
            .expect("validated trace height is nonzero");
        let committed = local.iter().map(|&value| value.into());
        let row = semantic_row(fixed_columns, fixed, committed);
        // an interaction that assumes guarantees pulls from the channel: it is received with the
        // negated multiplicity
        P::interactions(self.component, &row)
            .into_iter()
            .map(|interaction| {
                let (multiplicity, direction) = if interaction.assume_guarantees {
                    (-interaction.multiplicity, LookupDirection::Receive)
                } else {
                    (interaction.multiplicity, LookupDirection::Send)
                };
                Air::<AB>::register_lookup(
                    self,
                    Kind::Global(interaction.channel.into()),
                    &[(interaction.message, multiplicity, direction)],
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

#[cfg(test)]
mod tests {
    use super::semantic_row;
    use alloc::vec;

    #[test]
    fn semantic_row_puts_fixed_values_at_their_columns() {
        assert_eq!(
            semantic_row(&[1, 3, 4], [10, 30, 40], [0, 2, 5]),
            vec![0, 10, 2, 30, 40, 5]
        );
    }
}
