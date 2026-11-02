//! Generic Plonky3 AIR wrapper for programs extracted from Clean.
//!
//! Generated files provide component shapes and direct expression builders through
//! [`GeneratedAirSpec`], usually implemented by [`crate::ensemble`]. Lookup registration and
//! Plonky3 trait plumbing live here.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;

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
    /// The minimum trace height is not a power of two.
    MinimumHeight {
        height: usize,
    },
    /// A trace height is not a power of two of at least the minimum height.
    TraceHeight {
        component: usize,
        height: usize,
    },
    /// A trace height exceeds the largest the PCS supports.
    MaximumTraceHeight {
        log_height: usize,
        log_maximum: usize,
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
    /// The verifier failed to set up the ensemble's preprocessed columns and lookups.
    Setup,
    /// The configuration is zero-knowledge, which the backend doesn't support.
    ZeroKnowledge,
    /// Two interactions on a channel have messages of different widths.
    ChannelWidth {
        channel: &'static str,
        widths: (usize, usize),
    },
    InteractionCountOverflow,
    /// A channel has at least as many interactions as the field order.
    InteractionCountBound {
        channel: &'static str,
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

    /// The fixed-column values of one row of a component with fixed columns.
    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F>;

    fn constraints<E: PrimeCharacteristicRing + Clone>(component: usize, row: &[E]) -> Vec<E>;

    fn interactions<E: PrimeCharacteristicRing + Clone>(
        component: usize,
        row: &[E],
    ) -> Vec<Interaction<E>>;

    fn verifier_interactions<E: PrimeCharacteristicRing + Clone>(
        public_values: &[E],
    ) -> Vec<Interaction<E>>;
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
        let value = if fixed_columns
            .next_if(|&&column| column == row.len())
            .is_some()
        {
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

/// The AIR of one extracted component, or of the verifier's public interactions.
#[derive(Clone, Copy, Debug)]
enum AirKind {
    Component(usize),
    /// A trace of `height` rows that makes the verifier's interactions on its first row, from the
    /// public values.
    Verifier {
        height: usize,
    },
}

/// Plonky3 wrapper shared by every generated ensemble AIR.
#[derive(Clone, Debug)]
pub struct GeneratedAir<P> {
    kind: AirKind,
    _program: PhantomData<P>,
}

impl<P> GeneratedAir<P> {
    const fn new(kind: AirKind) -> Self {
        Self {
            kind,
            _program: PhantomData,
        }
    }
}

/// A complete generated Clean statement with its AIR components in canonical order.
///
/// The component AIRs are private so callers cannot omit, duplicate, or reorder them. Only
/// non-empty components have an AIR, and they are followed by the verifier AIR. Construction also checks that every channel has fewer interactions
/// than the field order, the bound of Clean's LogUp balance check, and one message width.
#[derive(Clone, Debug)]
pub struct GeneratedEnsemble<F, P> {
    airs: Vec<GeneratedAir<P>>,
    trace_heights: Vec<usize>,
    interaction_counts: BTreeMap<&'static str, u128>,
    _field: PhantomData<F>,
}

impl<F: WitnessField, P: GeneratedAirSpec> GeneratedEnsemble<F, P> {
    /// The statement with these component trace heights. The verifier AIR has `minimum_height`
    /// rows, the smallest trace height the proof configuration accepts, which every non-empty
    /// component trace height must reach. Only demand-generated components may be empty.
    pub fn new(trace_heights: &[usize], minimum_height: usize) -> Result<Self, EnsembleShapeError> {
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
        ] {
            if actual != expected {
                return Err(EnsembleShapeError::MetadataCount {
                    metadata,
                    expected,
                    actual,
                });
            }
        }
        if !minimum_height.is_power_of_two() {
            return Err(EnsembleShapeError::MinimumHeight {
                height: minimum_height,
            });
        }
        if trace_heights.len() != expected {
            return Err(EnsembleShapeError::ComponentCount {
                expected,
                trace_heights: trace_heights.len(),
            });
        }
        let mut airs = Vec::new();
        for (component, &trace_height) in trace_heights.iter().enumerate() {
            let fixed_height = P::FIXED_HEIGHTS[component];
            // a demand-generated table may be empty, and then has no AIR
            if trace_height == 0 && fixed_height == 0 {
                continue;
            }
            if !trace_height.is_power_of_two() || trace_height < minimum_height {
                return Err(EnsembleShapeError::TraceHeight {
                    component,
                    height: trace_height,
                });
            }
            if fixed_height != 0 && fixed_height != trace_height {
                return Err(EnsembleShapeError::FixedTraceHeight {
                    component,
                    expected: fixed_height,
                    actual: trace_height,
                });
            }
            airs.push(GeneratedAir::new(AirKind::Component(component)));
        }
        airs.push(GeneratedAir::new(AirKind::Verifier {
            height: minimum_height,
        }));

        // The generated interaction functions return the same interactions for every row, up to
        // their values, so evaluating them on zeros shows their channels and message widths.
        let verifier_interactions = P::verifier_interactions(&vec![F::ZERO; P::PUBLIC_VALUES]);
        let component_interactions = (0..expected)
            .map(|component| {
                let width = P::WIDTHS[component] + P::FIXED_COLUMNS[component].len();
                P::interactions(component, &vec![F::ZERO; width])
            })
            .collect::<Vec<_>>();
        let mut channel_widths = BTreeMap::new();
        for interaction in verifier_interactions
            .iter()
            .chain(component_interactions.iter().flatten())
        {
            let width = *channel_widths
                .entry(interaction.channel)
                .or_insert(interaction.message.len());
            if width != interaction.message.len() {
                return Err(EnsembleShapeError::ChannelWidth {
                    channel: interaction.channel,
                    widths: (width, interaction.message.len()),
                });
            }
        }
        // Each channel has the verifier's interactions with it, and those of every row of every
        // component, which the balance check is sound for while fewer than the field order.
        let mut interaction_counts = BTreeMap::<&'static str, u128>::new();
        let rows = core::iter::once(1)
            .chain(trace_heights.iter().copied())
            .zip(core::iter::once(&verifier_interactions).chain(&component_interactions));
        for (height, interactions) in rows {
            for interaction in interactions {
                let count = interaction_counts.entry(interaction.channel).or_insert(0);
                *count = count
                    .checked_add(height as u128)
                    .ok_or(EnsembleShapeError::InteractionCountOverflow)?;
            }
        }
        for (&channel, &interactions) in &interaction_counts {
            if interactions >= F::ORDER_U64 as u128 {
                return Err(EnsembleShapeError::InteractionCountBound {
                    channel,
                    interactions,
                    field_order: F::ORDER_U64,
                });
            }
        }

        Ok(Self {
            airs,
            trace_heights: trace_heights.to_vec(),
            interaction_counts,
            _field: PhantomData,
        })
    }

    pub fn trace_heights(&self) -> &[usize] {
        &self.trace_heights
    }

    pub fn component_count(&self) -> usize {
        self.trace_heights.len()
    }

    /// The number of interactions with each channel, by name.
    pub fn interaction_counts(&self) -> &BTreeMap<&'static str, u128> {
        &self.interaction_counts
    }

    /// The AIRs of the non-empty components followed by the verifier AIR.
    pub(crate) fn airs(&self) -> &[GeneratedAir<P>] {
        &self.airs
    }

    /// The trace heights of `airs`: those of the non-empty components, then the verifier's.
    pub(crate) fn air_heights(&self) -> Vec<usize> {
        self.trace_heights
            .iter()
            .copied()
            .filter(|&height| height != 0)
            .chain([self.verifier_height()])
            .collect()
    }

    /// The height of the verifier AIR's trace.
    pub(crate) fn verifier_height(&self) -> usize {
        match self.airs.last().map(|air| air.kind) {
            Some(AirKind::Verifier { height }) => height,
            _ => unreachable!("the verifier AIR is the last AIR"),
        }
    }
}

impl<F: WitnessField, P: GeneratedAirSpec> BaseAir<F> for GeneratedAir<P> {
    fn width(&self) -> usize {
        match self.kind {
            AirKind::Component(component) => P::WIDTHS[component],
            AirKind::Verifier { .. } => 1,
        }
    }

    fn num_public_values(&self) -> usize {
        match self.kind {
            AirKind::Component(_) => 0,
            AirKind::Verifier { .. } => P::PUBLIC_VALUES,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self.kind {
            AirKind::Component(component) => P::FIXED_COLUMNS[component].len(),
            AirKind::Verifier { .. } => 1,
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self.kind {
            AirKind::Component(component) => {
                let width = P::FIXED_COLUMNS[component].len();
                if width == 0 {
                    return None;
                }
                let height = P::FIXED_HEIGHTS[component];
                let mut values = Vec::with_capacity(height * width);
                for row in 0..height as u64 {
                    values.extend(P::fixed_row::<F>(component, row));
                }
                Some(RowMajorMatrix::new(values, width))
            }
            // the selector of the first row
            AirKind::Verifier { height } => {
                let mut values = vec![F::ZERO; height];
                values[0] = F::ONE;
                Some(RowMajorMatrix::new(values, 1))
            }
        }
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        Vec::new()
    }
}

impl<AB, P> Air<AB> for GeneratedAir<P>
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: WitnessField,
    P: GeneratedAirSpec,
{
    fn eval(&self, builder: &mut AB) {
        // Clean's LogUp balance check is over field multiplicities: every interaction is provided,
        // with the signed multiplicity of its push or pull, and the interaction-count bound of
        // `GeneratedEnsemble::new` replaces LogUp's height check.
        let interactions = match self.kind {
            AirKind::Component(component) => {
                let preprocessed = builder.preprocessed().current_slice().to_vec();
                let fixed = preprocessed.into_iter().map(Into::into);
                let main = builder.main();
                let committed = main.current_slice().iter().map(|&value| value.into());
                let row = semantic_row(P::FIXED_COLUMNS[component], fixed, committed);
                for constraint in P::constraints(component, &row) {
                    builder.assert_zero(constraint);
                }
                P::interactions(component, &row)
            }
            AirKind::Verifier { .. } => {
                let first_row: AB::Expr = builder.preprocessed().current_slice()[0].into();
                let public_values = builder
                    .public_values()
                    .iter()
                    .map(|&value| value.into())
                    .collect::<Vec<AB::Expr>>();
                P::verifier_interactions(&public_values)
                    .into_iter()
                    .map(|interaction| Interaction {
                        multiplicity: first_row.clone() * interaction.multiplicity,
                        ..interaction
                    })
                    .collect()
            }
        };
        for interaction in interactions {
            let multiplicity = interaction.signed_multiplicity();
            builder.push_interaction(
                interaction.channel,
                interaction.message,
                Count::provided(multiplicity),
            );
        }
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
