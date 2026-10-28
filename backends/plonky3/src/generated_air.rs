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

use crate::witness_generation::{Constraint, Gate, Interaction, WitnessField};

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
    InteractionCountBound {
        interactions: u128,
        field_order: u64,
    },
}

/// Direct expressions emitted for one Clean ensemble.
///
/// Constraints and interactions read a complete row: the fixed columns at their input columns, the
/// window cells of a two-row component, the next row's own input and three selector cells, after
/// the row's own input, and the committed columns in the others. They are generic over the ring of
/// values, so the same generated functions run on field elements during witness generation and on
/// symbolic expressions here. Constraint bodies and interactions never read the selector cells: a
/// constraint that reads a selector is gated by it instead.
pub trait GeneratedAirSpec: Clone + Sync {
    /// Order of the field whose constants and arithmetic the generated code was printed for.
    const FIELD_ORDER: u64;
    const PUBLIC_VALUES: usize;
    /// Committed widths, without the fixed columns.
    const WIDTHS: &'static [usize];
    /// The input columns that are fixed columns, per component, in increasing order.
    const FIXED_COLUMNS: &'static [&'static [usize]];
    const FIXED_HEIGHTS: &'static [usize];
    /// The own-input width of each two-row component.
    const WINDOWS: &'static [Option<usize>];

    /// The fixed-column values of one row of a component with fixed columns.
    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F>;

    fn constraints<E: PrimeCharacteristicRing + Clone>(
        component: usize,
        row: &[E],
    ) -> Vec<Constraint<E>>;

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

/// The complete row of a two-row component whose own input has width `width`, from the row without
/// its window cells: the next row's own input and three zero selector cells are inserted after the
/// row's own input.
fn window_row<E: PrimeCharacteristicRing + Clone>(
    window: Option<usize>,
    mut row: Vec<E>,
    next: impl FnOnce() -> Vec<E>,
) -> Vec<E> {
    let Some(width) = window else {
        return row;
    };
    let next = next();
    let rest = row.split_off(width);
    row.extend_from_slice(&next[..width]);
    row.extend([E::ZERO, E::ZERO, E::ZERO]);
    row.extend(rest);
    row
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
/// The component AIRs are private so callers cannot omit, duplicate, or reorder them. They are
/// followed by the verifier AIR. Construction also establishes the interaction-count side condition
/// required by Clean's channel semantics, and that every channel has one message width.
#[derive(Clone, Debug)]
pub struct GeneratedEnsemble<F, P> {
    airs: Vec<GeneratedAir<P>>,
    trace_heights: Vec<usize>,
    interaction_count: u128,
    _field: PhantomData<F>,
}

impl<F: WitnessField, P: GeneratedAirSpec> GeneratedEnsemble<F, P> {
    /// The statement with these component trace heights. The verifier AIR has `minimum_height`
    /// rows, the smallest trace height the proof configuration accepts, which every component trace
    /// height must reach.
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
            ("windows", P::WINDOWS.len()),
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
        let mut airs = trace_heights
            .iter()
            .copied()
            .enumerate()
            .map(|(component, trace_height)| {
                if !trace_height.is_power_of_two() || trace_height < minimum_height {
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
                Ok(GeneratedAir::new(AirKind::Component(component)))
            })
            .collect::<Result<Vec<_>, _>>()?;
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
        let interactions = trace_heights.iter().zip(&component_interactions).try_fold(
            verifier_interactions.len() as u128,
            |total, (&height, interactions)| {
                let component = (height as u128)
                    .checked_mul(interactions.len() as u128)
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
        self.trace_heights.len()
    }

    pub fn interaction_count(&self) -> u128 {
        self.interaction_count
    }

    /// The component AIRs followed by the verifier AIR.
    pub(crate) fn airs(&self) -> &[GeneratedAir<P>] {
        &self.airs
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
        match self.kind {
            AirKind::Component(component) if P::WINDOWS[component].is_some() => {
                (0..P::WIDTHS[component]).collect()
            }
            _ => Vec::new(),
        }
    }

    fn preprocessed_next_row_columns(&self) -> Vec<usize> {
        match self.kind {
            AirKind::Component(component) if P::WINDOWS[component].is_some() => {
                (0..P::FIXED_COLUMNS[component].len()).collect()
            }
            _ => Vec::new(),
        }
    }
}

impl<AB, P> Air<AB> for GeneratedAir<P>
where
    AB: AirBuilder + InteractionBuilder,
    AB::F: WitnessField,
    P: GeneratedAirSpec,
{
    fn eval(&self, builder: &mut AB) {
        // Clean's channel balance is over field multiplicities: every interaction is provided,
        // with the signed multiplicity of its push or pull, and the interaction-count bound of
        // `GeneratedEnsemble::new` replaces LogUp's height check.
        let interactions = match self.kind {
            AirKind::Component(component) => {
                let fixed_columns = P::FIXED_COLUMNS[component];
                let window = P::WINDOWS[component];
                let semantic = |fixed: &[AB::Var], committed: &[AB::Var]| -> Vec<AB::Expr> {
                    semantic_row(
                        fixed_columns,
                        fixed.iter().map(|&value| value.into()),
                        committed.iter().map(|&value| value.into()),
                    )
                };
                let row = semantic(
                    builder.preprocessed().current_slice(),
                    builder.main().current_slice(),
                );
                // only two-row components open the next row
                let row = window_row(window, row, || {
                    semantic(
                        builder.preprocessed().next_slice(),
                        builder.main().next_slice(),
                    )
                });
                for constraint in P::constraints(component, &row) {
                    match constraint.gate {
                        Gate::EveryRow => builder.assert_zero(constraint.value),
                        Gate::FirstRow => builder.when_first_row().assert_zero(constraint.value),
                        Gate::LastRow => builder.when_last_row().assert_zero(constraint.value),
                        Gate::Transition => builder.when_transition().assert_zero(constraint.value),
                    }
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
            builder.push_interaction(
                interaction.channel,
                interaction.message,
                Count::provided(interaction.multiplicity),
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
