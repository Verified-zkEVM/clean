//! Runtime for witness programs compiled from Clean's witness IR.
//!
//! This module contains no JSON parser. Lean-generated Rust implements [`Program`]
//! with ordinary field expressions; proving-time witness generation only executes
//! those compiled functions and this channel worklist.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use p3_field::{Field, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;

/// The field operations used by extracted witness programs.
pub trait WitnessField: Field + PrimeField64 + Copy + Eq {
    #[inline(always)]
    fn from_canonical_u64(value: u64) -> Self {
        Self::from_u64(value)
    }

    #[inline(always)]
    fn canonical_u64(self) -> u64 {
        self.as_canonical_u64()
    }

    #[inline(always)]
    fn inverse_or_zero(self) -> Self {
        self.try_inverse().unwrap_or(Self::ZERO)
    }
}

impl<F> WitnessField for F where F: Field + PrimeField64 + Copy + Eq {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Pull,
    Push,
}

impl Direction {
    fn opposite(self) -> Self {
        match self {
            Self::Pull => Self::Push,
            Self::Push => Self::Pull,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Aggregation {
    PerOccurrence,
    ByMessage,
}

#[derive(Clone, Debug)]
pub enum InputCell<F> {
    Message(usize),
    Multiplicity,
    Constant(F),
}

#[derive(Clone, Debug)]
pub struct DemandMode<F> {
    pub channel: &'static str,
    pub direction: Direction,
    pub aggregation: Aggregation,
    pub input: Vec<InputCell<F>>,
}

#[derive(Clone, Debug)]
pub struct FixedSlot<F> {
    pub channel: &'static str,
    pub direction: Direction,
    pub message: Vec<F>,
    pub row: usize,
    pub column: usize,
}

#[derive(Clone, Debug)]
pub enum Mode<F> {
    Demand(DemandMode<F>),
    Fixed {
        input_rows: Vec<Vec<F>>,
        slots: Vec<FixedSlot<F>>,
    },
}

/// A semantic component input used to extend a table to a power-of-two height.
#[derive(Clone, Debug)]
pub struct Padding<F> {
    pub input: Vec<F>,
    pub minimum_rows: usize,
}

#[derive(Clone, Debug)]
pub struct Interaction<F> {
    pub channel: &'static str,
    pub multiplicity: F,
    pub message: Vec<F>,
    pub assume_guarantees: bool,
}

/// The backend-neutral output of extracted ensemble witness generation.
#[derive(Clone, Debug)]
pub struct EnsembleWitness<F> {
    pub tables: Vec<Vec<Vec<F>>>,
}

impl<F: Field> EnsembleWitness<F> {
    /// Convert already-padded semantic tables to Plonky3 trace matrices.
    pub fn into_traces(self) -> Result<Vec<RowMajorMatrix<F>>, String> {
        self.tables
            .into_iter()
            .enumerate()
            .map(|(component, rows)| {
                if rows.is_empty() || !rows.len().is_power_of_two() {
                    return Err(format!(
                        "component {component} has non-power-of-two height {}",
                        rows.len()
                    ));
                }
                let width = rows[0].len();
                if width == 0 || rows.iter().any(|row| row.len() != width) {
                    return Err(format!(
                        "component {component} contains a row of the wrong width"
                    ));
                }
                Ok(RowMajorMatrix::new(
                    rows.into_iter().flatten().collect(),
                    width,
                ))
            })
            .collect()
    }
}

/// Implemented by Rust emitted directly from a Clean ensemble and its witness IR.
pub trait Program<F: WitnessField> {
    const FUEL: usize;
    const COMPONENTS: usize;

    fn modes() -> Vec<Mode<F>>;
    fn padding() -> Vec<Padding<F>>;
    fn complete_row(component: usize, input: &[F]) -> Result<Vec<F>, String>;
    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>>;
    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>>;
}

#[derive(Clone, Debug)]
struct Demand<F> {
    channel: &'static str,
    direction: Direction,
    message: Vec<F>,
    count: usize,
}

#[derive(Clone, Debug)]
struct Origin<F> {
    channel: &'static str,
    direction: Direction,
    message: Vec<F>,
    multiplicity: usize,
}

#[derive(Clone, Debug)]
struct Row<F> {
    values: Vec<F>,
    origin: Option<Origin<F>>,
}

fn interaction_demand<F: WitnessField>(interaction: Interaction<F>) -> Option<Demand<F>> {
    let (direction, count) = if interaction.assume_guarantees {
        (
            Direction::Pull,
            (-interaction.multiplicity).canonical_u64() as usize,
        )
    } else {
        (
            Direction::Push,
            interaction.multiplicity.canonical_u64() as usize,
        )
    };
    (count != 0).then_some(Demand {
        channel: interaction.channel,
        direction,
        message: interaction.message,
        count,
    })
}

/// Add a demand while eagerly cancelling the opposite direction.
fn add_demand<F: WitnessField>(demands: &mut Vec<Demand<F>>, mut demand: Demand<F>) {
    if demand.count == 0 {
        return;
    }
    if let Some(index) = demands
        .iter()
        .position(|current| current.channel == demand.channel && current.message == demand.message)
    {
        let current = &mut demands[index];
        if current.direction == demand.direction {
            current.count += demand.count;
        } else if current.count == demand.count {
            demands.remove(index);
        } else if current.count < demand.count {
            demand.count -= current.count;
            demands[index] = demand;
        } else {
            current.count -= demand.count;
        }
    } else {
        demands.push(demand);
    }
}

fn add_interactions<F: WitnessField>(
    demands: &mut Vec<Demand<F>>,
    interactions: impl IntoIterator<Item = Interaction<F>>,
) {
    for interaction in interactions {
        if let Some(demand) = interaction_demand(interaction) {
            add_demand(demands, demand);
        }
    }
}

fn remove_interactions<F: WitnessField>(
    demands: &mut Vec<Demand<F>>,
    interactions: impl IntoIterator<Item = Interaction<F>>,
) {
    for interaction in interactions {
        if let Some(mut demand) = interaction_demand(interaction) {
            demand.direction = demand.direction.opposite();
            add_demand(demands, demand);
        }
    }
}

fn mode_handles<F: WitnessField>(mode: &Mode<F>, demand: &Demand<F>) -> bool {
    match mode {
        Mode::Demand(mode) => mode.channel == demand.channel && mode.direction == demand.direction,
        Mode::Fixed { slots, .. } => slots.iter().any(|slot| {
            slot.channel == demand.channel
                && slot.direction == demand.direction
                && slot.message == demand.message
        }),
    }
}

fn input_for_demand<F: WitnessField>(
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    multiplicity: usize,
) -> Result<Vec<F>, String> {
    mode.input
        .iter()
        .map(|cell| match cell {
            InputCell::Message(index) => demand
                .message
                .get(*index)
                .copied()
                .ok_or_else(|| format!("channel message has no element at index {index}")),
            InputCell::Multiplicity => Ok(F::from_canonical_u64(multiplicity as u64)),
            InputCell::Constant(value) => Ok(*value),
        })
        .collect()
}

fn make_demand_row<F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    multiplicity: usize,
) -> Result<Row<F>, String> {
    let input = input_for_demand(mode, demand, multiplicity)?;
    let values = P::complete_row(component, &input)?;
    Ok(Row {
        values,
        origin: Some(Origin {
            channel: mode.channel,
            direction: mode.direction,
            message: demand.message.clone(),
            multiplicity,
        }),
    })
}

fn handle_demand<F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    table: &mut Vec<Row<F>>,
    demands: &mut Vec<Demand<F>>,
) -> Result<(), String> {
    match mode.aggregation {
        Aggregation::PerOccurrence => {
            for _ in 0..demand.count {
                let row = make_demand_row::<F, P>(component, mode, demand, 1)?;
                add_interactions(demands, P::interactions(component, &row.values));
                table.push(row);
            }
        }
        Aggregation::ByMessage => {
            let existing = table.iter().position(|row| {
                row.origin.as_ref().is_some_and(|origin| {
                    origin.channel == mode.channel
                        && origin.direction == mode.direction
                        && origin.message == demand.message
                })
            });
            match existing {
                None => {
                    let row = make_demand_row::<F, P>(component, mode, demand, demand.count)?;
                    add_interactions(demands, P::interactions(component, &row.values));
                    table.push(row);
                }
                Some(index) => {
                    let old = table[index].clone();
                    let multiplicity = old
                        .origin
                        .as_ref()
                        .expect("matched row must have an origin")
                        .multiplicity
                        + demand.count;
                    let updated = make_demand_row::<F, P>(component, mode, demand, multiplicity)?;
                    remove_interactions(demands, P::interactions(component, &old.values));
                    add_interactions(demands, P::interactions(component, &updated.values));
                    table[index] = updated;
                }
            }
        }
    }
    Ok(())
}

fn handle_fixed<F: WitnessField, P: Program<F>>(
    component: usize,
    slots: &[FixedSlot<F>],
    demand: &Demand<F>,
    table: &mut [Row<F>],
    demands: &mut Vec<Demand<F>>,
) -> Result<(), String> {
    let mut matches = slots.iter().filter(|slot| {
        slot.channel == demand.channel
            && slot.direction == demand.direction
            && slot.message == demand.message
    });
    let slot = matches
        .next()
        .ok_or_else(|| format!("fixed handler has no slot for channel '{}'", demand.channel))?;
    if matches.next().is_some() {
        return Err(format!(
            "fixed handler has duplicate slots for channel '{}'",
            demand.channel
        ));
    }
    let row = table
        .get_mut(slot.row)
        .ok_or_else(|| format!("fixed slot row {} is out of bounds", slot.row))?;
    let current = row
        .values
        .get(slot.column)
        .copied()
        .ok_or_else(|| format!("fixed slot column {} is out of bounds", slot.column))?;
    let count = current.canonical_u64() as usize + demand.count;
    let value = F::from_canonical_u64(count as u64);
    if value.canonical_u64() as usize != count {
        return Err(format!(
            "fixed multiplicity {count} overflows the field characteristic"
        ));
    }
    let mut input = row.values.clone();
    input[slot.column] = value;
    row.values = P::complete_row(component, &input)?;

    // The fixed row's only changed interaction is the slot represented by this
    // demand, so update the worklist directly instead of evaluating every fixed slot.
    add_demand(
        demands,
        Demand {
            channel: slot.channel,
            direction: slot.direction.opposite(),
            message: slot.message.clone(),
            count: demand.count,
        },
    );
    Ok(())
}

fn balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    tables: &mut [Vec<Row<F>>],
    demands: &mut Vec<Demand<F>>,
) -> Result<(), String> {
    for _ in 0..P::FUEL {
        if demands.is_empty() {
            return Ok(());
        }

        let mut action = None;
        for (demand_index, demand) in demands.iter().enumerate() {
            let handlers: Vec<_> = modes
                .iter()
                .enumerate()
                .filter_map(|(component, mode)| mode_handles(mode, demand).then_some(component))
                .collect();
            match handlers.as_slice() {
                [] => continue,
                [component] => {
                    action = Some((demand_index, *component));
                    break;
                }
                _ => {
                    return Err(format!(
                        "multiple generation handlers match channel '{}'",
                        demand.channel
                    ));
                }
            }
        }

        let (demand_index, component) = action.ok_or_else(|| {
            let channels = demands
                .iter()
                .map(|demand| demand.channel)
                .collect::<Vec<_>>()
                .join(", ");
            format!("unhandled channel imbalance on: {channels}")
        })?;
        // Keep the selected imbalance in the worklist. The generated row's
        // opposite interaction (or fixed-slot delta) cancels it incrementally.
        let demand = demands[demand_index].clone();
        match &modes[component] {
            Mode::Demand(mode) => {
                handle_demand::<F, P>(component, mode, &demand, &mut tables[component], demands)?
            }
            Mode::Fixed { slots, .. } => {
                handle_fixed::<F, P>(component, slots, &demand, &mut tables[component], demands)?
            }
        }
    }

    Err("ensemble witness generation exhausted its fuel".to_string())
}

fn target_height<F>(row_count: usize, padding: &Padding<F>) -> usize {
    row_count
        .max(padding.minimum_rows)
        .max(1)
        .next_power_of_two()
}

fn pad_and_balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    padding: &[Padding<F>],
    tables: &mut [Vec<Row<F>>],
) -> Result<(), String> {
    for _ in 0..P::FUEL {
        let mut demands = Vec::new();
        for (component, (table, padding)) in tables.iter_mut().zip(padding).enumerate() {
            let height = target_height(table.len(), padding);
            for _ in table.len()..height {
                let values = P::complete_row(component, &padding.input)?;
                add_interactions(&mut demands, P::interactions(component, &values));
                table.push(Row {
                    values,
                    origin: None,
                });
            }
        }

        balance::<F, P>(modes, tables, &mut demands)?;
        if tables
            .iter()
            .zip(padding)
            .all(|(table, padding)| table.len() == target_height(table.len(), padding))
        {
            return Ok(());
        }
    }

    Err("ensemble padding exhausted its fuel".to_string())
}

/// Run an extracted channel-driven ensemble witness program.
pub fn generate<F: WitnessField, P: Program<F>>(
    public_input: &[F],
) -> Result<EnsembleWitness<F>, String> {
    let modes = P::modes();
    let padding = P::padding();
    if modes.len() != P::COMPONENTS {
        return Err(format!(
            "generation-mode count {} does not match component count {}",
            modes.len(),
            P::COMPONENTS
        ));
    }
    if padding.len() != P::COMPONENTS {
        return Err(format!(
            "padding count {} does not match component count {}",
            padding.len(),
            P::COMPONENTS
        ));
    }

    let mut tables = Vec::with_capacity(modes.len());
    for (component, mode) in modes.iter().enumerate() {
        let mut rows = Vec::new();
        if let Mode::Fixed { input_rows, .. } = mode {
            for input in input_rows {
                rows.push(Row {
                    values: P::complete_row(component, input)?,
                    origin: None,
                });
            }
        }
        tables.push(rows);
    }

    let mut demands = Vec::new();
    add_interactions(&mut demands, P::verifier_interactions(public_input));
    for (component, table) in tables.iter().enumerate() {
        for row in table {
            add_interactions(&mut demands, P::interactions(component, &row.values));
        }
    }

    balance::<F, P>(&modes, &mut tables, &mut demands)?;
    pad_and_balance::<F, P>(&modes, &padding, &mut tables)?;

    Ok(EnsembleWitness {
        tables: tables
            .into_iter()
            .map(|table| table.into_iter().map(|row| row.values).collect())
            .collect(),
    })
}
