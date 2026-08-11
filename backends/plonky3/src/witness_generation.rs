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

/// Failures surfaced by the public witness-generation API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessGenerationError {
    PublicInputWidth { expected: usize, actual: usize },
    ProverInputWidth { expected: usize, actual: usize },
    Runtime(String),
}

impl core::fmt::Display for WitnessGenerationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::PublicInputWidth { expected, actual } => write!(
                formatter,
                "public input has width {actual}, expected {expected}"
            ),
            Self::ProverInputWidth { expected, actual } => write!(
                formatter,
                "prover input has width {actual}, expected {expected}"
            ),
            Self::Runtime(error) => formatter.write_str(error),
        }
    }
}

impl From<String> for WitnessGenerationError {
    fn from(error: String) -> Self {
        Self::Runtime(error)
    }
}

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
pub struct PreallocatedHandler {
    pub channel: &'static str,
    pub direction: Direction,
    pub interaction: usize,
    pub column: usize,
}

#[derive(Clone, Debug)]
pub enum Mode<F> {
    Demand(DemandMode<F>),
    Preallocated { handlers: Vec<PreallocatedHandler> },
}

/// Component-input rows available to extracted witness programs.
#[derive(Clone, Debug)]
pub struct WitnessData<F> {
    entries: Vec<(&'static str, Vec<Vec<F>>)>,
}

impl<F: Field + Copy> WitnessData<F> {
    fn from_initial_tables(names: &[&'static str], tables: &[Vec<Row<F>>]) -> Self {
        let entries = names
            .iter()
            .zip(tables)
            .map(|(name, table)| {
                let rows = table.iter().map(|row| row.input.clone()).collect();
                (*name, rows)
            })
            .collect();
        Self { entries }
    }

    #[inline(always)]
    pub fn get(&self, name: &str, width: usize, row: usize, column: usize) -> F {
        self.entries
            .iter()
            .find(|(entry_name, rows)| {
                *entry_name == name && rows.first().is_none_or(|value| value.len() == width)
            })
            .and_then(|(_, rows)| rows.get(row))
            .and_then(|value| value.get(column))
            .copied()
            .unwrap_or(F::ZERO)
    }
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
    fixed_widths: Vec<usize>,
    pub tables: Vec<Vec<Vec<F>>>,
}

impl<F: Field> EnsembleWitness<F> {
    /// Convert already-padded semantic tables to Plonky3 trace matrices.
    pub fn into_traces(self) -> Result<Vec<RowMajorMatrix<F>>, String> {
        self.tables
            .into_iter()
            .zip(self.fixed_widths)
            .enumerate()
            .map(|(component, (rows, fixed_width))| {
                if rows.is_empty() || !rows.len().is_power_of_two() {
                    return Err(format!(
                        "component {component} has non-power-of-two height {}",
                        rows.len()
                    ));
                }
                let semantic_width = rows[0].len();
                let width = semantic_width.checked_sub(fixed_width).ok_or_else(|| {
                    format!("component {component} fixed width exceeds its semantic row width")
                })?;
                if width == 0 || rows.iter().any(|row| row.len() != semantic_width) {
                    return Err(format!(
                        "component {component} contains a row of the wrong width"
                    ));
                }
                Ok(RowMajorMatrix::new(
                    rows.into_iter()
                        .flat_map(|row| row.into_iter().skip(fixed_width))
                        .collect(),
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
    const PUBLIC_INPUTS: usize;
    const PROVER_INPUTS: usize;
    const FIXED_WIDTHS: &'static [usize];
    const COMPONENT_NAMES: &'static [&'static str];

    fn modes() -> Vec<Mode<F>>;
    fn padding() -> Vec<Padding<F>>;
    fn initial_rows(component: usize, prover_input: &[F]) -> Result<Vec<Vec<F>>, String>;
    fn complete_row(component: usize, input: &[F], data: &WitnessData<F>)
        -> Result<Vec<F>, String>;
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
    input: Vec<F>,
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
        Mode::Preallocated { handlers } => handlers.iter().any(|handler| {
            handler.channel == demand.channel && handler.direction == demand.direction
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
    data: &WitnessData<F>,
) -> Result<Row<F>, String> {
    let input = input_for_demand(mode, demand, multiplicity)?;
    let values = P::complete_row(component, &input, data)?;
    Ok(Row {
        input,
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
    data: &WitnessData<F>,
) -> Result<(), String> {
    match mode.aggregation {
        Aggregation::PerOccurrence => {
            for _ in 0..demand.count {
                let row = make_demand_row::<F, P>(component, mode, demand, 1, data)?;
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
                    let row = make_demand_row::<F, P>(component, mode, demand, demand.count, data)?;
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
                    let updated =
                        make_demand_row::<F, P>(component, mode, demand, multiplicity, data)?;
                    remove_interactions(demands, P::interactions(component, &old.values));
                    add_interactions(demands, P::interactions(component, &updated.values));
                    table[index] = updated;
                }
            }
        }
    }
    Ok(())
}

fn handle_preallocated<F: WitnessField, P: Program<F>>(
    component: usize,
    handlers: &[PreallocatedHandler],
    demand: &Demand<F>,
    table: &mut [Row<F>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
) -> Result<(), String> {
    let mut matches = handlers.iter().flat_map(|handler| {
        table
            .iter()
            .enumerate()
            .filter_map(move |(row_index, row)| {
                if handler.channel != demand.channel || handler.direction != demand.direction {
                    return None;
                }
                let interaction = P::interactions(component, &row.values)
                    .into_iter()
                    .nth(handler.interaction)?;
                let direction = if interaction.assume_guarantees {
                    Direction::Push
                } else {
                    Direction::Pull
                };
                (interaction.channel == handler.channel
                    && direction == handler.direction
                    && interaction.message == demand.message)
                    .then_some((handler, row_index))
            })
    });
    let (handler, row_index) = matches.next().ok_or_else(|| {
        format!(
            "preallocated handler has no row for channel '{}'",
            demand.channel
        )
    })?;
    if matches.next().is_some() {
        return Err(format!(
            "preallocated handler has multiple rows for channel '{}'",
            demand.channel
        ));
    }
    let row = &mut table[row_index];
    let current = row.input.get(handler.column).copied().ok_or_else(|| {
        format!(
            "preallocated handler column {} is out of bounds",
            handler.column
        )
    })?;
    let count = current.canonical_u64() as usize + demand.count;
    let value = F::from_canonical_u64(count as u64);
    if value.canonical_u64() as usize != count {
        return Err(format!(
            "preallocated multiplicity {count} overflows the field characteristic"
        ));
    }
    let old_interactions = P::interactions(component, &row.values);
    row.input[handler.column] = value;
    row.values = P::complete_row(component, &row.input, data)?;
    remove_interactions(demands, old_interactions);
    add_interactions(demands, P::interactions(component, &row.values));
    Ok(())
}

fn balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    tables: &mut [Vec<Row<F>>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
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
            Mode::Demand(mode) => handle_demand::<F, P>(
                component,
                mode,
                &demand,
                &mut tables[component],
                demands,
                data,
            )?,
            Mode::Preallocated { handlers } => handle_preallocated::<F, P>(
                component,
                handlers,
                &demand,
                &mut tables[component],
                demands,
                data,
            )?,
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
    data: &WitnessData<F>,
) -> Result<(), String> {
    for _ in 0..P::FUEL {
        let mut demands = Vec::new();
        for (component, (table, padding)) in tables.iter_mut().zip(padding).enumerate() {
            let height = target_height(table.len(), padding);
            for _ in table.len()..height {
                let values = P::complete_row(component, &padding.input, data)?;
                add_interactions(&mut demands, P::interactions(component, &values));
                table.push(Row {
                    input: padding.input.clone(),
                    values,
                    origin: None,
                });
            }
        }

        balance::<F, P>(modes, tables, &mut demands, data)?;
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
    prover_input: &[F],
) -> Result<EnsembleWitness<F>, WitnessGenerationError> {
    let modes = P::modes();
    let padding = P::padding();
    if modes.len() != P::COMPONENTS {
        return Err(format!(
            "generation-mode count {} does not match component count {}",
            modes.len(),
            P::COMPONENTS
        )
        .into());
    }
    if padding.len() != P::COMPONENTS {
        return Err(format!(
            "padding count {} does not match component count {}",
            padding.len(),
            P::COMPONENTS
        )
        .into());
    }
    if P::FIXED_WIDTHS.len() != P::COMPONENTS {
        return Err(format!(
            "fixed-width count {} does not match component count {}",
            P::FIXED_WIDTHS.len(),
            P::COMPONENTS
        )
        .into());
    }
    if P::COMPONENT_NAMES.len() != P::COMPONENTS {
        return Err(format!(
            "component-name count {} does not match component count {}",
            P::COMPONENT_NAMES.len(),
            P::COMPONENTS
        )
        .into());
    }
    if public_input.len() != P::PUBLIC_INPUTS {
        return Err(WitnessGenerationError::PublicInputWidth {
            expected: P::PUBLIC_INPUTS,
            actual: public_input.len(),
        });
    }
    if prover_input.len() != P::PROVER_INPUTS {
        return Err(WitnessGenerationError::ProverInputWidth {
            expected: P::PROVER_INPUTS,
            actual: prover_input.len(),
        });
    }

    let mut tables = Vec::with_capacity(modes.len());
    for (component, mode) in modes.iter().enumerate() {
        let inputs = P::initial_rows(component, prover_input)?;
        if matches!(mode, Mode::Demand(_)) && !inputs.is_empty() {
            return Err(format!(
                "demand-driven component {component} unexpectedly initialized rows"
            )
            .into());
        }
        let rows = inputs
            .into_iter()
            .map(|input| Row {
                values: input.clone(),
                input,
                origin: None,
            })
            .collect();
        tables.push(rows);
    }

    for (component, mode) in modes.iter().enumerate() {
        let fixed_width = P::FIXED_WIDTHS[component];
        match mode {
            Mode::Demand(_) if fixed_width != 0 => {
                return Err(format!(
                    "fixed-column component {component} must use preallocated generation"
                )
                .into());
            }
            Mode::Preallocated { handlers } => {
                if let Some(handler) = handlers.iter().find(|handler| handler.column < fixed_width)
                {
                    return Err(format!(
                        "preallocated handler for component {component} mutates fixed column {}",
                        handler.column
                    )
                    .into());
                }
            }
            Mode::Demand(_) => {}
        }
    }

    let data = WitnessData::from_initial_tables(P::COMPONENT_NAMES, &tables);
    for (component, table) in tables.iter_mut().enumerate() {
        for row in table {
            row.values = P::complete_row(component, &row.input, &data)?;
        }
    }

    let mut demands = Vec::new();
    add_interactions(&mut demands, P::verifier_interactions(public_input));
    for (component, table) in tables.iter().enumerate() {
        for row in table {
            add_interactions(&mut demands, P::interactions(component, &row.values));
        }
    }

    balance::<F, P>(&modes, &mut tables, &mut demands, &data)?;
    pad_and_balance::<F, P>(&modes, &padding, &mut tables, &data)?;

    Ok(EnsembleWitness {
        fixed_widths: P::FIXED_WIDTHS.to_vec(),
        tables: tables
            .into_iter()
            .map(|table| table.into_iter().map(|row| row.values).collect())
            .collect(),
    })
}
