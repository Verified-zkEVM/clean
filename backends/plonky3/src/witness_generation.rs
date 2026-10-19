//! Witness generation for ensembles extracted from Clean. Generated Rust implements [`Program`], and
//! [`generate`] runs it with a channel worklist.

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

/// `UInt64` division in the witness IR: division by zero is zero.
#[inline(always)]
pub fn safe_div(left: u64, right: u64) -> u64 {
    if right == 0 {
        0
    } else {
        left / right
    }
}

/// `UInt64` remainder in the witness IR: the remainder modulo zero is the dividend.
#[inline(always)]
pub fn safe_rem(left: u64, right: u64) -> u64 {
    if right == 0 {
        left
    } else {
        left % right
    }
}

/// `UInt64` left shift in the witness IR, by the shift amount modulo 64.
#[inline(always)]
pub fn shift_left(value: u64, shift: u64) -> u64 {
    value.wrapping_shl((shift & 63) as u32)
}

/// `UInt64` right shift in the witness IR, by the shift amount modulo 64.
#[inline(always)]
pub fn shift_right(value: u64, shift: u64) -> u64 {
    value.wrapping_shr((shift & 63) as u32)
}

/// Bit `index` of `value`, as a number. Bits at index 64 and above are zero.
#[inline(always)]
pub fn bit_u64(value: u64, index: u64) -> u64 {
    if index < 64 {
        (value >> index) & 1
    } else {
        0
    }
}

/// Whether bit `index` of `value` is set. Bits at index 64 and above are unset.
#[inline(always)]
pub fn bit(value: u64, index: u64) -> bool {
    bit_u64(value, index) == 1
}

/// A witness generation failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessGenerationError {
    FieldOrder { expected: u64, actual: u64 },
    PublicInputWidth { expected: usize, actual: usize },
    ProverInputWidth { expected: usize, actual: usize },
    Runtime(String),
}

impl core::fmt::Display for WitnessGenerationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::FieldOrder { expected, actual } => write!(
                formatter,
                "generated program expects field order {expected}, got {actual}"
            ),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Aggregation {
    PerOccurrence,
    ByMessage,
}

#[derive(Clone, Debug)]
pub enum InputCell<F> {
    Message(usize),
    Constant(F),
}

#[derive(Clone, Debug)]
pub struct DemandMode<F> {
    pub channel: &'static str,
    /// Which unanswered messages create rows: pushed more often than pulled, or the opposite.
    pub surplus: Direction,
    pub aggregation: Aggregation,
    /// The input of a new row, without its counters.
    pub input: Vec<InputCell<F>>,
    /// With `ByMessage` aggregation, the counter on `channel`.
    pub counters: Vec<Counter>,
    pub padding: Padding<F>,
}

/// A counter: the multiplicity of a component's interaction on `channel`, which answers pull
/// surplus on that channel.
#[derive(Clone, Debug)]
pub struct Counter {
    pub channel: &'static str,
    /// The position of the counted interaction among the component's interactions.
    pub interaction: usize,
    /// The input column holding the interaction's multiplicity.
    pub column: usize,
}

#[derive(Clone, Debug)]
pub enum Mode<F> {
    Demand(DemandMode<F>),
    Preallocated { rows: usize, counters: Vec<Counter> },
}

/// A named hint table viewing the flattened private input: `rows` rows of `width` elements,
/// starting at element `offset`. Elements beyond the input read as zero.
#[derive(Clone, Copy, Debug)]
pub struct HintTable {
    pub key: &'static str,
    pub width: usize,
    pub offset: usize,
    pub rows: usize,
}

/// Component-input rows available to extracted witness programs.
#[derive(Clone, Debug)]
pub struct WitnessData<F> {
    entries: Vec<(&'static str, Vec<Vec<F>>)>,
}

impl<F: Field + Copy> WitnessData<F> {
    /// Named component-input rows, keyed like Clean's `ProverData`.
    pub fn from_entries(entries: Vec<(&'static str, Vec<Vec<F>>)>) -> Self {
        Self { entries }
    }

    /// The hint tables `tables` take from the flattened private input.
    fn from_hint_tables(tables: &[HintTable], prover_input: &[F]) -> Self {
        let entries = tables
            .iter()
            .map(|table| {
                let rows = (0..table.rows)
                    .map(|row| {
                        (0..table.width)
                            .map(|column| {
                                prover_input
                                    .get(table.offset + row * table.width + column)
                                    .copied()
                                    .unwrap_or(F::ZERO)
                            })
                            .collect()
                    })
                    .collect();
                (table.key, rows)
            })
            .collect();
        Self::from_entries(entries)
    }

    fn from_initial_tables(names: &[&'static str], tables: &[Vec<Row<F>>]) -> Self {
        let entries = names
            .iter()
            .zip(tables)
            .map(|(name, table)| {
                let rows = table.iter().map(|row| row.input.clone()).collect();
                (*name, rows)
            })
            .collect();
        Self::from_entries(entries)
    }

    /// Reads column `column` of the named rows cut off or zero-padded at `width` elements, as in
    /// Lean's `ProverData` and `ProverHint`.
    #[inline(always)]
    pub fn get(&self, name: &str, width: usize, row: usize, column: usize) -> F {
        if column >= width {
            return F::ZERO;
        }
        self.entries
            .iter()
            .find(|(entry_name, _)| *entry_name == name)
            .and_then(|(_, rows)| rows.get(row))
            .and_then(|value| value.get(column))
            .copied()
            .unwrap_or(F::ZERO)
    }
}

/// The input row that pads a demand-generated component to a power-of-two height, of at least `minimum_rows`.
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

/// A generated ensemble witness: the rows of each component.
#[derive(Clone, Debug)]
pub struct EnsembleWitness<F> {
    fixed_widths: Vec<usize>,
    pub tables: Vec<Vec<Vec<F>>>,
}

impl<F: Field> EnsembleWitness<F> {
    /// Convert the tables to Plonky3 trace matrices.
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

/// A witness generation program, implemented by Rust generated from a Clean ensemble.
pub trait Program<F: WitnessField> {
    /// Order of the field whose constants and arithmetic the generated code was printed for.
    const FIELD_ORDER: u64;
    const FUEL: usize;
    const COMPONENTS: usize;
    const PUBLIC_INPUTS: usize;
    const PROVER_INPUTS: usize;
    const HINT_TABLES: &'static [HintTable];
    const FIXED_WIDTHS: &'static [usize];
    const COMPONENT_NAMES: &'static [&'static str];

    fn modes() -> Vec<Mode<F>>;
    /// The initial input of row `row` of a preallocated component.
    fn initial_row(component: usize, row: u64, hint: &WitnessData<F>) -> Vec<F>;
    fn complete_row(
        component: usize,
        input: &[F],
        data: &WitnessData<F>,
        hint: &WitnessData<F>,
    ) -> Result<Vec<F>, String>;
    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>>;
    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>>;
}

/// A nonzero net multiplicity of one channel message.
#[derive(Clone, Debug)]
struct Demand<F> {
    channel: &'static str,
    message: Vec<F>,
    multiplicity: F,
}

impl<F: WitnessField> Demand<F> {
    /// The direction and size of a net multiplicity: pushes count positively and pulls negatively,
    /// so values above half the field order are read as negative.
    fn surplus(&self) -> (Direction, usize) {
        let value = self.multiplicity.canonical_u64();
        if 2 * u128::from(value) <= u128::from(F::ORDER_U64) {
            (Direction::Push, value as usize)
        } else {
            (
                Direction::Pull,
                (-self.multiplicity).canonical_u64() as usize,
            )
        }
    }

    fn direction(&self) -> Direction {
        self.surplus().0
    }

    fn count(&self) -> usize {
        self.surplus().1
    }
}

#[derive(Clone, Debug)]
struct Row<F> {
    input: Vec<F>,
    values: Vec<F>,
}

/// Add a multiplicity for a channel message, dropping the entry when it cancels to zero.
fn add_multiplicity<F: WitnessField>(
    demands: &mut Vec<Demand<F>>,
    channel: &'static str,
    message: Vec<F>,
    multiplicity: F,
) {
    if let Some(index) = demands
        .iter()
        .position(|current| current.channel == channel && current.message == message)
    {
        let total = demands[index].multiplicity + multiplicity;
        if total == F::ZERO {
            demands.remove(index);
        } else {
            demands[index].multiplicity = total;
        }
    } else if multiplicity != F::ZERO {
        demands.push(Demand {
            channel,
            message,
            multiplicity,
        });
    }
}

fn add_interactions<F: WitnessField>(
    demands: &mut Vec<Demand<F>>,
    interactions: impl IntoIterator<Item = Interaction<F>>,
) {
    for interaction in interactions {
        add_multiplicity(
            demands,
            interaction.channel,
            interaction.message,
            interaction.multiplicity,
        );
    }
}

fn remove_interactions<F: WitnessField>(
    demands: &mut Vec<Demand<F>>,
    interactions: impl IntoIterator<Item = Interaction<F>>,
) {
    for interaction in interactions {
        add_multiplicity(
            demands,
            interaction.channel,
            interaction.message,
            -interaction.multiplicity,
        );
    }
}

fn mode_handles<F: WitnessField>(mode: &Mode<F>, demand: &Demand<F>) -> bool {
    match mode {
        Mode::Demand(mode) => mode.channel == demand.channel && mode.surplus == demand.direction(),
        Mode::Preallocated { counters, .. } => {
            demand.direction() == Direction::Pull
                && counters
                    .iter()
                    .any(|counter| counter.channel == demand.channel)
        }
    }
}

/// A new row answering the demanded message, whose counter, if any, starts at the demanded count.
fn make_demand_row<F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<Row<F>, String> {
    let mut input = mode
        .input
        .iter()
        .map(|cell| match cell {
            InputCell::Message(index) => demand
                .message
                .get(*index)
                .copied()
                .ok_or_else(|| format!("channel message has no element at index {index}")),
            InputCell::Constant(value) => Ok(*value),
        })
        .collect::<Result<Vec<F>, String>>()?;
    let mut columns = mode
        .counters
        .iter()
        .map(|counter| counter.column)
        .collect::<Vec<_>>();
    columns.sort_unstable();
    for column in columns {
        if column > input.len() {
            return Err(format!("counter column {column} is out of bounds"));
        }
        input.insert(column, F::from_canonical_u64(demand.count() as u64));
    }
    let values = P::complete_row(component, &input, data, hint)?;
    Ok(Row { input, values })
}

/// The row whose counted interaction carries the demanded message, with its counter.
fn find_counted_row<'a, F: WitnessField, P: Program<F>>(
    component: usize,
    counters: &'a [Counter],
    demand: &Demand<F>,
    table: &[Row<F>],
) -> Result<Option<(&'a Counter, usize)>, String> {
    if demand.direction() != Direction::Pull {
        return Ok(None);
    }
    let mut matches = counters
        .iter()
        .filter(|counter| counter.channel == demand.channel)
        .flat_map(|counter| {
            table
                .iter()
                .enumerate()
                .filter_map(move |(row_index, row)| {
                    let interaction = P::interactions(component, &row.values)
                        .into_iter()
                        .nth(counter.interaction)?;
                    (interaction.message == demand.message).then_some((counter, row_index))
                })
        });
    let found = matches.next();
    if matches.next().is_some() {
        return Err(format!(
            "component {component} has multiple rows for a message on channel '{}'",
            demand.channel
        ));
    }
    Ok(found)
}

/// Add the demanded count to the counter of a row, and complete the row again.
#[allow(clippy::too_many_arguments)]
fn increment_counter<F: WitnessField, P: Program<F>>(
    component: usize,
    counter: &Counter,
    row_index: usize,
    demand: &Demand<F>,
    table: &mut [Row<F>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<(), String> {
    let row = &mut table[row_index];
    let current = row
        .input
        .get(counter.column)
        .copied()
        .ok_or_else(|| format!("counter column {} is out of bounds", counter.column))?;
    let old_interactions = P::interactions(component, &row.values);
    row.input[counter.column] = current + F::from_canonical_u64(demand.count() as u64);
    row.values = P::complete_row(component, &row.input, data, hint)?;
    remove_interactions(demands, old_interactions);
    add_interactions(demands, P::interactions(component, &row.values));
    Ok(())
}

fn handle_demand<F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    table: &mut Vec<Row<F>>,
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<(), String> {
    let new_rows = match mode.aggregation {
        Aggregation::PerOccurrence => demand.count(),
        Aggregation::ByMessage => {
            match find_counted_row::<F, P>(component, &mode.counters, demand, table)? {
                Some((counter, row_index)) => {
                    return increment_counter::<F, P>(
                        component, counter, row_index, demand, table, demands, data, hint,
                    );
                }
                None => 1,
            }
        }
    };
    for _ in 0..new_rows {
        let row = make_demand_row::<F, P>(component, mode, demand, data, hint)?;
        add_interactions(demands, P::interactions(component, &row.values));
        table.push(row);
    }
    Ok(())
}

fn handle_preallocated<F: WitnessField, P: Program<F>>(
    component: usize,
    counters: &[Counter],
    demand: &Demand<F>,
    table: &mut [Row<F>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<(), String> {
    let (counter, row_index) = find_counted_row::<F, P>(component, counters, demand, table)?
        .ok_or_else(|| {
            format!(
                "preallocated component has no row for a message on channel '{}'",
                demand.channel
            )
        })?;
    increment_counter::<F, P>(
        component, counter, row_index, demand, table, demands, data, hint,
    )
}

fn balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    tables: &mut [Vec<Row<F>>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
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
        // The demand stays in the worklist: the interactions of the new or updated row cancel it.
        let demand = demands[demand_index].clone();
        match &modes[component] {
            Mode::Demand(mode) => handle_demand::<F, P>(
                component,
                mode,
                &demand,
                &mut tables[component],
                demands,
                data,
                hint,
            )?,
            Mode::Preallocated { counters, .. } => handle_preallocated::<F, P>(
                component,
                counters,
                &demand,
                &mut tables[component],
                demands,
                data,
                hint,
            )?,
        }
    }

    Err("ensemble witness generation exhausted its fuel".to_string())
}

/// The padded height of a table. Preallocated tables are never padded.
fn target_height<F>(row_count: usize, mode: &Mode<F>) -> usize {
    match mode {
        Mode::Demand(mode) => row_count
            .max(mode.padding.minimum_rows)
            .max(1)
            .next_power_of_two(),
        Mode::Preallocated { .. } => row_count,
    }
}

fn pad_and_balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    tables: &mut [Vec<Row<F>>],
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<(), String> {
    for _ in 0..P::FUEL {
        let mut demands = Vec::new();
        for (component, (table, mode)) in tables.iter_mut().zip(modes).enumerate() {
            let Mode::Demand(DemandMode { padding, .. }) = mode else {
                continue;
            };
            let height = target_height(table.len(), mode);
            for _ in table.len()..height {
                let values = P::complete_row(component, &padding.input, data, hint)?;
                add_interactions(&mut demands, P::interactions(component, &values));
                table.push(Row {
                    input: padding.input.clone(),
                    values,
                });
            }
        }

        balance::<F, P>(modes, tables, &mut demands, data, hint)?;
        if tables
            .iter()
            .zip(modes)
            .all(|(table, mode)| table.len() == target_height(table.len(), mode))
        {
            return Ok(());
        }
    }

    Err("ensemble padding exhausted its fuel".to_string())
}

/// Run an extracted channel-driven ensemble witness program on the public input and the flattened
/// private input, which witness programs read through the program's hint tables.
pub fn generate<F: WitnessField, P: Program<F>>(
    public_input: &[F],
    prover_input: &[F],
) -> Result<EnsembleWitness<F>, WitnessGenerationError> {
    if F::ORDER_U64 != P::FIELD_ORDER {
        return Err(WitnessGenerationError::FieldOrder {
            expected: P::FIELD_ORDER,
            actual: F::ORDER_U64,
        });
    }
    let modes = P::modes();
    if modes.len() != P::COMPONENTS {
        return Err(format!(
            "generation-mode count {} does not match component count {}",
            modes.len(),
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
    let hint = &WitnessData::from_hint_tables(P::HINT_TABLES, prover_input);

    let mut tables = Vec::with_capacity(modes.len());
    for (component, mode) in modes.iter().enumerate() {
        let inputs = match mode {
            Mode::Demand(_) => Vec::new(),
            Mode::Preallocated { rows, .. } => (0..*rows as u64)
                .map(|row| P::initial_row(component, row, hint))
                .collect(),
        };
        let rows = inputs
            .into_iter()
            .map(|input| Row {
                values: input.clone(),
                input,
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
            Mode::Preallocated { counters, .. } => {
                if let Some(counter) = counters.iter().find(|counter| counter.column < fixed_width)
                {
                    return Err(format!(
                        "counter of component {component} is fixed column {}",
                        counter.column
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
            row.values = P::complete_row(component, &row.input, &data, hint)?;
        }
    }

    let mut demands = Vec::new();
    add_interactions(&mut demands, P::verifier_interactions(public_input));
    for (component, table) in tables.iter().enumerate() {
        for row in table {
            add_interactions(&mut demands, P::interactions(component, &row.values));
        }
    }

    balance::<F, P>(&modes, &mut tables, &mut demands, &data, hint)?;
    pad_and_balance::<F, P>(&modes, &mut tables, &data, hint)?;

    Ok(EnsembleWitness {
        fixed_widths: P::FIXED_WIDTHS.to_vec(),
        tables: tables
            .into_iter()
            .map(|table| table.into_iter().map(|row| row.values).collect())
            .collect(),
    })
}
