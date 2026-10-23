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
    FieldOrder {
        expected: u64,
        actual: u64,
    },
    PublicInputWidth {
        expected: usize,
        actual: usize,
    },
    ProverInputWidth {
        expected: usize,
        actual: usize,
    },
    /// A preallocated component has fewer rows than the minimum trace height.
    PreallocatedHeight {
        component: &'static str,
        height: usize,
        minimum: usize,
    },
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
            Self::PreallocatedHeight {
                component,
                height,
                minimum,
            } => write!(
                formatter,
                "preallocated component '{component}' has {height} rows, fewer than the minimum \
                 trace height {minimum}"
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

/// A condition on a demanded message, which can read the prover data and the hint.
pub type Guard<F> = fn(&[F], &WitnessData<F>, &WitnessData<F>) -> bool;

/// The input of a new row for a demanded message, which can read the prover data and the hint, with
/// the given value in its multiplicity cell.
pub type DemandInput<F> = fn(&[F], &WitnessData<F>, &WitnessData<F>, F) -> Vec<F>;

#[derive(Clone, Debug)]
pub struct DemandMode<F> {
    pub channel: &'static str,
    /// Which unanswered messages create rows: pushed more often than pulled, or the opposite.
    pub trigger: Direction,
    /// Which of these messages the component answers.
    pub guard: Guard<F>,
    pub input: DemandInput<F>,
    /// The multiplicity cell, which counts repeated demand for a message in one row. Without one,
    /// every occurrence gets its own row.
    pub multiplicity: Option<MultiplicityColumn>,
    /// The input of the rows that pad the component's table to a power-of-two height.
    pub padding: Vec<F>,
}

/// A multiplicity cell: the multiplicity of a component's interaction on its channel, which answers
/// unmatched pulls on that channel.
#[derive(Clone, Copy, Debug)]
pub struct MultiplicityColumn {
    /// The position of the counted interaction among the component's interactions.
    pub interaction: usize,
    /// The input column of the cell.
    pub column: usize,
}

#[derive(Clone, Debug)]
pub enum Mode<F> {
    Demand(DemandMode<F>),
    Preallocated {
        channel: &'static str,
        rows: usize,
        multiplicity: MultiplicityColumn,
    },
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
    fixed_columns: Vec<&'static [usize]>,
    pub tables: Vec<Vec<Vec<F>>>,
}

impl<F: Field> EnsembleWitness<F> {
    /// Convert the tables to Plonky3 trace matrices, without the fixed columns.
    pub fn into_traces(self) -> Result<Vec<RowMajorMatrix<F>>, String> {
        self.tables
            .into_iter()
            .zip(self.fixed_columns)
            .enumerate()
            .map(|(component, (rows, fixed_columns))| {
                if rows.is_empty() || !rows.len().is_power_of_two() {
                    return Err(format!(
                        "component {component} has non-power-of-two height {}",
                        rows.len()
                    ));
                }
                let semantic_width = rows[0].len();
                let width = semantic_width
                    .checked_sub(fixed_columns.len())
                    .ok_or_else(|| {
                        format!("component {component} fixed width exceeds its semantic row width")
                    })?;
                if width == 0 || rows.iter().any(|row| row.len() != semantic_width) {
                    return Err(format!(
                        "component {component} contains a row of the wrong width"
                    ));
                }
                Ok(RowMajorMatrix::new(
                    rows.into_iter()
                        .flat_map(|row| {
                            row.into_iter()
                                .enumerate()
                                .filter(|(column, _)| !fixed_columns.contains(column))
                                .map(|(_, value)| value)
                        })
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
    /// The input columns that are fixed columns, per component.
    const FIXED_COLUMNS: &'static [&'static [usize]];
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

/// How a component answers a demand it accepts.
enum Answer<'a, F> {
    /// With the component's demand mode.
    Demand(&'a DemandMode<F>),
    /// By incrementing the multiplicity cell of the row at `row_index`.
    Multiplicity {
        multiplicity: &'a MultiplicityColumn,
        row_index: usize,
    },
}

/// How the component answers the demand, if it accepts it: a demand component accepts the messages
/// on its channel that trigger it and that its guard holds for, a preallocated one those it has a
/// row for.
fn accepts<'a, F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &'a Mode<F>,
    demand: &Demand<F>,
    table: &[Row<F>],
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<Option<Answer<'a, F>>, String> {
    match mode {
        Mode::Demand(mode) => Ok((mode.channel == demand.channel
            && mode.trigger == demand.direction()
            && (mode.guard)(&demand.message, data, hint))
        .then_some(Answer::Demand(mode))),
        Mode::Preallocated {
            channel,
            multiplicity,
            ..
        } => {
            let found = find_counted_row::<F, P>(component, channel, multiplicity, demand, table)?;
            Ok(found.map(|row_index| Answer::Multiplicity {
                multiplicity,
                row_index,
            }))
        }
    }
}

/// A new row answering the demanded message, whose multiplicity cell, if any, starts at the
/// demanded count.
fn make_demand_row<F: WitnessField, P: Program<F>>(
    component: usize,
    mode: &DemandMode<F>,
    demand: &Demand<F>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<Row<F>, String> {
    let count = F::from_canonical_u64(demand.count() as u64);
    let input = (mode.input)(&demand.message, data, hint, count);
    let values = P::complete_row(component, &input, data, hint)?;
    Ok(Row { input, values })
}

/// The row whose counted interaction carries the demanded message.
fn find_counted_row<F: WitnessField, P: Program<F>>(
    component: usize,
    channel: &str,
    multiplicity: &MultiplicityColumn,
    demand: &Demand<F>,
    table: &[Row<F>],
) -> Result<Option<usize>, String> {
    if demand.direction() != Direction::Pull || demand.channel != channel {
        return Ok(None);
    }
    let mut matches = table.iter().enumerate().filter_map(|(row_index, row)| {
        let interaction = P::interactions(component, &row.values)
            .into_iter()
            .nth(multiplicity.interaction)?;
        (interaction.message == demand.message).then_some(row_index)
    });
    let found = matches.next();
    if matches.next().is_some() {
        return Err(format!(
            "component {component} has multiple rows for a message on channel '{channel}'"
        ));
    }
    Ok(found)
}

/// Add the demanded count to the multiplicity cell of a row, and complete the row again.
#[allow(clippy::too_many_arguments)]
fn increment_multiplicity<F: WitnessField, P: Program<F>>(
    component: usize,
    multiplicity: &MultiplicityColumn,
    row_index: usize,
    demand: &Demand<F>,
    table: &mut [Row<F>],
    demands: &mut Vec<Demand<F>>,
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
) -> Result<(), String> {
    let row = &mut table[row_index];
    let current = row.input.get(multiplicity.column).copied().ok_or_else(|| {
        format!(
            "multiplicity column {} is out of bounds",
            multiplicity.column
        )
    })?;
    let old_interactions = P::interactions(component, &row.values);
    row.input[multiplicity.column] = current + F::from_canonical_u64(demand.count() as u64);
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
    let new_rows = match &mode.multiplicity {
        None => demand.count(),
        Some(multiplicity) => {
            match find_counted_row::<F, P>(component, mode.channel, multiplicity, demand, table)? {
                Some(row_index) => {
                    return increment_multiplicity::<F, P>(
                        component,
                        multiplicity,
                        row_index,
                        demand,
                        table,
                        demands,
                        data,
                        hint,
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
            let mut answers = Vec::new();
            for (component, mode) in modes.iter().enumerate() {
                if let Some(answer) =
                    accepts::<F, P>(component, mode, demand, &tables[component], data, hint)?
                {
                    answers.push((component, answer));
                }
            }
            if answers.len() > 1 {
                let components = answers
                    .iter()
                    .map(|(component, _)| P::COMPONENT_NAMES[*component])
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(format!(
                    "components {components} all accept a message on channel '{}'",
                    demand.channel
                ));
            }
            if let Some((component, answer)) = answers.pop() {
                action = Some((demand_index, component, answer));
                break;
            }
        }

        let (demand_index, component, answer) = action.ok_or_else(|| {
            let channels = demands
                .iter()
                .map(|demand| demand.channel)
                .collect::<Vec<_>>()
                .join(", ");
            format!("unhandled channel imbalance on: {channels}")
        })?;
        // The demand stays in the worklist: the interactions of the new or updated row cancel it.
        let demand = demands[demand_index].clone();
        match answer {
            Answer::Demand(mode) => handle_demand::<F, P>(
                component,
                mode,
                &demand,
                &mut tables[component],
                demands,
                data,
                hint,
            )?,
            Answer::Multiplicity {
                multiplicity,
                row_index,
            } => increment_multiplicity::<F, P>(
                component,
                multiplicity,
                row_index,
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

/// The padded height of a table: a power of two of at least `minimum_height` rows. Preallocated
/// tables are never padded.
fn target_height<F>(row_count: usize, mode: &Mode<F>, minimum_height: usize) -> usize {
    match mode {
        Mode::Demand(_) => row_count.max(minimum_height).next_power_of_two(),
        Mode::Preallocated { .. } => row_count,
    }
}

fn pad_and_balance<F: WitnessField, P: Program<F>>(
    modes: &[Mode<F>],
    tables: &mut [Vec<Row<F>>],
    data: &WitnessData<F>,
    hint: &WitnessData<F>,
    minimum_height: usize,
) -> Result<(), String> {
    for _ in 0..P::FUEL {
        let mut demands = Vec::new();
        for (component, (table, mode)) in tables.iter_mut().zip(modes).enumerate() {
            let Mode::Demand(DemandMode { padding, .. }) = mode else {
                continue;
            };
            let height = target_height(table.len(), mode, minimum_height);
            for _ in table.len()..height {
                let values = P::complete_row(component, padding, data, hint)?;
                add_interactions(&mut demands, P::interactions(component, &values));
                table.push(Row {
                    input: padding.clone(),
                    values,
                });
            }
        }

        balance::<F, P>(modes, tables, &mut demands, data, hint)?;
        if tables
            .iter()
            .zip(modes)
            .all(|(table, mode)| table.len() == target_height(table.len(), mode, minimum_height))
        {
            return Ok(());
        }
    }

    Err("ensemble padding exhausted its fuel".to_string())
}

/// Run an extracted channel-driven ensemble witness program on the public input and the flattened
/// private input, which witness programs read through the program's hint tables.
///
/// `minimum_height` is the smallest trace height the prover's configuration accepts, which depends
/// on its FRI parameters. Demand-generated tables are padded to at least that height, and
/// preallocated tables, whose height is fixed, must have at least that many rows.
pub fn generate<F: WitnessField, P: Program<F>>(
    public_input: &[F],
    prover_input: &[F],
    minimum_height: usize,
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
    if P::FIXED_COLUMNS.len() != P::COMPONENTS {
        return Err(format!(
            "fixed-column count {} does not match component count {}",
            P::FIXED_COLUMNS.len(),
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
        if let Mode::Preallocated { rows, .. } = mode {
            if *rows < minimum_height {
                return Err(WitnessGenerationError::PreallocatedHeight {
                    component: P::COMPONENT_NAMES[component],
                    height: *rows,
                    minimum: minimum_height,
                });
            }
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
    pad_and_balance::<F, P>(&modes, &mut tables, &data, hint, minimum_height)?;

    Ok(EnsembleWitness {
        fixed_columns: P::FIXED_COLUMNS.to_vec(),
        tables: tables
            .into_iter()
            .map(|table| table.into_iter().map(|row| row.values).collect())
            .collect(),
    })
}
