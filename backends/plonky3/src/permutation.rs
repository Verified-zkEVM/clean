//! Functions for generating lookup AIRs with calculated traces

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use p3_air::lookup::Lookup;
use p3_field::{Field, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{Entry, SymbolicExpression};

use crate::StarkGenericConfig;
use crate::clean_ast::LookupRowScope;

/// Evaluate a SymbolicExpression on concrete row data.
///
/// Only supports expressions over current-row main and preprocessed variables
/// (offset 0), constants, and arithmetic operations.
fn eval_symbolic_on_row<F: Field>(
    expr: &SymbolicExpression<F>,
    main_row: &[F],
    preprocessed_row: &[F],
) -> F {
    match expr {
        SymbolicExpression::Constant(c) => *c,
        SymbolicExpression::Variable(v) => match v.entry {
            Entry::Main { offset: 0 } => main_row[v.index],
            Entry::Preprocessed { offset: 0 } => preprocessed_row[v.index],
            _ => panic!("Only current row expressions supported for row evaluation"),
        },
        SymbolicExpression::Add { x, y, .. } => {
            eval_symbolic_on_row(x, main_row, preprocessed_row)
                + eval_symbolic_on_row(y, main_row, preprocessed_row)
        }
        SymbolicExpression::Sub { x, y, .. } => {
            eval_symbolic_on_row(x, main_row, preprocessed_row)
                - eval_symbolic_on_row(y, main_row, preprocessed_row)
        }
        SymbolicExpression::Mul { x, y, .. } => {
            eval_symbolic_on_row(x, main_row, preprocessed_row)
                * eval_symbolic_on_row(y, main_row, preprocessed_row)
        }
        SymbolicExpression::Neg { x, .. } => -eval_symbolic_on_row(x, main_row, preprocessed_row),
        _ => panic!("Unsupported expression type for concrete row evaluation"),
    }
}

/// Generates multiplicity traces for all lookup tables,
/// based on the lookup operations from the main AIR's lookups.
///
/// This function:
/// 1. Gets the main AIR's global lookups (element tuples with their direction)
/// 2. For each non-main AIR, extracts its table name
/// 3. Matches main AIR lookups to table AIRs by global interaction name
/// 4. Uses `table_data[i]` to build a reverse map (column values → row number)
///    and determine table size
/// 5. Computes multiplicities by evaluating the element expressions on
///    each main trace row (adding F::ONE per match on active rows)
///
/// # Arguments
/// * `air_infos` - Vector of AirInfo instances (main + table AIRs)
/// * `table_data` - Reference data per table, parallel to `air_infos[1..]`.
///   For PreprocessedTableAir: the preprocessed trace.
///   For ProverTableAir: a data-only matrix (just the data columns, no multiplicity).
/// * `main_trace` - The main execution trace (corresponds to air_infos[0])
/// * `main_air_lookups` - The lookups registered by the main AIR
/// * `lookup_row_scopes` - Row scope for each lookup, parallel to `main_air_lookups`
fn generate_multiplicity_traces<F, SC>(
    air_infos: &[crate::key::AirInfo<F>],
    table_data: &[&RowMajorMatrix<F>],
    main_trace: &RowMajorMatrix<F>,
    main_air_lookups: &[Lookup<F>],
    lookup_row_scopes: &[LookupRowScope],
) -> Vec<RowMajorMatrix<F>>
where
    F: Field + PrimeField32 + From<crate::Val<SC>> + Into<crate::Val<SC>>,
    SC: StarkGenericConfig,
{
    assert_eq!(
        air_infos.len().checked_sub(1).expect("air_infos must not be empty"),
        table_data.len(),
        "table_data length must equal air_infos.len() - 1 (one per table AIR)"
    );
    assert_eq!(
        main_air_lookups.len(),
        lookup_row_scopes.len(),
        "main_air_lookups and lookup_row_scopes must have the same length"
    );

    let mut lookup_traces = Vec::new();

    // For each non-main AIR (table AIR), match lookups by table name
    for (i, air_info) in air_infos.iter().skip(1).enumerate() {
        let table_name = air_info
            .air
            .table_name()
            .expect("Non-main AIR must be a table with a name");

        let data = table_data[i];
        let table_size = data.height();

        // Find the main AIR lookups that target this table (by global interaction name),
        // keeping track of original index for scope lookup.
        let matching_lookups: Vec<(usize, &Lookup<F>)> = main_air_lookups
            .iter()
            .enumerate()
            .filter(|(_, lookup)| {
                if let p3_air::lookup::Kind::Global(name) = &lookup.kind {
                    name == table_name
                } else {
                    false
                }
            })
            .collect();

        // Build index: map from column-value tuple → row index in the table data.
        // This correctly handles tables whose column-0 values are not equal to the row index.
        let mut row_index: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
        for row_idx in 0..table_size {
            let data_row: Vec<F> = data.row(row_idx).unwrap().into_iter().collect();
            let key: Vec<u32> = data_row.iter().map(|v| v.as_canonical_u32()).collect();
            row_index.insert(key, row_idx);
        }

        // Create multiplicity trace for this table
        let mut multiplicity_trace = RowMajorMatrix::new(alloc::vec![F::ZERO; table_size], 1);

        // Calculate multiplicities by evaluating ALL columns of each lookup tuple
        // and looking up the resulting values in the table data index.
        let height = main_trace.height();
        for row_idx in 0..height {
            let row_slice: Vec<F> = main_trace.row(row_idx).unwrap().into_iter().collect();

            for &(global_idx, ref lookup) in &matching_lookups {
                if !lookup_row_scopes[global_idx].is_active(row_idx, height) {
                    continue;
                }
                for tuple in &lookup.element_exprs {
                    // Evaluate ALL element expressions to get the full lookup key
                    let values: Vec<u32> = tuple
                        .iter()
                        .map(|expr| eval_symbolic_on_row(expr, &row_slice, &[]).as_canonical_u32())
                        .collect();

                    let table_row = row_index.get(&values).unwrap_or_else(|| {
                        panic!(
                            "Lookup values {:?} not found in table '{}' (size {})",
                            values, table_name, table_size
                        )
                    });

                    let m = multiplicity_trace.row_mut(*table_row).get_mut(0).unwrap();
                    *m += F::ONE;
                }
            }
        }

        lookup_traces.push(multiplicity_trace);
    }

    lookup_traces
}

/// Append a width-1 multiplicity column to a data matrix, producing a
/// combined matrix of width `data.width() + 1`.
///
/// Used to build the full trace for a `ProverTableAir` from the
/// prover-supplied data and the multiplicities computed by
/// `generate_multiplicity_traces`.
fn append_multiplicity_column<F: Field>(
    data: &RowMajorMatrix<F>,
    multiplicity: &RowMajorMatrix<F>,
) -> RowMajorMatrix<F> {
    assert_eq!(
        data.height(),
        multiplicity.height(),
        "data and multiplicity must have the same number of rows"
    );
    assert_eq!(
        multiplicity.width(),
        1,
        "multiplicity matrix must have exactly one column"
    );

    let new_width = data.width() + 1;
    let num_rows = data.height();
    let mut combined = Vec::with_capacity(num_rows * new_width);

    for row in 0..num_rows {
        for col in 0..data.width() {
            combined.push(data.get(row, col).unwrap());
        }
        combined.push(multiplicity.get(row, 0).unwrap());
    }

    RowMajorMatrix::new(combined, new_width)
}

/// Generate the table traces needed by `prove()`, one per table AIR in
/// `air_infos[1..]`.
///
/// For `PreprocessedTableAir`: returns the width-1 multiplicity trace.
/// For `ProverTableAir`: returns the data + multiplicity combined trace.
///
/// `prover_table_data` supplies the data matrices for `ProverTableAir`
/// instances, matched by table name.  Pass `&[]` when all tables are
/// preprocessed.
pub fn generate_table_traces<F, SC>(
    air_infos: &[crate::key::AirInfo<F>],
    main_trace: &RowMajorMatrix<F>,
    prover_table_data: &[(&str, &RowMajorMatrix<F>)],
) -> Vec<RowMajorMatrix<F>>
where
    F: Field + PrimeField32 + From<crate::Val<SC>> + Into<crate::Val<SC>>,
    SC: StarkGenericConfig,
{
    // Build table_data: for each table AIR, choose preprocessed or prover data.
    let table_data: Vec<&RowMajorMatrix<F>> = air_infos[1..]
        .iter()
        .map(|ai| {
            if let Some(ref prep) = ai.preprocessed {
                prep
            } else {
                let table_name = ai
                    .air
                    .table_name()
                    .expect("Non-main AIR must be a table with a name");
                prover_table_data
                    .iter()
                    .find(|(name, _)| *name == table_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "ProverTableAir '{}' requires an entry in prover_table_data",
                            table_name
                        )
                    })
                    .1
            }
        })
        .collect();

    let multiplicity_traces = generate_multiplicity_traces::<F, SC>(
        air_infos,
        &table_data,
        main_trace,
        &air_infos[0].lookups,
        &air_infos[0].lookup_row_scopes,
    );

    // Post-process: for ProverTableAir tables, combine data + multiplicity.
    multiplicity_traces
        .into_iter()
        .enumerate()
        .map(|(i, mult)| {
            if air_infos[i + 1].preprocessed.is_some() {
                mult
            } else {
                let table_name = air_infos[i + 1]
                    .air
                    .table_name()
                    .expect("Non-main AIR must be a table with a name");
                let prover_data = prover_table_data
                    .iter()
                    .find(|(name, _)| *name == table_name)
                    .unwrap()
                    .1;
                append_multiplicity_column(prover_data, &mult)
            }
        })
        .collect()
}
