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
pub fn eval_symbolic_on_row<F: Field>(
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
/// 4. Uses preprocessed.height() for table size
/// 5. Computes multiplicities by evaluating the signed multiplicity expressions on
///    each main trace row (Direction::Receive adds, Direction::Send subtracts)
///
/// # Arguments
/// * `table_air_infos` - The preprocessed-table AirInfo instances (excludes the main AIR)
/// * `main_trace` - The main execution trace
/// * `selector_trace` - The preprocessed selector trace for lookup row scopes (if any)
/// * `main_air_lookups` - The lookups registered by the main AIR
/// * `lookup_row_scopes` - Row scope for each lookup, parallel to `main_air_lookups`
pub fn generate_multiplicity_traces<F, SC>(
    table_air_infos: &[crate::key::AirInfo<F>],
    main_trace: &RowMajorMatrix<F>,
    selector_trace: Option<&RowMajorMatrix<F>>,
    main_air_lookups: &[Lookup<F>],
    lookup_row_scopes: &[LookupRowScope],
) -> Vec<RowMajorMatrix<F>>
where
    F: Field + PrimeField32 + From<crate::Val<SC>> + Into<crate::Val<SC>>,
    SC: StarkGenericConfig,
{
    assert_eq!(
        main_air_lookups.len(),
        lookup_row_scopes.len(),
        "main_air_lookups and lookup_row_scopes must have the same length"
    );
    if let Some(sel) = selector_trace {
        assert_eq!(
            sel.height(),
            main_trace.height(),
            "selector_trace height ({}) must match main_trace height ({})",
            sel.height(),
            main_trace.height()
        );
    }

    let mut lookup_traces = Vec::new();

    // For each preprocessed table AIR, match lookups by table name
    for air_info in table_air_infos {
        let table_name = air_info
            .air
            .table_name()
            .expect("Non-main AIR must be a preprocessed table with a name");

        let preprocessed = air_info
            .preprocessed
            .as_ref()
            .expect("Preprocessed table AIR must have a preprocessed trace");

        let table_size = preprocessed.height();

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

        // Build index: map from column-value tuple → row index in the preprocessed table.
        // This correctly handles tables whose column-0 values are not equal to the row index.
        let mut row_index: BTreeMap<Vec<u32>, usize> = BTreeMap::new();
        for row_idx in 0..table_size {
            let prep_row: Vec<F> = preprocessed.row(row_idx).unwrap().into_iter().collect();
            let key: Vec<u32> = prep_row.iter().map(|v| v.as_canonical_u32()).collect();
            row_index.insert(key, row_idx);
        }

        // Create multiplicity trace for this table
        let mut multiplicity_trace = RowMajorMatrix::new(alloc::vec![F::ZERO; table_size], 1);

        // Calculate multiplicities by evaluating ALL columns of each lookup tuple
        // and looking up the resulting values in the preprocessed table index.
        //
        // The signed multiplicity expression (from Lookup::multiplicities_exprs)
        // is evaluated to determine the contribution: Direction::Receive yields +1,
        // Direction::Send yields -1 (on active rows).
        let height = main_trace.height();
        for row_idx in 0..height {
            let row_slice: Vec<F> = main_trace.row(row_idx).unwrap().into_iter().collect();
            let prep_slice: Vec<F> = selector_trace
                .map(|s| s.row(row_idx).unwrap().into_iter().collect())
                .unwrap_or_default();

            for &(global_idx, ref lookup) in &matching_lookups {
                if !lookup_row_scopes[global_idx].is_active(row_idx, height) {
                    continue;
                }
                for (tuple_idx, tuple) in lookup.element_exprs.iter().enumerate() {
                    // Evaluate ALL element expressions to get the full lookup key
                    let values: Vec<u32> = tuple
                        .iter()
                        .map(|expr| eval_symbolic_on_row(expr, &row_slice, &prep_slice).as_canonical_u32())
                        .collect();

                    let table_row = row_index.get(&values).unwrap_or_else(|| {
                        panic!(
                            "Lookup values {:?} not found in table '{}' (size {})",
                            values, table_name, table_size
                        )
                    });

                    // Evaluate the signed multiplicity: positive for Receive,
                    // negative for Send (Direction::Send negates the mult).
                    let mult_contribution = eval_symbolic_on_row(
                        &lookup.multiplicities_exprs[tuple_idx],
                        &row_slice,
                        &prep_slice,
                    );
                    let m = multiplicity_trace.row_mut(*table_row).get_mut(0).unwrap();
                    *m += mult_contribution;
                }
            }
        }

        lookup_traces.push(multiplicity_trace);
    }

    lookup_traces
}
