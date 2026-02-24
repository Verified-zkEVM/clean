//! Functions for generating lookup AIRs with calculated traces

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use p3_air::lookup::Lookup;
use p3_field::{Field, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{Entry, SymbolicExpression};

use crate::StarkGenericConfig;

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
/// 1. Gets the main AIR's global lookups (element tuples with Direction::Receive)
/// 2. For each non-main AIR, extracts its table name
/// 3. Matches main AIR lookups to table AIRs by global interaction name
/// 4. Uses preprocessed.height() for table size
/// 5. Computes multiplicities by evaluating symbolic expressions on each main trace row
///
/// # Arguments
/// * `air_infos` - Vector of AirInfo instances (main + lookup airs)
/// * `main_trace` - The main execution trace (corresponds to air_infos[0])
/// * `main_air_lookups` - The lookups registered by the main AIR
pub fn generate_multiplicity_traces<F, SC>(
    air_infos: &[crate::key::AirInfo<F>],
    main_trace: &RowMajorMatrix<F>,
    main_air_lookups: &[Lookup<F>],
) -> Vec<RowMajorMatrix<F>>
where
    F: Field + PrimeField32 + From<crate::Val<SC>> + Into<crate::Val<SC>>,
    SC: StarkGenericConfig,
{
    let mut lookup_traces = Vec::new();

    // For each non-main AIR (i.e. preprocessed table AIR), match lookups by table name.
    // Skip AIRs without a preprocessed trace (e.g. MainTraceTableAir) — their
    // traces (including multiplicities) are built externally.
    for air_info in air_infos.iter().skip(1) {
        let preprocessed = match air_info.preprocessed.as_ref() {
            Some(p) => p,
            None => continue, // main-trace table — skip
        };

        let table_name = air_info
            .air
            .table_name()
            .expect("Non-main AIR must be a table with a name");

        let table_size = preprocessed.height();

        // Find the main AIR lookup that targets this table (by global interaction name)
        let matching_lookups: Vec<&Lookup<F>> = main_air_lookups
            .iter()
            .filter(|lookup| {
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
        for row_idx in 0..main_trace.height() {
            let row_slice: Vec<F> = main_trace.row(row_idx).unwrap().into_iter().collect();

            for lookup in &matching_lookups {
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
