//! Functions for generating lookup AIRs with calculated traces

extern crate alloc;

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

    // For each non-main AIR (i.e. preprocessed table AIR), match lookups by table name
    for air_info in air_infos.iter().skip(1) {
        let table_name = air_info
            .air
            .table_name()
            .expect("Non-main AIR must be a preprocessed table with a name");

        let table_size = air_info
            .preprocessed
            .as_ref()
            .expect("Preprocessed table AIR must have a preprocessed trace")
            .height();

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

        // Create multiplicity trace for this table
        let mut multiplicity_trace = RowMajorMatrix::new(alloc::vec![F::ZERO; table_size], 1);

        // Calculate multiplicities by evaluating lookup expressions for each row.
        // For each element tuple in the matching lookups, evaluate the first element
        // (the address/index column) to determine which table row is accessed.
        for row_idx in 0..main_trace.height() {
            let row_slice: Vec<F> = main_trace.row(row_idx).unwrap().into_iter().collect();

            for lookup in &matching_lookups {
                for tuple in &lookup.element_exprs {
                    // Evaluate the first element expression to get the lookup index
                    let v = eval_symbolic_on_row(&tuple[0], &row_slice, &[]);
                    let lookup_idx = v.as_canonical_u32() as usize;

                    assert!(
                        lookup_idx < table_size,
                        "Lookup value {} out of range for table '{}' (size {})",
                        lookup_idx,
                        table_name,
                        table_size
                    );

                    let m = multiplicity_trace.row_mut(lookup_idx).get_mut(0).unwrap();
                    *m += F::ONE;
                }
            }
        }

        lookup_traces.push(multiplicity_trace);
    }

    lookup_traces
}
