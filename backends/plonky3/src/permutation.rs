//! Functions for generating lookup AIRs with calculated traces

extern crate alloc;

use alloc::vec::Vec;
use p3_air::{AirBuilder, ExtensionBuilder, PermutationAirBuilder, VirtualPairCol};
use p3_field::{ExtensionField, Field, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use crate::{
    ByteRangeAir, CleanAirInstance, Lookup, LookupType, StarkGenericConfig, Val, VerifyingKey,
};

/// Represents a lookup AIR with its calculated main trace
pub struct LookupAirWithTrace<F: Field> {
    pub air: ByteRangeAir<F>,
    pub main_trace: RowMajorMatrix<F>,
}

pub trait MultiTableBuilder: ExtensionBuilder {
    fn cumulative_sum(&self) -> Self::ExprEF {
        unimplemented!("cumulative_sum is not implemented for this builder")
    }
}

/// Generates lookup tables with multiplicity traces,
/// based on the lookup operations from the AirInfo instances.
///
/// This function:
/// 1. Uses the pre-computed lookup operations from the main air (index 0)
/// 2. Collect lookups and multiplicity traces for each lookup type using other airs
/// 3. Returns multiplicity traces
///
/// # Arguments
/// * `air_infos` - Vector of AirInfo instances (main + lookup airs)  
/// * `main_trace` - The main execution trace (corresponds to air_infos[0])
pub fn generate_multiplicity_traces<F, SC>(
    air_infos: &[crate::key::AirInfo<F>],
    main_trace: &RowMajorMatrix<F>,
) -> Vec<RowMajorMatrix<F>>
where
    F: Field + PrimeField32 + From<crate::Val<SC>> + Into<crate::Val<SC>>,
    SC: StarkGenericConfig,
{
    let mut lookup_traces = Vec::new();

    // Get lookup operations from the main air (first air in the list)
    let main_air_info = &air_infos[0];
    let lookups = main_air_info.lookups();
    let sends: Vec<_> = lookups
        .iter()
        .filter(|(_, is_send)| *is_send)
        .map(|(lookup, _)| lookup)
        .collect();

    // Main VK should only send lookups, not receive them
    let receives: Vec<_> = lookups.iter().filter(|(_, is_send)| !*is_send).collect();
    assert!(
        receives.is_empty(),
        "The main air should only send lookups, as it is not a lookup air"
    );

    // Group lookups by type and find corresponding airs in the VK
    // Process ByteRange lookups
    let byte_range_sends: Vec<_> = sends
        .iter()
        .filter(|send| matches!(send.kind, LookupType::ByteRange))
        .collect();

    if !byte_range_sends.is_empty() {
        // Find the corresponding ByteRange air in the VK
        let _byte_range_air_info = air_infos
            .iter()
            .find(|air_info| matches!(&air_info.air, CleanAirInstance::ByteRange(_)))
            .expect("ByteRange air not found in VK");

        // Create multiplicity trace for byte range lookups (256 possible values, 0-255)
        let mut multiplicity_trace = RowMajorMatrix::new(alloc::vec![F::ZERO; 256], 1);

        // Calculate multiplicities by evaluating lookup operations for each row
        for row_idx in 0..main_trace.height() {
            for send in &byte_range_sends {
                // Calculate the virtual column of the lookup values for the current row
                let row_slice: Vec<F> = main_trace.row(row_idx).unwrap().into_iter().collect();
                let v = send.value.apply::<F, F>(&[], &row_slice);

                // Convert lookup value to index of multiplicity trace and increment multiplicity
                let lookup_idx = v.as_canonical_u32() as usize;
                assert!(
                    lookup_idx < 256,
                    "Lookup value out of range for byte range lookup: {}",
                    lookup_idx
                );

                let m = multiplicity_trace.row_mut(lookup_idx).get_mut(0).unwrap();
                *m += F::ONE;
            }
        }

        lookup_traces.push(multiplicity_trace);
    }

    // TODO: Add support for other lookup types as needed

    lookup_traces
}

/// Generates a permutation trace for the given AIR.
/// 1. Builds the lookups using LookupBuilder for the given AIR.
/// 2. Computes the permutation trace based on the lookups and the traces for the Air.
pub fn generate_permutation_trace<SC, EF: ExtensionField<Val<SC>>>(
    air_info: &crate::key::AirInfo<Val<SC>>,
    main_trace: &RowMajorMatrix<Val<SC>>,
    random_elements: &[EF],
) -> (RowMajorMatrix<EF>, EF)
where
    SC: StarkGenericConfig,
{
    let z = random_elements[0];
    let lookups = air_info.lookups();

    let num_perm_cols = lookups.len() + 1; // +1 for cumulative sum column

    let mut permutation_trace = RowMajorMatrix::new(
        alloc::vec![EF::ZERO; main_trace.height() * num_perm_cols],
        num_perm_cols,
    );

    tracing::info!("perm height: {}", permutation_trace.height());

    // compute permutation trace via virtual columns represented by lookup values
    for row in 0..main_trace.height() {
        let r = permutation_trace.row_mut(row);

        let preprocessed_row: Vec<Val<SC>> = if let Some(pre) = air_info.preprocessed() {
            pre.row(row).unwrap().into_iter().collect()
        } else {
            Vec::new()
        };
        let main_row: Vec<Val<SC>> = main_trace.row(row).unwrap().into_iter().collect();

        for (i, (lookup, is_send)) in lookups.iter().enumerate() {
            let lookup_value: EF = lookup
                .value
                .apply::<Val<SC>, Val<SC>>(&preprocessed_row, &main_row)
                .into();
            let denominator: EF = z - lookup_value;

            let mut mult = lookup
                .multiplicity
                .apply::<Val<SC>, Val<SC>>(&preprocessed_row, &main_row);

            if !is_send {
                mult = -mult;
            }

            r[i] = EF::from(mult) / denominator;
        }
    }

    let local_cumulative_sums = permutation_trace
        .par_rows_mut()
        .map(|row| row.iter().take(num_perm_cols - 1).copied().sum::<EF>())
        .collect::<Vec<_>>();

    let zero = EF::ZERO;

    let local_cumulative_sums = local_cumulative_sums
        .into_iter()
        .scan(zero, |acc, val| {
            *acc += val;
            Some(*acc)
        })
        .collect::<Vec<_>>();

    let last_sum = *local_cumulative_sums.last().unwrap();

    // assign cumulative sums to the last column
    for (row, sum) in local_cumulative_sums.into_iter().enumerate() {
        let perm_val = permutation_trace
            .row_mut(row)
            .get_mut(num_perm_cols - 1)
            .unwrap();
        *perm_val = sum;
    }

    (permutation_trace, last_sum)
}

/// Evaluates permutation constraints
pub fn eval_permutation_constraints<AB>(
    lookups: &[(Lookup<VirtualPairCol<AB::F>>, bool)],
    builder: &mut AB,
) where
    AB: AirBuilder + PermutationAirBuilder + MultiTableBuilder,
    AB::Var: Copy,
{
    let main = builder.main();
    let preprocessed = builder.preprocessed();
    let perm = builder.permutation();

    let rands = builder.permutation_randomness();
    let rands: Vec<AB::ExprEF> = rands.iter().map(|x| (*x).into()).collect();
    let z = &rands[0];

    let main_local = main.row_slice(0).expect("main trace is empty?");
    let perm_local = perm.row_slice(0).expect("perm trace is empty?");
    let perm_next = perm.row_slice(1).expect("perm trace only has 1 row?");

    // constrain permutation entries (except for the cumulative sum column)
    for ((lookup, is_send), entry) in lookups.iter().zip(perm_local.iter()) {
        let entry: AB::ExprEF = (*entry).into();

        // Get preprocessed row once or use empty slice
        let preprocessed_row = preprocessed.as_ref().and_then(|p| p.row_slice(0));
        let empty_preprocessed: &[AB::Var] = &[];
        let preprocessed_ref = preprocessed_row.as_deref().unwrap_or(empty_preprocessed);

        let lookup_value: AB::ExprEF = lookup
            .value
            .apply::<AB::Expr, AB::Var>(preprocessed_ref, &main_local)
            .into();

        let denominator = z.clone() - lookup_value;

        let mut mult: AB::ExprEF = lookup
            .multiplicity
            .apply::<AB::Expr, AB::Var>(preprocessed_ref, &main_local)
            .into();

        if !is_send {
            mult = -mult;
        }

        builder.assert_eq_ext(entry * denominator, mult);
    }

    let sum_local: AB::ExprEF = perm_local
        .iter()
        .take(perm_local.len() - 1)
        .map(|x| (*x).into())
        .sum();
    let sum_next: AB::ExprEF = perm_next
        .iter()
        .take(perm_next.len() - 1)
        .map(|x| (*x).into())
        .sum();

    let perm_local_last: AB::ExprEF = (*perm_local.last().unwrap()).into();
    let perm_next_last: AB::ExprEF = (*perm_next.last().unwrap()).into();

    // constrain the first row
    builder
        .when_first_row()
        .assert_eq_ext(sum_local, perm_local_last.clone());

    // constrain the transition window
    builder
        .when_transition()
        .assert_eq_ext(sum_next, perm_next_last - perm_local_last.clone());

    // constrain the last row
    let cumulative_sum: AB::ExprEF = builder.cumulative_sum();
    builder
        .when_last_row()
        .assert_eq_ext(cumulative_sum, perm_local_last);
}
