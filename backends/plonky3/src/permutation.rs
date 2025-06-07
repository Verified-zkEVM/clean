//! Factory functions for generating lookup AIRs with calculated traces

extern crate alloc;

use core::panic;

use alloc::vec::Vec;
use p3_air::{Air, AirBuilder, ExtensionBuilder, PairBuilder, PermutationAirBuilder, VirtualPairCol};
use p3_baby_bear::BabyBear;
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_matrix::{Matrix, dense::RowMajorMatrix};

use crate::{ByteRangeAir, MainAir, Lookup, LookupBuilder, LookupType, StarkGenericConfig,  Val};

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

/// Factory function that generates lookup AIRs with calculated main traces
/// based on the lookup operations in the given CleanAir instance.
///
/// This function:
/// 1. Evaluates the CleanAir to extract lookup operations
/// 2. Calculates multiplicity traces for each lookup type
/// 3. Returns corresponding lookup AIRs with their traces
///
/// # Arguments
/// * `clean_air` - The CleanAir instance containing lookup operations
/// * `trace` - The main execution trace
///
/// # Returns
/// A vector of lookup AIRs paired with their calculated main traces
pub fn generate_lookup_airs<F>(
    // todo: 
    clean_air: &MainAir<F>,
    trace: &RowMajorMatrix<F>,
) -> Vec<LookupAirWithTrace<F>>
where
    F: Field + PrimeField64,
{
    let mut lookup_airs = Vec::new();

    // Create a lookup builder to extract lookup operations
    let mut lookup_builder = LookupBuilder::new(0, trace.width());
    clean_air.eval(&mut lookup_builder);
    let (sends, _receives) = lookup_builder.messages();

    // Group lookups by type and calculate multiplicities
    // For now, we focus on ByteRange lookups
    let mut has_byte_range_lookups = false;

    // Check if we have any byte range lookups
    for send in &sends {
        if matches!(send.kind, LookupType::ByteRange) {
            has_byte_range_lookups = true;
            break;
        }
    }

    if has_byte_range_lookups {
        // Create multiplicity trace for byte range lookups (256 possible values, 0-255)
        let mut multiplicity_trace = RowMajorMatrix::new(
            alloc::vec![F::ZERO; 256],
            1,
        );

        // Calculate multiplicities by evaluating lookup operations for each row
        for row_idx in 0..trace.height() {
            for send in &sends {
                if matches!(send.kind, LookupType::ByteRange) {
                    // Apply the lookup expression to get the value being looked up
                    let row_slice: Vec<F> = trace.row(row_idx).unwrap().into_iter().collect();
                    let v = send.value.apply::<F, F>(&[], &row_slice);
                    
                    // Convert to index and increment multiplicity
                    let lookup_value = v.as_canonical_u64() as usize;
                    if lookup_value < 256 {
                        let m = multiplicity_trace.row_mut(lookup_value).get_mut(0).unwrap();
                        *m += F::ONE;
                    }
                    else {
                        panic!("Lookup value out of range for byte range lookup: {}", lookup_value);
                    }
                }
            }
        }

        // Create the ByteRangeAir with its calculated trace
        let byte_range_air = ByteRangeAir::new();
        lookup_airs.push(LookupAirWithTrace {
            air: byte_range_air,
            main_trace: multiplicity_trace,
        });
    }

    // TODO: Add support for other lookup types as needed

    lookup_airs
}

/// Generates a permutation trace for the given AIR.
/// 1. Builds the lookups using LookupBuilder for the given AIR.
/// 2. Computes the permutation trace based on the lookups and the traces for the Air.
pub fn generate_permutation_trace<SC, A, EF: ExtensionField<Val<SC>>>(
    air: &A, // todo: use CleanAirWrapper
    main: &RowMajorMatrix<Val<SC>>,
    preprocessed: &RowMajorMatrix<Val<SC>>,
    random_elements: &[EF],
) -> (RowMajorMatrix<EF>, EF)
where
    SC: StarkGenericConfig,
    A: Air<LookupBuilder<Val<SC>>>,
{
    let z = random_elements[0];
    let mut lookup_builder = LookupBuilder::new(preprocessed.width(), main.width());
    air.eval(&mut lookup_builder);
    let lookups = lookup_builder.messages();
    // flatten the lookups into a single vector
    let lookups = lookups.0
        .into_iter().map(|l| (l, true))
        .chain(lookups.1.into_iter().map(|l| (l, false)))
        .collect::<Vec<_>>();

    let num_perm_cols = lookups.len() + 1; // +1 for cumulative sum column
    
    let mut permutation_trace = RowMajorMatrix::new(
        alloc::vec![EF::ZERO; main.height() * num_perm_cols],
        num_perm_cols, 
    );

    tracing::info!("perm height: {}", permutation_trace.height());

    // compute permutation trace via virtual columns represented by lookup values
    for row in 0..main.height() {
        // tracing::info!("Processing row {}", row);
        let r = permutation_trace.row_mut(row);

        for (i, (lookup, is_send)) in lookups.iter().enumerate() {
            let preprocessed_row: Vec<Val<SC>> = preprocessed.row(row).unwrap().into_iter().collect();
            let main_row: Vec<Val<SC>> = main.row(row).unwrap().into_iter().collect();
            let lookup_value: EF = lookup.value.apply::<Val<SC>, Val<SC>>(&preprocessed_row, &main_row).into();
            let denominator: EF = z - lookup_value;

            let mut mult = lookup.multiplicity.apply::<Val<SC>, Val<SC>>(&preprocessed_row, &main_row);

            if !is_send {
                mult = -mult;
            }

            r[i] = EF::from(mult) / denominator;
        }
    }

    let local_cumulative_sums = permutation_trace
        .par_rows_mut()
        .map(|row| {
            row.iter().take(num_perm_cols - 1).copied().sum::<EF>()
        })
        .collect::<Vec<_>>();

    let zero = EF::ZERO;

    let local_cumulative_sums = local_cumulative_sums.into_iter().scan(
        zero, |acc, val| {
            *acc += val;
            Some(*acc)
        }
    ).collect::<Vec<_>>();

    let last_sum = local_cumulative_sums.last().unwrap().clone();

    // assign cumulative sums to the last column
    for (row, sum) in local_cumulative_sums.into_iter().enumerate() {
        let perm_val = permutation_trace.row_mut(row).get_mut(num_perm_cols - 1).unwrap();
        *perm_val = sum;
    }

    (permutation_trace, last_sum)
}

/// Evaluates permutation constraints
pub fn eval_permutation_constraints<AB>(
    lookups: &[(Lookup<VirtualPairCol<AB::F>>, bool)],
    builder: &mut AB,
)
where
    AB: AirBuilder + PairBuilder + PermutationAirBuilder + MultiTableBuilder,
{
    let main = builder.main();
    let preprocessed = builder.preprocessed();
    let perm = builder.permutation();

    let rands = builder.permutation_randomness();
    let rands: Vec<AB::ExprEF> = rands.iter().map(|x| (*x).into()).collect();
    let z = &rands[0];

    let main_local = main.row_slice(0).expect("main trace is empty?");
    let preprocessed_local = preprocessed.row_slice(0).expect("preprocessed trace is empty?");
    let perm_local = perm.row_slice(0).expect("perm trace is empty?");
    let perm_next = perm.row_slice(1).expect("perm trace only has 1 row?");

    // constrain permutation entries (except for the cumulative sum column)
    for ((lookup, is_send), entry) in lookups.iter().zip(perm_local.iter()) {
        let entry: AB::ExprEF = (*entry).into();
        let lookup_value: AB::ExprEF = lookup.value.apply::<AB::Expr, AB::Var>(
                &preprocessed_local,
                &main_local,
            ).into();

        let denominator = z.clone() - lookup_value;

        let mut mult: AB::ExprEF = lookup.multiplicity.apply::<AB::Expr, AB::Var>(
                &preprocessed_local,
                &main_local,
            ).into();

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
    builder.when_first_row().assert_eq_ext(sum_local, perm_local_last.clone());

    // constrain the transition window
    builder.when_transition().assert_eq_ext(sum_next, perm_next_last - perm_local_last.clone());

    // // constrain the last row
    let cumulative_sum: AB::ExprEF = builder.cumulative_sum();
    builder.when_last_row().assert_eq_ext(
        cumulative_sum,
        perm_local_last,
    );
}