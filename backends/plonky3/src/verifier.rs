//! See `prover.rs` for an overview of the protocol and a more detailed soundness analysis.

use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::{Air, BaseAir};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field};
use p3_matrix::{Matrix};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_util::zip_eq::zip_eq;
use tracing::instrument;

use p3_uni_stark::{SymbolicAirBuilder, get_log_quotient_degree};
use crate::{BaseCleanAir, PcsError, Proof, StarkGenericConfig, Val, VerifierConstraintFolder};

#[instrument(skip_all)]
pub fn verify<SC, A>(
    config: &SC,
    airs: Vec<&A>,
    pres: Vec<RowMajorMatrix<Val<SC>>>,
    proof: &Proof<SC>,
    //todo: supply vk instead
    public_values: &Vec<Val<SC>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    A: BaseCleanAir<Val<SC>> + Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<VerifierConstraintFolder<'a, SC>>,
{
    let zero = SC::Challenge::default();

    let Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits,
    } = proof;

    let mut challenger = config.initialise_challenger();
    challenger.observe(commitments.trace.clone());
    challenger.observe(commitments.preprocessed.clone());
    challenger.observe_slice(public_values);

    let permutation_challenges: Vec<SC::Challenge> = (0..airs.len())
        .map(|_| challenger.sample_algebra_element())
        .collect();

    tracing::info!("permutation challenges: {:?}", permutation_challenges);

    challenger.observe(commitments.perm.clone());

    let alpha: SC::Challenge = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());

    let zeta: SC::Challenge = challenger.sample_algebra_element();

    tracing::info!("alpha: {}", alpha);
    tracing::info!("zeta: {}", zeta);

    let pcs = config.pcs();

    // First, collect all verification data and validate shapes for all AIRs
    let mut all_air_data = Vec::new();
    let mut trace_openings = Vec::new();
    let mut preprocessed_openings = Vec::new();
    let mut perm_openings = Vec::new();
    let mut quotient_openings = Vec::new();

    let log_quotient_degrees = (0..airs.len())
        .map(|i| {
            airs[i].log_quotient_degree(public_values.len())
        })
        .collect::<Vec<_>>();

    for i in 0..airs.len() {
        let air = airs[i];
        let pre = &pres[i];
        let opened_values_i = &opened_values[i];
        let degree_bits_i = degree_bits[i];

        let degree = 1 << degree_bits_i;
        // let log_quotient_degree =
        //     get_log_quotient_degree::<Val<SC>, A>(air, pre.width, public_values.len(), 0);
        let log_quotient_degree = log_quotient_degrees[i];
        
        tracing::info!("log_quotient_degree: {}", log_quotient_degree);
        let quotient_degree = 1 << log_quotient_degree;

        let trace_domain = pcs.natural_domain_for_degree(degree);

        let quotient_domain =
            trace_domain.create_disjoint_domain(1 << (degree_bits_i + log_quotient_degree));
        let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

        let air_width = <A as BaseAir<Val<SC>>>::width(air);
        let valid_shape = opened_values_i.trace_local.len() == air_width
            && opened_values_i.trace_next.len() == air_width
            && opened_values_i.preprocessed_local.len() == pre.width()
            && opened_values_i.preprocessed_next.len() == pre.width()
            //todo: review this perm check
            && !opened_values_i.perm_local.is_empty()  
            && !opened_values_i.perm_next.is_empty()
            && opened_values_i.perm_local.len() == opened_values_i.perm_next.len()
            && opened_values_i.quotient_chunks.len() == quotient_degree
            && opened_values_i
                .quotient_chunks
                .iter()
                .all(|qc| qc.len() == <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION);
        
        if !valid_shape {
            tracing::info!("invalid proof shape: trace_local: {}, trace_next: {}, quotient_chunks: {}, expected air width: {}, quotient degree: {}, challenge dimension: {}",
                opened_values_i.trace_local.len(),
                opened_values_i.trace_next.len(),
                opened_values_i.quotient_chunks.len(),
                air_width,
                quotient_degree,
                <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION,
            );
            return Err(VerificationError::InvalidProofShape);
        }

        // Get an out-of-domain point to open our values at.
        let zeta_next = trace_domain.next_point(zeta).unwrap();

        // Store data needed for constraint evaluation later
        all_air_data.push((
            air,
            trace_domain,
            quotient_chunks_domains.clone(),
            opened_values_i,
        ));

        // Collect opening points for each commitment type
        trace_openings.push((
            trace_domain,
            vec![
                (zeta, opened_values_i.trace_local.clone()),
                (zeta_next, opened_values_i.trace_next.clone()),
            ],
        ));

        preprocessed_openings.push((
            trace_domain,
            vec![
                (zeta, opened_values_i.preprocessed_local.clone()),
                (zeta_next, opened_values_i.preprocessed_next.clone()),
            ],
        ));

        perm_openings.push((
            trace_domain,
            vec![
                (zeta, opened_values_i.perm_local.clone()),
                (zeta_next, opened_values_i.perm_next.clone()),
            ],
        ));

        // Collect quotient chunk openings
        let quotient_chunk_openings = zip_eq(
            quotient_chunks_domains.iter(),
            &opened_values_i.quotient_chunks,
            VerificationError::InvalidProofShape,
        )?
            .map(|(domain, values)| (*domain, vec![(zeta, values.clone())]))
            .collect_vec();
        
        quotient_openings.extend(quotient_chunk_openings);
    }

    // Prepare commitments with their respective opening points
    let coms_to_verify = vec![
        (commitments.trace.clone(), trace_openings),
        (commitments.preprocessed.clone(), preprocessed_openings),
        (commitments.perm.clone(), perm_openings),
        (commitments.quotient_chunks.clone(), quotient_openings),
    ];

    // Verify all commitments at once
    pcs.verify(coms_to_verify, opening_proof, &mut challenger)
        .map_err(VerificationError::InvalidOpeningArgument)?;

    // Reconstruct the prmutation opening values as extension elements.
    let unflatten = |v: &[SC::Challenge]| {
        v.chunks_exact(SC::Challenge::DIMENSION)
            .map(|chunk| {
                chunk.iter().enumerate().map(|(e_i, &x)| {
                    // Using ith_basis_element which is available instead of monomial
                    SC::Challenge::ith_basis_element(e_i).unwrap() * x
                }).sum()
            })
            .collect::<Vec<SC::Challenge>>()
    };

    // Now process constraint evaluation for each AIR
    for (air, trace_domain, quotient_chunks_domains, opened_values_i) in all_air_data {

        let zps = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| {
                        other_domain.vanishing_poly_at_point(zeta)
                            * other_domain
                                .vanishing_poly_at_point(domain.first_point())
                                .inverse()
                    })
                    .product::<SC::Challenge>()
            })
            .collect_vec();

        let quotient = opened_values_i
            .quotient_chunks
            .iter()
            .enumerate()
            .map(|(ch_i, ch)| {
                tracing::info!("chi {}", ch_i);
                // We checked in valid_shape the length of "ch" is equal to
                // <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION. Hence
                // the unwrap() will never panic.
                zps[ch_i]
                    * ch.iter()
                        .enumerate()
                        .map(|(e_i, &c)| SC::Challenge::ith_basis_element(e_i).unwrap() * c)
                        .sum::<SC::Challenge>()
            })
            .sum::<SC::Challenge>();

        let sels = trace_domain.selectors_at_point(zeta);

        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(&opened_values_i.trace_local),
            RowMajorMatrixView::new_row(&opened_values_i.trace_next),
        );
        let preprocessed = VerticalPair::new(
            RowMajorMatrixView::new_row(&opened_values_i.preprocessed_local),
            RowMajorMatrixView::new_row(&opened_values_i.preprocessed_next),
        );

        let unflattened_perm_local = unflatten(&opened_values_i.perm_local);
        let unflattened_perm_next = unflatten(&opened_values_i.perm_next);
        let perm = VerticalPair::new(
            RowMajorMatrixView::new_row(&unflattened_perm_local),
            RowMajorMatrixView::new_row(&unflattened_perm_next),
        );

        let mut folder: VerifierConstraintFolder<SC> = VerifierConstraintFolder {
            main,
            preprocessed,
            perm,
            public_values,
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
            alpha,
            accumulator: zero,
            perm_challenges: &permutation_challenges,
            local_cumulative_sum: opened_values_i.local_cumulative_sum,
        };
        air.eval_constraints(&mut folder);
        let folded_constraints = folder.accumulator;

        // Finally, check that
        //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
        if folded_constraints * sels.inv_vanishing != quotient {
            tracing::info!("folded_constraints: {}, quotient: {}, vanishing: {}", folded_constraints, quotient, trace_domain.vanishing_poly_at_point(zeta));
            return Err(VerificationError::OodEvaluationMismatch);
        }
    }

    // check the sum of cumulative sums is zero
    let cum_sums = opened_values
        .iter()
        .map(|o| o.local_cumulative_sum)
        .sum::<SC::Challenge>();
    
    if cum_sums != zero {
        return Err(VerificationError::CumulativeSumMismatch);
    }

    Ok(())
}

#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    InvalidProofShape,
    /// An error occurred while verifying the claimed openings.
    InvalidOpeningArgument(PcsErr),
    /// Out-of-domain evaluation mismatch, i.e. `constraints(zeta)` did not match
    /// `quotient(zeta) Z_H(zeta)`.
    OodEvaluationMismatch,
    CumulativeSumMismatch,
    /// The FRI batch randomization does not correspond to the ZK setting.
    RandomizationError,
}
