use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::Air;
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_matrix::Matrix;
use p3_util::zip_eq::zip_eq;
use tracing::instrument;

use crate::{AirInfo, PcsError, Proof, StarkGenericConfig, Val, VerifierConstraintFolder, VerifyingKey, VK};

#[instrument(skip_all)]
pub fn verify<SC>(
    config: &SC,
    air_infos: &Vec<AirInfo<Val<SC>>>,
    proof: &Proof<SC>,
    public_values: &Vec<Val<SC>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
{
    let Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits,
    } = proof;


    let mut challenger = config.initialise_challenger();
    challenger.observe_slice(
        &degree_bits
            .iter()
            .map(|&d| Val::<SC>::from_usize(d))
            .collect_vec(),
    );

    // todo: construct VK without relying on degree_bits
    let vk = VK::new(air_infos.clone(), degree_bits.iter().map(|d| 1 << d).collect_vec(), config);

    challenger.observe(commitments.trace.clone());
    // Use VK's preprocessed commitment instead of proof's preprocessed commitment
    challenger.observe(vk.preprocessed_commitment().clone());
    challenger.observe_slice(public_values);

    // Sample permutation challenges for each air info.
    let permutation_challenges: Vec<SC::Challenge> = (0..air_infos.len())
        .map(|_| challenger.sample_algebra_element())
        .collect();

    challenger.observe_slice(
        &opened_values
            .iter()
            .flat_map(|o| o.local_cumulative_sum.as_basis_coefficients_slice())
            .copied()
            .collect_vec(),
    );

    challenger.observe(commitments.perm.clone());

    let alpha: SC::Challenge = challenger.sample_algebra_element();
    challenger.observe(commitments.quotient_chunks.clone());

    // Sample an evaluation point `zeta` for the out-of-domain evaluation.
    let zeta: SC::Challenge = challenger.sample_algebra_element();

    let pcs = config.pcs();

    // First, collect all verification data and validate shapes for all AIRs
    let mut all_air_data = Vec::new();
    let mut trace_openings = Vec::new();
    let mut preprocessed_openings = Vec::new();
    let mut perm_openings = Vec::new();
    let mut quotient_openings = Vec::new();

    let log_quotient_degrees = (0..air_infos.len())
        .map(|i| air_infos[i].log_quotient_degree(public_values.len()))
        .collect::<Vec<_>>();

    for i in 0..air_infos.len() {
        let air_info = &air_infos[i];
        let pre = if let Some(preprocessed) = air_info.preprocessed() {
            preprocessed
        } else {
            // Create a default preprocessed trace if none exists
            let degree = 1 << degree_bits[i];
            RowMajorMatrix::new(vec![Val::<SC>::default(); degree], 1)
        };
        let opened_values_i = &opened_values[i];
        let degree_bits_i = degree_bits[i];

        let degree = 1 << degree_bits_i;
        let log_quotient_degree = log_quotient_degrees[i];

        tracing::info!("log_quotient_degree: {}", log_quotient_degree);
        let quotient_degree = 1 << log_quotient_degree;

        let trace_domain = pcs.natural_domain_for_degree(degree);

        let quotient_domain =
            trace_domain.create_disjoint_domain(1 << (degree_bits_i + log_quotient_degree));
        let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);

        let air_width = air_info.width();
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
            air_info,
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
        (vk.preprocessed_commitment().clone(), preprocessed_openings),
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
                chunk
                    .iter()
                    .enumerate()
                    .map(|(e_i, &x)| {
                        // Using ith_basis_element which is available instead of monomial
                        SC::Challenge::ith_basis_element(e_i).unwrap() * x
                    })
                    .sum()
            })
            .collect::<Vec<SC::Challenge>>()
    };

    // Init accumulative value for the cumulative sums
    let zero = SC::Challenge::default();
    // Now process constraint evaluation for each AIR
    for (air_info, trace_domain, quotient_chunks_domains, opened_values) in all_air_data {
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

        let quotient = opened_values
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
            RowMajorMatrixView::new_row(&opened_values.trace_local),
            RowMajorMatrixView::new_row(&opened_values.trace_next),
        );
        let preprocessed = VerticalPair::new(
            RowMajorMatrixView::new_row(&opened_values.preprocessed_local),
            RowMajorMatrixView::new_row(&opened_values.preprocessed_next),
        );

        let unflattened_perm_local = unflatten(&opened_values.perm_local);
        let unflattened_perm_next = unflatten(&opened_values.perm_next);
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
            local_cumulative_sum: opened_values.local_cumulative_sum,
        };
        air_info.eval_constraints(&mut folder);
        let folded_constraints = folder.accumulator;

        tracing::info!(
            "folded_constraints: {}, quotient: {}, vanishing: {}",
            folded_constraints,
            quotient,
            trace_domain.vanishing_poly_at_point(zeta)
        );
        // Finally, check that
        //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
        if folded_constraints * sels.inv_vanishing != quotient {
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
