use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::lookup::{Kind, LookupData};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, PackedValue, PrimeCharacteristicRing};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::lookup_traits::LookupGadget;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;
use p3_util::zip_eq::zip_eq;
use tracing::{debug_span, info_span, instrument};

use crate::{
    AirInfo, Commitments, Domain, OpenedValues, PackedChallenge, PackedVal, Proof,
    ProverConstraintFolder, StarkGenericConfig, Val, VerifyingKey, VK,
};

#[instrument(skip_all)]
pub fn prove<SC>(
    config: &SC,
    air_infos: &Vec<AirInfo<Val<SC>>>,
    traces: &[RowMajorMatrix<Val<SC>>],
    public_values: &Vec<Val<SC>>,
) -> Proof<SC>
where
    SC: StarkGenericConfig,
{
    let pcs = config.pcs();
    let mut challenger = config.initialise_challenger();
    let gadget = LogUpGadget::new();

    // Ensure we have the same number of traces as air infos
    assert_eq!(
        traces.len(),
        air_infos.len(),
        "Number of traces must match number of AirInfo instances"
    );

    let degrees = traces.iter().map(|trace| trace.height());

    let log_degrees = degrees.clone().map(log2_strict_usize).collect_vec();

    // observe the degrees of the traces
    challenger.observe_slice(
        &log_degrees
            .iter()
            .map(|&d| Val::<SC>::from_usize(d))
            .collect_vec(),
    );

    let vk = VK::new(air_infos.to_vec(), degrees.clone().collect_vec(), config);

    let constraint_counts = air_infos
        .iter()
        .map(|air_info| air_info.count_constraints(public_values.len()))
        .collect_vec();

    let log_quotient_degrees = air_infos
        .iter()
        .map(|air_info| air_info.log_quotient_degree(public_values.len()))
        .collect::<Vec<_>>();

    let quotient_degrees = log_quotient_degrees.iter().map(|&d| 1 << d).collect_vec();

    let trace_domains: Vec<Domain<SC>> = degrees
        .clone()
        .map(|d| pcs.natural_domain_for_degree(d))
        .collect_vec();

    let traces_and_domains = zip_eq(
        trace_domains.iter(),
        traces.iter(),
        "Trace domains and traces length mismatch",
    )
    .unwrap()
    .map(|(domain, trace)| (*domain, trace.clone()))
    .collect_vec();

    let (trace_commit, trace_data) =
        info_span!("commit to trace data").in_scope(|| pcs.commit(traces_and_domains));

    // Use the preprocessed commitment and data from the VK
    let pre_commit = vk.preprocessed_commitment().clone();
    let pre_data = vk.preprocessed_data();

    // Observe the instance.
    challenger.observe(trace_commit.clone());
    challenger.observe(pre_commit.clone());
    challenger.observe_slice(public_values);

    // Determine the number of global lookups from the main AIR (air_infos[0])
    let main_air_lookups = &air_infos[0].lookups;
    let num_global_lookups = main_air_lookups
        .iter()
        .filter(|l| matches!(l.kind, Kind::Global(_)))
        .count();

    // Total permutation challenges: 2 per global lookup (alpha + beta)
    let num_perm_challenges = 2 * num_global_lookups;

    // Get the challenges for the permutation trace calculation.
    let permutation_challenges: Vec<SC::Challenge> = (0..num_perm_challenges)
        .map(|_| challenger.sample_algebra_element())
        .collect_vec();

    // Compute permutation traces using LogUpGadget
    let mut all_lookup_data: Vec<Vec<LookupData<SC::Challenge>>> = Vec::new();

    let perm_traces: Vec<RowMajorMatrix<SC::Challenge>> = air_infos
        .iter()
        .enumerate()
        .zip(traces.iter())
        .map(|((air_idx, air_info), trace)| {
            let lookups = &air_info.lookups;

            if lookups.is_empty() {
                // No lookups for this AIR - create empty permutation trace
                let empty_perm =
                    RowMajorMatrix::new(vec![SC::Challenge::ZERO; trace.height()], 1);
                all_lookup_data.push(Vec::new());
                return empty_perm;
            }

            // Determine which challenges this AIR gets
            let air_challenges = if air_idx == 0 {
                // Main AIR gets all challenges
                permutation_challenges.clone()
            } else {
                // Table AIR i gets the challenges corresponding to its table
                // Find which main AIR lookup index corresponds to this table
                let table_name = air_info
                    .air
                    .table_name()
                    .expect("Non-main AIR must have a table name");

                let main_lookup_idx = main_air_lookups
                    .iter()
                    .position(|l| {
                        if let Kind::Global(name) = &l.kind {
                            name == table_name
                        } else {
                            false
                        }
                    })
                    .expect("Table AIR must correspond to a main AIR lookup");

                // This table's challenges are at index [2*main_lookup_idx .. 2*main_lookup_idx+2]
                permutation_challenges[2 * main_lookup_idx..2 * main_lookup_idx + 2].to_vec()
            };

            // Prepare lookup_data for global lookups
            let mut lookup_data: Vec<LookupData<SC::Challenge>> = lookups
                .iter()
                .filter_map(|l| {
                    if let Kind::Global(name) = &l.kind {
                        Some(LookupData {
                            name: name.clone(),
                            aux_idx: l.columns[0],
                            expected_cumulated: SC::Challenge::default(),
                        })
                    } else {
                        None
                    }
                })
                .collect();

            let preprocessed = air_info.preprocessed.clone();

            let perm_trace = gadget.generate_permutation::<SC>(
                trace,
                &preprocessed,
                public_values,
                lookups,
                &mut lookup_data,
                &air_challenges,
            );

            all_lookup_data.push(lookup_data);
            perm_trace
        })
        .collect_vec();

    // Collect all expected_cumulated values for observation
    let all_expected_cumulated: Vec<Vec<SC::Challenge>> = all_lookup_data
        .iter()
        .map(|data| data.iter().map(|d| d.expected_cumulated).collect())
        .collect();

    // Observe expected_cumulated values
    challenger.observe_slice(
        &all_expected_cumulated
            .iter()
            .flat_map(|v| {
                v.iter()
                    .flat_map(|s| s.as_basis_coefficients_slice().iter())
            })
            .cloned()
            .collect_vec(),
    );

    let perm_and_domains: Vec<_> = zip_eq(
        trace_domains.iter(),
        perm_traces.iter(),
        "Trace domains and perm traces length mismatch",
    )
    .unwrap()
    .map(|(domain, perm_trace)| {
        tracing::info!("perm trace width: {}", perm_trace.width());
        (*domain, perm_trace.clone().flatten_to_base())
    })
    .collect();

    let (perm_commit, perm_data) =
        info_span!("commit to permutation traces").in_scope(|| pcs.commit(perm_and_domains));

    challenger.observe(perm_commit.clone());

    // Get the Fiat Shamir challenge which will be used to combine all constraint polynomials
    // into a single polynomial.
    let alpha: SC::Challenge = challenger.sample_algebra_element();

    let quotient_domains = zip_eq(
        zip_eq(
            trace_domains.iter(),
            log_degrees.iter(),
            "Trace domains and log degrees length mismatch",
        )
        .unwrap(),
        log_quotient_degrees.iter(),
        "Combined domains and log quotient degrees length mismatch",
    )
    .unwrap()
    .map(|((trace_domain, &log_degree), &log_quotient_degree)| {
        trace_domain.create_disjoint_domain(1 << (log_degree + log_quotient_degree))
    })
    .collect_vec();

    let quotient_values = zip_eq(
        air_infos.iter().enumerate(),
        trace_domains.iter(),
        "Air infos and trace domains length mismatch",
    )
    .unwrap()
    .map(|((i, air_info), trace_domain)| {
        let quotient_domain = quotient_domains[i];
        let trace_on_quotient_domain =
            pcs.get_evaluations_on_domain(&trace_data, i, quotient_domains[i]);
        let pre_on_quotient_domain =
            pcs.get_evaluations_on_domain(&pre_data, i, quotient_domains[i]);
        let perm_on_quotient_domain =
            pcs.get_evaluations_on_domain(&perm_data, i, quotient_domains[i]);

        let constraint_count = constraint_counts[i];

        // Determine challenges for this AIR
        let air_challenges = if i == 0 {
            permutation_challenges.clone()
        } else {
            let table_name = air_info
                .air
                .table_name()
                .expect("Non-main AIR must have a table name");
            let main_lookup_idx = main_air_lookups
                .iter()
                .position(|l| {
                    if let Kind::Global(name) = &l.kind {
                        name == table_name
                    } else {
                        false
                    }
                })
                .expect("Table AIR must correspond to a main AIR lookup");
            permutation_challenges[2 * main_lookup_idx..2 * main_lookup_idx + 2].to_vec()
        };

        quotient_values::<SC, _>(
            air_info,
            public_values,
            *trace_domain,
            quotient_domain,
            trace_on_quotient_domain,
            pre_on_quotient_domain,
            perm_on_quotient_domain,
            &all_lookup_data[i],
            alpha,
            &air_challenges,
            constraint_count,
        )
    })
    .collect_vec();

    let quotient_domains_and_chunks = zip_eq(
        zip_eq(
            quotient_domains.iter(),
            quotient_degrees.iter(),
            "Quotient domains and degrees length mismatch",
        )
        .unwrap(),
        quotient_values.iter(),
        "Combined domains/degrees and values length mismatch",
    )
    .unwrap()
    .flat_map(|((domain, &degree), values)| {
        let quotient_flat = RowMajorMatrix::new_col(values.to_vec()).flatten_to_base();
        let quotient_chunks = domain.split_evals(degree, quotient_flat);
        let domain_chunks = domain.split_domains(degree);
        domain_chunks
            .into_iter()
            .zip_eq(quotient_chunks.into_iter())
    })
    .collect_vec();

    let (quotient_commit, quotient_data) = info_span!("commit to quotient poly chunks")
        .in_scope(|| pcs.commit(quotient_domains_and_chunks));

    challenger.observe(quotient_commit.clone());

    let commitments = Commitments {
        trace: trace_commit,
        preprocessed: pre_commit,
        perm: perm_commit,
        quotient_chunks: quotient_commit,
    };

    // Out of domain challenge point.
    let zeta: SC::Challenge = challenger.sample_algebra_element();

    let trace_points = (0..air_infos.len())
        .map(|i| {
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let pre_points = (0..air_infos.len())
        .map(|i| {
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let perm_points = (0..air_infos.len())
        .map(|i| {
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let quotient_points = (0..air_infos.len())
        .flat_map(|i| (0..quotient_degrees[i]).map(|_| vec![zeta]).collect_vec())
        .collect_vec();

    let (openings, opening_proof) = info_span!("open commitments").in_scope(|| {
        pcs.open(
            vec![
                (&trace_data, trace_points),
                (&pre_data, pre_points),
                (&perm_data, perm_points),
                (&quotient_data, quotient_points),
            ],
            &mut challenger,
        )
    });

    let [trace_opened_values, preprocessed_opened_values, perm_opened_values, mut quotient_values] =
        openings.try_into().unwrap();

    let mut quotient_opened_values = Vec::with_capacity(log_quotient_degrees.len());
    for log_quotient_degree in log_quotient_degrees.iter() {
        let degree = 1 << *log_quotient_degree;
        let slice = quotient_values.drain(0..degree);
        quotient_opened_values.push(slice.collect_vec());
    }

    let opened_values = (0..air_infos.len())
        .map(|i| OpenedValues {
            trace_local: trace_opened_values[i][0].clone(),
            trace_next: trace_opened_values[i][1].clone(),
            preprocessed_local: preprocessed_opened_values[i][0].clone(),
            preprocessed_next: preprocessed_opened_values[i][1].clone(),
            perm_local: perm_opened_values[i][0].clone(),
            perm_next: perm_opened_values[i][1].clone(),
            expected_cumulated: all_expected_cumulated[i].clone(),
            quotient_chunks: quotient_opened_values[i]
                .iter()
                .map(|v| v[0].clone())
                .collect_vec(),
        })
        .collect_vec();

    Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits: log_degrees,
    }
}

#[instrument(name = "compute quotient polynomial", skip_all)]
#[allow(clippy::too_many_arguments)]
fn quotient_values<SC, Mat>(
    air_info: &crate::key::AirInfo<Val<SC>>,
    public_values: &Vec<Val<SC>>,
    trace_domain: Domain<SC>,
    quotient_domain: Domain<SC>,
    trace_on_quotient_domain: Mat,
    pre_on_quotient_domain: Mat,
    perm_on_quotient_domain: Mat,
    lookup_data: &[LookupData<SC::Challenge>],
    alpha: SC::Challenge,
    perm_challenges: &[SC::Challenge],
    constraint_count: usize,
) -> Vec<SC::Challenge>
where
    SC: StarkGenericConfig,
    Mat: Matrix<Val<SC>> + Sync,
{
    let quotient_size = quotient_domain.size();
    let width = trace_on_quotient_domain.width();
    let pre_width = pre_on_quotient_domain.width();
    let perm_width = perm_on_quotient_domain.width();
    tracing::info!("trace width: {}", width);
    tracing::info!("perm width: {}", perm_width);
    let mut sels = debug_span!("Compute Selectors")
        .in_scope(|| trace_domain.selectors_on_coset(quotient_domain));

    let qdb = log2_strict_usize(quotient_domain.size()) - log2_strict_usize(trace_domain.size());
    let next_step = 1 << qdb;

    let ext_degree = SC::Challenge::DIMENSION;

    // We take PackedVal::<SC>::WIDTH worth of values at a time from a quotient_size slice, so we need to
    // pad with default values in the case where quotient_size is smaller than PackedVal::<SC>::WIDTH.
    for _ in quotient_size..PackedVal::<SC>::WIDTH {
        sels.is_first_row.push(Val::<SC>::default());
        sels.is_last_row.push(Val::<SC>::default());
        sels.is_transition.push(Val::<SC>::default());
        sels.inv_vanishing.push(Val::<SC>::default());
    }

    let mut alpha_powers = alpha.powers().take(constraint_count).collect_vec();
    alpha_powers.reverse();
    // alpha powers looks like Vec<EF> ~ Vec<[F; D]>
    // It's useful to also have access to the transpose of this of form [Vec<F>; D].
    let decomposed_alpha_powers: Vec<_> = (0..SC::Challenge::DIMENSION)
        .map(|i| {
            alpha_powers
                .iter()
                .map(|x| x.as_basis_coefficients_slice()[i])
                .collect()
        })
        .collect();

    // Convert LookupData<SC::Challenge> to LookupData<PackedChallenge<SC>> for the prover folder
    let lookup_data_packed: Vec<LookupData<PackedChallenge<SC>>> = lookup_data
        .iter()
        .map(|d| LookupData {
            name: d.name.clone(),
            aux_idx: d.aux_idx,
            expected_cumulated: d.expected_cumulated.into(),
        })
        .collect();

    let lookups = &air_info.lookups;
    let gadget = LogUpGadget::new();

    (0..quotient_size)
        .into_par_iter()
        .step_by(PackedVal::<SC>::WIDTH)
        .flat_map_iter(|i_start| {
            let wrap = |i| i % quotient_size;
            let i_range = i_start..i_start + PackedVal::<SC>::WIDTH;

            let is_first_row = *PackedVal::<SC>::from_slice(&sels.is_first_row[i_range.clone()]);
            let is_last_row = *PackedVal::<SC>::from_slice(&sels.is_last_row[i_range.clone()]);
            let is_transition = *PackedVal::<SC>::from_slice(&sels.is_transition[i_range.clone()]);
            let inv_vanishing = *PackedVal::<SC>::from_slice(&sels.inv_vanishing[i_range]);

            // Create local and next vectors for main trace
            let main_local: Vec<_> = (0..width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        trace_on_quotient_domain
                            .get(wrap(i_start + offset), col)
                            .unwrap()
                    })
                })
                .collect();
            let main_next: Vec<_> = (0..width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        trace_on_quotient_domain
                            .get(wrap(i_start + next_step + offset), col)
                            .unwrap()
                    })
                })
                .collect();

            // Create local and next vectors for preprocessed trace
            let prep_local: Vec<_> = (0..pre_width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        pre_on_quotient_domain
                            .get(wrap(i_start + offset), col)
                            .unwrap()
                    })
                })
                .collect();
            let prep_next: Vec<_> = (0..pre_width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        pre_on_quotient_domain
                            .get(wrap(i_start + next_step + offset), col)
                            .unwrap()
                    })
                })
                .collect();

            let perm_local: Vec<_> = (0..perm_width)
                .step_by(ext_degree)
                .map(|col| {
                    PackedChallenge::<SC>::from_basis_coefficients_fn(|i| {
                        PackedVal::<SC>::from_fn(|offset| {
                            perm_on_quotient_domain
                                .get(wrap(i_start + offset), col + i)
                                .unwrap()
                        })
                    })
                })
                .collect();

            let perm_next: Vec<_> = (0..perm_width)
                .step_by(ext_degree)
                .map(|col| {
                    PackedChallenge::<SC>::from_basis_coefficients_fn(|i| {
                        PackedVal::<SC>::from_fn(|offset| {
                            perm_on_quotient_domain
                                .get(wrap(i_start + next_step + offset), col + i)
                                .unwrap()
                        })
                    })
                })
                .collect();

            let accumulator = PackedChallenge::<SC>::ZERO;
            let mut folder: ProverConstraintFolder<SC> = ProverConstraintFolder {
                main: VerticalPair::new(
                    RowMajorMatrixView::new_row(&main_local),
                    RowMajorMatrixView::new_row(&main_next),
                ),
                preprocessed: VerticalPair::new(
                    RowMajorMatrixView::new_row(&prep_local),
                    RowMajorMatrixView::new_row(&prep_next),
                ),
                perm: VerticalPair::new(
                    RowMajorMatrixView::new_row(&perm_local),
                    RowMajorMatrixView::new_row(&perm_next),
                ),
                public_values,
                is_first_row,
                is_last_row,
                is_transition,
                alpha_powers: &alpha_powers,
                decomposed_alpha_powers: &decomposed_alpha_powers,
                perm_challenges,
                accumulator,
                constraint_index: 0,
            };

            // Use eval_with_lookups to evaluate both AIR constraints and lookup constraints
            use p3_air::Air;
            air_info.air.eval_with_lookups(
                &mut folder,
                lookups,
                &lookup_data_packed,
                &gadget,
            );

            // quotient(x) = constraints(x) / Z_H(x)
            let quotient = folder.accumulator * inv_vanishing;

            // "Transpose" D packed base coefficients into WIDTH scalar extension coefficients.
            (0..core::cmp::min(quotient_size, PackedVal::<SC>::WIDTH)).map(move |idx_in_packing| {
                SC::Challenge::from_basis_coefficients_fn(|coeff_idx| {
                    quotient.as_basis_coefficients_slice()[coeff_idx].as_slice()[idx_in_packing]
                })
            })
        })
        .collect()
}
