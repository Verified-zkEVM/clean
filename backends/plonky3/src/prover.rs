use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::Air;
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, PackedValue, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;
use tracing::{debug_span, info_span, instrument};

use p3_uni_stark::SymbolicAirBuilder;

use crate::{permutation, CleanAir, Commitments, Domain, LookupBuilder, OpenedValues, PackedChallenge, PackedVal, Proof, ProverConstraintFolder, StarkGenericConfig, Val};

#[instrument(skip_all)]
#[allow(clippy::multiple_bound_locations)] // cfg not supported in where clauses?
pub fn prove<
    SC,
    #[cfg(debug_assertions)] A: for<'a> Air<crate::check_constraints::DebugConstraintBuilder<'a, Val<SC>>>,
    #[cfg(not(debug_assertions))] A,
>(
    config: &SC,
    airs: Vec<&A>,
    traces: Vec<RowMajorMatrix<Val<SC>>>,
    pres: Vec<RowMajorMatrix<Val<SC>>>,
    public_values: &Vec<Val<SC>>,
) -> Proof<SC>
where
    SC: StarkGenericConfig,
    A: CleanAir<Val<SC>> + Air<SymbolicAirBuilder<Val<SC>>> + Air<LookupBuilder<Val<SC>>> + for<'a> Air<ProverConstraintFolder<'a, SC>>,
{
    let pcs = config.pcs();

    tracing::info!("main trace width: {}", traces[0].width());

    let degrees = traces
        .iter().enumerate()
        .map(|(i, _)| {
            traces[i].height()
        });

    let log_degrees = degrees
        .clone()
        .map(log2_strict_usize)
        .collect_vec();

    let constraint_counts = airs.
        iter()
        .map(|air| {
            air.count_constraints(public_values.len())
        })
        .collect_vec();

    let log_quotient_degrees = (0..airs.len())
        .map(|i| {
            airs[i].log_quotient_degree(public_values.len())
        })
        .collect::<Vec<_>>();

    tracing::info!("constraint counts: {:?}, log_quotient_degrees: {:?}", constraint_counts, log_quotient_degrees);

    let quotient_degrees = log_quotient_degrees
        .iter()
        .map(|&d| 1 << d)
        .collect_vec();

    let mut challenger = config.initialise_challenger();

    let trace_domains: Vec<Domain<SC>> = degrees
        .clone()
        .map(|d| pcs.natural_domain_for_degree(d))
        .collect_vec();


    let trace_and_domains = trace_domains
        .iter()
        .zip(traces.iter())
        .map(|(domain, trace)| {
            (*domain, trace.clone())
        })
        .collect_vec();

    // todo: use preprocessed trace domains
    let pre_and_domains = trace_domains
        .iter()
        .zip(pres.iter())
        .map(|(domain, pre)| (*domain, pre.clone()))
        .collect_vec();

    let (trace_commit, trace_data) =
        info_span!("commit to trace data").in_scope(|| pcs.commit(trace_and_domains));

    let (pre_commit, pre_data) =
        info_span!("commit to preprocessed data").in_scope(|| pcs.commit(pre_and_domains));

    // Observe the instance.
    challenger.observe(trace_commit.clone());
    challenger.observe(pre_commit.clone());
    challenger.observe_slice(public_values);

    // Get the challenges for the permutation trace calculation.
    let permutation_challenges: Vec<SC::Challenge> = (0..traces.len())
        .map(|_| challenger.sample_algebra_element())
        .collect_vec();

    tracing::info!("permutation challenges: {:?}", permutation_challenges);

    // compute permutation traces
    let perm_traces = (0..traces.len())
        .map(|i| {
            let air = airs[i];
            let trace = &traces[i];
            let preprocessed = &pres[i];

            permutation::generate_permutation_trace::<SC, A, SC::Challenge>(
                air,
                trace,
                preprocessed,
                &permutation_challenges,
            )
        })
        .collect_vec();

    let (perm_and_domains, last_sums): (Vec<_>, Vec<&SC::Challenge>) = trace_domains
        .iter()
        .zip(perm_traces.iter())
        .map(|(domain, (perm_trace, last_sum))| {
            tracing::info!("perm trace width: {}", perm_trace.width());
            ((*domain, perm_trace.clone().flatten_to_base()), last_sum)
        })
        .unzip();

    let (perm_commit, perm_data) =
        info_span!("commit to permutation traces").in_scope(|| pcs.commit(perm_and_domains));

    // print out the sum of last sums
    tracing::info!(
        "Sum of last sums: {:?}",
        last_sums.clone().into_iter().map(|s| { 
            tracing::info!("Last sum: {:?}", s);
            s.clone()
        }).sum::<SC::Challenge>()
    );

    challenger.observe(perm_commit.clone());

    // Get the Fiat Shamir challenge which will be used to combine all constraint polynomials
    // into a single polynomial.
    let alpha: SC::Challenge = challenger.sample_algebra_element();

    let quotient_domains = trace_domains
        .iter()
        .zip(log_degrees.iter())
        .zip(log_quotient_degrees.iter())
        .map(|((trace_domain, &log_degree), &log_quotient_degree)| {
            trace_domain.create_disjoint_domain(
                1 << (log_degree + log_quotient_degree),
            )
        })
        .collect_vec();

    let quotient_values = (0..traces.len())
        .map(|i| {
            let air = airs[i];
            let trace_domain = trace_domains[i];
            let quotient_domain = quotient_domains[i];
            let trace_on_quotient_domain = pcs.get_evaluations_on_domain(&trace_data, i, quotient_domains[i]);
            let pre_on_quotient_domain = pcs.get_evaluations_on_domain(&pre_data, i, quotient_domains[i]);
            let perm_on_quotient_domain = pcs.get_evaluations_on_domain(&perm_data, i, quotient_domains[i]);

            let constraint_count = constraint_counts[i];
            
            quotient_values(
                air,
                public_values,
                trace_domain,
                quotient_domain,
                trace_on_quotient_domain,
                pre_on_quotient_domain,
                perm_on_quotient_domain,
                *last_sums[i],
                alpha,
                &permutation_challenges,
                constraint_count,
            )
        })
        .collect_vec();

    let quotient_domains_and_chunks = quotient_domains
        .iter()
        .zip(quotient_degrees.iter())
        .zip(quotient_values.iter())
        .flat_map(|((domain, &degree), values)| {
            let quotient_flat = RowMajorMatrix::new_col(values.to_vec()).flatten_to_base();
            let quotient_chunks = domain.split_evals(degree, quotient_flat);
            let domain_chunks = domain.split_domains(degree);
            domain_chunks.into_iter().zip_eq(quotient_chunks.into_iter())
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
        random: None,
    };


    let zeta: SC::Challenge = challenger.sample_algebra_element();

    tracing::info!("alpha: {}", alpha);
    tracing::info!("zeta: {:?}", zeta);

    let trace_points = (0..traces.len())
        .map(|i| {
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let pre_points = (0..traces.len())
        .map(|i| {
            // todo: get domain from natural domain
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let perm_points = (0..traces.len())
        .map(|i| {
            let trace_domain = trace_domains[i];
            let zeta_next = trace_domain.next_point(zeta).unwrap();
            vec![zeta, zeta_next]
        })
        .collect_vec();

    let quotient_points = (0..traces.len())
        .flat_map(|i| {
            (0..quotient_degrees[i]).map(|_| vec![zeta]).collect_vec()

        })
        .collect_vec();

    tracing::info!("quotient point size: {}", quotient_points.len());

    let (openings, opening_proof) = info_span!("open commitments")
        .in_scope(|| pcs.open(
            vec![
                (&trace_data, trace_points),
                (&pre_data, pre_points),
                (&perm_data, perm_points),
                (&quotient_data, quotient_points),
            ],
            &mut challenger,
        ));

    let [
        trace_opened_values,
        preprocessed_opened_values,
        perm_opened_values,
        mut quotient_values,
    ] = openings.try_into().unwrap();

    let mut quotient_opened_values = Vec::with_capacity(log_quotient_degrees.len());
    for log_quotient_degree in log_quotient_degrees.iter() {
        let degree = 1 << *log_quotient_degree;
        let slice = quotient_values.drain(0..degree);
        quotient_opened_values.push(slice.collect_vec());
    }

    let opened_values = (0..traces.len()).map(|i| {
        OpenedValues {
            trace_local: trace_opened_values[i][0].clone(),
            trace_next: trace_opened_values[i][1].clone(),
            preprocessed_local: preprocessed_opened_values[i][0].clone(),
            preprocessed_next: preprocessed_opened_values[i][1].clone(),
            perm_local: perm_opened_values[i][0].clone(),
            perm_next: perm_opened_values[i][1].clone(),
            local_cumulative_sum: *last_sums[i],
            quotient_chunks: quotient_opened_values[i]
                .iter()
                .map(|v| v[0].clone())
                .collect_vec(),
            random: None,
        }
    }).collect_vec();

    Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits: log_degrees,
    }
}

#[instrument(name = "compute quotient polynomial", skip_all)]
// TODO: Group some arguments to remove the `allow`?
#[allow(clippy::too_many_arguments)]
fn quotient_values<SC, A, Mat>(
    air: &A,
    public_values: &Vec<Val<SC>>,
    trace_domain: Domain<SC>,
    quotient_domain: Domain<SC>,
    trace_on_quotient_domain: Mat,
    pre_on_quotient_domain: Mat,
    perm_on_quotient_domain: Mat,
    local_cumulative_sum: SC::Challenge,
    alpha: SC::Challenge,
    perm_challenges: &[SC::Challenge],
    constraint_count: usize,
) -> Vec<SC::Challenge>
where
    SC: StarkGenericConfig,
    A: for<'a> Air<ProverConstraintFolder<'a, SC>> + CleanAir<Val<SC>>,
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

    // todo: is this correct?
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
                        trace_on_quotient_domain.get(wrap(i_start + offset), col).unwrap()
                    })
                })
                .collect();
            let main_next: Vec<_> = (0..width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        trace_on_quotient_domain.get(wrap(i_start + next_step + offset), col).unwrap()
                    })
                })
                .collect();

            // Create local and next vectors for preprocessed trace
            let prep_local: Vec<_> = (0..pre_width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        pre_on_quotient_domain.get(wrap(i_start + offset), col).unwrap()
                    })
                })
                .collect();
            let prep_next: Vec<_> = (0..pre_width)
                .map(|col| {
                    PackedVal::<SC>::from_fn(|offset| {
                        pre_on_quotient_domain.get(wrap(i_start + next_step + offset), col).unwrap()
                    })
                })
                .collect();

            let perm_local: Vec<_> = (0..perm_width)
                .step_by(ext_degree)
                .map(|col| {
                    PackedChallenge::<SC>::from_basis_coefficients_fn(|i| {
                        PackedVal::<SC>::from_fn(|offset| {
                            perm_on_quotient_domain
                                .get(wrap(i_start + offset), col + i).unwrap()
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
                                .get(wrap(i_start + next_step + offset), col + i).unwrap()
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
                local_cumulative_sum: local_cumulative_sum.into(),
                accumulator,
                constraint_index: 0,
            };
            air.eval_constraints(&mut folder);

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
