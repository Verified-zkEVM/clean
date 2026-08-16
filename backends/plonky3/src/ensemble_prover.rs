//! Generic batch proving for AIR enums emitted by Clean.

use alloc::vec::Vec;

use p3_air::{Air, BaseAir};
#[cfg(all(debug_assertions, not(doc)))]
use p3_batch_stark::DebugConstraintBuilderWithLookups;
use p3_batch_stark::{
    prove_batch_with_public_lookups, verify_batch_with_public_lookups, BatchProof, ProverData,
    PublicLookup, StarkInstance,
};
use p3_field::BasedVectorSpace;
use p3_lookup::folder::{ProverConstraintFolderWithLookups, VerifierConstraintFolderWithLookups};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression, VerificationError};
use p3_util::log2_strict_usize;

use crate::witness_generation::{Interaction, WitnessField};
use crate::{
    EnsembleShapeError, GeneratedAir, GeneratedAirSpec, GeneratedEnsemble, PcsError,
    StarkGenericConfig, Val,
};

fn public_lookups<F: WitnessField>(interactions: Vec<Interaction<F>>) -> Vec<PublicLookup<F>> {
    interactions
        .into_iter()
        .map(|interaction| PublicLookup {
            name: interaction.channel.into(),
            values: interaction.message,
            // Generated AIR lookups encode both Clean push and pull multiplicities with
            // the opposite sign. Apply that same convention to the one-shot public side.
            multiplicity: -interaction.multiplicity,
        })
        .collect()
}

/// Verification failures are separated into caller-visible statement-shape errors and
/// cryptographic Plonky3 verification errors.
#[derive(Debug)]
pub enum EnsembleVerificationError<E: core::fmt::Debug> {
    Shape(EnsembleShapeError),
    Proof(VerificationError<E>),
}

#[cfg(all(debug_assertions, not(doc)))]
#[doc(hidden)]
pub trait ProverAir<SC: StarkGenericConfig>:
    Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
    + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
    + for<'a> Air<DebugConstraintBuilderWithLookups<'a, Val<SC>, SC::Challenge>>
    + Clone
{
}

#[cfg(all(debug_assertions, not(doc)))]
impl<SC, A> ProverAir<SC> for A
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
        + for<'a> Air<DebugConstraintBuilderWithLookups<'a, Val<SC>, SC::Challenge>>
        + Clone,
{
}

#[cfg(any(not(debug_assertions), doc))]
#[doc(hidden)]
pub trait ProverAir<SC: StarkGenericConfig>:
    Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
    + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
    + Clone
{
}

#[cfg(any(not(debug_assertions), doc))]
impl<SC, A> ProverAir<SC> for A
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
        + Clone,
{
}

/// Prove a complete generated ensemble and its canonically ordered padded traces.
pub fn prove_ensemble<SC, P>(
    config: &SC,
    ensemble: &GeneratedEnsemble<Val<SC>, P>,
    traces: Vec<RowMajorMatrix<Val<SC>>>,
    public_values: &[Val<SC>],
) -> Result<(BatchProof<SC>, ProverData<SC>), EnsembleShapeError>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
    Val<SC>: WitnessField,
    P: GeneratedAirSpec,
    GeneratedAir<P>: ProverAir<SC>,
{
    let airs = ensemble.airs();
    let trace_heights = ensemble.trace_heights();
    if airs.len() != traces.len() {
        return Err(EnsembleShapeError::TraceCount {
            expected: airs.len(),
            actual: traces.len(),
        });
    }
    let expected_public_values = P::PUBLIC_VALUES;
    if public_values.len() != expected_public_values {
        return Err(EnsembleShapeError::PublicValueCount {
            expected: expected_public_values,
            actual: public_values.len(),
        });
    }
    for (component, (air, trace)) in airs.iter().zip(&traces).enumerate() {
        if air.width() != trace.width() {
            return Err(EnsembleShapeError::TraceWidth {
                component,
                expected: air.width(),
                actual: trace.width(),
            });
        }
        if trace.height() == 0 || !trace.height().is_power_of_two() {
            return Err(EnsembleShapeError::TraceHeight {
                component,
                height: trace.height(),
            });
        }
        if trace.height() != trace_heights[component] {
            return Err(EnsembleShapeError::StatementTraceHeight {
                component,
                expected: trace_heights[component],
                actual: trace.height(),
            });
        }
    }
    let log_degrees = traces
        .iter()
        .map(|trace| log2_strict_usize(trace.height()) + config.is_zk())
        .collect::<Vec<_>>();
    let mut prover_airs = airs.to_vec();
    let prover_data = ProverData::from_airs_and_degrees(config, &mut prover_airs, &log_degrees);
    let instances = airs
        .iter()
        .zip(traces)
        .zip(prover_data.common.lookups.iter())
        .map(|((air, trace), lookups)| StarkInstance {
            air,
            trace,
            public_values: public_values.to_vec(),
            lookups: lookups.clone(),
        })
        .collect::<Vec<_>>();
    let public_lookups = public_lookups(P::verifier_interactions(public_values));
    let proof = prove_batch_with_public_lookups(config, &instances, &prover_data, &public_lookups);
    Ok((proof, prover_data))
}

/// Verify a proof against a complete generated ensemble statement.
pub fn verify_ensemble<SC, P>(
    config: &SC,
    ensemble: &GeneratedEnsemble<Val<SC>, P>,
    proof: &BatchProof<SC>,
    public_values: &[Val<SC>],
) -> Result<(), EnsembleVerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
    P: GeneratedAirSpec,
    GeneratedAir<P>: Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>>
        + Clone,
    Val<SC>: WitnessField,
{
    let airs = ensemble.airs();
    let trace_heights = ensemble.trace_heights();
    let expected_public_values = P::PUBLIC_VALUES;
    if public_values.len() != expected_public_values {
        return Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::PublicValueCount {
                expected: expected_public_values,
                actual: public_values.len(),
            },
        ));
    }
    let expected_degree_bits = trace_heights
        .iter()
        .map(|height| log2_strict_usize(*height) + config.is_zk())
        .collect::<Vec<_>>();
    if proof.degree_bits != expected_degree_bits {
        return Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::ProofDegreeBits {
                expected: expected_degree_bits,
                actual: proof.degree_bits.clone(),
            },
        ));
    }
    let mut verifier_airs = airs.to_vec();
    let prover_data =
        ProverData::from_airs_and_degrees(config, &mut verifier_airs, &proof.degree_bits);
    let per_air_public_values = airs
        .iter()
        .map(|_| public_values.to_vec())
        .collect::<Vec<_>>();
    let public_lookups = public_lookups(P::verifier_interactions(public_values));
    verify_batch_with_public_lookups(
        config,
        airs,
        proof,
        &per_air_public_values,
        &prover_data.common,
        &public_lookups,
    )
    .map_err(EnsembleVerificationError::Proof)
}
