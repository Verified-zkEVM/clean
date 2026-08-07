//! Generic batch proving for AIR enums emitted by Clean.

use alloc::vec::Vec;

use p3_air::Air;
#[cfg(all(debug_assertions, not(doc)))]
use p3_batch_stark::DebugConstraintBuilderWithLookups;
use p3_batch_stark::{prove_batch, verify_batch, BatchProof, ProverData, StarkInstance};
use p3_field::BasedVectorSpace;
use p3_lookup::folder::{ProverConstraintFolderWithLookups, VerifierConstraintFolderWithLookups};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression, VerificationError};
use p3_util::log2_strict_usize;

use crate::{PcsError, StarkGenericConfig, Val};

/// Static physical trace height expected by the verifier for one generated AIR.
pub trait EnsembleAir {
    fn trace_height(&self) -> usize;
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

/// Prove a collection of generated AIR components and their padded traces.
pub fn prove_ensemble<SC, A>(
    config: &SC,
    airs: &[A],
    traces: Vec<RowMajorMatrix<Val<SC>>>,
    public_values: &[Val<SC>],
) -> (BatchProof<SC>, ProverData<SC>)
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
    A: ProverAir<SC>,
{
    assert_eq!(airs.len(), traces.len());
    for (air, trace) in airs.iter().zip(&traces) {
        assert_eq!(air.width(), trace.width());
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
    let proof = prove_batch(config, &instances, &prover_data);
    (proof, prover_data)
}

/// Verify a proof produced for direct generated ensemble AIR code.
pub fn verify_ensemble<SC, A>(
    config: &SC,
    airs: &[A],
    proof: &BatchProof<SC>,
    public_values: &[Val<SC>],
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
    A: Air<SymbolicAirBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>>
        + EnsembleAir
        + Clone,
{
    let expected_degree_bits = airs
        .iter()
        .map(|air| log2_strict_usize(air.trace_height()) + config.is_zk())
        .collect::<Vec<_>>();
    if proof.degree_bits != expected_degree_bits {
        return Err(VerificationError::InvalidProofShape);
    }
    let mut verifier_airs = airs.to_vec();
    let prover_data =
        ProverData::from_airs_and_degrees(config, &mut verifier_airs, &proof.degree_bits);
    let per_air_public_values = airs
        .iter()
        .map(|_| public_values.to_vec())
        .collect::<Vec<_>>();
    verify_batch(
        config,
        airs,
        proof,
        &per_air_public_values,
        &prover_data.common,
    )
}
