//! Proving and verification of ensembles extracted from Clean.

use alloc::vec;
use alloc::vec::Vec;

use p3_air::symbolic::SymbolicExpressionExt;
#[cfg(debug_assertions)]
use p3_air::DebugConstraintBuilder;
use p3_air::{Air, BaseAir};
use p3_batch_stark::folder::{
    ProverConstraintFolderWithLookups, VerifierConstraintFolderWithLookups,
};
use p3_batch_stark::{
    prove_batch, verify_batch, BatchProof, BatchVerificationError, PcsError, ProverData,
    ProvingError, StarkGenericConfig, StarkInstance, Val,
};
use p3_challenger::GrindingChallenger;
use p3_commit::Pcs;
use p3_field::{Algebra, BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_lookup::InteractionSymbolicBuilder;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

use crate::witness_generation::WitnessField;
use crate::{EnsembleShapeError, GeneratedAir, GeneratedAirSpec, GeneratedEnsemble};

/// The errors of the PCS when proving.
pub type PcsProverError<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::ProverError;

/// A proving failure: a statement-shape error, or a Plonky3 proving error.
#[derive(Debug)]
pub enum EnsembleProvingError<E: core::fmt::Debug> {
    Shape(EnsembleShapeError),
    Proof(ProvingError<E>),
}

/// A verification failure: a statement-shape error, or a Plonky3 verification error.
#[derive(Debug)]
pub enum EnsembleVerificationError<E: core::fmt::Debug> {
    Shape(EnsembleShapeError),
    Proof(BatchVerificationError<E>),
}

#[cfg(debug_assertions)]
#[doc(hidden)]
pub trait ProverAir<SC: StarkGenericConfig>:
    Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
    + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
    + for<'a> Air<DebugConstraintBuilder<'a, Val<SC>, SC::Challenge>>
    + Clone
{
}

#[cfg(debug_assertions)]
impl<SC, A> ProverAir<SC> for A
where
    SC: StarkGenericConfig,
    A: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
        + for<'a> Air<DebugConstraintBuilder<'a, Val<SC>, SC::Challenge>>
        + Clone,
{
}

#[cfg(not(debug_assertions))]
#[doc(hidden)]
pub trait ProverAir<SC: StarkGenericConfig>:
    Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
    + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
    + Clone
{
}

#[cfg(not(debug_assertions))]
impl<SC, A> ProverAir<SC> for A
where
    SC: StarkGenericConfig,
    A: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<ProverConstraintFolderWithLookups<'a, SC>>
        + Clone,
{
}

/// The public values of every AIR: only the verifier AIR, which is last, reads them.
fn per_air_public_values<F: Clone>(airs: usize, public_values: &[F]) -> Vec<Vec<F>> {
    let mut values = vec![Vec::new(); airs - 1];
    values.push(public_values.to_vec());
    values
}

/// Prove a complete generated ensemble and its canonically ordered padded traces.
pub fn prove_ensemble<SC, P>(
    config: &SC,
    ensemble: &GeneratedEnsemble<Val<SC>, P>,
    traces: Vec<RowMajorMatrix<Val<SC>>>,
    public_values: &[Val<SC>],
) -> Result<BatchProof<SC>, EnsembleProvingError<PcsProverError<SC>>>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    Val<SC>: WitnessField + PrimeField64,
    P: GeneratedAirSpec,
    GeneratedAir<P>: ProverAir<SC>,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain: Send + Sync,
    SC::Pcs: Sync,
    PcsProverError<SC>: Send,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::ProverData: Sync,
    <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Commitment: Sync,
{
    let airs = ensemble.airs();
    let trace_heights = ensemble.trace_heights();
    if trace_heights.len() != traces.len() {
        return Err(EnsembleProvingError::Shape(
            EnsembleShapeError::TraceCount {
                expected: trace_heights.len(),
                actual: traces.len(),
            },
        ));
    }
    if public_values.len() != P::PUBLIC_VALUES {
        return Err(EnsembleProvingError::Shape(
            EnsembleShapeError::PublicValueCount {
                expected: P::PUBLIC_VALUES,
                actual: public_values.len(),
            },
        ));
    }
    for (component, (air, trace)) in airs.iter().zip(&traces).enumerate() {
        let width = BaseAir::<Val<SC>>::width(air);
        if width != trace.width() {
            return Err(EnsembleProvingError::Shape(
                EnsembleShapeError::TraceWidth {
                    component,
                    expected: width,
                    actual: trace.width(),
                },
            ));
        }
        if trace.height() != trace_heights[component] {
            return Err(EnsembleProvingError::Shape(
                EnsembleShapeError::StatementTraceHeight {
                    component,
                    expected: trace_heights[component],
                    actual: trace.height(),
                },
            ));
        }
    }
    let mut traces = traces;
    traces.push(RowMajorMatrix::new(
        vec![Val::<SC>::ZERO; ensemble.verifier_height()],
        1,
    ));
    let log_degrees = traces
        .iter()
        .map(|trace| log2_strict_usize(trace.height()) + config.is_zk())
        .collect::<Vec<_>>();
    let prover_data = ProverData::from_airs_and_degrees(config, airs, &log_degrees)
        .map_err(EnsembleProvingError::Proof)?;
    let public_values = per_air_public_values(airs.len(), public_values);
    let traces = traces.iter().collect::<Vec<_>>();
    let instances = StarkInstance::new_multiple(airs, &traces, &public_values);
    prove_batch(config, &instances, &prover_data).map_err(EnsembleProvingError::Proof)
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
    SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    Val<SC>: WitnessField + PrimeField64,
    P: GeneratedAirSpec,
    GeneratedAir<P>: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>
        + for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>>
        + Clone,
{
    let airs = ensemble.airs();
    if public_values.len() != P::PUBLIC_VALUES {
        return Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::PublicValueCount {
                expected: P::PUBLIC_VALUES,
                actual: public_values.len(),
            },
        ));
    }
    let degree_bits = ensemble
        .trace_heights()
        .iter()
        .chain([&ensemble.verifier_height()])
        .map(|height| log2_strict_usize(*height) + config.is_zk())
        .collect::<Vec<_>>();
    if proof.degree_bits != degree_bits {
        return Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::ProofDegreeBits {
                expected: degree_bits,
                actual: proof.degree_bits.clone(),
            },
        ));
    }
    let common = ProverData::from_airs_and_degrees(config, airs, &degree_bits)
        .map_err(|_| EnsembleVerificationError::Shape(EnsembleShapeError::Setup))?
        .common;
    let public_values = per_air_public_values(airs.len(), public_values);
    verify_batch(config, airs, proof, &public_values, &common)
        .map_err(EnsembleVerificationError::Proof)
}
