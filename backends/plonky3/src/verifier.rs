use alloc::vec::Vec;

use p3_batch_stark::{BatchProof, ProverData, verify_batch};
use p3_field::BasedVectorSpace;
use p3_uni_stark::SymbolicExpression;
use p3_util::log2_strict_usize;
use tracing::instrument;

use crate::{AirInfo, CleanAirInstance, PcsError, StarkGenericConfig, Val};
use p3_uni_stark::VerificationError;

#[instrument(skip_all)]
pub fn verify<SC>(
    config: &SC,
    air_infos: &[AirInfo<Val<SC>>],
    proof: &BatchProof<SC>,
    public_values: &[Val<SC>],
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
{
    assert!(
        !air_infos.is_empty() && air_infos[0].air.table_name().is_none(),
        "air_infos[0] must be the main AIR (not a table AIR)"
    );
    assert!(
        air_infos[1..].iter().all(|ai| ai.air.table_name().is_some()),
        "air_infos[1..] must all be table AIRs. \
         Multiple main traces are not supported yet."
    );

    let degree_bits = verifier_degree_bits(config, air_infos, &proof.degree_bits)?;

    // Rebuild CommonData deterministically from air_infos (same as prover).
    let mut airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();
    let prover_data = ProverData::from_airs_and_degrees(config, &mut airs, &degree_bits);
    let common = prover_data.common;

    let airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();

    let per_instance_pvs: Vec<Vec<Val<SC>>> =
        air_infos.iter().map(|_| public_values.to_vec()).collect();

    verify_batch(config, &airs, proof, &per_instance_pvs, &common)
}

fn verifier_degree_bits<SC>(
    config: &SC,
    air_infos: &[AirInfo<Val<SC>>],
    proof_degree_bits: &[usize],
) -> Result<Vec<usize>, VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
{
    if air_infos.len() != proof_degree_bits.len() {
        return Err(VerificationError::InvalidProofShape);
    }

    air_infos
        .iter()
        .zip(proof_degree_bits.iter())
        .map(|(air_info, &proof_degree_bits)| {
            let Some(trace_height) = air_info.expected_trace_height else {
                return Ok(proof_degree_bits);
            };

            let expected_degree_bits = log2_strict_usize(trace_height) + config.is_zk();
            if proof_degree_bits != expected_degree_bits {
                return Err(VerificationError::InvalidProofShape);
            }
            Ok(expected_degree_bits)
        })
        .collect()
}
