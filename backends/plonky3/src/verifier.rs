use alloc::vec::Vec;

use p3_batch_stark::{BatchProof, ProverData, verify_batch};
use p3_field::BasedVectorSpace;
use p3_uni_stark::SymbolicExpression;
use tracing::instrument;

use crate::{AirInfo, CleanAirInstance, PcsError, StarkGenericConfig, Val};
use p3_uni_stark::VerificationError;

#[instrument(skip_all)]
pub fn verify<SC>(
    config: &SC,
    air_infos: &Vec<AirInfo<Val<SC>>>,
    proof: &BatchProof<SC>,
    public_values: &Vec<Val<SC>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
{
    // Rebuild CommonData deterministically from air_infos (same as prover).
    let mut airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();
    let prover_data =
        ProverData::from_airs_and_degrees(config, &mut airs, &proof.degree_bits);
    let common = prover_data.common;

    let airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();

    let per_instance_pvs: Vec<Vec<Val<SC>>> =
        air_infos.iter().map(|_| public_values.clone()).collect();

    verify_batch(config, &airs, proof, &per_instance_pvs, &common)
}
