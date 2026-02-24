use alloc::vec::Vec;

use p3_batch_stark::{BatchProof, CommonData, verify_batch};
use p3_field::BasedVectorSpace;
use p3_uni_stark::{SymbolicExpression, VerificationError};
use tracing::instrument;

use crate::{AirInfo, CleanAirInstance, PcsError, StarkGenericConfig, Val};
use crate::prover::build_prover_data;

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
    let prover_data = build_prover_data(config, air_infos);
    let common: CommonData<SC> = prover_data.common;

    let airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();

    let per_instance_pvs: Vec<Vec<Val<SC>>> =
        air_infos.iter().map(|_| public_values.clone()).collect();

    verify_batch(config, &airs, proof, &per_instance_pvs, &common)
}
