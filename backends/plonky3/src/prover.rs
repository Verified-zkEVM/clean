use alloc::vec::Vec;

use p3_batch_stark::{BatchProof, ProverData, StarkInstance, prove_batch};
use p3_field::BasedVectorSpace;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::SymbolicExpression;
use p3_util::log2_strict_usize;
use tracing::instrument;

use p3_air::BaseAir;

use crate::{AirInfo, CleanAirInstance, StarkGenericConfig, Val};

#[instrument(skip_all)]
pub fn prove<SC>(
    config: &SC,
    air_infos: &Vec<AirInfo<Val<SC>>>,
    traces: &[RowMajorMatrix<Val<SC>>],
    public_values: &Vec<Val<SC>>,
) -> BatchProof<SC>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
{
    assert_eq!(
        traces.len(),
        air_infos.len(),
        "Number of traces must match number of AirInfo instances"
    );

    assert!(
        !air_infos.is_empty() && air_infos[0].air.table_name().is_none(),
        "air_infos[0] must be the main AIR (not a preprocessed table)"
    );
    assert!(
        air_infos[1..].iter().all(|ai| ai.air.table_name().is_some()),
        "air_infos[1..] must all be table AIRs. \
         Multiple main traces are not supported yet."
    );

    for (i, (ai, trace)) in air_infos.iter().zip(traces.iter()).enumerate() {
        assert_eq!(
            trace.width(),
            ai.air.width(),
            "traces[{}] width ({}) does not match air_infos[{}] width ({})",
            i, trace.width(), i, ai.air.width()
        );
    }

    let prover_data = build_prover_data(config, air_infos, traces);

    let instances: Vec<StarkInstance<'_, SC, CleanAirInstance<Val<SC>>>> = air_infos
        .iter()
        .zip(traces.iter())
        .zip(prover_data.common.lookups.iter())
        .map(|((air_info, trace), lookups)| StarkInstance {
            air: &air_info.air,
            trace: trace.clone(),
            public_values: public_values.clone(),
            lookups: lookups.clone(),
        })
        .collect();

    prove_batch(config, &instances, &prover_data)
}

/// Build [`ProverData`] using `ProverData::from_airs_and_degrees()`.
fn build_prover_data<SC>(
    config: &SC,
    air_infos: &[AirInfo<Val<SC>>],
    traces: &[RowMajorMatrix<Val<SC>>],
) -> ProverData<SC>
where
    SC: StarkGenericConfig,
    SC::Challenge: BasedVectorSpace<Val<SC>>,
    SymbolicExpression<SC::Challenge>: From<SymbolicExpression<Val<SC>>>,
{
    let mut airs: Vec<CleanAirInstance<Val<SC>>> =
        air_infos.iter().map(|ai| ai.air.clone()).collect();
    let log_degrees: Vec<usize> = traces
        .iter()
        .map(|t| log2_strict_usize(t.height()) + config.is_zk())
        .collect();
    ProverData::from_airs_and_degrees(config, &mut airs, &log_degrees)
}
