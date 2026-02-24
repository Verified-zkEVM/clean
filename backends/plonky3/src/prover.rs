use alloc::vec::Vec;

use p3_batch_stark::common::{GlobalPreprocessed, PreprocessedInstanceMeta};
use p3_batch_stark::{
    BatchProof, CommonData, ProverData, ProverOnlyData, StarkInstance, prove_batch,
};
use p3_commit::Pcs;
use p3_field::BasedVectorSpace;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_uni_stark::SymbolicExpression;
use p3_util::log2_strict_usize;
use tracing::instrument;

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

    let prover_data = build_prover_data(config, air_infos);

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

/// Build [`ProverData`] manually from [`AirInfo`] instances.
///
/// This avoids calling `ProverData::from_instances` which would invoke
/// `get_lookups()` on the AIR (our `build_lookups()` is not idempotent).
/// Instead, we take the pre-built lookups from `AirInfo` directly.
pub fn build_prover_data<SC>(
    config: &SC,
    air_infos: &[AirInfo<Val<SC>>],
) -> ProverData<SC>
where
    SC: StarkGenericConfig,
{
    let pcs = config.pcs();
    let num_instances = air_infos.len();

    let mut instances_meta: Vec<Option<PreprocessedInstanceMeta>> =
        Vec::with_capacity(num_instances);
    let mut matrix_to_instance: Vec<usize> = Vec::new();
    let mut domains_and_traces = Vec::new();

    for (i, air_info) in air_infos.iter().enumerate() {
        if let Some(preprocessed) = &air_info.preprocessed {
            let width = preprocessed.width();
            if width == 0 {
                instances_meta.push(None);
                continue;
            }

            let degree_bits = log2_strict_usize(preprocessed.height());
            let domain = pcs.natural_domain_for_degree(preprocessed.height());
            let matrix_index = domains_and_traces.len();

            domains_and_traces.push((domain, preprocessed.clone()));
            matrix_to_instance.push(i);

            instances_meta.push(Some(PreprocessedInstanceMeta {
                matrix_index,
                width,
                degree_bits,
            }));
        } else {
            instances_meta.push(None);
        }
    }

    let (preprocessed, preprocessed_prover_data) = if domains_and_traces.is_empty() {
        (None, None)
    } else {
        let (commitment, prover_data) = pcs.commit_preprocessing(domains_and_traces);
        (
            Some(GlobalPreprocessed {
                commitment,
                instances: instances_meta,
                matrix_to_instance,
            }),
            Some(prover_data),
        )
    };

    let lookups = air_infos.iter().map(|ai| ai.lookups.clone()).collect();

    ProverData {
        common: CommonData::new(preprocessed, lookups),
        prover_only: ProverOnlyData {
            preprocessed_prover_data,
        },
    }
}
