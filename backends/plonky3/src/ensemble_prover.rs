//! Proving and verification of ensembles extracted from Clean.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem;

use p3_air::symbolic::SymbolicExpressionExt;
use p3_air::Air;
#[cfg(debug_assertions)]
use p3_air::DebugConstraintBuilder;
use p3_batch_stark::common::{GlobalPreprocessed, PreprocessedInstanceMeta};
use p3_batch_stark::config::Commitment;
use p3_batch_stark::folder::{
    ProverConstraintFolderWithLookups, VerifierConstraintFolderWithLookups,
};
use p3_batch_stark::{
    prove_batch, verify_batch, BatchProof, BatchVerificationError, CommonData, PcsError,
    ProverData, ProverOnlyData, ProvingError, StarkGenericConfig, StarkInstance, Val,
};
use p3_challenger::GrindingChallenger;
use p3_commit::{Pcs, UnivariateStarkPcs};
use p3_field::{Algebra, BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_lookup::{InteractionSymbolicBuilder, Lookups};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

use crate::generated_air::fixed_height_airs;
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

/// The base-2 logarithms of `heights`, which the configuration must support.
fn degree_bits<SC: StarkGenericConfig>(
    config: &SC,
    heights: &[usize],
) -> Result<Vec<usize>, EnsembleShapeError> {
    let log_maximum = config.pcs().log_max_trace_height();
    heights
        .iter()
        .map(|&height| {
            let log_height = log2_strict_usize(height);
            if log_height > log_maximum {
                return Err(EnsembleShapeError::MaximumTraceHeight {
                    log_height,
                    log_maximum,
                });
            }
            Ok(log_height)
        })
        .collect()
}

/// The public values of every AIR: only the verifier AIR, which is last, reads them.
fn per_air_public_values<F: Clone>(airs: usize, public_values: &[F]) -> Vec<Vec<F>> {
    let mut values = vec![Vec::new(); airs - 1];
    values.push(public_values.to_vec());
    values
}

/// The proving and verification key of a generated ensemble under one proof configuration.
///
/// The key commits to the preprocessed columns once, and computes the lookups of the AIRs whose
/// height the program fixes: the components with a fixed height, and the verifier AIR, whose
/// height is the minimum trace height. Each statement adds the lookups of its demand-generated
/// components, which have no preprocessed columns.
pub struct EnsembleKey<SC: StarkGenericConfig, P> {
    config: SC,
    minimum_height: usize,
    commitment: Option<Commitment<SC>>,
    /// The preprocessed matrix and the lookups of each fixed-height AIR, in statement order.
    fixed_instances: Vec<Option<PreprocessedInstanceMeta>>,
    fixed_lookups: Vec<Lookups<Val<SC>>>,
    prover_only: ProverOnlyData<SC>,
    _program: PhantomData<P>,
}

impl<SC, P> EnsembleKey<SC, P>
where
    SC: StarkGenericConfig,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>: Algebra<SC::Challenge>,
    Val<SC>: WitnessField,
    P: GeneratedAirSpec,
    GeneratedAir<P>: Air<InteractionSymbolicBuilder<Val<SC>, SC::Challenge>>,
{
    /// The key for statements whose verifier AIR has `minimum_height` rows, the smallest trace
    /// height the configuration accepts. The configuration must not be zero-knowledge.
    pub fn new(
        config: SC,
        minimum_height: usize,
    ) -> Result<Self, EnsembleProvingError<PcsProverError<SC>>> {
        // a hiding PCS salts the preprocessed commitments, which the verifier then can't recompute
        if config.is_zk() != 0 {
            return Err(EnsembleProvingError::Shape(
                EnsembleShapeError::ZeroKnowledge,
            ));
        }
        let (airs, heights) =
            fixed_height_airs::<P>(minimum_height).map_err(EnsembleProvingError::Shape)?;
        let degree_bits = degree_bits(&config, &heights).map_err(EnsembleProvingError::Shape)?;
        let ProverData {
            common,
            prover_only,
        } = ProverData::from_airs_and_degrees(&config, &airs, &degree_bits)
            .map_err(EnsembleProvingError::Proof)?;
        let (commitment, fixed_instances) = match common.preprocessed {
            Some(preprocessed) => (Some(preprocessed.commitment), preprocessed.instances),
            None => (None, vec![None; airs.len()]),
        };
        Ok(Self {
            config,
            minimum_height,
            commitment,
            fixed_instances,
            fixed_lookups: common.lookups,
            prover_only,
            _program: PhantomData,
        })
    }

    /// The degree bits of the statement's AIRs, and their data shared by prover and verifier.
    fn common_data(
        &self,
        ensemble: &GeneratedEnsemble<Val<SC>, P>,
    ) -> Result<(Vec<usize>, CommonData<SC>), EnsembleShapeError> {
        if ensemble.verifier_height() != self.minimum_height {
            return Err(EnsembleShapeError::KeyMinimumHeight {
                expected: self.minimum_height,
                actual: ensemble.verifier_height(),
            });
        }
        let degree_bits = degree_bits(&self.config, &ensemble.air_heights())?;
        let fixed_height = ensemble.fixed_height_airs();
        let (demand_airs, demand_degree_bits): (Vec<_>, Vec<_>) = ensemble
            .airs()
            .iter()
            .zip(&degree_bits)
            .zip(&fixed_height)
            .filter(|(_, &fixed)| !fixed)
            .map(|((air, &bits), _)| (air.clone(), bits))
            .unzip();
        // demand-generated components have no preprocessed columns to commit to
        let mut demand_lookups =
            ProverData::from_airs_and_degrees(&self.config, &demand_airs, &demand_degree_bits)
                .map_err(|_| EnsembleShapeError::Setup)?
                .common
                .lookups
                .into_iter();
        let mut fixed = self.fixed_instances.iter().zip(&self.fixed_lookups);
        let mut instances = Vec::with_capacity(fixed_height.len());
        let mut lookups = Vec::with_capacity(fixed_height.len());
        for is_fixed in fixed_height {
            let (instance, air_lookups) = if is_fixed {
                let (instance, air_lookups) = fixed.next().expect("every fixed-height AIR");
                (instance.clone(), air_lookups.clone())
            } else {
                (None, demand_lookups.next().expect("every demand AIR"))
            };
            instances.push(instance);
            lookups.push(air_lookups);
        }
        let preprocessed = self.commitment.clone().map(|commitment| {
            let mut matrix_to_instance = vec![0; instances.iter().flatten().count()];
            for (instance, meta) in instances.iter().enumerate() {
                if let Some(meta) = meta {
                    matrix_to_instance[meta.matrix_index] = instance;
                }
            }
            GlobalPreprocessed {
                commitment,
                instances,
                matrix_to_instance,
            }
        });
        Ok((
            degree_bits,
            CommonData {
                preprocessed,
                lookups,
            },
        ))
    }

    /// Prove a complete generated ensemble and its canonically ordered padded traces, where empty
    /// components have traces of height zero.
    pub fn prove(
        &mut self,
        ensemble: &GeneratedEnsemble<Val<SC>, P>,
        traces: Vec<RowMajorMatrix<Val<SC>>>,
        public_values: &[Val<SC>],
    ) -> Result<BatchProof<SC>, EnsembleProvingError<PcsProverError<SC>>>
    where
        SC::Challenge: BasedVectorSpace<Val<SC>>,
        SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
        Val<SC>: PrimeField64,
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
        for (component, trace) in traces.iter().enumerate() {
            let width = P::WIDTHS[component];
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
        let (_, common) = self
            .common_data(ensemble)
            .map_err(EnsembleProvingError::Shape)?;
        // empty traces have no AIR
        let mut traces = traces
            .into_iter()
            .filter(|trace| trace.height() != 0)
            .collect::<Vec<_>>();
        traces.push(RowMajorMatrix::new(
            vec![Val::<SC>::ZERO; ensemble.verifier_height()],
            1,
        ));
        let public_values = per_air_public_values(airs.len(), public_values);
        let traces = traces.iter().collect::<Vec<_>>();
        let instances = StarkInstance::new_multiple(airs, &traces, &public_values);
        // the PCS data of the preprocessed commitment moves into the statement's prover data and
        // back
        let prover_data = ProverData {
            common,
            prover_only: mem::replace(
                &mut self.prover_only,
                ProverOnlyData {
                    preprocessed_prover_data: None,
                },
            ),
        };
        let proof = prove_batch(&self.config, &instances, &prover_data);
        self.prover_only = prover_data.prover_only;
        proof.map_err(EnsembleProvingError::Proof)
    }

    /// Verify a proof against a complete generated ensemble statement.
    pub fn verify(
        &self,
        ensemble: &GeneratedEnsemble<Val<SC>, P>,
        proof: &BatchProof<SC>,
        public_values: &[Val<SC>],
    ) -> Result<(), EnsembleVerificationError<PcsError<SC>>>
    where
        SC::Challenge: BasedVectorSpace<Val<SC>>,
        SC::Challenger: GrindingChallenger<Witness = Val<SC>>,
        Val<SC>: PrimeField64,
        GeneratedAir<P>: for<'a> Air<VerifierConstraintFolderWithLookups<'a, SC>> + Clone,
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
        let (degree_bits, common) = self
            .common_data(ensemble)
            .map_err(EnsembleVerificationError::Shape)?;
        if proof.degree_bits != degree_bits {
            return Err(EnsembleVerificationError::Shape(
                EnsembleShapeError::ProofDegreeBits {
                    expected: degree_bits,
                    actual: proof.degree_bits.clone(),
                },
            ));
        }
        let public_values = per_air_public_values(airs.len(), public_values);
        verify_batch(&self.config, airs, proof, &public_values, &common)
            .map_err(EnsembleVerificationError::Proof)
    }
}
