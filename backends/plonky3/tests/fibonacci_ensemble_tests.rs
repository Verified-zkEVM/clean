extern crate alloc;

mod common;

mod generated {
    include!("generated/fibonacci_ensemble.rs");
}

use clean_backend::witness_generation::{Interaction, WitnessField, WitnessGenerationError};
use clean_backend::StarkConfig;
use clean_backend::{
    prove_ensemble, verify_ensemble, EnsembleProvingError, EnsembleShapeError,
    EnsembleVerificationError, GeneratedAirSpec, GeneratedEnsemble,
};
use common::setup;
use p3_baby_bear::BabyBear;
use p3_commit::ExtensionMmcs;
use p3_field::Field;
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_fri::{FriParameters, HidingFriPcs};
use p3_koala_bear::KoalaBear;
#[cfg(not(debug_assertions))]
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use rand::rngs::{SmallRng, StdRng};
use rand::SeedableRng;
use std::time::Instant;

fn field(value: u64) -> BabyBear {
    BabyBear::from_u64(value)
}

#[test]
fn extracted_rust_generates_fibonacci_ensemble_witness() {
    let witness = generated::generate(
        &[field(32), field(5), field(226)],
        &[],
        setup::MINIMUM_TRACE_HEIGHT,
    )
    .expect("extracted Rust witness generation failed");

    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![32, 32, 256]
    );
    let bytes = witness.tables[2]
        .iter()
        .map(|row| row[1])
        .collect::<Vec<_>>();
    assert_eq!(
        bytes
            .iter()
            .map(|value| value.as_canonical_u64())
            .sum::<u64>(),
        32
    );
    assert_eq!(
        bytes.iter().map(|value| value.as_canonical_u64()).max(),
        Some(2)
    );
}

#[test]
fn extracted_rust_coalesces_repeated_chip_pulls() {
    let witness = generated::generate(
        &[field(400), field(219), field(61)],
        &[],
        setup::MINIMUM_TRACE_HEIGHT,
    )
    .expect("extracted Rust witness generation failed");

    assert_eq!(
        witness.tables.iter().map(Vec::len).collect::<Vec<_>>(),
        vec![512, 512, 256]
    );
}

#[test]
fn extracted_fibonacci_air_proves_and_verifies() {
    let config = setup::test_config(7);
    let public_values = vec![field(4096), field(59), field(29)];
    let witness_started = Instant::now();
    let witness = generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");

    let traces = witness.into_traces().expect("invalid extracted traces");
    assert_eq!(
        traces.iter().map(Matrix::height).collect::<Vec<_>>(),
        vec![4096, 512, 256]
    );
    assert_eq!(
        traces.iter().map(Matrix::width).collect::<Vec<_>>(),
        vec![5, 5, 1]
    );

    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let witness_elapsed = witness_started.elapsed();
    let proving_started = Instant::now();
    let proof =
        prove_ensemble(&config, &statement, traces, &public_values).expect("invalid proving shape");
    let proving_elapsed = proving_started.elapsed();
    let proof_json_bytes = serde_json::to_vec(&proof)
        .expect("proof serialization failed")
        .len();
    let verification_started = Instant::now();
    verify_ensemble(&config, &statement, &proof, &public_values)
        .expect("extracted Fibonacci AIR proof failed verification");
    eprintln!(
        "4096 steps: witness+padding={witness_elapsed:?}, proving={proving_elapsed:?}, \
         verification={:?}, proof_json={proof_json_bytes} bytes",
        verification_started.elapsed()
    );
}

#[test]
fn ensemble_api_reports_shape_errors() {
    let config = setup::test_config(7);
    let public_values = vec![field(32), field(5), field(226)];
    let witness = generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let traces = witness.into_traces().expect("invalid extracted traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    assert_eq!(statement.component_count(), 3);
    assert_eq!(statement.trace_heights(), trace_heights);
    assert_eq!(statement.interaction_count(), 418);
    let different_dynamic_shape =
        generated::Statement::<BabyBear>::new(&[64, 32, 256], setup::MINIMUM_TRACE_HEIGHT)
            .expect("valid alternative dynamic shape");
    assert!(matches!(
        prove_ensemble(
            &config,
            &different_dynamic_shape,
            traces.clone(),
            &public_values,
        ),
        Err(EnsembleProvingError::Shape(
            EnsembleShapeError::StatementTraceHeight {
                component: 0,
                expected: 64,
                actual: 32,
            }
        ))
    ));
    let mut traces = traces;
    traces.pop();

    assert!(matches!(
        prove_ensemble(&config, &statement, traces, &public_values),
        Err(EnsembleProvingError::Shape(
            EnsembleShapeError::TraceCount {
                expected: 3,
                actual: 2,
            }
        ))
    ));
    assert!(matches!(
        generated::Statement::<BabyBear>::new(&trace_heights[..2], setup::MINIMUM_TRACE_HEIGHT),
        Err(EnsembleShapeError::ComponentCount {
            expected: 3,
            trace_heights: 2,
        })
    ));
    let mut wrong_fixed_height = trace_heights.clone();
    wrong_fixed_height[2] = 128;
    assert!(matches!(
        generated::Statement::<BabyBear>::new(&wrong_fixed_height, setup::MINIMUM_TRACE_HEIGHT),
        Err(EnsembleShapeError::FixedTraceHeight {
            component: 2,
            expected: 256,
            actual: 128,
        })
    ));

    assert!(matches!(
        generated::Statement::<BabyBear>::new(&[2, 32, 256], setup::MINIMUM_TRACE_HEIGHT),
        Err(EnsembleShapeError::TraceHeight {
            component: 0,
            height: 2,
        })
    ));
    assert!(matches!(
        generated::Statement::<BabyBear>::new(&trace_heights, 3),
        Err(EnsembleShapeError::MinimumHeight { height: 3 })
    ));
    assert!(matches!(
        GeneratedEnsemble::<BabyBear, WideVerifierMessages>::new(
            &trace_heights,
            setup::MINIMUM_TRACE_HEIGHT
        ),
        Err(EnsembleShapeError::ChannelWidth {
            channel: "fibonacci",
            ..
        })
    ));
    let zk_config = zk_test_config(7);
    assert!(matches!(
        prove_ensemble(&zk_config, &statement, Vec::new(), &public_values),
        Err(EnsembleProvingError::Shape(
            EnsembleShapeError::ZeroKnowledge
        ))
    ));

    let excessive_interactions = [1usize << 30, setup::MINIMUM_TRACE_HEIGHT, 256];
    assert!(matches!(
        generated::Statement::<BabyBear>::new(&excessive_interactions, setup::MINIMUM_TRACE_HEIGHT),
        Err(EnsembleShapeError::InteractionCountBound {
            interactions,
            field_order,
        }) if interactions >= field_order as u128
    ));
}

#[test]
fn generated_code_rejects_other_fields() {
    assert!(matches!(
        generated::Statement::<KoalaBear>::new(&[32, 32, 256], setup::MINIMUM_TRACE_HEIGHT),
        Err(EnsembleShapeError::FieldOrder { expected, actual })
            if expected == BabyBear::ORDER_U64 && actual == KoalaBear::ORDER_U64
    ));
    let public_values = [32, 5, 226].map(KoalaBear::from_u64);
    assert!(matches!(
        generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT),
        Err(WitnessGenerationError::FieldOrder { expected, actual })
            if expected == BabyBear::ORDER_U64 && actual == KoalaBear::ORDER_U64
    ));
}

#[test]
fn short_runs_are_padded_to_the_minimum_trace_height() {
    let config = setup::test_config(5);
    let public_values = vec![field(4), field(3), field(5)];
    let witness = generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let traces = witness.into_traces().expect("invalid extracted traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    assert_eq!(
        trace_heights,
        vec![
            setup::MINIMUM_TRACE_HEIGHT,
            setup::MINIMUM_TRACE_HEIGHT,
            256
        ]
    );
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let proof =
        prove_ensemble(&config, &statement, traces, &public_values).expect("invalid proving shape");
    verify_ensemble(&config, &statement, &proof, &public_values)
        .expect("extracted Fibonacci AIR proof failed verification");
}

#[test]
fn witness_generation_rejects_preallocated_tables_below_the_minimum_height() {
    assert_eq!(
        generated::generate(&[field(32), field(5), field(226)], &[], 512).map(|_| ()),
        Err(WitnessGenerationError::PreallocatedHeight {
            component: "bytes",
            height: 256,
            minimum: 512,
        })
    );
}

#[test]
fn verifier_rejects_a_valid_proof_at_the_wrong_height() {
    let config = setup::test_config(11);
    let public_values = vec![field(32), field(5), field(226)];
    let expected = generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let wrong = generated::generate(&public_values, &[], 64)
        .expect("wrong-height witness generation failed");

    let wrong_traces = wrong.into_traces().expect("invalid wrong-height traces");
    let wrong_heights = wrong_traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let wrong_statement =
        generated::Statement::<BabyBear>::new(&wrong_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid wrong-height AIR shape");
    let wrong_proof = prove_ensemble(&config, &wrong_statement, wrong_traces, &public_values)
        .expect("invalid wrong-height proving shape");
    verify_ensemble(&config, &wrong_statement, &wrong_proof, &public_values)
        .expect("the wrong-height proof must be otherwise valid");
    let altered_public_values = vec![field(32), field(6), field(226)];
    assert!(matches!(
        verify_ensemble(
            &config,
            &wrong_statement,
            &wrong_proof,
            &altered_public_values,
        ),
        Err(EnsembleVerificationError::Proof(_))
    ));

    let expected_traces = expected.into_traces().expect("invalid expected traces");
    let expected_heights = expected_traces
        .iter()
        .map(Matrix::height)
        .collect::<Vec<_>>();
    let expected_statement =
        generated::Statement::<BabyBear>::new(&expected_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid expected AIR shape");
    assert!(matches!(
        verify_ensemble(&config, &expected_statement, &wrong_proof, &public_values),
        Err(EnsembleVerificationError::Shape(
            EnsembleShapeError::ProofDegreeBits { .. }
        ))
    ));
}

/// Prove a tampered trace of the 32-step execution and assert that verification rejects it. The
/// prover checks constraints in debug builds, so such proofs exist only in release builds.
#[cfg(not(debug_assertions))]
fn assert_tampered_trace_rejected(
    seed: u64,
    tamper: impl FnOnce(&mut Vec<RowMajorMatrix<BabyBear>>),
) {
    let config = setup::test_config(seed);
    let public_values = vec![field(32), field(5), field(226)];
    let witness = generated::generate(&public_values, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed");
    let mut traces = witness.into_traces().expect("invalid extracted traces");
    tamper(&mut traces);
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let proof =
        prove_ensemble(&config, &statement, traces, &public_values).expect("invalid proving shape");
    assert!(matches!(
        verify_ensemble(&config, &statement, &proof, &public_values),
        Err(EnsembleVerificationError::Proof(_))
    ));
}

/// The `add8` carry occurs in no interaction, so changing it violates only the printed constraints.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_a_violated_constraint() {
    assert_tampered_trace_rejected(13, |traces| {
        let add8 = &mut traces[1];
        assert_eq!(add8.width(), 5);
        add8.values[4] += BabyBear::ONE;
    });
}

/// The byte table has no constraints, so changing a multiplicity unbalances only the `bytes`
/// channel.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_an_unbalanced_channel() {
    assert_tampered_trace_rejected(17, |traces| {
        traces[2].values[0] += BabyBear::ONE;
    });
}

type Spec = generated::Ensemble;

/// The Fibonacci statement with a wider message in the verifier's first interaction.
#[derive(Clone, Debug)]
struct WideVerifierMessages;

impl GeneratedAirSpec for WideVerifierMessages {
    const FIELD_ORDER: u64 = Spec::FIELD_ORDER;
    const PUBLIC_VALUES: usize = Spec::PUBLIC_VALUES;
    const WIDTHS: &'static [usize] = Spec::WIDTHS;
    const FIXED_COLUMNS: &'static [&'static [usize]] = Spec::FIXED_COLUMNS;
    const FIXED_HEIGHTS: &'static [usize] = Spec::FIXED_HEIGHTS;

    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F> {
        Spec::fixed_row(component, row)
    }

    fn constraints<E: PrimeCharacteristicRing + Clone>(component: usize, row: &[E]) -> Vec<E> {
        Spec::constraints(component, row)
    }

    fn interactions<E: PrimeCharacteristicRing + Clone>(
        component: usize,
        row: &[E],
    ) -> Vec<Interaction<E>> {
        Spec::interactions(component, row)
    }

    fn verifier_interactions<E: PrimeCharacteristicRing + Clone>(
        public_values: &[E],
    ) -> Vec<Interaction<E>> {
        let mut interactions = Spec::verifier_interactions(public_values);
        interactions[0].message.push(E::ZERO);
        interactions
    }
}

/// Traces generated for one public input, proven and verified under another: only the verifier
/// AIR's interactions differ, so the lookup argument must reject them, not only Fiat-Shamir. Proving
/// unbalanced traces panics in debug builds.
#[cfg(not(debug_assertions))]
#[test]
fn verifier_rejects_traces_of_other_public_values() {
    let config = setup::test_config(21);
    let honest = [field(32), field(5), field(226)];
    let claimed = [field(32), field(6), field(226)];
    let traces = generated::generate(&honest, &[], setup::MINIMUM_TRACE_HEIGHT)
        .expect("extracted Rust witness generation failed")
        .into_traces()
        .expect("invalid extracted traces");
    let trace_heights = traces.iter().map(Matrix::height).collect::<Vec<_>>();
    let statement =
        generated::Statement::<BabyBear>::new(&trace_heights, setup::MINIMUM_TRACE_HEIGHT)
            .expect("invalid generated AIR shape");
    let proof =
        prove_ensemble(&config, &statement, traces, &claimed).expect("invalid proving shape");
    assert!(matches!(
        verify_ensemble(&config, &statement, &proof, &claimed),
        Err(EnsembleVerificationError::Proof(_))
    ));
}

type HidingValMmcs = MerkleTreeHidingMmcs<
    <setup::Val as Field>::Packing,
    <setup::Val as Field>::Packing,
    setup::MyHash,
    setup::MyCompress,
    StdRng,
    2,
    8,
    4,
>;
type HidingChallengeMmcs = ExtensionMmcs<setup::Val, setup::Challenge, HidingValMmcs>;
type HidingPcs = HidingFriPcs<setup::Val, setup::Dft, HidingValMmcs, HidingChallengeMmcs, StdRng>;
type ZkConfig = StarkConfig<HidingPcs, setup::Challenge, setup::Challenger>;

/// A zero-knowledge configuration, which the backend rejects.
fn zk_test_config(seed: u64) -> ZkConfig {
    let mut rng = SmallRng::seed_from_u64(seed);
    let perm = setup::Perm::new_from_rng_128(&mut rng);
    let hash = setup::MyHash::new(perm.clone());
    let compress = setup::MyCompress::new(perm.clone());
    let val_mmcs = HidingValMmcs::new(hash, compress, 0, StdRng::seed_from_u64(seed));
    let challenge_mmcs = HidingChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters::new_testing_zk(challenge_mmcs);
    let pcs = HidingPcs::new(
        setup::Dft::default(),
        val_mmcs,
        fri,
        4,
        StdRng::seed_from_u64(seed),
    );
    ZkConfig::new(pcs, setup::Challenger::new(perm))
}
