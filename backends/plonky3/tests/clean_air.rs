use std::vec::Vec;

use clean_backend::{
    generate_lookup_airs, parse_init_trace, prove, verify, CleanAirInstance,
    Table, StarkConfig,
};
use itertools::Itertools;
use p3_air::BaseAir;
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{create_test_fri_config, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::rngs::SmallRng;
use rand::SeedableRng;

const JSON_PATH: &str = "clean_fib.json";

/// Helper function to read JSON file content from the tests directory
fn read_test_json(filename: &str) -> String {
    let tests_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let json_path = tests_dir.join(filename);
    std::fs::read_to_string(json_path)
        .unwrap_or_else(|e| panic!("Failed to read JSON file '{}': {}", filename, e))
}

#[test]
fn test_clean() {
    // Initialize tracing subscriber to see tracing output
    let _ = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(tracing::Level::INFO)
        .try_init();

    type Val = BabyBear;
    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs =
        MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
    type Challenge = BinomialExtensionField<Val, 4>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type Dft = Radix2DitParallel<Val>;
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let config = create_test_fri_config(challenge_mmcs, 2);
    let pcs = Pcs::new(dft, val_mmcs, config);

    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);

    // Read the trace JSON file content
    let trace_json_content = read_test_json("trace.json");
    let init_trace = parse_init_trace::<BabyBear>(&trace_json_content);

    let width = init_trace[0].len();

    let main_trace: RowMajorMatrix<BabyBear> =
        RowMajorMatrix::new(init_trace.iter().flatten().cloned().collect(), width);

    // Get the result
    let x = main_trace.get(main_trace.height() - 1, 1).unwrap();

    // Read the JSON file content
    let json_content = read_test_json(JSON_PATH);

    let table = Table::new(&json_content, main_trace.clone());

    // Generate lookup AIRs with calculated multiplicity traces 
    let lookup_airs_with_traces =
        generate_lookup_airs(table.as_clean_air().unwrap(), &main_trace);

    // Create properly typed vectors for the multi-AIR interface using wrapper
    let mut airs = vec![&table];
    let mut traces = vec![table.main_trace().clone()];

    // Add lookup AIRs and their traces - create wrappers for them
    let lookup_air_wrappers: Vec<Table<BabyBear>> = lookup_airs_with_traces
        .iter()
        .map(|lookup_air| {
            let instance = CleanAirInstance::ByteRange(lookup_air.air.clone());
            Table::from_instance(instance, lookup_air.main_trace.clone())
        })
        .collect();

    for wrapper in &lookup_air_wrappers {
        airs.push(wrapper);
        traces.push(wrapper.main_trace().clone());
    }
    // Build the preprocessed traces vector
    let mut pres = vec![table.inner().preprocessed_trace()];

    // Add preprocessed traces for lookup AIRs
    for lookup_air in &lookup_airs_with_traces {
        pres.push(lookup_air.air.preprocessed_trace());
    }

    // todo: allow null preprocessed traces, so we don't have to create default traces
    let pres = pres
        .into_iter()
        .enumerate()
        .map(|(i, pre)| {
            pre.unwrap_or_else(|| RowMajorMatrix::new(vec![BabyBear::ZERO; traces[i].height()], 1))
        })
        .collect_vec();

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, x];
    // todo: let air wrappers to hold the corresponding traces
    let proof = prove(&config, airs.clone(), traces, pres.clone(), &pis);
    verify(&config, airs, pres, &proof, &pis).expect("verification failed");
}
