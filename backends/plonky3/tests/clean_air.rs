use clean_backend::{
    generate_lookup_tables, parse_init_trace, prove, verify, CleanAirInstance, MainAir,
    Table, StarkConfig, VK, ByteRangeAir,
};
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

/// test fibonacci8 exported from clean
#[test]
fn test_clean_fib() {
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

    // Create the MainAir from JSON content
    let main_air = MainAir::new(&json_content, main_trace.width());
    let air_instance = CleanAirInstance::Main(main_air);
    
    // Create VK first, then use it to create Table
    let main_vk = VK::new(air_instance, main_trace.width());
    let table = Table::new(main_vk.clone(), main_trace.clone());
    let mut tables = vec![&table];
    let mut vks = vec![&main_vk];

    // Create lookup VKs first
    let byte_range_air = ByteRangeAir::new();
    let byte_range_air_instance = CleanAirInstance::ByteRange(byte_range_air);
    let byte_range_vk = VK::new(byte_range_air_instance, 1); // ByteRange has width 1
    let lookup_vks = vec![byte_range_vk];

    let lookup_tables =
        generate_lookup_tables(&main_vk, &lookup_vks, &main_trace);

    for lookup_table in &lookup_tables {
        tables.push(lookup_table);
    }
    
    // Add lookup VKs to the vks array
    for lookup_vk in &lookup_vks {
        vks.push(lookup_vk);
    }

    let pis = vec![BabyBear::ZERO, BabyBear::ONE, x];
    let proof = prove(&config, &tables, &pis);
    verify(&config, &vks, &proof, &pis).expect("verification failed");
}
