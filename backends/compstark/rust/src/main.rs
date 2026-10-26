//! Plonky3's side of the keccak-air showcase: the upstream example `prove_prime_field_31
//! --field koala-bear --objective keccak-f-permutations --merkle-hash poseidon2
//! --discrete-fourier-transform radix-2-dit-parallel` (Plonky3 `a4982ec`), reproduced from the
//! same upstream functions since the example binary neither writes its proof nor reads one.
//!
//! Both configurations commit with the example's Merkle tree (`MerkleTreeMmcs` over Poseidon2,
//! caps of height 3) and challenger, with the Poseidon2 constants `new_from_rng_128` draws from
//! `SmallRng` seeded with `1`. They differ in FRI's parameters:
//!
//! * `example`: the example's `new_benchmark_high_arity` (blowup 2, arity up to 8, 16 bits of
//!   query and 10 of batching grinding) with its query count for 100 conjectured bits;
//! * `proven`: the example's with 188 queries and 2, 24 and 12 bits of grinding before the
//!   out-of-domain point, the batching challenge and each fold, for which CompStark's security
//!   calculator proves 100 bits per oracle answer
//!   (`CleanCompStark.KeccakShowcase.keccak_soundness_ro`).
//!
//! The permutations' inputs are the example's: `2^L / 24` draws of `SmallRng` seeded with `1`.
//!
//! Commands, `L` the log of the trace's height:
//!
//! * `inputs L FILE`: the inputs, one permutation's 25 lanes per line;
//! * `trace L`: the FNV-1a hash of every row of `generate_trace_rows`, one per line in hex;
//! * `prove CONFIG L FILE`: the proof as JSON, after Plonky3 verified it (run with
//!   `RAYON_NUM_THREADS=1` for the smallest grinding witnesses, as CompStark grinds);
//! * `verify CONFIG L FILE`: Plonky3's verdict on the JSON proof in `FILE`;
//! * `bench CONFIG L REPS`: the median milliseconds of trace generation, proof and verification.
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_keccak_air::{generate_trace_rows, KeccakAir};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{prove, verify, ConjecturedSecurity, Proof, StarkConfig};
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};
use std::time::Instant;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;
type P16 = Poseidon2KoalaBear<16>;
type P24 = Poseidon2KoalaBear<24>;
type ValMmcs = MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing,
    PaddingFreeSponge<P24, 24, 16, 8>, TruncatedPermutation<P16, 2, 8, 16>, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
type Config = StarkConfig<TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>, EF,
    DuplexChallenger<F, P24, 24, 16>>;

/// The configuration `name`, `example` or `proven`.
fn config(name: &str) -> Config {
    let mut rng = SmallRng::seed_from_u64(1);
    let p16 = P16::new_from_rng_128(&mut rng);
    let p24 = P24::new_from_rng_128(&mut rng);
    let val_mmcs = ValMmcs::new(PaddingFreeSponge::new(p24.clone()), TruncatedPermutation::new(p16),
        3);
    let mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let (fri, ood_pow_bits) = match name {
        "example" => {
            let mut fri = FriParameters::new_benchmark_high_arity(mmcs);
            // `example_fri_parameters`: the fewest queries for 100 conjectured bits.
            fri.num_queries = (100 - fri.query_proof_of_work_bits).div_ceil(fri.log_blowup);
            while ConjecturedSecurity::compute_ldt_only(fri.log_blowup, fri.num_queries,
                fri.query_proof_of_work_bits, 128, EF::bits()).security_bits < 100
            {
                fri.num_queries += 1;
            }
            (fri, 0)
        }
        "proven" => {
            let fri = FriParameters {
                num_queries: 188,
                batch_proof_of_work_bits: 24,
                commit_proof_of_work_bits: 12,
                ..FriParameters::new_benchmark_high_arity(mmcs)
            };
            (fri, 2)
        }
        _ => panic!("unknown configuration {name}: example or proven"),
    };
    let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri);
    StarkConfig::new(pcs, DuplexChallenger::new(p24)).with_ood_proof_of_work_bits(ood_pow_bits)
}

/// The example's inputs on `2^log_n` rows.
fn inputs(log_n: usize) -> Vec<[u64; 25]> {
    let mut rng = SmallRng::seed_from_u64(1);
    (0..(1usize << log_n) / 24).map(|_| rng.random()).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let args: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match args[1..] {
        ["inputs", log_n, file] => {
            let lines: String = inputs(log_n.parse().unwrap()).iter()
                .map(|i| i.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ") + "\n")
                .collect();
            std::fs::write(file, lines).unwrap();
        }
        ["trace", log_n] => {
            let trace = generate_trace_rows::<F>(inputs(log_n.parse().unwrap()), 1);
            for row in trace.row_slices() {
                let hash = row.iter().fold(0xcbf29ce484222325u64, |h, x| {
                    (h ^ x.as_canonical_u32() as u64).wrapping_mul(0x100000001b3)
                });
                println!("{hash:016x}");
            }
        }
        ["prove", name, log_n, file] => {
            let config = config(name);
            let trace = generate_trace_rows::<F>(inputs(log_n.parse().unwrap()), 1);
            let proof = prove(&config, &KeccakAir {}, trace, &[]).expect("Plonky3 cannot prove");
            verify(&config, &KeccakAir {}, &proof, &[]).expect("Plonky3 rejects its own proof");
            std::fs::write(file, serde_json::to_string(&proof).unwrap()).unwrap();
        }
        ["verify", name, log_n, file] => {
            let config = config(name);
            let proof: Proof<Config> =
                serde_json::from_str(&std::fs::read_to_string(file).unwrap()).unwrap();
            assert_eq!(proof.degree_bits, log_n.parse::<usize>().unwrap(), "degree bits");
            match verify(&config, &KeccakAir {}, &proof, &[]) {
                Ok(()) => println!("accepted"),
                Err(e) => {
                    println!("rejected: {e:?}");
                    std::process::exit(1);
                }
            }
        }
        ["bench", name, log_n, reps] => {
            let config = config(name);
            let log_n: usize = log_n.parse().unwrap();
            let (mut tg, mut tp, mut tt, mut tv) = (vec![], vec![], vec![], vec![]);
            for _ in 0..reps.parse().unwrap() {
                let ins = inputs(log_n);
                let t = Instant::now();
                let trace = generate_trace_rows::<F>(ins, 1);
                tg.push(t.elapsed().as_secs_f64() * 1e3);
                let t = Instant::now();
                let proof = prove(&config, &KeccakAir {}, trace, &[]).unwrap();
                tp.push(t.elapsed().as_secs_f64() * 1e3);
                tt.push(tg[tg.len() - 1] + tp[tp.len() - 1]);
                let t = Instant::now();
                verify(&config, &KeccakAir {}, &proof, &[]).unwrap();
                tv.push(t.elapsed().as_secs_f64() * 1e3);
            }
            let med = |v: &mut Vec<f64>| {
                v.sort_by(|a, b| a.partial_cmp(b).unwrap());
                v[v.len() / 2]
            };
            println!(
                "plonky3 {name} 2^{log_n} tracegen {:.1} prove {:.1} total {:.1} verify {:.1} ms",
                med(&mut tg), med(&mut tp), med(&mut tt), med(&mut tv));
        }
        _ => panic!("usage: inputs L FILE | trace L | prove CONFIG L FILE | verify CONFIG L FILE \
            | bench CONFIG L REPS"),
    }
}
