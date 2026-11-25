# Midnight SHA-256 in Clean

Circuits written as Clean programs, proved in Lean, compiled to midnight-zk; Lean derives the same verifying key as Rust.

## What is proved

About midnight-zk `1e39c120`'s `sha_preimage` (k = 13):

- [`Preimage.formal_instance_sha256`](SHA256/Semantics/Formal.lean): soundness, the instance column holds the SHA-256 of the message.
- [`WitnessComplete.exists_for_message`](SHA256/WitnessComplete.lean): completeness, for every 24-byte message.
- [`KeyCheck.rust_key`](SHA256/KeyCheck.lean): Lean's key hashes to Rust's `ShaPreImageCircuitVk`; `KeyCheck.srs_anchor` ties the setup to Filecoin's.
- [`CS.Checked.additive_selector_clean`](Additive.lean): the additive-selector (trashcan) check equals the trashcans' gates, outside a bounded set of challenges.

## Build

Needs Linux, Lean 4.35, Rust 1.90+, Python 3.

1. Check out midnight-zk `1e39c120` as `../midnight-zk`.
2. Derive the k = 13 setup:
   ```bash
   cd ../midnight-zk/zk_stdlib
   curl -L -o examples/assets/bls_filecoin_2p19 \
     https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19
   cargo run --release --example sha_preimage
   ```
3. Build all proofs and key checks (~40 min on 16 cores): `lake build Midnight`.

## Tools

- [`scripts/vk-export`](../scripts/vk-export): export a [challenge](https://github.com/zksecurity/midnight-sha256-challenge) submission and compare Lean's key with Rust's.
- [`scripts/lowering-replay`](../scripts/lowering-replay): check Lean's lowering against Rust's on 191 fixtures.
