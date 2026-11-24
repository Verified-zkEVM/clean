# vk-export

Export a challenge submission from Lean, compare Lean's verifying key with Rust's, and prove with Rust alone.

## Quick check (your own submission)

From this repository's root, with `CHALLENGE` a checkout of [midnight-sha256-challenge](https://github.com/zksecurity/midnight-sha256-challenge):

```bash
VK_KERNEL=1 VK_CONTRACT=CHALLENGE/Challenge scripts/vk-export/run.sh --witgen SUBMISSION OUT
```

- `SUBMISSION`: a directory or `.tar.gz`.
- `OUT/report.json`: `key_status` `PASS` when Lean's and Rust's keys match; `status` `PASS` when the layout and certified checks also hold; `vk` the circuit's fingerprint (below).
- `VK_KERNEL=1`: builds the submission with kernel checking.
- Needs a clean midnight-zk `1e39c120` in `../midnight-zk` (`VK_ALLOW_DIRTY_ZK=1` to override, reported as `PASS-UNPINNED-ZK`).
- Limits: `k ≤ 19` (the Filecoin setup size); no unblinded advice.

## Prove with Rust alone

```bash
cargo run --release --manifest-path scripts/vk-export/native/Cargo.toml --example prove -- OUT              # prints the key
cargo run --release --manifest-path scripts/vk-export/native/Cargo.toml --example prove -- OUT MESSAGE_HEX  # proves a 24-byte message
```

It prints `vk FINGERPRINT FORMAT raw-sha256 SHA256`. The fingerprint is the transcript representative of the inner Halo2 key (k, commitments, pinned domain and constraint system), so circuits that differ only in gates or degree get different fingerprints, while the raw bytes' SHA-256 (midnight-zk's `static_vks` value) can coincide for them; only the raw SHA-256 covers the midnight header (architecture, k, public-input count). The baseline prints `vk 0x2be57df2…0c0f1477 midnight raw-sha256 071bd29a…`, both Rust's `ShaPreImageCircuitVk`. `OUT` can move to any machine with this repository and `../midnight-zk`.

## Untrusted submissions

Building a submission runs its code as you. Use a disposable machine with no credentials, with `W` (this repository's parent) holding only this repository, `midnight-zk` and the challenge checkout.

1. Build the seed once:
   ```bash
   W=$(dirname "$PWD")
   VK_CONTRACT="$W/midnight-sha256-challenge/Challenge" VK_PROJECT="$W/out/project" CARGO_TARGET_DIR="$W/out/target" \
     scripts/vk-export/run.sh --witgen "$W/midnight-sha256-challenge/examples/baseline" "$W/out/baseline"
   ```
2. Export each submission `SUB` (`.tar.gz`) in a fresh sandboxed copy; results land in `R`:
   ```bash
   S=$(mktemp -d); R=~/vk-results/$(basename "$SUB" .tar.gz); cp -a "$W/out/." "$S/"
   bwrap --unshare-all --die-with-parent --new-session --clearenv \
     --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
     --ro-bind-try /etc/alternatives /etc/alternatives --ro-bind-try /etc/ld.so.cache /etc/ld.so.cache \
     --dev /dev --proc /proc --tmpfs /tmp --tmpfs "$HOME" \
     --ro-bind ~/.elan ~/.elan --ro-bind ~/.rustup ~/.rustup --ro-bind ~/.cargo/bin ~/.cargo/bin \
     --ro-bind ~/.cargo/registry ~/.cargo/registry --ro-bind-try ~/.cargo/git ~/.cargo/git \
     --ro-bind "$W" "$W" --bind "$S" "$W/out" --ro-bind "$SUB" /submission.tar.gz --chdir "$PWD" \
     --setenv HOME "$HOME" --setenv PATH "$HOME/.elan/bin:$HOME/.cargo/bin:/usr/bin" \
     --setenv CARGO_NET_OFFLINE true --setenv CARGO_TARGET_DIR "$W/out/target" --setenv VK_PROJECT "$W/out/project" \
     --setenv VK_CONTRACT "$W/midnight-sha256-challenge/Challenge" \
     scripts/vk-export/run.sh --witgen /submission.tar.gz "$W/out/result"
   mkdir -p "$R" && find "$S/result" -maxdepth 1 -type f -name "*.json" -exec cp -t "$R" {} + && rm -rf "$S"
   ```
3. Notes:
   - Pass `VK_KERNEL` or `VK_ALLOW_DIRTY_ZK` with `--setenv` (`--clearenv` drops them); `VK_KERNEL=1` needs a seed built with it.
   - Ubuntu 23.10+: bwrap fails with `loopback: Failed RTM_NEWADDR` until you set `kernel.apparmor_restrict_unprivileged_userns=0` or give bwrap an AppArmor `userns` profile.
   - The comparator on zk.golf, not this export, decides whether a submission is accepted.
