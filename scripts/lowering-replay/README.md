# Lowering replay

Check that Lean lowers circuits to midnight-zk's constraint system exactly as Rust does.

```bash
scripts/lowering-replay/run.sh OUT              # Simple floor planner
PLANNER=v1 scripts/lowering-replay/run.sh OUT   # V1
```

- 191 fixtures: 15 real chips (13 from midnight-zk, 2 from blake2b_halo2 and sha3-circuit), the rest synthetic edge cases.
- Expected, Simple: 149 key identically, 40 rejected by both sides, 2 rejected by Lean as streams no Rust API call spells. V1: 145, 44, 2.
- Simple also replays five programs compiled by `Midnight.Backend.compile` (`LoweringFixtures/Compiled.lean`).
- Anchors to Rust's own configuration: the `midnight` key format and 3 fixtures keyed to midnight-zk's stored `ShaPreImageCircuitVk`.
- Needs a clean midnight-zk `1e39c120` in `../midnight-zk` (`REPLAY_ALLOW_ZK=1` to override; the summary records it).
