# Build Benchmark

This benchmark removes the local `.lake/build` directory, runs `lake exe cache get`, then runs `lake build --no-cache` and records build metrics in `measurements.jsonl`.

It deliberately preserves `.lake/packages`, so dependency source trees and downloaded dependency build artifacts can be reused by the runner cache while the project itself is rebuilt from scratch.

Whole-build metrics:

- `build//instructions`
- `build//maxrss`
- `build//task-clock`
- `build//wall-clock`

Per-module metrics:

- `build/module/<module>//instructions`
- `build/module/<module>//lines`
- `build/module/<module>//heartbeats` when `BENCH_HEARTBEATS=1`

Lean profile metrics, summed by downstream consumers when metric names repeat:

- `build/profile/<name>//wall-clock`

The benchmark overrides the Lean executable that Lake uses, so module measurements come from the actual Lake build graph rather than a separate one-file-at-a-time pass.

The heartbeat metric is experimental. It enables Lean's heartbeat profiler and sums top-level profiler events for each module invocation.
