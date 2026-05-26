# Build Benchmark

This benchmark removes the local package `.lake/build` directory, runs `lake exe cache get`, then runs `lake build --no-cache` and records build metrics in `measurements.jsonl`.

Whole-build metrics:

- `build//instructions`
- `build//maxrss`
- `build//task-clock`
- `build//wall-clock`

Per-module metrics:

- `build/module/<module>//instructions`
- `build/module/<module>//lines`

Lean profile metrics, summed by downstream consumers when metric names repeat:

- `build/profile/<name>//wall-clock`

The benchmark overrides the Lean executable that Lake uses, so module measurements come from the actual Lake build graph rather than a separate one-file-at-a-time pass.
