# Build Benchmark

This benchmark runs `lake exe cache get`, then runs `lake build` and records build metrics in `measurements.jsonl`.

It preserves `.lake/packages` and does not delete `.lake/build`, so persistent or local worktrees can reuse dependency, downloaded, and project build artifacts.

Whole-build metrics:

- `build//maxrss`
- `build//wall-clock`

Per-module metrics:

- `build/module/<module>//lines`
- `build/module/<module>//heartbeats`

After the build finishes, the benchmark enumerates every built `Clean` module from `.lake/build/lib/lean/Clean/**/*.olean` and records heartbeat measurements for the corresponding source modules. This keeps module coverage aligned with the default Lake build graph even when Lake reuses cached build artifacts.

Heartbeat measurement runs in parallel. Set `BENCH_HEARTBEAT_JOBS` to control the worker count; by default it uses up to 6 workers.

The heartbeat metric reruns Lean's frontend for each successfully built module, re-elaborates each command with Mathlib's heartbeat-counting helper before elaborating it for real, and records the sum of user-facing heartbeat counts.
