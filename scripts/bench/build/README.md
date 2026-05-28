# Build Benchmark

This benchmark runs `lake exe cache get`, then runs `lake build` and records build metrics in `measurements.jsonl`.

It preserves `.lake/packages` and does not delete `.lake/build`, so persistent or local worktrees can reuse dependency, downloaded, and project build artifacts.

Whole-build metrics:

- `build//maxrss`
- `build//wall-clock`

Per-module metrics:

- `build/module/<module>//lines`
- `build/module/<module>//heartbeats`

After the initial build finishes, the benchmark enumerates every tracked `Clean/**/*.lean` module with Lean's module discovery helpers. It asks Lake to build each module target before recording that module's heartbeat measurement, so the benchmark surfaces modules that are not buildable instead of silently omitting them.

The heartbeat metric reruns Lean's frontend for each successfully built module, re-elaborates each command with Mathlib's heartbeat-counting helper before elaborating it for real, and records the sum of user-facing heartbeat counts.
