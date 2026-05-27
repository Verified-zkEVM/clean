# Benchmark Suite

This directory contains benchmarks for tracking Lean build regressions.
The format follows the mathlib4 benchmark suite: each benchmark appends JSON Lines records to `measurements.jsonl`.

Run the full suite from the repository root:

```bash
scripts/bench/run
```

Run only the build benchmark:

```bash
scripts/bench/build/run
```

The build benchmark records whole-build resource metrics and per-module instruction counts. When `BENCH_HEARTBEATS=1` is set, it also records deterministic per-module frontend heartbeat counts. The maintainer-triggered PR workflow enables heartbeat collection by default.

Render a report from one run:

```bash
scripts/bench/report.py measurements.jsonl
```

Compare a current run against a baseline:

```bash
scripts/bench/report.py current.jsonl baseline.jsonl
```

Comparison reports show the whole-build summary plus the top 10 module heartbeat regressions, top 10 module heartbeat improvements, and top 10 highest-heartbeat modules.

Render the module tables by instructions instead of heartbeats:

```bash
scripts/bench/report.py current.jsonl baseline.jsonl --module-metric instructions
```

Set `BENCH_HEARTBEATS=1` when running the benchmark to collect heartbeat measurements.

## Maintainer-triggered PR benchmarks

After the benchmark workflows are present on the default branch, maintainers can comment on a pull request with:

```text
/bench
```

The command workflow verifies that the commenter is an owner, member, or collaborator, then dispatches the benchmark workflow for the pull request's exact base and head commits. The benchmark job runs the base commit first and the pull request commit second on the same runner, then comments on the pull request with a comparison report.

The benchmark scripts themselves are checked out from the default branch and overlaid onto each measured checkout before running. This keeps the reporting machinery stable and lets the baseline commit be measured even when it predates the benchmark suite.

The benchmark workflow expects a repo-scoped self-hosted runner with labels:

```text
self-hosted, linux, x64, clean-bench
```

The workflow runs checked-out code inside a Docker container. Persistent Lean toolchain state lives under `/var/lib/clean-bench/cache/elan`, and persistent Lake dependency package caches live under `/var/lib/clean-bench/cache/lake-packages`, keyed by `lean-toolchain` plus `lake-manifest.json`. Each baseline/current checkout and writable non-dependency cache directory uses a per-run workspace that is removed after the benchmark. The persistent Lean toolchain cache is mounted read-only when benchmarked code runs.

The host must provide working userspace `perf` instruction counters. In practice this means configuring the host so `perf stat -e instructions:u -- true` reports a numeric count for the runner environment. The container is run without host networking, without privileged mode, and without the Docker socket mounted.
