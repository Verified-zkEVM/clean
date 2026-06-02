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

The build benchmark records whole-build resource metrics and deterministic per-module frontend heartbeat counts.

Render a report from one run:

```bash
scripts/bench/report.py measurements.jsonl
```

Compare a current run against a baseline:

```bash
scripts/bench/report.py current.jsonl baseline.jsonl
```

Comparison reports show the whole-build summary plus the top 10 module heartbeat regressions, top 10 module heartbeat improvements, and top 10 highest-heartbeat modules.

Render a full alphabetically sorted module table for detailed investigation:

```bash
scripts/bench/report.py current.jsonl baseline.jsonl --all-modules
```

Measure heartbeats for one module in the current working tree:

```bash
scripts/bench/heartbeats Clean.Gadgets.BLAKE3.ApplyRounds
```

Compare one module against a baseline revision, defaulting to `main`:

```bash
scripts/bench/heartbeat-diff Clean.Gadgets.BLAKE3.ApplyRounds
scripts/bench/heartbeat-diff Clean.Gadgets.BLAKE3.ApplyRounds 6bc9fb25
```

`heartbeat-diff` reuses a persistent baseline worktree at `.bench-baseline-worktree/`. It checks that worktree out at the requested baseline, runs `lake exe cache get` and `lake build`, then compares the current working tree count against the baseline count.

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

The workflow runs checked-out code inside a Docker container. Persistent Lean toolchain state lives under `/var/lib/clean-bench/cache/elan`, persistent Lake dependency package caches live under `/var/lib/clean-bench/cache/lake-packages`, and persistent mathlib `.ltar` download caches live under `/var/lib/clean-bench/cache/mathlib-cache`; these are keyed by `lean-toolchain` plus `lake-manifest.json`. Baseline/main runs from the canonical repository also reuse a persistent project build cache under `/var/lib/clean-bench/cache/lake-build`, keyed the same way. PR-head checkouts reuse a separate persistent project build cache under `/var/lib/clean-bench/cache/pr-lake-build/<head-repo>/<pr>/<key>`, so repeated benchmarks on the same PR can reuse previous build artifacts without sharing them with main or other PRs. Cache-mounted benchmark runs take a host `flock` under `/var/lib/clean-bench/cache/locks` for that dependency key, preventing concurrent writers from sharing the same persistent Lake cache. PR-head build caches older than 30 days are pruned after benchmark runs; set `BENCH_PR_BUILD_CACHE_MAX_AGE_DAYS=0` to disable pruning or another positive integer to change the retention period. Each measured checkout and writable non-dependency cache directory uses a per-run workspace that is removed after the benchmark. The persistent Lean toolchain cache is mounted read-only when benchmarked code runs.

Pushes to `main` run the heartbeat benchmark and store the resulting baseline measurements under `/var/lib/clean-bench/cache/baselines/<sha>.jsonl`. A PR benchmark reuses that file when the requested base SHA has already been measured; otherwise it measures the baseline and stores it for future runs. The PR head is always measured from the requested checkout and is never reused from another SHA or checkout. Workflow artifacts include the summary report and a full alphabetically sorted module table.

The container is run without host networking, without privileged mode, and without the Docker socket mounted.
