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

The build benchmark records whole-build resource metrics and per-module instruction counts. Instruction counts are the preferred regression signal because wall-clock time is noisy on shared CI runners.

Render a report from one run:

```bash
scripts/bench/report.py measurements.jsonl
```

Compare a current run against a baseline:

```bash
scripts/bench/report.py measurements.jsonl baseline-measurements.jsonl
```

## Maintainer-triggered PR benchmarks

After the benchmark workflows are present on the default branch, maintainers can comment on a pull request with:

```text
/bench
```

The command workflow verifies that the commenter is an owner, member, or collaborator, then dispatches the benchmark workflow for the pull request's exact head commit.

The benchmark workflow expects a repo-scoped self-hosted runner with labels:

```text
self-hosted, linux, x64, clean-bench
```

The workflow runs pull request code inside a Docker container. Persistent Lean toolchain state lives under `/var/lib/clean-bench/cache/elan`, while each pull request checkout and writable cache directory uses a per-run workspace that is removed after the benchmark. The persistent Lean toolchain cache is mounted read-only when pull request code runs.

The host must provide working userspace `perf` instruction counters. In practice this means configuring the host so `perf stat -e instructions:u -- true` reports a numeric count for the runner environment. The container is run without host networking, without privileged mode, and without the Docker socket mounted.
