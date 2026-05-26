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
