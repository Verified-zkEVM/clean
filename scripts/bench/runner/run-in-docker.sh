#!/usr/bin/env bash
set -euo pipefail

: "${BENCH_PR:?BENCH_PR is required}"
: "${BENCH_SHA:?BENCH_SHA is required}"
: "${BENCH_HEAD_REPO:?BENCH_HEAD_REPO is required}"
: "${BENCH_REPOSITORY:?BENCH_REPOSITORY is required}"
: "${BENCH_RUN_ID:?BENCH_RUN_ID is required}"
: "${BENCH_OUTPUT_DIR:?BENCH_OUTPUT_DIR is required}"

ROOT="${BENCH_ROOT:-/var/lib/clean-bench}"
IMAGE="${BENCH_IMAGE:-clean-bench-runner:latest}"
RUN_DIR="$ROOT/runs/$BENCH_RUN_ID"
CACHE_DIR="$ROOT/cache"
WORK_DIR="$RUN_DIR/work"

mkdir -p "$CACHE_DIR/elan" "$WORK_DIR" "$RUN_DIR/xdg-cache" "$BENCH_OUTPUT_DIR"
rm -rf "$WORK_DIR/clean"

docker build -t "$IMAGE" -f scripts/bench/runner/Dockerfile scripts/bench/runner

git clone --filter=blob:none "https://github.com/$BENCH_HEAD_REPO.git" "$WORK_DIR/clean"
git -C "$WORK_DIR/clean" fetch --no-tags "https://github.com/$BENCH_HEAD_REPO.git" "$BENCH_SHA"
git -C "$WORK_DIR/clean" checkout --detach "$BENCH_SHA"

TOOLCHAIN="$(sed -n '1p' "$WORK_DIR/clean/lean-toolchain")"
docker run --rm \
  --network bridge \
  -e ELAN_HOME=/bench-cache/elan \
  -v "$CACHE_DIR/elan:/bench-cache/elan" \
  "$IMAGE" \
  elan toolchain install "$TOOLCHAIN"

PERF_MOUNTS=()
HOST_PERF=""
if [ -x "/usr/lib/linux-tools/$(uname -r)/perf" ]; then
  HOST_PERF="/usr/lib/linux-tools/$(uname -r)/perf"
elif [ -x "/usr/lib/linux-tools-$(uname -r | sed 's/-generic$//')/perf" ]; then
  HOST_PERF="/usr/lib/linux-tools-$(uname -r | sed 's/-generic$//')/perf"
elif [ -x /usr/bin/perf ]; then
  HOST_PERF="/usr/bin/perf"
fi
if [ -n "$HOST_PERF" ]; then
  PERF_MOUNTS+=(-v "$HOST_PERF:/usr/local/bin/perf:ro")
fi

docker run --rm \
  --cap-add PERFMON \
  --security-opt seccomp=unconfined \
  --security-opt no-new-privileges \
  --network bridge \
  -e XDG_CACHE_HOME=/workspace/xdg-cache \
  -e ELAN_HOME=/bench-cache/elan \
  -v "$WORK_DIR/clean:/workspace/clean" \
  -v "$CACHE_DIR/elan:/bench-cache/elan:ro" \
  -v "$RUN_DIR/xdg-cache:/workspace/xdg-cache" \
  -v "$BENCH_OUTPUT_DIR:/bench-output" \
  "${PERF_MOUNTS[@]}" \
  "$IMAGE" \
  bash -lc 'scripts/bench/build/run && cp measurements.jsonl /bench-output/measurements.jsonl'

rm -rf "$RUN_DIR"
