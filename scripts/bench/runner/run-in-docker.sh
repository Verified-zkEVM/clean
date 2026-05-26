#!/usr/bin/env bash
set -euo pipefail

: "${BENCH_PR:?BENCH_PR is required}"
: "${BENCH_BASE_SHA:?BENCH_BASE_SHA is required}"
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

mkdir -p "$CACHE_DIR/elan" "$WORK_DIR" "$BENCH_OUTPUT_DIR"
trap 'rm -rf "$RUN_DIR"' EXIT

docker build -t "$IMAGE" -f scripts/bench/runner/Dockerfile scripts/bench/runner

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

run_benchmark() {
  local label="$1"
  local repo="$2"
  local sha="$3"
  local checkout="$WORK_DIR/$label/clean"
  local xdg_cache="$RUN_DIR/xdg-cache/$label"

  mkdir -p "$xdg_cache"
  git clone --filter=blob:none "https://github.com/$repo.git" "$checkout"
  git -C "$checkout" fetch --no-tags "https://github.com/$repo.git" "$sha"
  git -C "$checkout" checkout --detach "$sha"
  rm -rf "$checkout/scripts/bench"
  mkdir -p "$checkout/scripts"
  cp -a scripts/bench "$checkout/scripts/bench"

  local toolchain
  toolchain="$(sed -n '1p' "$checkout/lean-toolchain")"
  docker run --rm \
    --network bridge \
    -e ELAN_HOME=/bench-cache/elan \
    -v "$CACHE_DIR/elan:/bench-cache/elan" \
    "$IMAGE" \
    elan toolchain install "$toolchain"

  docker run --rm \
    --cap-add PERFMON \
    --security-opt seccomp=unconfined \
    --security-opt no-new-privileges \
    --network bridge \
    -e XDG_CACHE_HOME=/workspace/xdg-cache \
    -e ELAN_HOME=/bench-cache/elan \
    -e BENCH_OUTPUT_FILE="/bench-output/$label.jsonl" \
    -v "$checkout:/workspace/clean" \
    -v "$CACHE_DIR/elan:/bench-cache/elan:ro" \
    -v "$xdg_cache:/workspace/xdg-cache" \
    -v "$BENCH_OUTPUT_DIR:/bench-output" \
    "${PERF_MOUNTS[@]}" \
    "$IMAGE" \
    bash -lc 'scripts/bench/build/run && cp measurements.jsonl "$BENCH_OUTPUT_FILE"'
}

run_benchmark baseline "$BENCH_REPOSITORY" "$BENCH_BASE_SHA"
run_benchmark current "$BENCH_HEAD_REPO" "$BENCH_SHA"
