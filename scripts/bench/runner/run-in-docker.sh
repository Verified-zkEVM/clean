#!/usr/bin/env bash
set -euo pipefail

: "${BENCH_REPOSITORY:?BENCH_REPOSITORY is required}"
: "${BENCH_RUN_ID:?BENCH_RUN_ID is required}"
: "${BENCH_OUTPUT_DIR:?BENCH_OUTPUT_DIR is required}"

if [ "${BENCH_BASELINE_ONLY:-}" = "1" ]; then
  : "${BENCH_SHA:?BENCH_SHA is required}"
  BENCH_HEAD_REPO="${BENCH_HEAD_REPO:-$BENCH_REPOSITORY}"
else
  : "${BENCH_PR:?BENCH_PR is required}"
  : "${BENCH_BASE_SHA:?BENCH_BASE_SHA is required}"
  : "${BENCH_SHA:?BENCH_SHA is required}"
  : "${BENCH_HEAD_REPO:?BENCH_HEAD_REPO is required}"
fi

ROOT="${BENCH_ROOT:-/var/lib/clean-bench}"
IMAGE="${BENCH_IMAGE:-clean-bench-runner:latest}"
RUN_DIR="$ROOT/runs/$BENCH_RUN_ID"
CACHE_DIR="$ROOT/cache"
WORK_DIR="$RUN_DIR/work"
BASELINE_CACHE_DIR="$CACHE_DIR/baselines"
LOCK_DIR="$CACHE_DIR/locks"

cleanup() {
  rm -rf "$RUN_DIR" 2>/dev/null && return
  docker run --rm \
    --network none \
    --security-opt no-new-privileges \
    -v "$RUN_DIR:$RUN_DIR" \
    "$IMAGE" \
    rm -rf "$RUN_DIR" >/dev/null 2>&1 || true
}

trap cleanup EXIT

docker build -t "$IMAGE" -f scripts/bench/runner/Dockerfile scripts/bench/runner

prepare_runner_dirs() {
  local uid
  local gid
  uid="$(id -u)"
  gid="$(id -g)"

  mkdir -p "$BENCH_OUTPUT_DIR"
  docker run --rm \
    --network none \
    --security-opt no-new-privileges \
    -e HOST_UID="$uid" \
    -e HOST_GID="$gid" \
    -v "$ROOT:$ROOT" \
    "$IMAGE" \
    bash -lc '
      set -euo pipefail
      mkdir -p "$@"
      find "$1" -mindepth 1 -maxdepth 4 -type d -exec chown "$HOST_UID:$HOST_GID" {} +
      find "$4" -mindepth 1 -maxdepth 1 -type f -exec chown "$HOST_UID:$HOST_GID" {} +
      chown "$HOST_UID:$HOST_GID" "$@"
    ' bash \
      "$CACHE_DIR" \
      "$CACHE_DIR/elan" \
      "$BASELINE_CACHE_DIR" \
      "$LOCK_DIR" \
      "$RUN_DIR" \
      "$WORK_DIR" \
      "$CACHE_DIR/lake-packages" \
      "$CACHE_DIR/mathlib-cache" \
      "$CACHE_DIR/lake-build" \
      "$CACHE_DIR/pr-lake-build"
}

prepare_runner_dirs

prune_pr_build_caches() {
  local root="$CACHE_DIR/pr-lake-build"
  local max_age_days="${BENCH_PR_BUILD_CACHE_MAX_AGE_DAYS:-30}"

  case "$max_age_days" in
    '' | *[!0-9]*)
      echo "invalid BENCH_PR_BUILD_CACHE_MAX_AGE_DAYS: $max_age_days" >&2
      return 1
      ;;
  esac
  if [ "$max_age_days" -eq 0 ] || [ ! -d "$root" ]; then
    return 0
  fi

  find "$root" -mindepth 3 -maxdepth 3 -type d -mtime +"$max_age_days" -prune -exec rm -rf {} + || true
  find "$root" -mindepth 1 -type d -empty -delete || true
}

run_benchmark() {
  local label="$1"
  local repo="$2"
  local sha="$3"
  local checkout="$WORK_DIR/$label/clean"
  local elan_home="$RUN_DIR/elan-home/$label"
  local xdg_cache="$RUN_DIR/xdg-cache/$label"

  mkdir -p "$elan_home" "$xdg_cache"
  git clone --filter=blob:none "https://github.com/$repo.git" "$checkout"
  git -C "$checkout" fetch --no-tags "https://github.com/$repo.git" "$sha"
  git -C "$checkout" checkout --detach "$sha"
  rm -rf "$checkout/scripts/bench"
  mkdir -p "$checkout/scripts"
  cp -a scripts/bench "$checkout/scripts/bench"

  local toolchain
  toolchain="$(sed -n '1p' "$checkout/lean-toolchain")"
  local package_cache_key
  package_cache_key="$(
    {
      printf '%s\n' "$toolchain"
      sha256sum "$checkout/lake-manifest.json" | cut -d' ' -f1
    } | sha256sum | cut -d' ' -f1
  )"
  local package_cache="$CACHE_DIR/lake-packages/$package_cache_key"
  local mathlib_cache="$CACHE_DIR/mathlib-cache/$package_cache_key"
  local lock_file="$LOCK_DIR/$package_cache_key.lock"
  local build_mount=()
  if [ "$label" = "baseline" ] && [ "$repo" = "$BENCH_REPOSITORY" ]; then
    local build_cache="$CACHE_DIR/lake-build/$package_cache_key"
    mkdir -p "$build_cache"
    build_mount=(-v "$build_cache:/workspace/clean/.lake/build")
  elif [ "$label" = "current" ]; then
    local head_repo_key="${BENCH_HEAD_REPO//[^A-Za-z0-9_.-]/__}"
    local build_cache="$CACHE_DIR/pr-lake-build/$head_repo_key/$BENCH_PR/$package_cache_key"
    mkdir -p "$build_cache"
    build_mount=(-v "$build_cache:/workspace/clean/.lake/build")
  fi
  mkdir -p "$checkout/.lake" "$package_cache" "$mathlib_cache"

  docker run --rm \
    --network bridge \
    -e ELAN_HOME=/bench-cache/elan \
    -v "$CACHE_DIR/elan:/bench-cache/elan" \
    "$IMAGE" \
    bash -lc 'elan toolchain install "$1" || elan toolchain list | grep -Fxq "$1"' bash "$toolchain"

  flock "$lock_file" docker run --rm \
    --security-opt no-new-privileges \
    --network bridge \
    -e XDG_CACHE_HOME=/workspace/xdg-cache \
    -e ELAN_HOME=/workspace/elan-home \
    -e MATHLIB_CACHE_DIR=/workspace/mathlib-cache \
    -e BENCH_OUTPUT_FILE="/bench-output/$label.jsonl" \
    -v "$checkout:/workspace/clean" \
    -v "$package_cache:/workspace/clean/.lake/packages" \
    -v "$mathlib_cache:/workspace/mathlib-cache" \
    "${build_mount[@]}" \
    -v "$elan_home:/workspace/elan-home" \
    -v "$CACHE_DIR/elan/toolchains:/workspace/elan-home/toolchains:ro" \
    -v "$xdg_cache:/workspace/xdg-cache" \
    -v "$BENCH_OUTPUT_DIR:/bench-output" \
    "$IMAGE" \
    bash -lc 'status=0; scripts/bench/build/run || status=$?; cp measurements.jsonl "$BENCH_OUTPUT_FILE" 2>/dev/null || true; exit "$status"'
}

baseline_cache_path() {
  local sha="$1"
  case "$sha" in
    *[!0-9a-fA-F]* | "")
      echo "invalid SHA for baseline cache: $sha" >&2
      return 1
      ;;
  esac
  printf '%s/%s.jsonl\n' "$BASELINE_CACHE_DIR" "$sha"
}

store_baseline_cache() {
  local sha="$1"
  local source="$2"
  local target
  target="$(baseline_cache_path "$sha")"
  cp "$source" "$target.tmp"
  mv "$target.tmp" "$target"
}

if [ "${BENCH_BASELINE_ONLY:-}" = "1" ]; then
  run_benchmark baseline "$BENCH_HEAD_REPO" "$BENCH_SHA"
  store_baseline_cache "$BENCH_SHA" "$BENCH_OUTPUT_DIR/baseline.jsonl"
  prune_pr_build_caches
  exit 0
fi

baseline_cache="$(baseline_cache_path "$BENCH_BASE_SHA")"
if [ -f "$baseline_cache" ]; then
  cp "$baseline_cache" "$BENCH_OUTPUT_DIR/baseline.jsonl"
else
  run_benchmark baseline "$BENCH_REPOSITORY" "$BENCH_BASE_SHA"
  store_baseline_cache "$BENCH_BASE_SHA" "$BENCH_OUTPUT_DIR/baseline.jsonl"
fi
run_benchmark current "$BENCH_HEAD_REPO" "$BENCH_SHA"
prune_pr_build_caches
