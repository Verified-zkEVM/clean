#!/usr/bin/env bash

bench_repo_root() {
  cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd
}

module_path() {
  local module="$1"
  printf '%s.lean\n' "${module//.//}"
}

module_setup_path() {
  local module="$1"
  printf '.lake/build/ir/%s.setup.json\n' "${module//.//}"
}

fmt_int() {
  local value="$1"
  awk -v value="$value" '
    function fmt(n,    s, out) {
      s = sprintf("%.0f", n)
      out = ""
      while (length(s) > 3) {
        out = "," substr(s, length(s) - 2) out
        s = substr(s, 1, length(s) - 3)
      }
      return s out
    }
    BEGIN { print fmt(value) }
  '
}

fmt_signed_int() {
  local value="$1"
  if [ "$value" -lt 0 ]; then
    printf -- '-%s\n' "$(fmt_int "$((-value))")"
  else
    printf -- '+%s\n' "$(fmt_int "$value")"
  fi
}

measure_heartbeats() {
  local repo="$1"
  local module="$2"
  local heartbeat_check="$3"
  local setup="${4:-}"
  local path
  path="$(module_path "$module")"

  if [ ! -f "$repo/$path" ]; then
    echo "module file not found: $repo/$path" >&2
    return 1
  fi

  local output
  local args=("$path")
  if [ -n "$setup" ]; then
    # a setup file records absolute artifact paths; if any point outside this repo
    # (e.g. a sibling git worktree), the measurement would silently load a different
    # branch's library — refuse instead of reporting a number for the wrong code
    local foreign
    foreign="$(grep -oE '"/[^"]*/\.lake/' "$repo/$setup" | sed 's/^"//; s|/\.lake/$||' | sort -u |
      awk -v repo="$repo" '!($0 == repo || index($0, repo "/.lake/") == 1)')"
    if [ -n "$foreign" ]; then
      echo "stale setup file: $repo/$setup references artifacts outside $repo:" >&2
      printf '  %s\n' $foreign >&2
      echo "rebuild the module in this worktree (lake build $module) and retry" >&2
      return 1
    fi
    args+=("--setup" "$setup")
  fi
  if ! output="$(cd "$repo" && lake env lean --run "$heartbeat_check" "${args[@]}" 2>&1)"; then
    printf '%s\n' "$output" >&2
    return 1
  fi

  local value
  value="$(awk -v module="$module" '$1 == "HEARTBEATS" && $2 == module { print $3 }' <<<"$output")"
  if [ -z "$value" ]; then
    printf '%s\n' "$output" >&2
    echo "heartbeat frontend did not report heartbeats for $module" >&2
    return 1
  fi
  printf '%s\n' "$value"
}
