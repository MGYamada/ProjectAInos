#!/usr/bin/env bash
# Run every check file in this directory, in parallel, exactly as the required
# Lean build job does. Build the library first: `lake build --wfail ProjectAInos`.
#
#   checks/run.sh          # up to four processes
#   JOBS=2 checks/run.sh   # choose the parallelism
#
# Each `checks/*.lean` file is compiled with warnings as errors. `CoreImports`
# is a script and is run with `--run`. A new check file is picked up
# automatically. The exit status is nonzero if any check fails.
set -u

cd "$(dirname "$0")/.."

# Every process loads the whole library, so memory, not the CPU count, bounds
# the useful parallelism. Four fits the 16 GB of a standard CI runner.
cpus="$( (nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2) | head -n 1)"
jobs="${JOBS:-$(( cpus < 4 ? cpus : 4 ))}"
logs="$(mktemp -d)"
trap 'rm -rf "$logs"' EXIT

run_one() {
  local file="$1" name start status
  name="$(basename "$file" .lean)"
  start="$(date +%s)"
  if [ "$name" = CoreImports ]; then
    lake env lean -DwarningAsError=true --run "$file" > "$logs/$name.log" 2>&1
  else
    lake env lean -DwarningAsError=true "$file" > "$logs/$name.log" 2>&1
  fi
  status=$?
  echo "$status $(( $(date +%s) - start ))" > "$logs/$name.status"
}
export -f run_one
export logs

printf '%s\0' checks/*.lean | xargs -0 -n 1 -P "$jobs" bash -c 'run_one "$1"' _

failed=()
for file in checks/*.lean; do
  name="$(basename "$file" .lean)"
  status=1
  seconds="?"
  if [ -r "$logs/$name.status" ]; then
    read -r status seconds < "$logs/$name.status"
  fi
  if [ "$status" -eq 0 ]; then
    verdict=PASS
  else
    verdict=FAIL
    failed+=("$name")
  fi
  if [ -n "${GITHUB_ACTIONS:-}" ]; then
    # Collapse each log in the workflow view; failures get an annotation.
    echo "::group::$verdict $name (${seconds}s)"
    cat "$logs/$name.log" 2>/dev/null
    echo "::endgroup::"
    if [ "$verdict" = FAIL ]; then
      echo "::error file=$file::$name failed"
    fi
  else
    echo "$verdict $name (${seconds}s)"
    if [ "$verdict" = FAIL ]; then
      cat "$logs/$name.log" 2>/dev/null
    fi
  fi
done

if [ "${#failed[@]}" -ne 0 ]; then
  echo "Failed checks: ${failed[*]}"
  exit 1
fi
echo "All $(ls checks/*.lean | wc -l | tr -d ' ') checks passed."
