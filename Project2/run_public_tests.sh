#!/usr/bin/env bash

set -u

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
SOLVER=${SOLVER:-"$SCRIPT_DIR/proj2.py"}
TEST_DIR=${TEST_DIR:-"$SCRIPT_DIR/public_tests"}
CSV_OUT=${CSV_OUT:-"$SCRIPT_DIR/time_bool.csv"}
TEST_TIMEOUT=${TEST_TIMEOUT:-600}  # Seconds: 10 minutes per solver execution.

if ! command -v timeout > /dev/null 2>&1; then
    printf 'Erro: o comando timeout (GNU coreutils) não está instalado.\n' >&2
    exit 1
fi

passed=0
failed=0
tmp_dir=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp_dir"' EXIT
results="$tmp_dir/results.tsv"
: > "$results"

TIMEFORMAT='%R'

while IFS= read -r input; do
    name=$(basename "$input" .drn)
    expected="$TEST_DIR/$name.out"
    actual="$tmp_dir/$name.out"
    error="$tmp_dir/$name.err"
    timing="$tmp_dir/$name.time"

    if [[ ! -f "$expected" ]]; then
        printf 'FAIL %s (missing expected output)\n' "$name"
        printf '%s\tFAIL\t\n' "$name" >> "$results"
        ((failed += 1))
        continue
    fi

    expected_cost=$(awk 'NR == 1 { print $1 }' "$expected")

    # Stop at the time limit; force termination after 1 second if needed.
    # Keep the elapsed time separate from error messages.
    if { time timeout --kill-after=1s "${TEST_TIMEOUT}s" python3 "$SOLVER" < "$input" > "$actual" 2> "$error"; } 2> "$timing"; then
        solver_status=0
    else
        solver_status=$?
    fi
    exec_time=$(tail -n 1 "$timing")

    if ((solver_status == 0)) \
        && [[ $(awk 'NR == 1 { print $1 }' "$actual") == "$expected_cost" ]] \
        && python3 "$SCRIPT_DIR/validateP2.py" "$input" --solution "$actual" > /dev/null; then

        printf 'PASS %s (%ss)\n' "$name" "$exec_time"
        printf '%s\tPASS\t%s\n' "$name" "$exec_time" >> "$results"
        ((passed += 1))
    else
        if ((solver_status == 124)); then
            status="TIMEOUT"
            printf 'TIMEOUT %s (%ss)\n' "$name" "$exec_time"
        else
            status="FAIL"
            printf 'FAIL %s (%ss)\n' "$name" "$exec_time"
        fi
        printf '%s\t%s\t%s\n' "$name" "$status" "$exec_time" >> "$results"
        if [[ -s "$error" ]]; then
            sed 's/^/  /' "$error"
        fi
        if [[ -f "$actual" ]]; then
            printf '  expected cost: %s; actual cost: %s\n' \
                "$expected_cost" "$(awk 'NR == 1 { print $1 }' "$actual")"
        fi
        ((failed += 1))
    fi
done < <(find "$TEST_DIR" -maxdepth 1 -type f -name '*.drn' | sort -V)

printf '\nSummary: %d passed, %d failed\n' "$passed" "$failed"

# Export all results to CSV, normalizing decimal commas in elapsed times.
if python3 - "$results" "$CSV_OUT" <<'PYCSV'
import csv
import math
import sys
from pathlib import Path

input_file, output_file = map(Path, sys.argv[1:])
output_file.parent.mkdir(parents=True, exist_ok=True)
with input_file.open(encoding="utf-8", newline="") as source, \
        output_file.open("w", encoding="utf-8-sig", newline="") as destination:
    writer = csv.writer(destination)
    writer.writerow(["Teste", "Resultado", "Tempo (s)"])
    for name, status, elapsed in csv.reader(source, delimiter="\t"):
        seconds = float(elapsed.replace(",", ".")) if elapsed.strip() else None
        if seconds is not None and not math.isfinite(seconds):
            raise ValueError(f"Invalid elapsed time for {name}: {elapsed}")
        writer.writerow([name, status, f"{seconds:.3f}" if seconds is not None else ""])

print(f"CSV criado: {output_file}")
PYCSV
then
    :
else
    printf 'Erro ao criar o CSV.\n' >&2
    exit 1
fi

((failed == 0))
