#!/usr/bin/env bash

set -u

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
SOLVER=${SOLVER:-"$SCRIPT_DIR/proj1.py"}
TEST_DIR=${TEST_DIR:-"$SCRIPT_DIR/public-tests"}

passed=0
failed=0
tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT

# CHANGED: Format the output of the 'time' command to only show elapsed seconds (e.g., 0.123)
TIMEFORMAT='%R'

while IFS= read -r input; do
    name=$(basename "$input" .drn)
    expected="$TEST_DIR/$name.out"
    actual="$tmp_dir/$name.out"
    error="$tmp_dir/$name.err"

    if [[ ! -f "$expected" ]]; then
        printf 'FAIL %s (missing expected output)\n' "$name"
        ((failed += 1))
        continue
    fi

    expected_cost=$(awk 'NR == 1 { print $1 }' "$expected")
    
    if exec_time=$( { time python3 "$SOLVER" < "$input" > "$actual" 2> "$error"; } 2>&1 ) \
        && [[ $(awk 'NR == 1 { print $1 }' "$actual") == "$expected_cost" ]] \
        && python3 "$SCRIPT_DIR/validate.py" "$input" --solution "$actual" > /dev/null; then
        
        printf 'PASS %s (%ss)\n' "$name" "$exec_time"
        ((passed += 1))
    else
        # CHANGED: Added time to FAIL output
        printf 'FAIL %s (%ss)\n' "$name" "$exec_time"
        if [[ -s "$error" ]]; then
            sed 's/^/  /' "$error"
        fi
        if [[ -f "$actual" ]]; then
            printf '  expected cost: %s; actual cost: %s\n' \
                "$expected_cost" "$(awk 'NR == 1 { print $1 }' "$actual")"
        fi
        ((failed += 1))
    fi
done < <(find "$TEST_DIR" -maxdepth 1 -name '*.drn' | sort -V)

printf '\nSummary: %d passed, %d failed\n' "$passed" "$failed"
((failed == 0))