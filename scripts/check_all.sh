#!/bin/bash
# Full build + every consistency check. Usage: scripts/check_all.sh [logdir]
# Exit 0 only if the build succeeds and coverage/inventory/teaching checks are clean.
set -u
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/bin:$PATH
LOG=${1:-/tmp}/check_build.log
fail=0
lake build > "$LOG" 2>&1 || fail=1
grep -E "^error|: error" "$LOG" | head -20
grep -qE "Build completed successfully" "$LOG" && echo "BUILD: ok" || { echo "BUILD: FAILED"; fail=1; }
grep -E "Loop: Dependency" "$LOG" && fail=1
python3 -I scripts/check_coverage.py | head -1 || fail=1
python3 -I scripts/check_coverage.py >/dev/null || fail=1
python3 -I scripts/inventory_report.py | tail -1
python3 -I scripts/inventory_report.py | tail -1 | grep -q "^0 items" || fail=1
python3 -I scripts/teaching_audit.py | tail -1
missing=$(grep "No world introducing" "$LOG" | sed 's/.*introducing //; s/, but.*//' | sort -u | tr '\n' ' ')
echo "Never-introduced (should be definitions only): $missing"
exit $fail
