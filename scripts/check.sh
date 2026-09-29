#!/usr/bin/env bash
# CI acceptance checks for the Complexity library.
#   1. `lake build` completes with no errors and no `sorry` warnings.
#   2. No `sorry`/`admit`/`axiom`/`native_decide`/... token in any Lean source (outside comments).
#   3. Every ported top-level theorem depends only on propext, Classical.choice, Quot.sound
#      (`#print axioms` output is shown, and the check fails on anything else).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== 1. lake build"
lake build 2>&1 | tee build.log
if grep -Eq "declaration uses 'sorry'|^error:|: error:" build.log; then
  echo "build log contains errors or sorry warnings" >&2
  exit 1
fi

echo "== 2. forbidden-token scan"
python3 scripts/forbidden_tokens.py

echo "== 3. axiom check"
lake env lean scripts/AxiomCheck.lean 2>&1 | tee axioms.log
if grep -Eq "^error:|: error:|non-standard axioms" axioms.log; then
  echo "axiom check failed" >&2
  exit 1
fi
grep -q "statements checked: only propext, Classical.choice, Quot.sound are used" axioms.log
rm -f axioms.log
echo "== all checks passed"
