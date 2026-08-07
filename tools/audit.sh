#!/bin/sh
# Mechanically enforce the axiom-freeness claim.
#
# `Print Assumptions` does NOT fail a build when a result depends on an
# axiom: it just prints a different line.  Nor does the build notice when
# a new result is added and nobody adds it to the audit block.  This
# script closes both gaps, so "the development is axiom-free" is checked
# by CI rather than promised by a human.
#
# Usage: tools/audit.sh            (from the repository root)
#
# Checks:
#   1. no Admitted / Axiom / Parameter / Conjecture in proofs.v
#   2. every top-level Theorem/Lemma/Corollary/Example is audited
#   3. the build prints nothing but "Closed under the global context"

set -eu

SRC=proofs.v
ROCQ=${ROCQ:-rocq}
status=0

echo "== 1. no admitted results, axioms or parameters =="
if grep -nE '^[[:space:]]*(Admitted|Axiom|Parameter|Conjecture)\b' "$SRC"; then
  echo "FAIL: the lines above introduce an assumption." >&2
  status=1
else
  echo "ok"
fi

echo "== 2. audit block covers every top-level result =="
declared=$(mktemp); audited=$(mktemp); missing=$(mktemp)
trap 'rm -f "$declared" "$audited" "$missing"' EXIT

grep -oE '^(Theorem|Lemma|Corollary|Example)[[:space:]]+[A-Za-z_][A-Za-z0-9_'"'"']*' "$SRC" \
  | awk '{print $2}' | sort -u > "$declared"
grep -oE '^Print Assumptions[[:space:]]+[A-Za-z_][A-Za-z0-9_'"'"']*' "$SRC" \
  | awk '{print $3}' | sort -u > "$audited"
comm -23 "$declared" "$audited" > "$missing"

if [ -s "$missing" ]; then
  echo "FAIL: declared but never passed to Print Assumptions:" >&2
  sed 's/^/  /' "$missing" >&2
  status=1
else
  echo "ok ($(wc -l < "$declared" | tr -d ' ') results, all audited)"
fi

echo "== 3. every audited result is closed under the global context =="
out=$(mktemp); trap 'rm -f "$declared" "$audited" "$missing" "$out"' EXIT
rm -f proofs.vo
$ROCQ c -Q . RCore "$SRC" 2>/dev/null > "$out"
# Every line of stdout comes from Print Assumptions.  Any line other than
# the closed-world verdict means something depends on an assumption.
if [ ! -s "$out" ]; then
  echo "FAIL: the build printed no assumption verdicts at all." >&2
  status=1
elif sort -u "$out" | grep -qvx 'Closed under the global context'; then
  echo "FAIL: unexpected assumption verdicts:" >&2
  sort -u "$out" | grep -vx 'Closed under the global context' | sed 's/^/  /' >&2
  status=1
else
  echo "ok ($(wc -l < "$out" | tr -d ' ') verdicts, all closed)"
fi

[ "$status" -eq 0 ] && echo "AUDIT PASSED" || echo "AUDIT FAILED" >&2
exit "$status"
