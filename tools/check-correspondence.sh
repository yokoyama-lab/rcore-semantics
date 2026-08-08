#!/bin/sh
# Keep correspondence.tsv complete against proofs.v.
#
# See the header of correspondence.tsv for why.  In short: the diff between
# a paper's printed rules and the rules actually mechanized is the place
# where defects hide, and nothing computes that diff unless something
# insists.  This is that something.
#
# Checks:
#   1. every constructor of the mechanized semantics has exactly one row
#      (adding or renaming a rule without recording what it does to the
#      correspondence fails the build)
#   2. every row names a constructor that really exists
#   3. the divergences are listed, so the companion paper's "departures
#      from the printed rules" section can be checked against them
#
# Usage: tools/check-correspondence.sh

set -eu

cd "$(dirname "$0")"/..
SRC=proofs.v
TAB=correspondence.tsv
status=0
# printf, not echo: dash's echo eats backslash escapes.
fail() { printf 'FAIL: %s\n' "$*" >&2; status=1; }

[ -f "$TAB" ] || { echo "no $TAB" >&2; exit 1; }

# The relations that model the paper's three semantics.  A relation added
# here starts failing until its constructors are documented.
RELS='exec_ss exec_ds loop_sem fstep'

decl=$(mktemp); rows=$(mktemp); listed=$(mktemp)
trap 'rm -f "$decl" "$rows" "$listed"' EXIT

for r in $RELS; do
  awk -v r="$r" '
    $0 ~ "^(Inductive|with) " r " " { on=1; next }
    on && /^Inductive |^with / { on=0 }
    on && /^ *\| *[A-Za-z_]/ { gsub(/^ *\| */,""); split($0,a,/[ :]/); print a[1] }
  ' "$SRC"
done | sort -u > "$decl"

grep -v '^#' "$TAB" | grep -v '^[[:space:]]*$' > "$rows"
cut -f3 "$rows" | sed 's/^ *//;s/ *$//' | sort > "$listed"

echo "== 1. every mechanized rule has exactly one row =="
while read -r c; do
  [ -n "$c" ] || continue
  n=$(grep -c -x -- "$c" "$listed" || true)
  case "$n" in
    1) ;;
    0) fail "rule '$c' is mechanized but has no row in $TAB" ;;
    *) fail "rule '$c' has $n rows in $TAB; expected 1" ;;
  esac
done < "$decl"
[ "$status" -eq 0 ] && echo "ok ($(wc -l < "$decl" | tr -d ' ') rules over: $RELS)"

echo "== 2. every row names a real constructor =="
while read -r c; do
  [ -n "$c" ] || continue
  grep -q -x -- "$c" "$decl" || fail "$TAB names '$c', which is not a constructor of: $RELS"
done < "$listed"
[ "$status" -eq 0 ] && echo "ok ($(wc -l < "$listed" | tr -d ' ') rows)"

echo "== 3. divergences from the printed rules =="
awk -F'	' '$4 != "identical" { printf "  %-14s %-16s %s\n", $4, $3, $1 }' "$rows"
printf '  %s\n' "(the companion letter must disclose every line above)"

[ "$status" -eq 0 ] && echo "CORRESPONDENCE PASSED" || echo "CORRESPONDENCE FAILED" >&2
exit "$status"
