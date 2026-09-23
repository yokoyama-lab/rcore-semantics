#!/bin/sh
# Run the gap witnesses through the two 2015/2016 R-CORE interpreters.
#
#   usage: difftest/run_witnesses.sh <rcore-haskell binary> <ri binary>
#
# The witness programs are in difftest/witnesses/ and are accepted verbatim
# by both dialects (variables X0..X9, flat expressions, values over nil).
# Each line prints the interpreter's stdout+stderr verbatim, followed by its
# exit code, so the table in docs/gap-witness-table.md can be re-derived.
# The OCaml interpreter's -inverse flag is used to print the inverse program
# beside the hand-inverted *_inv.rcore files; rcore-haskell exposes no
# inverter on its command line (src/Main.hs), so the *_inv.rcore files are
# run as ordinary forward programs on both.

HS=${1:?rcore-haskell binary}
ML=${2:?ri binary}
W=$(cd "$(dirname "$0")/witnesses" && pwd)

run1() { # label binary prog val
  out=$("$2" "$W/$3" "$W/$4" 2>&1); rc=$?
  printf '  %-14s %s [exit %d]\n' "$1" "$(printf '%s' "$out" | tr '\n' ' ')" "$rc"
}

run() { # name prog val
  printf '== %s: %s, input %s\n' "$1" "$2" "$(cat "$W/$3")"
  run1 rcore-haskell "$HS" "$2" "$3"
  run1 rcore-C-ocaml "$ML" "$2" "$3"
}

run gapwitness1     gapwitness1.rcore    nil.val
run gapwitness2     gapwitness2.rcore    nil.val
run gapwitness2_inv gapwitness2_inv.rcore t.val
run oddloop         oddloop.rcore        nil.val
run oddloop_inv     oddloop_inv.rcore    oddval.val
run loop_t          loop_t.rcore         nil.val
run selfassign      selfassign.rcore     nil.val
run selfassign_inv  selfassign_inv.rcore nil.val
run mismatchclear   mismatchclear.rcore  nil.val
run reverse_atoms_hs reverse_hs.rcore    list123_atom.val
run reverse_atoms_ml reverse_ml.rcore    list_abc.val
run reverse_niltrees reverse_hs.rcore    list_niltrees.val

printf '\n== inverse programs as printed by "%s -inverse"\n' "$ML"
for p in gapwitness2 oddloop selfassign; do
  printf -- '-- %s.rcore:\n' "$p"; "$ML" -inverse "$W/$p.rcore"; echo
done
