# The gap witnesses on two older R-CORE interpreters

Supplement to the IEICE letter.  The witnesses of `proofs.v` Sect. 41A/41B
(the assignment gap, the loop guards) and Sect. 41B''' (the store `E` is
read in) were run through two independent R-CORE interpreters written
before the RC 2026 semantics: `rcore-haskell` (T. Yokoyama, 2015,
`src/RCore/Eval.hs`) and `rcore-C-ocaml` (2016, `web/src/EvalRcore.ml`),
and through the interpreter extracted from `proofs.v`.  Programs, inputs,
build recipe and runner: `difftest/`.  Stores list non-nil variables only;
`t` is `(nil.nil)`.  Line numbers refer to `proofs.v` unless prefixed.

| witness (initial store) | printed rules, transcribed: `ds_paper` / `ss_paper` | repaired: `exec_ds` / `exec_ss` | rcore-haskell 2015 | rcore-C-ocaml 2016 | extracted `step_fun` |
|---|---|---|---|---|---|
| **W1** `X0 ^= nil` at `nil_store` (`gap_witness`, l.3762) | ds defined, store unchanged (`gap_witness_paper_ds` l.4124) / ss **STUCK**: neither AsnSet nor AsnClear fires (l.3779, l.3916) | unchanged (`gap_witness_ds` l.3765, `gap_witness_ss` l.3771) | `nil` (exit 0) -- `Nil -> update x v'`, Eval.hs:53-54 | `nil` (exit 0) -- `vy = VNil -> (y, vx)`, EvalRcore.ml:28-29 | `Some (post, nil_store)` (`step_fun_on_gap_witness` l.4801) |
| **W2** `X0 ^= =? X1 X2` at `neq_store` = {X2=t} (`gap_witness2`, l.3786) | ds defined, unchanged (l.4131) / ss **STUCK** (l.3797, l.3924) | unchanged (`gap_witness2_ds` l.3791) | `(nil.nil)` = X2, exit 0 | `(nil . nil)`, exit 0 | `Some (post, neq_store)`: `eval_expr` = `Some Vnil`, `odot Vnil Vnil` = `Some Vnil` (l.4517-4520, hand-evaluated) |
| **W3** `from X0 loop X5 ^= nil until X1` at `odd_store` = {X0=((nil.nil).nil), X1=t} (l.3851, reached by l.3860) | ds **UNDEFINED**: `PD_Loop` needs `X0 = t` (l.4077, `ds_paper_loop_guard_is_stricter` l.4159) / ss **STUCK** at entry (`loop_gap_paper_stuck` l.3873) | enter (`loop_gap_ss` l.3867), exit at once (`S_LoopExit`, X1 <> nil): unchanged, output `((nil.nil).nil)` | `((nil.nil).nil)`, exit 0 -- guards test `/= Nil`, Eval.hs:66, 76 | **ERROR** `Fatal error: exception Failure("Assertion X0 is not true. ")`, exit 2 -- entry test `= vtrue`, EvalRcore.ml:91-93 | `Some (mid_loop, s)` then `Some (post, s)` (l.4524-4530, hand-evaluated) |
| **W3⁻¹** `from X1 loop X5 ^= nil until X0` at `odd_store` (`inv` of W3; whole inverse program `oddloop_inv.rcore`) | ds **UNDEFINED**, ss enters (X1 = t) then **STUCK** in mid-loop: exit needs `X0 = t`, iteration needs `X0 = nil` (l.3840-3845) | exit at once: unchanged; inverse program outputs `nil` | `nil`, exit 0 | **ERROR** `Assert_failure("EvalRcore.ml", 104, 4)`, exit 2 -- exit test `= vtrue` fails (l.97), body runs, then `assert (X1 = vfalse)` (l.104) | `Some (post, s)` (hand-evaluated) |
| control `loop_t`: W3 with X0 = t | ds/ss defined | `(nil.nil)` | `(nil.nil)` | `(nil . nil)` | terminal |
| **W4** `X0 ^= X0` at {X0=t} (not well-formed: `nf_expr_not_self` l.409, `wf_cc_dec_rejects` l.4380; constructed here from `eval_readings_differ_without_wf` l.4213) | paper's text (`E` read in `s`, X ∉ dom s): **UNDEFINED**; the transcriptions read the full store (l.4064, l.202) and clear X0 | X0 cleared: `nil` (`eval_readings_agree_on_wf` l.4207 does not apply) | **ERROR** `in lookupEnv: Variable X0 not found ... Eval.hs:13`, exit 1 -- `eval (ev \`minus\` x) e`, Eval.hs:52 | `nil`, exit 0 -- `evalExp s e` on the full store, EvalRcore.ml:86-87, cleared by l.30-31 | `Some (post, nil_store)`, `wf_cmd_dec` = false |
| **W4⁻¹** `selfassign_inv.rcore` from `nil` | (as above) | X0 ^= X0 at nil sets nil, not t: inverse program ends with X0 = t ≠ nil | **ERROR** `Variable X0 not found`, exit 1 | **ERROR** `Failure("Some variables are not nil.")`, exit 2 | `Some (post, nil_store)` |
| **W5** `X0 ^= nil` at {X0=t} (constructed here) | ds **UNDEFINED**: `d = t, e = nil` fails `d = nil ∨ (d = e ∧ d ≠ nil)` (l.4069) / ss **STUCK** (AsnSet needs `d = nil`, AsnClear needs `d = e`, l.3734-3745) | **UNDEFINED / STUCK**: `odot t nil = None` (l.214-218, `ss_asn_stuck_iff` l.4632) | `nil`, exit 0 -- **accepted**: `v' == Nil -> ev`, Eval.hs:62-63 | **ERROR** `Failure("error in update")`, exit 2 -- EvalRcore.ml:32 | `None` (stuck) |
| control `reverse.rcore` (both repos' example) on `('1.('2.('3.nil)))`, `('a.('b.('c.nil)))`, `(nil.((nil.nil).nil))` | n/a (atoms) | `[t, nil]` on the nil-tree list | `('3.('2.('1.nil)))`, parse error on the OCaml file's leading comment, `((nil.nil).(nil.nil))` | `('3 . ('2 . ('1 . nil)))`, `('c . ('b . ('a . nil)))`, `((nil . nil) . (nil . nil))` | `{X2=((nil.nil).(nil.nil))}` |

The `step_fun` column: W1 is the proved `Example`; the other cells are
what `difftest/witness_driver.ml` asserts and were executed against the
extracted code (`make witness-test`, Rocq 9.1.1 built from source, all
checks pass, transcript in `difftest/witness_driver.out`; CI runs the same
target after `make extract-test`).

**Interpretation.**  On the assignment gap (W1, W2) both older
interpreters take the side of the repaired rule: each implements the
reversible update as the single partial operator `d ⊙ e` (set when `d =
nil`, clear when `d = e`), which is `odot` (l.214) and `D_Asn` (l.772), and
neither reproduces the two printed small-step rules of Fig. 9b with their
`e ≠ nil` / `d ≠ nil` premises; the printed `ss` is the only one of the five
columns that is stuck there.  On the loop guards (W3, W3⁻¹) the two sit on
opposite sides: `rcore-haskell` tests `≠ nil` exactly as `S_LoopEnter` /
`S_LoopExit` do (l.230-235), `rcore-C-ocaml` tests `= t` exactly as
`P_LoopEnter` / `P_LoopExit` do (l.3837-3842) and fails on a value that is
neither `t` nor `nil`, forward at entry and backward at exit.  On the store
`E` is read in (W4) they again sit on opposite sides, the other way round:
`rcore-haskell` evaluates `E` in `s` minus `X`, the paper's `s + {X -> d}`,
and `rcore-C-ocaml` in the whole store, as `eval_expr` does; as
`eval_readings_agree_on_wf` (l.4207) predicts, the difference is invisible
on well-formed programs and appears only on the self-assignment that
`wf_cmd` excludes, where the full-store reading also loses reversibility
(W4⁻¹).  The two readings of the loop guard and of the store are therefore
independent choices, made in opposite combinations by the two
implementers, and neither of them is the assignment gap: that gap is a
defect of the printed `ss` rules alone, which no implementation followed.
W5 is not a semantic choice but a leniency of `rcore-haskell`: the branch
`v' == Nil -> ev` (Eval.hs:57-58, 62-63) accepts `X ^= E` when `E` is nil
and `X` is not, a case outside the printed side condition and outside
`odot`; it extends every assignment by the identity, so it stays
injective, but it silently accepts programs that the paper, the artifact
and `rcore-C-ocaml` reject.

**Threats.**  No dialect translation was needed: every witness is a
program over `X0..X9` with flat expressions and nil-only values that both
parsers accept byte-for-byte (`rcore-haskell` only rejects a comment
before `read`, and `ri` prints values with spaces), so the rows compare
the same text.  The value domain of `proofs.v` has no atoms, whereas both
interpreters do; the witnesses use none, and the `reverse.rcore` control
gives the same result on atom lists and on a nil-tree list.  `proofs.v`
has a total store of exactly ten variables, whereas both interpreters
build the store from the variables occurring in the program (Eval.hs:85,
EvalRcore.ml:109) and require all but the output to be `nil` at the end
(Eval.hs:87, EvalRcore.ml:114); `nil_store`, `neq_store` and `odd_store` are
therefore reached by reading `nil` into an unused variable and by the
well-formed assignments of `odd_store_reachable` (l.3860), and each witness
clears its scaffolding before `write`, so the outputs are those of whole
programs, not of the single command.  `rcore-C-ocaml` allows arbitrary
expressions as loop guards, so its W3⁻¹ failure surfaces as the body-side
`assert` (l.104) rather than as a stuck exit test.
