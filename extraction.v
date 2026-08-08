(*
  extraction.v -- Extract a verified OCaml interpreter for R-CORE from
  the formalization in proofs.v.

  Why this file exists.  [eval_cmd_correct] and [step_fun_correct] are
  statements inside the Rocq kernel; on their own they produce nothing a
  reader can run.  Extraction turns them into an executable whose
  correctness is the theorem rather than a test suite:

    eval_cmd_correct : (exists fuel, eval_cmd_fuel fuel c s = Some s')
                         <-> exec_ds c s s'
    step_fun_correct : step_fun cc s = Some cfg' <-> exec_ss (cc, s) cfg'

  so the big-step evaluator agrees with the denotational semantics and
  the single stepper agrees with the small-step semantics, and by
  [semantic_equivalence_p] the two agree with each other.  What is
  extracted is the same code the theorems are about, not a reimplementation.

  [step_fun] and [steps_n] are what make this a SMALL-STEP interpreter:
  a run can be advanced one transition at a time, which is what a
  reversible debugger needs, and [inv]/[cc_inv] give the reverse
  direction ([inv_step_reverses]).

  Build with:
    rocq c -Q . RCore extraction.v      (* produces rcore_interp.ml + .mli *)
  or
    make extract
*)

From RCore Require Import proofs.
From Stdlib Require Import Extraction.

(* Use native OCaml types where possible to make the output idiomatic. *)
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extraction Language OCaml.

Extract Inductive bool    => "bool"   [ "true" "false" ].
Extract Inductive option  => "option" [ "Some" "None" ].
Extract Inductive sumbool => "bool"   [ "true" "false" ].

(* The big-step evaluator, the small-step stepper and its iteration, the
   syntactic inverter on programs and on token positions, and the two
   well-formedness decision procedures that discharge the side condition
   of backward determinism. *)
Extraction "rcore_interp.ml"
  eval_cmd_fuel
  step_fun steps_n
  inv cc_inv
  wf_cmd_dec wf_cc_dec.
