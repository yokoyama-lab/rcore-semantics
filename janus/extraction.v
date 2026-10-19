(*
  janus/extraction.v -- Extract a verified small-step interpreter for the
  Janus core of janus.v, forwards and backwards.

  step_fun_correct  : step_fun Γ cs s = Some (cs', s') <-> jstep Γ (cs, s) (cs', s')
  bstep_fun_correct : wf_penv Γ -> wf_cs cs ->
                      (bstep_fun Γ cs s = Some (cs', s') <-> bstep Γ (cs, s) (cs', s'))

  so the extracted [step_fun] / [run] go forwards by the semantics and
  [bstep_fun] / [brun] go backwards by it: a reversible debugger whose
  correctness is the theorem.  The worked examples of janus.v are
  extracted too, so that janus/test_janus.ml can run them.

  Build with  make janus-extract  (produces janus/janus_interp.ml + .mli).
*)

From RCore.janus Require Import janus.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Extraction Language OCaml.

Extract Inductive bool    => "bool"   [ "true" "false" ].
Extract Inductive option  => "option" [ "Some" "None" ].
Extract Inductive sumbool => "bool"   [ "true" "false" ].

Extraction "janus/janus_interp.ml"
  step_fun run bstep_fun brun inv cs_inv wf_stmt_dec wf_cs_dec
  Γ0 Γ1 zero_store
  ex_divmod ex_divmod_pre ex_divmod_post
  ex_call ex_arr ex_local ex_local_pre ex_local_post
  ex_small small_zero ex_small_post Γs.
