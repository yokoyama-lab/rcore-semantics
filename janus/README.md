# janus/ — control-token semantics for a Janus core

A control-token small-step semantics (`jstep Γ`) for a Janus core — `skip`, `+= -= ^=`,
sequence, `if–fi`, `from–do–loop–until`, `call`/`uncall` with call-by-reference parameters
against a procedure environment — extending the R-CORE semantics of `../proofs.v` to the fragment
of Lanese–Vidal (RC 2026) without arrays, `local`/`delocal`, `/` and `%`, plus parameters (which
Lanese–Vidal do not treat). Self-contained: it does
not import `proofs.v`, but mirrors its proof architecture section by section.

## Build (from the repository root)

    make janus         # rocq c -Q . RCore janus/janus.v   (this is the proof)
    make janus-check   # kernel re-validation of RCore.janus.janus
    make janus-audit   # tools/audit.sh with SRC=janus/janus.v: no Admitted/Axiom, all Closed

## Files

- `janus.v` — syntax, `jstep Γ` (27 rules), `bstep`, `inv`/`cs_inv`, well-formedness with decision procedures, `step_fun`, all proofs (56 results, axiom-free, Rocq 9.1.1).
- `RULES.md` — the 27-rule table, the derivation of each rule from `exec_ss`, per-rule partial injectivity, the theorem table, exclusions and next steps.
- `LANESE_VIDAL.md` — construct-by-construct and result-by-result comparison with the PC-based semantics of Lanese and Vidal, and what still needs the paper's figures.

## Headline theorems

`jstep_deterministic` (forward determinism, no hypothesis); `wf_cs_step_preserved` / `wf_cs_step_reflected` (well-formedness invariant in both directions, needs `wf_penv Γ`); `jstep_bwd_deterministic`, `jstep_bwd_deterministic_tgt`, `bstep_deterministic` (backward determinism under `wf_cs`, no reachability hypothesis); `inv_step_reverses`, `inv_step_reverses_iff`, `bstep_is_fwd_of_inv` (the syntactic inverter reverses every step at the `cs_inv`-mirrored position); `nf_expr_dec`, `wf_stmt_dec`, `wf_cs_dec`; `step_fun_correct` (verified executable stepper); `j_example_run` (a 7-step run).
Parameters: `wf_inst` (an accepted call instantiates a well-formed body), `inst_no_params`
(conservative extension), `j_call_by_reference`, `j_uncall_undoes_call`,
`j_alias_actuals_stuck`, `j_alias_global_stuck`, `alias_breaks_wf`.

Excluded for now: arrays, `local`/`delocal`, `/` and `%`.

## Resume notes

Next steps, in priority order (details in `RULES.md` §7):

1. `local x = e … delocal x = e`: a second data-carrying rule pair; delocal is a value assertion.
   With parameters in place, locals are what makes procedures modular (a body can then have
   private variables instead of relying on globals).
2. Arrays (`x[e1] op= e2`): indexed store, well-formedness on both `e1` and `e2`.
3. `bstep_fun` (via `bstep_is_fwd_of_inv`) and extraction of `step_fun` into `../extraction.v`.
4. The R-CORE→Janus embedding as a formal theorem (`RULES.md` §4, §7 item 6).
5. A CFG/fss layer and a formal, rule-by-rule comparison with Lanese–Vidal once the paper's
   figures are available: only the `pdftotext` extraction in rc-survey was readable here, so
   `LANESE_VIDAL.md` §5 lists what still needs the paper (rule shapes, loop-label alignment).
6. A big-step semantics and its equivalence with `jstep`.
