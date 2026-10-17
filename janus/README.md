# janus/ — control-token semantics for a Janus core

A control-token small-step semantics (`jstep Γ`) for a Janus core — `skip`, `+= -= ^=`,
sequence, `if–fi`, `from–do–loop–until`, `call`/`uncall` with call-by-reference parameters
against a procedure environment — extending the R-CORE semantics of `../proofs.v` to the fragment
of Lanese–Vidal (RC 2026) with arrays and their whole operator set (`/` and `%` included,
with partial expression evaluation), plus parameters and
`local`/`delocal` blocks (which Lanese–Vidal do not treat). Self-contained: it does
not import `proofs.v`, but mirrors its proof architecture section by section.

## Build (from the repository root)

    make janus         # rocq c -Q . RCore janus/janus.v   (this is the proof)
    make janus-check   # kernel re-validation of RCore.janus.janus
    make janus-audit   # tools/audit.sh with SRC=janus/janus.v: no Admitted/Axiom, all Closed
    make janus-mutants # tools/janus-mutants.py: 12 one-point mutants, each must fail in the expected proof

## Files

- `janus.v` — syntax, `jstep Γ` (31 rules), `bstep`, `inv`/`cs_inv`, well-formedness with decision procedures, `step_fun`, all proofs (110 results, axiom-free, Rocq 9.1.1). Every definition and theorem takes the store size (`nv` variables, `na` arrays of length `asize`) as implicit arguments; the examples fix 10, 4, 8 (and §15f 3, 1, 2).
- `RULES.md` — the 31-rule table, the derivation of each rule from `exec_ss`, per-rule partial injectivity, the theorem table, exclusions and next steps.
- `lv.v` — the program-counter semantics of Lanese–Vidal (forward and backward rules, as printed and repaired), the map `phi` from token positions to their configurations, `lv_fwd_sim` / `lv_bwd_sim` / `lv_run` / `exec_lv` (every token step is zero or one step of their machine, forwards and backwards), and three errata of the published rules as examples (49 results, axiom-free; `make janus-lv janus-lv-check janus-lv-audit`).
- `LANESE_VIDAL.md` — construct-by-construct and result-by-result comparison with the PC-based semantics of Lanese and Vidal, and what still needs the paper's figures.

## Headline theorems

`jstep_deterministic` (forward determinism, no hypothesis); `wf_cs_step_preserved` / `wf_cs_step_reflected` (well-formedness invariant in both directions, needs `wf_penv Γ`); `jstep_bwd_deterministic`, `jstep_bwd_deterministic_tgt`, `bstep_deterministic` (backward determinism under `wf_cs`, no reachability hypothesis); `inv_step_reverses`, `inv_step_reverses_iff`, `bstep_is_fwd_of_inv` (the syntactic inverter reverses every step at the `cs_inv`-mirrored position); `nf_expr_dec`, `wf_stmt_dec`, `wf_cs_dec`; `step_fun_correct` (verified executable stepper); `j_example_run` (a 7-step run).
Parameters: `wf_inst` (an accepted call instantiates a well-formed body), `inst_no_params`
(conservative extension), `j_call_by_reference`, `j_uncall_undoes_call`,
`j_alias_actuals_stuck`, `j_alias_global_stuck`, `alias_breaks_wf`.

Locals: `local_enter_injective`, `local_exit_injective`, `j_local_shadows`, `j_local_inverse`,
`j_delocal_mismatch_stuck`, `local_bwd_needs_nf` (why `x ∉ e2` is required).

Arrays: `aasn_step_injective`, `j_array_run`, `j_array_inverse`, `j_array_out_of_bounds_stuck`,
`aasn_bwd_needs_anf` (why `a ∉ e2` is required).

Big-step: `exec_iff_jstar` (the natural big-step semantics `exec` is exactly the runs of
`jstep` from entry to exit), and as corollaries `exec_deterministic` and `exec_inv` /
`exec_inv_iff` (the program inverter is correct for `exec`, derived from step-level
reversibility).

Partial evaluation (2026-10-18): `eval : store -> expr -> option Z`. Division and remainder by
zero and out-of-bounds reads have no value, and a rule that needs that value does not apply
(the configuration is stuck): `j_div_by_zero_stuck`, `j_oob_read_stuck`, `j_until_error_stuck`,
`j_delocal_error_stuck`, via `stuck_of_step_fun_none`. Evaluation is strict (`j_strict_and_stuck`;
jana short-circuits `&&`), `/` and `%` round towards minus infinity as in jana (`j_div_run`),
and the inverse program undoes division (`j_divmod_inverse`). No theorem statement changed:
the expression read by a step is unaffected by the step's own update (`x ∉ e`, `a ∉ e`), so
partiality never reaches the backward direction (`RULES.md` §1).

## Resume notes

Next steps, in priority order (details in `RULES.md` §7):

1. ~~Partial `eval` (`/`, `%`, out-of-bounds reads as errors)~~ — done 2026-10-18.
1a. ~~Arbitrary number of variables and arrays, arbitrary array length~~ — done 2026-10-18.
2. Refine `call_ok` to ignore variables bound by an enclosing `local` in the body (currently a
   body-local name counts as a global, which is conservative: it rejects some harmless calls).
3. `bstep_fun` (via `bstep_is_fwd_of_inv`) and extraction of `step_fun` into `../extraction.v`.
4. The R-CORE→Janus embedding as a formal theorem (`RULES.md` §4, §7 item 6).
5. ~~Formal comparison with Lanese–Vidal~~ — started 2026-10-18 in `lv.v` (see
   `LANESE_VIDAL.md` §6); the converse direction (every step of the repaired machine is matched)
   is open. Earlier note: only the `pdftotext` extraction in rc-survey was readable here, so
   `LANESE_VIDAL.md` §5 lists what still needs the paper (rule shapes, loop-label alignment).
6. ~~A big-step semantics and its equivalence with `jstep`~~ — done (`exec_iff_jstar`).
