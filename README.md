# rcore-semantics

A Rocq (Coq Prover 9.1.1) mechanization of the small-step reversible
operational semantics of the minimalist reversible language **R-CORE**.

This is the artifact accompanying:

> Toya Makino and Tetsuo Yokoyama,
> *Small-Step Semantics with Meta-Level Reversibility for a Reversible
> Core Language*, Reversible Computation (RC 2026), Springer LNCS.
> DOI: [10.1007/978-3-032-30839-9_12](https://doi.org/10.1007/978-3-032-30839-9_12)

and its companion letter on the machine-checked determinism of the
semantics (IEICE, in preparation).

## Contents

The entire development is the single self-contained file **`proofs.v`**
(about 5,400 lines, no dependencies beyond the Rocq standard library).
It defines the R-CORE syntax and three semantics: the denotational
semantics (**ds**), rendered as an inductive relation, the token-based
small-step semantics (**ss**), and the flowchart-based finer-grained
small-step semantics (**fss**). Among the results proved:

| Result | Identifier |
|---|---|
| **Theorem 1 of the paper fails as printed.** `AsnSet_ss` requires `e ≠ nil` and `AsnClear_ss` requires `d ≠ nil`, so ss is stuck when the target and the value of the right-hand side are both `nil`, while `Asn_ds` is defined there and `AsnClear_fss` carries no such premise. `S_Asn` merges the two rules and closes the gap | `rc2026_theorem1_fails_as_printed_full` (whole printed relation), `rc2026_theorem1_fails_as_printed` (assignment rules alone), `ss_paper`, `ss_paper_asn`, `exec_ss_from_pre_asn_inv` |
| **The printed loop guards are stricter than ours.** They test equality with `t` and `f`; since the data domain is all binary trees over `nil`, a variable can hold a value that is neither, and there the printed rules are stuck. A two-line well-formed program reaches such a store | `rc2026_loop_guards_are_stricter`, `ss_paper_loop`, `odd_store_reachable` |
| **The structural congruence is not quotiented away but recovered.** Every member of a congruence class stays a distinct `cont_cmd`; the three equations of Eq. (7) are oriented as `S_Seq_Enter`/`S_Seq_Mid`/`S_Seq_Exit`, and the congruence is exactly their equivalence closure. It only moves the token, so it preserves the program and well-formedness | `cong_iff_admin`, `admin_step_is_ss`, `cc_cong_erase`, `cc_cong_preserves_wf` |
| Forward determinism of ss (Lemma 1, forward) | `ss_step_deterministic` / `rev_com_forward` |
| Backward determinism of ss, modulo well-formedness (Lemma 1, backward) | `ss_bwd_deterministic` / `rev_com_backward` |
| Backward determinism from a single well-formed target | `ss_bwd_deterministic_tgt` |
| Well-formedness is invariant under steps (both directions) | `wf_cc_step_preserved`, `wf_cc_step_reflected` |
| ... and along whole executions, so backward determinism needs only reachability from a well-formed program | `wf_cc_steps_preserved`, `ss_bwd_deterministic_reachable` |
| `wf_cmd` (hence well-formedness of a command) is decidable | `nf_expr_dec`, `wf_cmd_dec` |
| Backward determinism of a whole run: two runs of the same length into a common well-formed target coincide at the start, and (once they do) at every intermediate configuration | `ss_run_state_unique_bwd`, `ss_run_trace_unique_bwd` |
| Semantic equivalence ds ⇔ ss ⇔ fss for terminating runs (Theorem 1) | `semantic_equivalence`, `semantic_equivalence_p` |
| Theorem 1 at the program level: for `read X; C; write X`, the token traverses the flowchart from entry to exit | `prog_traversal`, `prog_traversal_data` |
| Verified syntactic program inverter | `inv_correct`, `inv_involutive` |
| The inverse is unique up to denotational (hence contextual) equality | `inv_unique`, `inv_unique_cxt` |
| **The printed rules are deterministic.** What Fig. 9b loses is coverage, not determinism: it is stuck where ds is defined, and nothing more. This is what makes the defect a gap rather than an ambiguity | `ss_paper_deterministic`, `ss_paper_asn_deterministic`, `ss_paper_loop_deterministic`, `ss_paper_at_post_stuck` |
| **The transition relation is executable.** `step_fun` decides it, so the semantics can be run rather than only reasoned about | `step_fun`, `step_fun_correct` |
| **Stuckness is decidable, and the repair is sufficient.** The amended assignment rule is stuck only when the expression or the update operator is undefined, never because of a premise about `nil`; and wherever ds denotes an assignment, ss makes exactly that step | `ss_stuck_iff_step_fun_none`, `ss_asn_stuck_iff`, `ss_asn_covers_ds` |
| **Iterating the stepper halts exactly when ds is defined**, and a run that never halts has no denotation. The converse is deliberately not claimed: separating stuck from divergent runs needs excluded middle | `steps_n`, `ss_halts_iff_ds_defined`, `ss_diverges_implies_ds_undefined`, `ds_defined_implies_not_diverges` |
| **The inverter, one step at a time.** A forward step of `C` is a forward step of `inv C` taken in the opposite direction. `inv_correct` says this denotationally; this is the small-step form, which is what "reversible at the meta level" actually asks for | `cc_inv`, `inv_step_reverses`, `cc_inv_involutive` |
| Well-formedness of a *controlled* command (what backward determinism hypothesizes) is decidable | `wf_cc_dec` |
| Which store the paper's `⊎` notation evaluates `E` in: the two readings agree exactly on well-formed assignments, and well-formedness is strictly stronger than they require (`=? X X` does not depend on `X`) | `eval_readings_agree_on_wf`, `eval_readings_differ_without_wf`, `eval_indep_not_implies_nf` |
| **The printed rules are a sub-relation of the amended ones.** Everything Fig. 9b does, `exec_ss` does. With the gap witnesses this is the exact statement of the defect: the printed relation is **sound but not complete**. Backward determinism for it is then inherited rather than reproved, so determinism of the printed rules holds in both directions, as the paper's Lemma 1 does | `ss_paper_included`, `ss_paper_bwd_deterministic`, `fstep_paper_asn_deterministic` |
| **The backward relation, which the paper defines but the development did not.** `←` = `→⁻¹`, deterministic on well-formed configurations (Theorem 2 in the form a reverse interpreter uses), and executable by stepping the inverted program forwards | `bstep`, `bstep_deterministic`, `bstep_fun`, `bstep_fun_correct` |
| **Inversion of a whole run, at no cost in steps.** Running `inv C` from where `C` stopped returns to where `C` started, in *exactly* the same number of steps | `inv_run_reverses`, `inv_program_run_reverses` |
| `inv` preserves well-formedness, on commands and on token positions | `wf_cmd_inv`, `wf_cc_cc_inv` |
| The paper's `P ::= read X; C; write X` on the command side (the flowchart side already had `flow_program`), with its store map injective | `prog`, `prog_denot`, `prog_inv`, `prog_denot_injective` |
| The paper's `f`, so the printed loop guards can be written in the paper's own vocabulary | `Vf`, `Vt_neq_Vf` |
| Inverse correctness at the ss and fss levels | `inv_correct_ss`, `inv_correct_fss` (and `_iff`) |
| `c ; inv c` and `inv c ; c` behave as the identity, on the domain and range of `c` respectively | `inv_compose_id`, `inv_compose_id_sym` |
| Full abstraction | `full_abstraction` |
| Uniqueness of terminating runs | `ss_run_unique` |
| The run itself, not just its final store, is determined: the configuration after *n* steps is unique, a shorter run is a prefix of a longer one, and two maximal runs agree in length and in endpoint | `ss_run_state_unique`, `ss_run_prefix`, `ss_run_trace_unique` |
| Determinism of the big-step semantics (no side condition) | `ds_deterministic` |
| A well-formed command denotes an injective store map | `ds_injective`, `cmd_denot_partial_injective` |
| `read X; C; write X` denotes a partial injective map on *data*, not just on stores | `prog_data_injective` |
| `cmd_denot` is a dagger functor into the category of relations: `cmd_denot (inv c)` is exactly the converse of `cmd_denot c`, and this image is closed under taking the converse | `cmd_denot_dagger`, `cmd_denot_dagger_image` |
| The syntactic inverter is an anti-homomorphism for sequencing at the semantic level too, not just syntactically (`inv_seq`) | `cmd_denot_inv_seq` |
| The abstract dagger-category laws `cmd_denot` instantiates (identity, associativity, dagger involution, dagger anti-homomorphism over composition) | `denot_comp_id_l`/`_r`, `denot_comp_assoc`, `denot_dagger_involutive`, `denot_dagger_id`, `denot_dagger_comp` |
| The self-assignment `X ^= X` that would collapse every value to `nil` (and break backward determinism) is exactly what well-formedness excludes | `nf_expr_not_self` |

The development is **axiom-free**: every top-level result prints
`Closed under the global context` under `Print Assumptions`, and the
final section audits every one of them in one build. Because
`Print Assumptions` does not fail a build when a result *does* depend on
an axiom, `make audit` (`tools/audit.sh`, run in CI) enforces the claim
mechanically: it rejects any `Admitted`/`Axiom`/`Parameter`/`Conjecture`,
any top-level result missing from the audit block, and any verdict other
than the closed-world one. In particular,
functional extensionality is not assumed: the ten-variable
store of the paper is realized as a length-indexed vector
(`var := Fin.t 10`, `store := Vector.t val 10`), which makes store
extensionality a theorem.

## Correspondence with the companion letter

The companion letter states three theorems and one lemma and argues from a
handful of further results.  This table names the identifier that proves
each of them, so that the correspondence survives the letter's own appendix
being shortened for length.

The last block, *Also in the same file*, is here on purpose.  `proofs.v` is
considerably larger than the results the letter states, and this is what the
rest of it is; its size is not the price of those theorems.

| Result | RC 2026 | Identifier in `proofs.v` |
|---|---|---|
| **Determinism** | | |
| Theorem 1 (forward determinism) | Lemma 1, forward | `ss_step_deterministic` |
| &nbsp;&nbsp;&nbsp;&nbsp;in the paper's own statement | Lemma 1, forward | `rev_com_forward` |
| Lemma 1 (invariance), reflection | — | `wf_cc_step_reflected` |
| Theorem 2 (backward determinism) | Lemma 1, backward | `ss_bwd_deterministic_tgt` \* |
| &nbsp;&nbsp;&nbsp;&nbsp;both predecessors well-formed | Lemma 1, backward | `ss_bwd_deterministic` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;the same, in the paper's phrasing | Lemma 1, backward | `rev_com_backward` |
| &nbsp;&nbsp;&nbsp;&nbsp;preservation | — | `wf_cc_step_preserved` |
| &nbsp;&nbsp;&nbsp;&nbsp;along a run | — | `ss_bwd_deterministic_reachable` |
| &nbsp;&nbsp;&nbsp;&nbsp;well-formedness is decidable, command and controlled | — | `wf_cmd_dec`, `wf_cc_dec` |
| &nbsp;&nbsp;&nbsp;&nbsp;self-assignment `X ^= X` is excluded by it | — | `nf_expr_not_self` |
| **Divergences from the printed rules (Sect. 2)** | | |
| the equivalence theorem does not hold as printed | Theorem 1 | `rc2026_theorem1_fails_as_printed_full` |
| &nbsp;&nbsp;&nbsp;&nbsp;from the assignment rules alone | Theorem 1 | `rc2026_theorem1_fails_as_printed` |
| &nbsp;&nbsp;&nbsp;&nbsp;the printed ss rules, transcribed | Fig. 9b | `ss_paper_asn`, `ss_paper_loop`, `ss_paper` |
| &nbsp;&nbsp;&nbsp;&nbsp;the printed ds rules, transcribed | Fig. 2c | `ds_paper`, `loop_paper` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;its side condition is the domain of ⊙ | Fig. 2c | `ds_paper_side_iff_odot` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;so on assignments it is our `Asn_ds` | Fig. 2c | `ds_paper_asn_agrees` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;and it denotes both witnesses | Fig. 2c | `gap_witness_paper_ds`, `gap_witness2_paper_ds` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;its loop guard is stricter too | Fig. 2c | `ds_paper_loop_guard_is_stricter` |
| &nbsp;&nbsp;&nbsp;&nbsp;every leg against a transcribed printed rule | Theorem 1 | `rc2026_theorem1_fails_as_printed_all_printed` |
| &nbsp;&nbsp;&nbsp;&nbsp;only an assignment rule applies there | — | `exec_ss_from_pre_asn_inv` |
| &nbsp;&nbsp;&nbsp;&nbsp;the equality-test witness | Theorem 1 | `gap_witness2_wf`, `gap_witness2_ds` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;on which the printed ss is stuck | Theorem 1 | `gap_witness2_paper_ss_stuck` |
| &nbsp;&nbsp;&nbsp;&nbsp;the printed fss rules, transcribed | Fig. 11a | `fstep_paper_asn` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;on which witness 1 moves | Fig. 11a | `gap_witness_paper_fss_moves` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;and witness 2 | Fig. 11a | `gap_witness2_paper_fss_moves` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;the three facts in one statement | Theorem 1 | `rc2026_printed_fss_moves_where_ss_is_stuck` |
| the printed loop guards are stricter | `Loop_ss` | `rc2026_loop_guards_are_stricter` |
| &nbsp;&nbsp;&nbsp;&nbsp;a well-formed program reaches the witness | — | `odd_store_reachable` |
| which store the printed rules evaluate `E` in | Fig. 9b | (a reading, not a theorem) |
| &nbsp;&nbsp;&nbsp;&nbsp;the two readings agree on well-formed assignments | — | `eval_readings_agree_on_wf` |
| &nbsp;&nbsp;&nbsp;&nbsp;and differ without well-formedness | — | `eval_readings_differ_without_wf` |
| &nbsp;&nbsp;&nbsp;&nbsp;well-formedness is strictly stronger than needed | — | `eval_indep_not_implies_nf`, `nf_expr_implies_eval_indep` |
| the store extensionality used throughout | — | `store_ext` |
| the congruence, recovered as token movements | Eq. (7) | `cong_iff_admin` |
| &nbsp;&nbsp;&nbsp;&nbsp;each movement is a step of → | — | `admin_step_is_ss` |
| &nbsp;&nbsp;&nbsp;&nbsp;the three oriented equations | — | `S_Seq_Enter`, `S_Seq_Mid`, `S_Seq_Exit` |
| &nbsp;&nbsp;&nbsp;&nbsp;it never changes the program | — | `cc_cong_erase` |
| &nbsp;&nbsp;&nbsp;&nbsp;hence well-formedness is class-invariant | — | `cc_cong_preserves_wf` |
| **Semantic equivalence** | | |
| Theorem 3 (three semantics) | Theorem 1 | `semantic_equivalence_p` † |
| &nbsp;&nbsp;&nbsp;&nbsp;residual-flowchart reading | Theorem 1 | `semantic_equivalence` † |
| &nbsp;&nbsp;&nbsp;&nbsp;program level | Theorem 1 | `prog_traversal_data` |
| &nbsp;&nbsp;&nbsp;&nbsp;translation of `C` into a flowchart | — | `translate`, `translate_ctrl` |
| &nbsp;&nbsp;&nbsp;&nbsp;each ss step is simulated by fss steps | Theorem 1 | `ss_step_implies_fss_steps` |
| &nbsp;&nbsp;&nbsp;&nbsp;ss ⇔ fss | Theorem 1 | `semantic_equivalence_ss_fss` |
| &nbsp;&nbsp;&nbsp;&nbsp;ds ⇔ fss | Theorem 1 | `semantic_equivalence_ds_fss` |
| **Finer-grained semantics** | | |
| fss, forward determinism (unconditional) | prose ‡ | `pstep_forward_deterministic` |
| fss, backward determinism | prose ‡ | `pstep_backward_deterministic` |
| &nbsp;&nbsp;&nbsp;&nbsp;counterexample | — | `fstep_not_backward_deterministic` |
| &nbsp;&nbsp;&nbsp;&nbsp;within one flowchart | — | `fstep_backward_deterministic_pos` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;hence along its executions | — | `fstep_backward_deterministic_reachable` |
| **Consequences of determinism** | | |
| (1) uniqueness of the terminal store | — | `ss_run_unique` |
| &nbsp;&nbsp;&nbsp;&nbsp;configuration after *n* steps is unique | — | `ss_run_state_unique` |
| &nbsp;&nbsp;&nbsp;&nbsp;shorter runs are prefixes of longer ones | — | `ss_run_prefix` |
| &nbsp;&nbsp;&nbsp;&nbsp;maximal runs agree in length and endpoint | — | `ss_run_trace_unique` |
| &nbsp;&nbsp;&nbsp;&nbsp;backward: same-length runs to a wf target agree at the start | — | `ss_run_state_unique_bwd` |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;hence at every step | — | `ss_run_trace_unique_bwd` |
| (2) determinism of ds | prose ‡ | `ds_deterministic` |
| (3) injectivity of the store map | prose ‡ | `ds_injective` |
| &nbsp;&nbsp;&nbsp;&nbsp;data-level version (`read X; C; write X`) | prose ‡ | `prog_data_injective` |
| **Also in the same file** | | |
| Verified interpreter | — | `eval_cmd_correct` |
| Syntactic inverter, correct | — | `inv_correct` |
| &nbsp;&nbsp;&nbsp;&nbsp;unique | — | `inv_unique_cxt` |
| &nbsp;&nbsp;&nbsp;&nbsp;`C; inv C` acts as identity (on `C`'s domain) | — | `inv_compose_id` |
| &nbsp;&nbsp;&nbsp;&nbsp;`inv C; C` acts as identity (on `C`'s range) | — | `inv_compose_id_sym` |
| &nbsp;&nbsp;&nbsp;&nbsp;`cmd_denot`(`inv` c) = converse of `cmd_denot`(c) | — | `cmd_denot_dagger` |
| &nbsp;&nbsp;&nbsp;&nbsp;closure under taking the converse | — | `cmd_denot_dagger_image` |
| &nbsp;&nbsp;&nbsp;&nbsp;anti-homomorphism for sequencing, semantically | — | `cmd_denot_inv_seq` |
| Full abstraction | — | `full_abstraction` |
| &nbsp;&nbsp;&nbsp;&nbsp;soundness | — | `fa_soundness` |
| &nbsp;&nbsp;&nbsp;&nbsp;completeness | — | `fa_completeness` |

\* strengthens `ss_bwd_deterministic`, which hypothesizes well-formedness of
both predecessors.

† the fixed-position reading of fss stated as Theorem 3 of the letter;
`semantic_equivalence` is the same equivalence for the residual-flowchart
reading.

‡ asserted in the prose of the RC 2026 paper without proof.

## Determinism of the finer-grained semantics (fss)

| Theorem | Statement | Axioms |
|---------|-----------|--------|
| `fstep_forward_deterministic` | forward determinism of `fstep` (unconditional) | **none** |
| `fstep_not_backward_deterministic` | backward determinism of the raw `fstep` relation fails, even under `wf_cf` (explicit counterexample) | **none** |
| `fstep_backward_store_deterministic_nf` | local invertibility: with the source control component fixed, the pre-store is unique under the minimal head-atom condition `nf_head` (the `wf_cf` version is the corollary `fstep_backward_store_deterministic`) | **none** |
| `posf_step_preserved` / `posf_steps_preserved` | the token never leaves the program: `posf` is preserved by (sequences of) steps | **none** |
| `fstep_backward_deterministic_reachable` | corollary: any two predecessors of a common target reachable from the entry of one well-formed program coincide | **none** |
| `fstep_backward_deterministic_pos` | backward determinism holds over the token positions (`posf`) of one fixed well-formed program | **none** |
| `pstep_forward_deterministic` / `pstep_backward_deterministic` | the fss **as presented in the paper**, a token travelling over a fixed flowchart `F` (`pstep F`): forward determinism is unconditional and backward determinism needs only `wf_flow F`, no hypothesis on any configuration | **none** |
| `ds_iff_pfss` | a terminating big-step run of `c` is exactly a traversal of its flowchart from entry to exit, `psteps (translate c F_nil) (CF_pre (translate c F_nil), s) (CF_pre F_nil, s')` | **none** |

## Lessons learned

Mechanizing a metatheory that a paper presents in a page or two is not a
matter of retyping the argument. The points below record where this
development had to depart from the paper proofs, as data for anyone
mechanizing a similar semantics. Every backquoted name is a top-level
declaration of `proofs.v` and can be located by searching for it.

**1. Backward determinism depends on how a configuration is represented,
and one natural choice makes it false.** If an fss configuration records
only the *remaining* flowchart, the executed prefix is lost and backward
determinism fails even under `wf_cf`: an assignment atom that rewrites
`nil` to `nil` and a loop exit can land on the same fall-through position
`CF_pre F_nil` with the same store
(`fstep_not_backward_deterministic`). The reading of the paper,
a token travelling over a *fixed* flowchart, is what makes the property
true, and recovering it took a separate position predicate `posf` and a
separate relation `pstep F`. Contrast ss, where a `cont_cmd`
carries the whole program, which is exactly why
`ss_bwd_deterministic_tgt` goes through.

**2. The repair rests on a structural lemma that no paper proof states.**
Within one flowchart the continuation chain is linear and sizes strictly
decrease, so every suffix occurs exactly once and the target position
pins down the atom that was crossed (`tailf_parent_unique`).
Formalizing "the token never revisits a position" required the auxiliary
`fsize`, `fchild` and `tailf`.

**3. "The derivation passes through this point" is not free.** Splitting
a complete fss derivation at `CF_pre R` needs a no-cycle argument, built
here from an `outer_rest` measure, the suffix order `sub_flow` with its
antisymmetry, and `flow_size` (`fnsteps_pre_no_cycle`).

**4. Structural induction does not close; derivation length does.** The
development adds length-indexed relations `nsteps` and `fnsteps` with a
well-founded `nsteps_strong_ind`. Loop-body
factorization has to *return* the bound (`m < n` in
`fnsteps_in_loop_to_pre`) for the induction to close. The longest proofs
in the file live here (`fss_seq_factor`, `factor_in_loop_via`,
`fss_complete_to_pre`).

**5. The ss-to-fss simulation is one-to-many, and sometimes one-to-none.**
A single ss step maps to a finite, possibly empty, sequence of fss steps,
so there is no lock-step relation to exploit;
`ss_step_implies_fss_steps` goes through a context-lifting
lemma `fsteps_lift_loop` and a root-command rewrite
`step_preserves_root`.

**6. The side condition the paper imposes is stronger than the one the
proof needs.** Backward store determinism of fss needs the "assigned
variable not free in the right-hand side" condition only of the atom
currently under the token (`nf_head`); full `wf_cf` is a corollary
(`fstep_backward_store_deterministic_nf`). At the ss level,
hypothesizing well-formedness of both predecessors
(`ss_bwd_deterministic`, at 76 lines the longest single proof here)
weakens to the single common target (`ss_bwd_deterministic_tgt`) via the
reflection lemma `wf_cc_step_reflected`. Both weakenings surfaced while
mechanizing, not before.

**7. Staying axiom-free is a design constraint, not a checkbox.** A store
as `var -> val` would have made functional extensionality necessary in
the backward-determinism endgame. Realizing it as `Vector.t val 10` over
`Fin.t 10` turns store extensionality into a theorem, at the price of
dependent-type friction in `inversion` and equality reasoning throughout.

**8. An executable interpreter is a separate proof effort.** `exec_ds` is
a relation and needs none; making it executable took a fuel-bounded
`eval_cmd_fuel` with mutual recursion, plus fuel monotonicity, soundness
and completeness lemmas for the loop case (`eval_cmd_loop_mono`,
`eval_cmd_loop_sound`, `eval_cmd_loop_complete`).

**9. Notation does not survive contact with the proof assistant.** The
single arrow of the paper's transition relation clashes irreparably with
Coq's `fun .. => ..`, so the development writes `==>`.

**What was easy, for balance.** Forward determinism
(`ss_step_deterministic`) is short: terminal configurations are stuck and
the loop rules are mutually exclusive by their guards, so only
assignment-versus-assignment has content. Preservation of
well-formedness is routine. The difficulty was concentrated in the
backward direction and in the fss layer.

## Build

Requires Rocq (Coq Prover) 9.0 or later; tested with 9.1.1, which is
what CI pins and what `rocq-rcore-semantics.opam` records. `_CoqProject`
carries the logical path (`-Q . RCore`), so an IDE (VsRocq, Proof
General, coq-lsp) resolves `From RCore Require Import proofs` without
extra configuration.

```sh
rocq c -Q . RCore proofs.v      # build (this IS the proof)
rocq check -Q . RCore RCore.proofs   # kernel re-validation
```

Or equivalently via the provided `Makefile`:

```sh
make                # build (this IS the proof)
make check          # kernel re-validation
make audit          # enforce the axiom-free claim (see below)
make correspondence # enforce the paper-to-artifact rule diff
make extract        # extract a verified OCaml interpreter
make extract-test   # build and RUN the extracted interpreter
make clean
```

`make extract` produces `rcore_interp.ml`/`.mli` from `extraction.v`.
What is extracted is the same code the theorems are about
(`eval_cmd_fuel`, `step_fun`, `steps_n`, `inv`, `cc_inv`, `wf_cmd_dec`,
`wf_cc_dec`), not a reimplementation, so `eval_cmd_correct` and
`step_fun_correct` apply to it directly. Extraction that is never run is
an unverified claim, so `make extract-test` compiles the output with
`ocamlc` and executes `test_interp.ml` against it.

The trailing `Print Assumptions` commands in the file reproduce the
axiom audit.

## License

MIT. See [LICENSE](LICENSE).
