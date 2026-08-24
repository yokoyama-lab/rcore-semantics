# Transcription audit of the printed semantics

This document records a rule-by-rule visual comparison between the published
rules and the relations that transcribe them in `proofs.v`.  It concerns the
printed-rule relations (`ds_paper`, `loop_paper`, `ss_paper_asn`,
`ss_paper_loop`, `ss_paper`, and `fstep_paper_asn`), not the amended semantics
used by the main equivalence theorem.

## Source and method

Checked on 2026-08-25 against the publisher's final PDF of:

> Toya Makino and Tetsuo Yokoyama, "Small-Step Semantics with Meta-Level
> Reversibility for a Reversible Core Language," *Reversible Computation*,
> LNCS 16626, pp. 201--218, 2026.
> [doi:10.1007/978-3-032-30839-9_12](https://doi.org/10.1007/978-3-032-30839-9_12)

The PDF was inspected visually with each figure beside the corresponding
inductive definition.  Premises and conclusions were checked separately.
The following notation changes are not counted as differences:

- `Vnil` is the paper's `f` (and `nil`), and `Vt := Vpair Vnil Vnil` is `t`.
- `Cass`, `Cseq`, and `Cloop` encode the three command forms.
- `update s x v` is the total-store form of replacing the binding of `x` by
  `v`; `s x` is lookup.
- A partial semantic function is represented by an inductive relation, and
  expression undefinedness is represented by `eval_expr ... = None`.
- `CC_*` and `CF_*` constructors encode the positions of the printed control
  token.

One substantive convention does matter.  The paper writes an assignment store
as `sigma + {X -> d}` and evaluates `E` in the residual `sigma`, which has no
binding for `X`.  The artifact uses a total store `s`, requires `s x = d`, and
evaluates `E` in that full store.  The readings agree for well-formed
assignments but can differ otherwise (`eval_readings_agree_on_wf` and
`eval_readings_differ_without_wf`).

## Figure 2c, p. 204: `ds_paper` and `loop_paper`

| Artifact constructor | Printed rule or clause | Audit result |
|---|---|---|
| `PD_Asn` | `Asn_ds` | **Difference recorded.** The side condition, update, and conclusion agree after expanding `odot`; the artifact additionally names the result `v_new` and states its `odot` equation.  The expression-store reading differs as described above: the figure evaluates `E` in residual `sigma`, while `PD_Asn` evaluates it in the full store `s`. |
| `PD_Seq` | `Seq_ds` | **Matches.** Its two premises and conclusion are exactly relational composition, up to relationalizing the printed partial functions. |
| `PD_Loop` | `Loop_ds` | **Matches after unfolding the fixed point.** `s x = Vt` is the printed entry premise and `loop_paper x c y s s'` represents `s' = fix(F)(s)`; the conclusion is the relational form of the printed equation. |
| `PL_Base` | First clause of `F(phi)` | **Matches.** The premise is `s(Y) = t` and the input and output stores are both `s`. |
| `PL_Rec` | Second clause of `F(phi)` | **Matches.** The premises occur in the printed order modulo conjunction: `s(Y) = f`, execution of `C` from `s` to `s1`, `s1(X) = f`, and recursive execution from `s1` to `s2`; the conclusion relates `s` to `s2`. |

Thus the loop and sequencing transcription is faithful up to standard
relationalization.  The only substantive discrepancy in this block is the
assignment expression-store reading.

## Figure 9b, p. 211: `ss_paper_asn`, `ss_paper_loop`, and `ss_paper`

### Assignment and loop rules

| Artifact constructor | Printed rule | Audit result |
|---|---|---|
| `P_AsnSet` | `AsnSet_ss` | **Difference recorded.** `e != nil`, the `X = nil` source binding, the update to `e`, and the token movement agree.  The artifact evaluates `E` in the full store and factors the printed evaluation context out through `ss_paper`; the figure evaluates `E` in residual `sigma` and displays `E[...]` in the rule. |
| `P_AsnClear` | `AsnClear_ss` | **Difference recorded.** `d != nil`, evaluation of `E` to `d`, clearing `X`, and token movement agree.  `s x = v_e` reconstructs the printed common value `d`.  The same full-store and factored-context differences as for `P_AsnSet` remain. |
| `P_LoopEnter` | `LoopEnter_ss` | **Matches within `ss_paper`.** `s x = Vt` is `sigma(X) = t`, and source, target, store, and token positions agree after restoring the factored evaluation context. |
| `P_LoopExit` | `LoopExit_ss` | **Matches within `ss_paper`.** `s y = Vt` is `sigma(Y) = t`, and the conclusion moves the token to the loop exit without changing the store. |
| `P_LoopIter1` | `LoopIter1_ss` | **Matches within `ss_paper`.** `s y = Vnil` is `sigma(Y) = f`, and the token enters the body. |
| `P_LoopIter2` | `LoopIter2_ss` | **Matches within `ss_paper`.** `s x = Vnil` is `sigma(X) = f`, and the token returns from the end of the body to the loop midpoint. |

### Packaging as `ss_paper`

| Artifact constructor | Printed counterpart | Audit result |
|---|---|---|
| `SP_asn` | Assignment cases of Fig. 9b | **Faithful factoring.** This is an embedding constructor, not an additional printed rule. |
| `SP_loop` | Loop cases of Fig. 9b | **Faithful factoring.** This is an embedding constructor, not an additional printed rule. |
| `SP_ctx_L` | Evaluation context `E = E'; C` | **Faithful factoring.** It makes explicit the context closure displayed implicitly by `E[...]` in every printed rule. |
| `SP_ctx_R` | Evaluation context `E = C; E'` | **Faithful factoring.** It makes the corresponding right-sequence context explicit. |
| `SP_ctx_lp` | Evaluation context `E = from X loop E' until Y` | **Faithful factoring.** It makes the loop-body context explicit. |

Scope limitation: the paper states that its transition relation is taken modulo
the structural congruence of Eq. (7).  `ss_paper` transcribes Fig. 9b and its
evaluation-context closure, but it does **not** quotient by or otherwise include
Eq. (7).  Consequently, it is not by itself a complete transcription of the
paper's full transition relation modulo structural congruence.  This limitation
does not affect the two assignment counterexamples, which contain no sequence.

## Figure 11a, p. 214: `fstep_paper_asn`

| Artifact constructor | Printed rule | Audit result |
|---|---|---|
| `PF_AsnSet` | `AsnSet_fss` | **Difference recorded.** The premise `e != nil`, update from `nil` to `e`, and crossing of the assignment atom agree.  The artifact evaluates `E` in the full store and represents only a root assignment followed by residual flowchart `F`; the figure evaluates in residual `sigma` and permits an arbitrary flowchart context `E_fss`. |
| `PF_AsnClear` | `AsnClear_fss` | **Difference recorded.** Evaluation to `d`, update from `d` to `nil`, and crossing of the atom agree, including the important absence of a `d != nil` premise.  The same full-store and restricted-context differences as for `PF_AsnSet` remain. |

Scope limitation: `fstep_paper_asn` transcribes only the two assignment rules of
Fig. 11a.  It does not transcribe `TestT_fss`, `TestF_fss`, their inverse
assertion relations, or closure under arbitrary `E_fss`.  The two checked gap
witnesses place the assignment at the root, so this restricted relation is
sufficient for `gap_witness_paper_fss_moves` and
`gap_witness2_paper_fss_moves`, but it must not be described as a transcription
of all of Fig. 11a.

## Summary

- The premises and conclusions of all sequencing and loop clauses match the
  printed figure, up to notation and relationalization.
- The assignment clauses preserve the printed side conditions, including the
  asymmetric absence of `d != nil` from `AsnClear_fss`, but use the artifact's
  full-store reading of expression evaluation.
- `ss_paper` covers Fig. 9b with explicit evaluation-context closure but omits
  the separate structural congruence of Eq. (7).
- `fstep_paper_asn` is an assignment-only, root-position transcription, not the
  whole relation printed in Fig. 11a.
