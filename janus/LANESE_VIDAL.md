# Correspondence with Lanese–Vidal, "A Reversible Semantics for Janus" (RC 2026)

> **要旨（日本語）** Lanese–Vidal の PC（プログラムカウンタ）方式の可逆 small-step 意味論と、本ディレクトリの制御トークン方式を構成要素ごとに対応づける。
> 配置 ⟨σ, ℓ, ℓ′, π⟩ の 2 本のラベルとスタック π は、`cont_stmt` の 1 個のトークンと文脈スパインが構造的に担う。
> 彼らの Loop Lemma（到達可能配置上の ⇀ iff ↽）は、こちらでは後向き関係を逆関係として定義するため定義上成り立ち、内容は前向き決定性・整形式性下の後向き決定性・`inv_step_reverses` に移る。
> 彼らの規則の正確な形（図）は本稿では読めていないため未検証として明示する。

Status (2026-09-23): every result named below is proved in `janus/janus.v` (Rocq 9.1.1, 36 audited results, no `Admitted`, `make janus-audit` passes: all `Closed under the global context`).

---

## 1. What is compared, and the evidence base

**Compared.** Lanese & Vidal, *A Reversible Semantics for Janus*, RC 2026, LNCS 16626,
pp. 184–200, doi:10.1007/978-3-032-30839-9_11 (extended version arXiv:2602.16913), against the
control-token semantics `jstep Γ` of `janus/janus.v` described in `RULES.md`, which extends the
R-CORE semantics of Makino & Yokoyama, RC 2026, LNCS 16626, pp. 201–218,
doi:10.1007/978-3-032-30839-9_12 (`proofs.v`).

**Evidence base, and how each claim is tagged.** arxiv.org and the publisher are unreachable
from here, and the PDF was not opened. What was read:

- the `pdftotext -raw` extraction of the LNCS paper kept in the rc-survey clone,
  `rc-survey/papers/RC2026/RC2026-09-a-reversible-semantics-for-janus.txt` (727 lines). It
  contains the prose, the lemma statements and the footnotes, but **none of the figures**: Fig. 1
  (syntax), Fig. 3/5 (stack-based rules), Fig. 4 (inverter), Fig. 8 (entry/exit), Fig. 9 (flow),
  Fig. 11/12 (forward rules), Fig. 14/15 (backward rules) and the derivations Fig. 13/16 are
  captions only. Label symbols (ℓ), the empty store (ε) and the arrows ⇀/↽ are dropped by the
  extraction. Claims checked against this text are tagged **(text Lnn)** with the line number in
  that file.
- the rc-survey card `rc-survey/cards/RC2026/RC2026-09-a-reversible-semantics-for-janus.md`
  (11 lines) and full summary `rc-survey/summaries/RC2026-09-a-reversible-semantics-for-janus.md`
  (21 lines), and the cross-references in `rc-survey/docs/forward/core.md` L260–290, L329–352,
  L394, L426–435, L490–494, L542–545, `docs/40_findings.md` L50–62,
  `docs/50_forward_citations.md` L110–118, `docs/40_discrepancies.md` L94. Claims that rest on
  the survey's reconstruction rather than on the extraction are tagged **(rc-survey)**.
- anything that is this document's own reading is tagged **(inferred)**; anything about the
  shape of a rule is tagged **(unverified: figure)**, because the rules live in the figures.

The paragraph on Makino–Yokoyama (their §4, printed p.198) is **present in the LNCS text**
(text L624–630) and, per the survey's check of arXiv:2602.16913 v2, **absent from the arXiv
version**, whose Related Work reads "The only small-step reversible semantics we are aware of…"
where LNCS has "The only other…" (rc-survey: `docs/forward/core.md` L275–290). When citing that
paragraph, cite the LNCS version. Their reference [15] to Makino–Yokoyama is printed with
`pp. xx–yy` (text L693–695; rc-survey `docs/40_discrepancies.md` L94).

---

## 2. Side-by-side: their construct → ours

| Lanese–Vidal (PC-based) | Control-token semantics (`janus.v`) | Notes / evidence |
|---|---|---|
| Configuration ⟨σ, ℓ, ℓ′, π⟩: store, **last executed** label, **next** label, stack (text L285–291) | `(cs, s) : cont_stmt * store` | One token instead of two labels and a stack. |
| Two labels: "a pair of labels representing the last executed statement and the next statement to be executed, respectively"; the first is unused forwards and "will be used by the transition rules of the backward semantics" (text L286–291) | the single token position | (inferred) A `cont_stmt` keeps the **whole program** around the token, so the token's position in the tree determines both what was just executed (the maximal `CS_post` below/left of it, or the guard just passed) and what comes next. The "two pointers vs one •" remark of their p.198 (text L625–627) lands here: the second pointer is information the token representation already carries structurally. |
| Labelled elementary blocks `[o]ℓ`, `start`/`stop` added to every program and procedure, `block(ℓ)`, `entry`/`exit`, `ctx(ℓ)`, CFG `flow(s)` (text L226–256) | none: the semantics is syntax-directed; there is no labelling pass and no CFG | Their `exit` "always returns a single label because of Janus conditionals with a single exit point" (text L240–241); in ours the single exit is the constructor `CS_post (Sif …)`. |
| Stack π, elements `seq(…)`, `if true(ℓ1,ℓ2)`, `if false(ℓ1,ℓ2)`, `loop1(ℓ1,s1,ℓ2,s2)`, `loop2(ℓ1,s1,ℓ2,s2)`, `call(ℓ)`, `uncall(ℓ)` (stack-based version: text L147–150; PC version: `if true`/`if false` carry both labels L349–352, `loop1`/`loop2` carry `(ℓ1, s1, ℓ2, s2)` L405–409, `call(ℓ)`/`uncall(ℓ)` in footnote 3 L383–388) | the **context spine** of `cont_stmt`: `CS_seq_L`/`CS_seq_R` (seq), `CS_if_then`/`CS_if_else` (if true/false), `CS_loop_do`/`CS_loop_loop` (loop1/loop2), `CS_call`/`CS_uncall` (call/uncall) | They say the stack elements deliberately carry more than forward execution needs: "we include both labels in the elements of the stack so that they can be used by both the forward and the backward semantics" (text L367–368) and "in the backward semantics, we will need to access exit(s1) and exit(s2). Therefore, we use (ℓ1, s1, ℓ2, s2)" (text L407–409). (inferred) That extra information is exactly what the spine constructors hold: `CS_if_then e1 cs s2 e2` has both guards, `CS_loop_do e1 cs s2 e2` has both guards and both bodies. |
| Side condition `ℓ2 = entry(s1)` in forward `LoopBase` "in order to ensure that we are considering the right edge" (text L394–397); `ℓ = exit(s2)` in backward `LoopMain` because "there are two outgoing edges in the inverse CFG" (text L572–578) | pattern matching on `CS_pre` / `CS_post` inside a spine constructor, e.g. `J_Loop_Iter1` fires on `CS_loop_until`, `J_Loop_Iter2` on `CS_loop_loop e1 s1 (CS_post s2) e2` | (inferred) Where they disambiguate a CFG node of out-degree 2 by an equation on labels, the token semantics has two different constructors, so there is nothing to disambiguate; see `RULES.md` §5 for the pairs that *do* share a pattern and the guard that separates them. |
| Static inverse `I[[s]]` (Fig. 4, unverified: figure) extended with `I[[start]] = stop`, `I[[stop]] = start`; an inverse procedure `procedure id⁻¹ I[[s]]` is generated for every procedure, and CFGs are computed for it too (text L262–268) | `inv` on statements (`RULES.md` §1) and `cs_inv` on token positions; `uncall p` runs `inv (Γ p)` **forwards** (`J_Uncall_Enter`), no inverse procedure is generated | The stack-based version's `UnCallS` also "reduces to the inversion I[[Γ(id)]] of the body" (text L164–168), so the idea of running the inverse body forwards is shared. |
| "we do not have edges for call/return (resp. uncall/return) in a CFG. The control flow for these cases will be dealt with dynamically in the corresponding transition rules" (text L258–260); forward `Call` "updates the control … with the labels from the first two statements of the procedure", `Return1` fires when the next statement is `stop` (text L303–318) | `CS_call p cs` / `CS_uncall p cs` frames: `J_Call_Enter` puts `•(Γ p)` under a `CS_call p` frame, `J_Call_Exit` removes the frame when the body reaches `(Γ p)•` | (inferred) The frame plays the role of their `call(ℓ)` stack element *and* of the return edge that the CFG lacks; the return point is the frame's position in the enclosing tree. |
| Expression evaluation "is not reversible (but considered a one-step evaluation)" (footnote 1, text L171–172) | `eval s e : Z` total, one step, not reversible | **Same design** on this axis. This is a difference from R-CORE (`proofs.v`), where `⊙` is partial and evaluation is input-preserving; the survey warns not to lump the two RC 2026 papers together on this point (rc-survey summary, "当研究での使い道" (ii)). |
| "procedures have neither parameters nor local variables" (text L121–124) | same: `Γ : pid -> stmt`, no parameters, no `local`/`delocal` | Same fragment. Both also omit arrays here (ours by choice; theirs has `x[e1] ⊕= e2` in Fig. 1 per text L106–107, so their fragment is slightly larger). |
| Sequence is right-associative, labels unique (text L177–178, L230) | `Sseq` is a binary constructor, any association; no labels | (inferred) irrelevant for us. |
| Store σ total with default 0, "we assume that σ is defined (with value zero if not explicitly initialized)" (text L142–143) | `store := Vector.t Z 10`, total by construction | Same convention. |

---

## 3. Their results ↔ ours

| Lanese–Vidal | Control-token semantics | Comment |
|---|---|---|
| **Lemma 1** (§3.1, p.194; text L414–420, symbols reconstructed by rc-survey): the stack-based small-step semantics of §2 and the forward PC semantics agree on terminating runs | no counterpart needed | There is a single representation, so there is no "stack vs PC" equivalence to prove. (inferred) The closest thing in `proofs.v` is `cong_iff_admin` (L4321): the paper's Eq. (7) structural congruence is recovered as the administrative token moves `S_Seq_*`, i.e. the R-CORE artifact also had to show that a second presentation of control coincides with the token one. |
| **Lemma 2** (§3.2, p.195; text L466–467): `flow⁻¹(s) = flow(I[[s]])` — the inverse CFG is the CFG of the inverted program | `inv_step_reverses` (`wf_cs cs -> jstep Γ (cs,s) (cs',s') -> jstep Γ (cs_inv cs', s') (cs_inv cs, s)`) and `bstep_is_fwd_of_inv` (`wf_cs cs -> wf_cs cs' -> (bstep Γ (cs,s) (cs',s') <-> jstep Γ (cs_inv cs, s) (cs_inv cs', s'))`): a forward step of `s` is, read backwards, a forward step of `inv s` at the `cs_inv`-mirrored position; hence `bstep` is the forward relation of the inverted program. The only hypothesis is `wf_cs` (for the `J_Asn` case); no `wf_penv`, no reachability | Their statement is about the static graph; ours is about the transition relation, one step at a time. (inferred) Ours is the dynamic form of theirs; a Janus CFG layer (RULES.md §7 item 7) would let the static form be stated too. |
| **Definition 1** (reachable configuration, p.197; text L586–598): obtainable from an initial ⟨ε, ℓ1, ℓ2, []⟩ by (⇀ ∪ ↽)*; "This rules out, e.g., the case of configurations ⟨σ, ℓ, ℓ′, π⟩ where ℓ and ℓ′ are not the two ends of an edge of the CFG" | not needed as a hypothesis; the only hypothesis is `wf_cs` (and `wf_penv Γ`) | See the table below. |
| **Lemma 3 (loop lemma)** (p.198; text L601–612): for a reachable ⟨σ,ℓ1,ℓ2,π⟩, `⇀` to ⟨σ′,…⟩ iff ⟨σ′,…⟩ `↽` back. "The proof is by case distinction on the applied rule. Full details can be found in the extended version [13]." | `bstep Γ cfg cfg' := jstep Γ cfg' cfg`, so "⇀ iff ↽" holds **by definition**. The content moves to three theorems: (a) `jstep_deterministic` (forward determinism, no hypothesis); (b) `jstep_bwd_deterministic_tgt` / `bstep_deterministic` (backward determinism under `wf_cs` of the common target, **no reachability**); (c) `inv_step_reverses` / `bstep_is_fwd_of_inv` (under `wf_cs`: the backward relation is computed by running the inverted program forwards). | (inferred) In their setting the backward relation is given by a second set of rules (Fig. 14/15), so the Loop Lemma is a genuine theorem relating two definitions. In ours the second definition is the pair `inv`/`cs_inv`, and (c) is the theorem relating it to the converse; (a)+(b) are what make the converse a *function*, which the Loop Lemma alone does not give (it states existence of an inverse step, not uniqueness — the extraction does not show a determinism lemma in the conference text). |
| Equivalence with the big-step semantics of the literature: asserted in §4 (text L613–617), proofs in the extended version | not yet (RULES.md §7 item 8) | Both developments leave this to another document; theirs to arXiv:2602.16913, ours to future work. |
| Mechanization: none (rc-survey card, "手法"; no proof assistant is mentioned anywhere in the extraction) | Rocq 9.1.1, axiom-free (`make janus-audit`) | 36 results, all `Qed`, every one `Closed under the global context`; audited by the same script as `proofs.v` (`tools/audit.sh` with `SRC=janus/janus.v`). |

### Conditions under which the Loop Lemma holds

| | Lanese–Vidal | Control-token semantics |
|---|---|---|
| Hypothesis | **reachability** of the configuration (Definition 1), plus Janus well-formedness of the program (abstract: "reversible (for well-formed Janus programs)", text L21–22; the `x ∉ e` requirement is stated at text L109–110) | **well-formedness** `wf_cs cs` of the (target) configuration and `wf_penv Γ`; `wf_cs` is `x ∉ e` for every assignment in the tree — nothing else |
| Why it is needed | the labels ℓ1, ℓ2 must be the two ends of a CFG edge and the stack must be consistent with them (text L596–598); an arbitrary ⟨σ,ℓ,ℓ′,π⟩ can be undone in a way that does not redo to it | only `J_Asn` can merge two distinct pre-configurations into one post-configuration, and only when `x ∈ e` (`RULES.md` §5); every other rule is injective by its constructor pattern and its guard. Control consistency is enforced by the type `cont_stmt` (exactly one token, whole program kept), so there is no "ill-matched labels" case to exclude |
| Relation between the two hypotheses | — | (inferred) Reachability from a well-formed initial configuration implies `wf_cs` at every step (`wf_cs_step_preserved`), so our hypothesis is implied by theirs in spirit; ours is also decidable on the configuration alone (`wf_cs_dec`) whereas reachability is a property of a run. Conversely we cannot drop `wf_cs`: the self-assignment `x ^= x` collapses every value to 0 and breaks backward determinism (cf. `nf_expr_not_self`, `proofs.v` L410). |
| Where the proof is | extended version only (text L94, L611–612) | in `janus/janus.v` (all Qed, axiom-free) |

---

## 4. What is new, what is partially known

The rc-survey card grades the novelty of a token semantics for Janus as **partially known**: the
problem (a reversible small-step semantics for Janus) is solved by Lanese–Vidal with a different
representation, and they themselves pose the token approach as an open question (text L628–630).

New here:

- **The control-token semantics for the Janus core itself** — conditionals, `do`-part loops,
  `call`/`uncall` — answering the question of their §4 for the fragment they treat (no
  parameters, no locals) minus arrays. Whether it "scales" in their sense is answered for this
  fragment only; arrays and locals remain open (RULES.md §7).
- **Per-rule partial injectivity, mechanized.** The property proved is that each of the 27
  inference rules is a partial injection on well-formed configurations (`RULES.md` §5), not only
  that every step has an inverse step. This is the meta-level reversibility of Makino–Yokoyama,
  carried to Janus and checked in Rocq. **Correction (2026-09-24):** an earlier version of this
  bullet said, following rc-survey (`docs/forward/core.md` L426–435), that there was no prior
  mechanization of a small-step semantics for a reversible imperative language. That is wrong:
  the public Rocq development of `yokoyama-lab/PyJanus` (`coq/`) already contains two small-step
  semantics for a Janus-shaped language, see §4a. What is new here is narrower, and §4a states it.
- **The from/until split**  of the loop token position, which is what makes `cs_inv` an
  involution on token positions and lets `bstep` be computed by the forward relation on the
  inverted program (`RULES.md` §2).
- **`uncall` as forward execution of the inverse body inside a token semantics**, with
  `J_Uncall_*` mirroring `J_Call_*` under `cs_inv`, and no generated inverse procedures or
  inverse CFGs.

Not new:

- A reversible (Loop-Lemma-satisfying) small-step semantics for a Janus fragment: Lanese–Vidal.
- The idea of the Loop Lemma as the reversibility criterion for a small-step semantics, imported
  from process calculi (text L66–69: RCCS, CCSK, reversible Erlang).
- Running the inverted body for `uncall` (already in their stack-based `UnCallS`, text L164–168,
  and in the Janus literature they cite).
- Irreversible one-step expression evaluation: shared with them (footnote 1).
- The token representation itself and the shape of the determinism proofs: `proofs.v`.

---

## 4a. Relation to the PyJanus Rocq development (`yokoyama-lab/PyJanus`, `coq/`)

Checked against `PyJanus` HEAD `9d30e2f` (2026-09-05). Its language (`RevCore.v`, `RevLang`) has
the same statement forms as ours (`Skip`, primitive, `Seq`, `If g1 s1 s2 g2`,
`Loop g1 s1 s2 g2`, `Call p`, `Uncall p`, no parameters, no locals), but over **abstract**
primitives: a module type `REV_PRIM` whose `pstep` is *assumed* deterministic and reversible
(`pstep_det`, `pstep_rev`, `RevCore.v` L37–47). Two of its files are small-step semantics:

| | `RevSmallStep.v` | `RevLoopLemma.v` | `janus/janus.v` (this directory) |
|---|---|---|---|
| Configuration | runtime statement `rs` + state (context-based, after Lami–Lanese–Stefani RC 2024) | control stack `list rs` + state + **history** `list ev`, one event per step (after Lanese–Vidal) | `cont_stmt` (whole program, one token) + store; **no history** |
| Backward determinism | **refuted**: `step_not_backward_deterministic` (L344), `exit_assertion_collapses` (L358) | yes, no hypothesis: `fstep_backward_det` (L239), via `loop_lemma` (L180) | yes, under `wf_cs` (decidable on the configuration): `jstep_bwd_deterministic`, `bstep_deterministic` |
| Backward relation | — | `bstep`, defined separately; reads the history | the converse of `jstep`; `bstep_is_fwd_of_inv`: it *is* forward `jstep` on `cs_inv` |
| Where injectivity of assignment comes from | axiom of the module type (`pstep_rev`) | same | proved for concrete `+= -= ^=` from `x ∉ e` (`asn_step_injective`); `x ^= x` shows `wf_cs` cannot be dropped |
| Relation to big-step | `equiv` (L320) | `exec_iff_pc` | none yet (`README.md`, next steps) |

So the accurate statement of what `janus/janus.v` adds is:

- a small-step semantics for this Janus core that is backward deterministic **without storing a
  history** — the configuration size does not grow with the run, unlike `RevLoopLemma.v`, where
  the history is what restores the information that `RevSmallStep.v` shows is lost;
- the obstruction exhibited in `RevSmallStep.v` is avoided by representation alone: the
  sequencing collapse cannot occur because `CS_seq_L`/`CS_seq_R` keep the other component, and the
  exit-assertion collapse cannot occur because `CS_if_then`/`CS_if_else` keep both guards;
- the backward relation needs no separate definition: it is the forward relation on the
  `cs_inv`-image (`bstep_is_fwd_of_inv`);
- assignment is concrete, so the well-formedness side condition `x ∉ e` is a *proved*
  hypothesis, not an axiom of an abstract primitive interface.

Not new relative to PyJanus: the language shape, the inverter on statements, the existence of a
small-step semantics for it, and a Loop Lemma for a Janus-shaped language (history-based).

---

## 5. Open items that need the paper's figures or the extended version

1. **Exact rule shapes** (Fig. 11, 12, 14, 15). The extraction has only the prose around them.
   In particular it is not verified how `Skip`, `Call`, `Return1/2`, `LoopMain`, `Loop1/2`,
   `LoopBase`, `IfTrue1/2`, `IfFalse1/2` manipulate ℓ, ℓ′ and π, so no rule-to-rule table can be
   given here. (unverified: figure)
2. **Whether their loop labels coincide with our from/until points.** Their `from [e1]ℓ1 do s1
   loop s2 until [e2]ℓ2` labels the two *guards*; forward `LoopBase` has the side condition
   `ℓ2 = entry(s1)` (text L394–397) — the extraction garbles which label is meant. (inferred)
   The natural guess is: a configuration with next label ℓ1 after `LoopMain`/`Loop2` corresponds
   to `CS_loop_from`, and one with next label ℓ2 to `CS_loop_until`; our `J_Loop_Do` and
   `J_Loop_DoDone` would then be steps that their semantics folds into the label increment.
   Needs Fig. 12.
3. **Treatment of assertion failure.** Ours: stuck configuration (no rule). Theirs: the prose says
   the assertion "must" hold (text L111–120) and that a rule "is not applicable" when a premise
   fails (text L343–348), which suggests stuck as well, but there is no explicit statement about
   error configurations in the extraction. (inferred)
4. **Whether the Lemma 3 proof covers recursion through `uncall`** (an inverse procedure calling
   `uncall` of another, or of itself). The conference text only says "case distinction on the
   applied rule"; the extended version [13] has the details. In ours `J_Ctx_Call`/`J_Ctx_Uncall`
   nest freely and the induction is on the derivation, so recursion is covered by the IH; nothing
   comparable can be checked on their side from here.
5. **The stack-based semantics of their §2** (Fig. 3, 5) and their Lemma 1 are needed if one wants
   to state a formal simulation between their configurations and ours; only the prose
   description of the stack elements is available (text L147–150, L176–208).
6. The example program's name wavers (Sum2 / Sum3 / sumMul3 / sumMul2) in the text (text L213,
   L273–274, L275, L282); irrelevant to the comparison but noted by rc-survey.

---

## 6. References

- Ivan Lanese, Germán Vidal. *A Reversible Semantics for Janus.* In C. Aubert, L. Roversi (eds.),
  Reversible Computation, RC 2026, LNCS 16626, pp. 184–200. Springer, 2026.
  doi:10.1007/978-3-032-30839-9_11. Extended version: arXiv:2602.16913 (v2, 2026-02-26; not
  read here — the survey reports its Related Work lacks the R-CORE paragraph, rc-survey
  `docs/forward/core.md` L275–290).
- Toya Makino, Tetsuo Yokoyama. *Small-Step Semantics with Meta-Level Reversibility for a
  Reversible Core Language.* RC 2026, LNCS 16626, pp. 201–218. doi:10.1007/978-3-032-30839-9_12.
  Artifact: this repository (`proofs.v`).
- Pietro Lami, Ivan Lanese, Jean-Bernard Stefani. *A Small-Step Semantics for Janus.* RC 2024,
  LNCS 14680, pp. 105–123. doi:10.1007/978-3-031-62076-8_8 (the context-based semantics both
  RC 2026 papers criticize; text L54–66).
- Luca Paolini, Mauro Piccolo, Luca Roversi. *A Certified Study of a Reversible Programming
  Language.* TYPES 2015, LIPIcs 69, 7:1–7:21 (2018). doi:10.4230/LIPIcs.TYPES.2015.7
  (Matita, big-step Janus; rc-survey `docs/forward/core.md` L329–352).
- `yokoyama-lab/PyJanus`, `coq/` (Rocq 9.1; HEAD `9d30e2f`, 2026-09-05):
  `RevCore.v` (L37–72: `REV_PRIM`, `stmt`, `invert`), `RevSmallStep.v` (L320 `equiv`,
  L344 `step_not_backward_deterministic`, L358 `exit_assertion_collapses`),
  `RevLoopLemma.v` (L77 `conf`, L180 `loop_lemma`, L239 `fstep_backward_det`).
  https://github.com/yokoyama-lab/PyJanus
- rc-survey files used (clone at `/home/claude/ctoken/rc-survey`, HEAD `9f2b6fa2`):
  - `papers/RC2026/RC2026-09-a-reversible-semantics-for-janus.txt` — extraction; lines cited
    above as (text Lnn). Key anchors: abstract L18–22; Loop Lemma criterion L66–69; extended
    version L94; syntax and `x ∉ e` L106–110; no parameters/locals L121–124; stack elements
    L147–150; footnote 1 L171–172; blocks/labels L226–231; `exit` single L240–241; no call
    edges L258–260; inverse procedures L262–268; two labels L285–291; both labels in `if`
    elements L349–352; `ℓ2 = entry(s1)` L394–397; `(ℓ1,s1,ℓ2,s2)` L405–409; Lemma 1 L414–420;
    Lemma 2 L466–467; `ℓ = exit(s2)` L572–578; Definition 1 L586–598; Lemma 3 L601–612;
    §4 equivalence claim L613–617; R-CORE paragraph L624–630; "only other" L632; ref. [15]
    with `pp. xx–yy` L693–695.
  - `cards/RC2026/RC2026-09-a-reversible-semantics-for-janus.md` (card; novelty grading and
    "格上げ推奨").
  - `summaries/RC2026-09-a-reversible-semantics-for-janus.md` (full summary; the three
    differences to keep distinct — control representation, expression evaluation, proof
    location — are in its "当研究での使い道" item).
  - `docs/40_findings.md` L50–62; `docs/50_forward_citations.md` L110–118;
    `docs/40_discrepancies.md` L94; `docs/forward/core.md` L260–290, L329–352, L394,
    L426–435, L490–494, L542–545.
