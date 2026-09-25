# Janus control-token semantics: the rule table

> **要旨（日本語）** R-CORE の制御トークン（•）小ステップ意味論を、除算を除いた Janus コア（配列・参照渡しの手続き引数・local/delocal を含む。2026-09-24〜25 追加）へ拡張したときの全 31 規則を一覧にする。
> Janus の `from e1 do s1 loop s2 until e2` では二つのガードが s1 を挟んで別の地点にあるため、R-CORE の `CC_mid_loop` を from 地点と until 地点に分割する。
> 各規則の前向き・後向き決定性の根拠（ソース／ターゲットのパタンとガードの排他性）と、`proofs.v` の定理との対応を表にする。

Status (2026-09-26): every result named below is proved in `janus/janus.v` (Rocq 9.1.1, 97 audited results, no `Admitted`, `make janus-audit` passes: all `Closed under the global context`).

---

## 1. Scope and syntax

The language is the Janus core of Lanese–Vidal (RC 2026), arrays included, minus the partial
operators `/` and `%`, **plus** call-by-reference procedure parameters and `local`/`delocal`
blocks (neither of which Lanese–Vidal treat). Values are `Z`
(Rocq `Z`), truth is "nonzero". Variables are `X0..X9`, realized as `Fin.t 10` exactly as in
`proofs.v`; arrays are `A0..A3` (`Fin.t 4`), each of fixed length `asize = 8`. A store is the
record `{sv : Vector.t Z 10; sa : Vector.t (Vector.t Z asize) 4}`, so store extensionality stays
a theorem (`store_ext`, `vec_ext`), no axiom.

```
e ::= n                       constant (Z)
    | x                       variable (Fin.t 10)
    | e1 ⊕ e2                 ⊕ ∈ { + , - , * , xor , & , | , < , > , = , != , && , || }
    | a[e]                    array read (Eidx a e); out of bounds reads 0

s ::= skip                                        Sskip
    | x op= e        op ∈ { += , -= , ^= }         Sass x op e     (op : Uadd | Usub | Uxor)
    | s1 ; s2                                      Sseq s1 s2
    | if e1 then s1 else s2 fi e2                  Sif e1 s1 s2 e2
    | from e1 do s1 loop s2 until e2               Sloop e1 s1 s2 e2
    | call p(y1, …, yn)                            Scall p ys      (ys : list var)
    | uncall p(y1, …, yn)                          Suncall p ys
    | local x = e1; s; delocal x = e2              Slocal x e1 s e2
    | a[e1] op= e2                                 Saass a e1 op e2

Γ : pid -> proc      procedure environment, a parameter of the step relation (jstep Γ)
proc = { formals : list var ; body : stmt }
```

**Parameters (by reference).** `call p(ys)` runs `inst (Γ p) ys := rename (ren xs ys) (body)`,
where `xs = formals (Γ p)` and `ren xs ys` maps the i-th formal to the i-th actual and every other
variable to itself (variables that are not formals are globals). With one global store and no
locals, running the renamed body *is* call-by-reference. All four call/uncall rules carry the
decidable side condition

    call_ok (Γ p) ys  :=  |xs| = |ys|  ∧  nodup xs  ∧  nodup ys  ∧  ren xs ys injective on vars(body)

which is Janus's no-aliasing rule: two actuals may not coincide, and an actual may not coincide with
a global the body uses. An aliasing call is stuck (`j_alias_actuals_stuck`,
`j_alias_global_stuck`). The side condition is what keeps well-formedness invariant
(`wf_inst`, via `wf_stmt_rename`); without it a well-formed environment can instantiate `X1 ^= X1`
(`alias_breaks_wf`), and removing it from `J_Call_Enter` makes `wf_cs_step_preserved_cfg` fail
(mutation-checked 2026-09-24). A parameterless procedure is the case `xs = ys = []`
(`inst_no_params`, `call_ok_no_params`), so the previous parameterless core is a special case.

**Local blocks.** `local x = e1; s; delocal x = e2` shadows `x` inside `s`. Entering sets
`x := eval e1` and saves the outer value of `x` in the frame `CS_local x v e1 cs e2`; leaving
requires the delocal assertion `x = eval e2` and restores `v`. Well-formedness requires
`x ∉ e1` and `x ∉ e2` (`wf_Slocal`), and `inv` swaps the two expressions:
`inv (local x = e1; s; delocal x = e2) = local x = e2; inv s; delocal x = e1`.
The saved value is a stack frame, not a history: there is one per *active* block, so the
configuration grows with nesting (and recursion) depth, not with the length of the run.
A failed delocal assertion is a stuck configuration (`j_delocal_mismatch_stuck`) — the first
place where being stuck depends on a data value rather than on a guard.

**Arrays.** `a[e1] op= e2` evaluates the index `e1`; if it is in bounds (`idx`, `0 ≤ i < asize`)
the cell is updated with `op`, otherwise the configuration is stuck
(`j_array_out_of_bounds_stuck`). Well-formedness requires that `a` occur in neither `e1` nor
`e2` (`anf_expr`, `wf_Saass`) — Janus's rule. `inv` inverts `op` and keeps the index.
*Deviation:* an out-of-bounds **read** `a[e]` inside an expression yields 0 instead of being an
error, which keeps `eval` total (as in the rest of this file); making it partial is the same work
as adding `/` and `%` (§7 item 4).

Expression evaluation `eval s e : Z` is **total** (every operator is total on `Z`; the
comparison and logical operators return 0/1). It is **not** reversible, and is not meant to
be: like Lanese–Vidal (their footnote 1), an expression is evaluated in one step. This is a
deliberate departure from R-CORE, where `⊙` is partial and its partiality is what the
determinism proofs have to fight.

Reversible update: `apply_upd op d v` is `d+v`, `d-v`, `d xor v`; `inv_upd` swaps `Uadd ↔ Usub`
and fixes `Uxor`. `apply_upd (inv_upd op) (apply_upd op d v) v = d`, and
`apply_upd op d1 v = apply_upd op d2 v -> d1 = d2` (`apply_upd_injective`).

### Syntactic inverter `inv`

| `s` | `inv s` |
|---|---|
| `skip` | `skip` |
| `x op= e` | `x (inv_upd op)= e` |
| `s1 ; s2` | `inv s2 ; inv s1` |
| `if e1 then s1 else s2 fi e2` | `if e2 then inv s1 else inv s2 fi e1` |
| `from e1 do s1 loop s2 until e2` | `from e2 do inv s1 loop inv s2 until e1` |
| `call p(ys)` | `uncall p(ys)` |
| `uncall p(ys)` | `call p(ys)` |

`inv_involutive : inv (inv s) = s`; `wf_stmt_inv : wf_stmt s -> wf_stmt (inv s)`.
The procedure environment is **not** inverted: `uncall p` runs `inv (Γ p)` forwards, so a single Γ
serves both directions (Lanese–Vidal instead generate a static inverse procedure `p⁻¹`).

---

## 2. Token positions (`cont_stmt`)

A controlled statement is a statement tree with exactly one control token `•`. The constructors
are listed in the order of the Rocq inductive. Notation: `⟨cs⟩` marks the sub-tree that holds the
token; `;▷` / `◁;` point at the side that holds it (as in `proofs.v`).

| Paper-style notation | Constructor | Meaning |
|---|---|---|
| `•s` | `CS_pre s` | about to execute `s` |
| `s•` | `CS_post s` | `s` has just finished (terminal at top level: no rule steps from `s•`) |
| `⟨cs⟩ ;▷ s2` | `CS_seq_L cs s2` | inside the first component of a sequence |
| `s1 ◁; ⟨cs⟩` | `CS_seq_R s1 cs` | inside the second component of a sequence |
| `if e1 then ⟨cs⟩ else s2 fi e2` | `CS_if_then e1 cs s2 e2` | inside the then-branch (e1 was true) |
| `if e1 then s1 else ⟨cs⟩ fi e2` | `CS_if_else e1 s1 cs e2` | inside the else-branch (e1 was false) |
| `from e1 •do s1 loop s2 until e2` | `CS_loop_from e1 s1 s2 e2` | **from-point**: e1 has just been tested (true on entry, false after an iteration), s1 about to start |
| `from e1 do ⟨cs⟩ loop s2 until e2` | `CS_loop_do e1 cs s2 e2` | inside s1 |
| `from e1 do s1 loop s2 •until e2` | `CS_loop_until e1 s1 s2 e2` | **until-point**: s1 has just finished, e2 about to be tested |
| `from e1 do s1 loop ⟨cs⟩ until e2` | `CS_loop_loop e1 s1 cs e2` | inside s2 |
| `call p ⟨cs⟩` | `CS_call p cs` | inside the body `Γ p` |
| `uncall p ⟨cs⟩` | `CS_uncall p cs` | inside the inverted body `inv (Γ p)` |
| `local x = e1 [v] ⟨cs⟩ delocal x = e2` | `CS_local x v e1 cs e2` | inside a local block; `v` is the shadowed outer value of `x` |

Why two loop points where R-CORE has one. R-CORE's `from x loop c until y` tests **both** guards
at one program point, so `CC_mid_loop x c y` suffices. In Janus the two guards are separated by
`s1`: `e1` is tested at the from-point and `e2` at the until-point. Splitting `CC_mid_loop` into
`CS_loop_from` / `CS_loop_until` is exactly what makes the token-position inverter a syntactic
involution:

```
cs_inv (CS_pre s)                 = CS_post (inv s)
cs_inv (CS_post s)                = CS_pre (inv s)
cs_inv (CS_seq_L cs s2)           = CS_seq_R (inv s2) (cs_inv cs)
cs_inv (CS_seq_R s1 cs)           = CS_seq_L (cs_inv cs) (inv s1)
cs_inv (CS_if_then e1 cs s2 e2)   = CS_if_then e2 (cs_inv cs) (inv s2) e1
cs_inv (CS_if_else e1 s1 cs e2)   = CS_if_else e2 (inv s1) (cs_inv cs) e1
cs_inv (CS_loop_from e1 s1 s2 e2) = CS_loop_until e2 (inv s1) (inv s2) e1
cs_inv (CS_loop_do e1 cs s2 e2)   = CS_loop_do e2 (cs_inv cs) (inv s2) e1
cs_inv (CS_loop_until e1 s1 s2 e2)= CS_loop_from e2 (inv s1) (inv s2) e1
cs_inv (CS_loop_loop e1 s1 cs e2) = CS_loop_loop e2 (inv s1) (cs_inv cs) e1
cs_inv (CS_call p cs)             = CS_uncall p (cs_inv cs)
cs_inv (CS_uncall p cs)           = CS_call p (cs_inv cs)
```

`cs_inv_involutive : cs_inv (cs_inv cs) = cs`; `wf_cs_cs_inv : wf_cs cs -> wf_cs (cs_inv cs)`.
(The from-point of `inv (loop)` is "e2 just tested, `inv s1` about to start", which is the
until-point of the original read backwards; with a single mid-point this identity would fail.)

---

## 3. The rules of `jstep Γ`

Configurations are pairs `(cs, s)` with `s : store`. In every rule the store is unchanged unless
the target shows otherwise. Guards: "`e` true" means `eval s e <> 0`, "`e` false" means
`eval s e = 0`. Kind: **data** (changes the store), **control** (tests a guard),
**administrative** (no guard, no store change, only moves the token), **congruence** (steps
inside the hole). Assertion failures (`e2` false at the end of a then-branch, `e1` true after
`s2`, …) have no rule: the configuration is stuck, as in Janus.

| # | Rule | Premise | Source configuration | Target configuration | Kind |
|---|---|---|---|---|---|
| 1 | `J_Skip` | — | `•skip` (`CS_pre Sskip`) | `skip•` (`CS_post Sskip`) | administrative |
| 2 | `J_Asn` | — (total) | `•(x op= e), s` (`CS_pre (Sass x op e)`) | `(x op= e)•, s[x := apply_upd op (s x) (eval s e)]` (`CS_post (Sass x op e)`) | **data** |
| 3 | `J_Seq_Enter` | — | `•(s1 ; s2)` (`CS_pre (Sseq s1 s2)`) | `⟨•s1⟩ ;▷ s2` (`CS_seq_L (CS_pre s1) s2`) | administrative |
| 4 | `J_Seq_Mid` | — | `⟨s1•⟩ ;▷ s2` (`CS_seq_L (CS_post s1) s2`) | `s1 ◁; ⟨•s2⟩` (`CS_seq_R s1 (CS_pre s2)`) | administrative |
| 5 | `J_Seq_Exit` | — | `s1 ◁; ⟨s2•⟩` (`CS_seq_R s1 (CS_post s2)`) | `(s1 ; s2)•` (`CS_post (Sseq s1 s2)`) | administrative |
| 6 | `J_If_True` | `e1` true | `•if e1 then s1 else s2 fi e2` (`CS_pre (Sif e1 s1 s2 e2)`) | `if e1 then ⟨•s1⟩ else s2 fi e2` (`CS_if_then e1 (CS_pre s1) s2 e2`) | control |
| 7 | `J_If_False` | `e1` false | `•if e1 then s1 else s2 fi e2` (`CS_pre (Sif e1 s1 s2 e2)`) | `if e1 then s1 else ⟨•s2⟩ fi e2` (`CS_if_else e1 s1 (CS_pre s2) e2`) | control |
| 8 | `J_Fi_True` | `e2` true | `if e1 then ⟨s1•⟩ else s2 fi e2` (`CS_if_then e1 (CS_post s1) s2 e2`) | `(if e1 then s1 else s2 fi e2)•` (`CS_post (Sif e1 s1 s2 e2)`) | control |
| 9 | `J_Fi_False` | `e2` false | `if e1 then s1 else ⟨s2•⟩ fi e2` (`CS_if_else e1 s1 (CS_post s2) e2`) | `(if e1 then s1 else s2 fi e2)•` (`CS_post (Sif e1 s1 s2 e2)`) | control |
| 10 | `J_Loop_Enter` | `e1` true | `•from e1 do s1 loop s2 until e2` (`CS_pre (Sloop e1 s1 s2 e2)`) | `from e1 •do s1 loop s2 until e2` (`CS_loop_from e1 s1 s2 e2`) | control |
| 11 | `J_Loop_Do` | — | `from e1 •do s1 loop s2 until e2` (`CS_loop_from e1 s1 s2 e2`) | `from e1 do ⟨•s1⟩ loop s2 until e2` (`CS_loop_do e1 (CS_pre s1) s2 e2`) | administrative |
| 12 | `J_Loop_DoDone` | — | `from e1 do ⟨s1•⟩ loop s2 until e2` (`CS_loop_do e1 (CS_post s1) s2 e2`) | `from e1 do s1 loop s2 •until e2` (`CS_loop_until e1 s1 s2 e2`) | administrative |
| 13 | `J_Loop_Exit` | `e2` true | `from e1 do s1 loop s2 •until e2` (`CS_loop_until e1 s1 s2 e2`) | `(from e1 do s1 loop s2 until e2)•` (`CS_post (Sloop e1 s1 s2 e2)`) | control |
| 14 | `J_Loop_Iter1` | `e2` false | `from e1 do s1 loop s2 •until e2` (`CS_loop_until e1 s1 s2 e2`) | `from e1 do s1 loop ⟨•s2⟩ until e2` (`CS_loop_loop e1 s1 (CS_pre s2) e2`) | control |
| 15 | `J_Loop_Iter2` | `e1` false | `from e1 do s1 loop ⟨s2•⟩ until e2` (`CS_loop_loop e1 s1 (CS_post s2) e2`) | `from e1 •do s1 loop s2 until e2` (`CS_loop_from e1 s1 s2 e2`) | control |
| 16 | `J_Call_Enter` | `call_ok (Γ p) ys` | `•call p(ys)` (`CS_pre (Scall p ys)`) | `call p(ys) ⟨•b⟩`, `b = inst (Γ p) ys` (`CS_call p ys (CS_pre b)`) | administrative |
| 17 | `J_Call_Exit` | `call_ok (Γ p) ys` | `call p(ys) ⟨b•⟩` (`CS_call p ys (CS_post b)`) | `(call p(ys))•` (`CS_post (Scall p ys)`) | administrative |
| 18 | `J_Uncall_Enter` | `call_ok (Γ p) ys` | `•uncall p(ys)` (`CS_pre (Suncall p ys)`) | `uncall p(ys) ⟨•(inv b)⟩` (`CS_uncall p ys (CS_pre (inv b))`) | administrative |
| 19 | `J_Uncall_Exit` | `call_ok (Γ p) ys` | `uncall p(ys) ⟨(inv b)•⟩` (`CS_uncall p ys (CS_post (inv b))`) | `(uncall p(ys))•` (`CS_post (Suncall p ys)`) | administrative |
| 20 | `J_Ctx_Seq_L` | `(cs, s) → (cs', s')` | `⟨cs⟩ ;▷ s2, s` (`CS_seq_L cs s2`) | `⟨cs'⟩ ;▷ s2, s'` (`CS_seq_L cs' s2`) | congruence |
| 21 | `J_Ctx_Seq_R` | `(cs, s) → (cs', s')` | `s1 ◁; ⟨cs⟩, s` (`CS_seq_R s1 cs`) | `s1 ◁; ⟨cs'⟩, s'` (`CS_seq_R s1 cs'`) | congruence |
| 22 | `J_Ctx_If_Then` | `(cs, s) → (cs', s')` | `if e1 then ⟨cs⟩ else s2 fi e2, s` (`CS_if_then e1 cs s2 e2`) | `if e1 then ⟨cs'⟩ else s2 fi e2, s'` (`CS_if_then e1 cs' s2 e2`) | congruence |
| 23 | `J_Ctx_If_Else` | `(cs, s) → (cs', s')` | `if e1 then s1 else ⟨cs⟩ fi e2, s` (`CS_if_else e1 s1 cs e2`) | `if e1 then s1 else ⟨cs'⟩ fi e2, s'` (`CS_if_else e1 s1 cs' e2`) | congruence |
| 24 | `J_Ctx_Loop_Do` | `(cs, s) → (cs', s')` | `from e1 do ⟨cs⟩ loop s2 until e2, s` (`CS_loop_do e1 cs s2 e2`) | `from e1 do ⟨cs'⟩ loop s2 until e2, s'` (`CS_loop_do e1 cs' s2 e2`) | congruence |
| 25 | `J_Ctx_Loop_Loop` | `(cs, s) → (cs', s')` | `from e1 do s1 loop ⟨cs⟩ until e2, s` (`CS_loop_loop e1 s1 cs e2`) | `from e1 do s1 loop ⟨cs'⟩ until e2, s'` (`CS_loop_loop e1 s1 cs' e2`) | congruence |
| 26 | `J_Ctx_Call` | `(cs, s) → (cs', s')` | `call p(ys) ⟨cs⟩, s` (`CS_call p ys cs`) | `call p(ys) ⟨cs'⟩, s'` (`CS_call p ys cs'`) | congruence |
| 27 | `J_Ctx_Uncall` | `(cs, s) → (cs', s')` | `uncall p(ys) ⟨cs⟩, s` (`CS_uncall p ys cs`) | `uncall p(ys) ⟨cs'⟩, s'` (`CS_uncall p ys cs'`) | congruence |
| 28 | `J_Local_Enter` | — | `•local x = e1; s; delocal x = e2`, `σ` | `CS_local x (σ x) e1 (CS_pre s) e2`, `σ[x ↦ eval σ e1]` | data |
| 29 | `J_Local_Exit` | `σ x = eval σ e2` | `CS_local x v e1 (CS_post s) e2`, `σ` | `(local x = e1; s; delocal x = e2)•`, `σ[x ↦ v]` | data |
| 30 | `J_Ctx_Local` | `(cs, s) → (cs', s')` | `CS_local x v e1 cs e2, s` | `CS_local x v e1 cs' e2, s'` | congruence |
| 31 | `J_AAsn` | `idx (eval σ e1) = Some i` | `•a[e1] op= e2`, `σ` | `(a[e1] op= e2)•`, `σ[a[i] ↦ σ(a[i]) op eval σ e2]` | data |

Where `→` in a premise abbreviates `jstep Γ` for the same Γ. Counting: 1 data, 8 control,
10 administrative, 8 congruence = 27, plus the local rules 28–30 (2 data, 1 congruence) = 30, plus the array rule 31 (data) = 31.
Partial injectivity of 31 (`aasn_step_injective`): `a ∉ e1` makes the index a function of the
post-store (the update only touches `a`), and `a ∉ e2` plus injectivity of `op=` recovers the cell;
without `a ∉ e2`, `A0[0] ^= A0[0]` sends two stores to one (`aasn_bwd_needs_anf`).
Partial injectivity of 28: the saved `v` fixes the pre-store at `x` and the update leaves the rest
(`local_enter_injective`; no well-formedness needed). Of 29: the restored value fixes `v`, and the
delocal assertion fixes the pre-store at `x` provided `x ∉ e2` (`local_exit_injective`); without
`x ∉ e2`, `delocal x = x` is vacuous and two configurations differing only in the local `x` step to
the same one (`local_bwd_needs_nf`). The side condition of rules 16–19 depends only on the
syntax (`Γ p` and `ys`), never on the store, so these rules stay administrative.

Two structural facts carry most of the determinism proofs, exactly as `no_step_from_at_post` and
`no_step_to_at_pre` do in `proofs.v`:

- `no_step_from_post : ~ jstep Γ (CS_post s, σ) cfg` — no rule has `s•` as its source, and
  `CS_post` has no hole for a congruence rule to enter.
- `no_step_to_pre : ~ jstep Γ cfg (CS_pre s, σ)` — no rule has `•s` as its target.

---

## 4. How each rule derives from R-CORE (`exec_ss` in `proofs.v`, L224–256)

| R-CORE `exec_ss` constructor | Janus `jstep` rule(s) | Change |
|---|---|---|
| `S_Asn` (`eval_expr s e = Some v_e`, `odot (s x) v_e = Some v_new`) | `J_Asn` | `⊙` is partial (undefined unless one operand is `nil` or both are equal); `apply_upd op` is total on `Z`, so the rule has **no premise**. `x ^= e` becomes `x op= e` with three operators. |
| `S_LoopEnter` (`s x <> Vnil`; `•loop → mid_loop`) | `J_Loop_Enter` (`e1` true; `•loop → loop_from`) | the entry guard is an arbitrary expression, not a variable; target is the from-point instead of the single mid-point |
| `S_LoopExit` (`s y <> Vnil`; `mid_loop → loop•`) | `J_Loop_Exit` (`e2` true; `loop_until → loop•`) | source is the until-point |
| `S_LoopIter1` (`s y = Vnil`; `mid_loop → in_loop(•c)`) | `J_Loop_Iter1` (`e2` false; `loop_until → loop_loop(•s2)`) | R-CORE's body `c` is Janus's `s2` |
| `S_LoopIter2` (`s x = Vnil`; `in_loop(c•) → mid_loop`) | `J_Loop_Iter2` (`e1` false; `loop_loop(s2•) → loop_from`) | target is the from-point |
| `S_Seq_Enter` / `S_Seq_Mid` / `S_Seq_Exit` | `J_Seq_Enter` / `J_Seq_Mid` / `J_Seq_Exit` | identical (R-CORE's oriented Eq. (7) congruence, `cong_iff_admin`) |
| `S_Ctx_Seq_L` / `S_Ctx_Seq_R` | `J_Ctx_Seq_L` / `J_Ctx_Seq_R` | identical |
| `S_Ctx_Loop` (`in_loop`) | `J_Ctx_Loop_Loop` | R-CORE's single body position is Janus's `s2` position |
| — | `J_Loop_Do`, `J_Loop_DoDone`, `J_Ctx_Loop_Do` | **new**: the `s1` segment between the two guards (R-CORE has `s1 = skip`) |
| — | `J_Skip` | **new**: R-CORE has no `skip` (`from x loop c until y` has an implicit empty do-part) |
| — | `J_If_True`, `J_If_False`, `J_Fi_True`, `J_Fi_False`, `J_Ctx_If_Then`, `J_Ctx_If_Else` | **new**: R-CORE has no conditional |
| — | `J_Call_Enter`, `J_Call_Exit`, `J_Uncall_Enter`, `J_Uncall_Exit`, `J_Ctx_Call`, `J_Ctx_Uncall` | **new**: R-CORE has no procedures; `uncall` runs `inv (Γ p)` forwards |

**R-CORE loops as Janus loops (embedding remark).** At the control level, R-CORE's
`from x loop c until y` is Janus's `from (x ≠ nil) do skip loop c until (y ≠ nil)`, and
`CC_mid_loop x c y` corresponds to the *pair* `CS_loop_from` / `CS_loop_until` of the image,
connected by the three administrative steps `J_Loop_Do ; J_Ctx_Loop_Do(J_Skip) ; J_Loop_DoDone`.
So one R-CORE step `S_LoopEnter` is simulated by `J_Loop_Enter` followed by those three steps,
and one `S_LoopIter2` by `J_Loop_Iter2` followed by them; `S_LoopExit` / `S_LoopIter1` map to
`J_Loop_Exit` / `J_Loop_Iter1` one-to-one; the sequence and congruence rules map one-to-one.
The value domains differ (binary trees over `nil` with the partial `⊙`, versus `Z` with total
updates), so the embedding as a **formal** theorem needs a value translation and is deferred to
Sect. 7; the remark here is about control only.

---

## 5. Per-rule partial injectivity

Forward determinism: from a fixed source `(cs, s)` at most one rule applies and it has at most one
target. Backward determinism: from a fixed target `(cs', s')` at most one rule applies and it has at
most one source, **provided** the configurations are well-formed (Sect. 6). The table names, for
each rule, the pattern that isolates it and the guard that separates it from the other rule(s)
sharing that pattern. Store equalities are automatic for every rule but `J_Asn`, because the store
is carried unchanged.

| Rule | Forward: why the source determines the step | Backward: why the target determines the step |
|---|---|---|
| `J_Skip` | source `•skip`: only rule on `CS_pre Sskip` | target `skip•`: only rule targeting `CS_post Sskip` |
| `J_Asn` | source `•(x op= e)`: only rule on `CS_pre (Sass …)`; `apply_upd`/`eval` are functions | target `(x op= e)•, s'`: only rule targeting `CS_post (Sass …)`. Two sources `s1, s2` with `s1[x:=…] = s2[x:=…]` agree off `x` (`update_injective_off_x`); with `x ∉ e` (`nf_expr`) `eval s1 e = eval s2 e` (`eval_agree`); then `apply_upd_injective` gives `s1 x = s2 x`, and `store_ext` closes. **This is the only rule that needs well-formedness**, and the only one that can merge two pre-stores. Packaged as `asn_step_injective`. |
| `J_Seq_Enter` | source `•(s1;s2)`: unique | target `⟨•s1⟩ ;▷ s2`: shared pattern with `J_Ctx_Seq_L` (target `⟨cs'⟩ ;▷ s2`), excluded because `cs' = •s1` contradicts `no_step_to_pre` |
| `J_Seq_Mid` | source `⟨s1•⟩ ;▷ s2`: shared with `J_Ctx_Seq_L` (source `⟨cs⟩ ;▷ s2`), excluded by `no_step_from_post` | target `s1 ◁; ⟨•s2⟩`: shared with `J_Ctx_Seq_R`, excluded by `no_step_to_pre` |
| `J_Seq_Exit` | source `s1 ◁; ⟨s2•⟩`: shared with `J_Ctx_Seq_R`, excluded by `no_step_from_post` | target `(s1;s2)•`: unique |
| `J_If_True` | source `•if…`: shared with `J_If_False`; separated by `e1` true vs `e1` false in the same store | target `if e1 then ⟨•s1⟩ …`: shared with `J_Ctx_If_Then`, excluded by `no_step_to_pre` |
| `J_If_False` | as above, `e1` false | target `… else ⟨•s2⟩ fi e2`: shared with `J_Ctx_If_Else`, excluded by `no_step_to_pre` |
| `J_Fi_True` | source `if e1 then ⟨s1•⟩ …`: shared with `J_Ctx_If_Then`, excluded by `no_step_from_post` | target `(if…)•`: **shared with `J_Fi_False`** (same target, same store); separated by `e2` true vs false, and the source branch (`CS_if_then` vs `CS_if_else`) follows from the guard |
| `J_Fi_False` | source `… else ⟨s2•⟩ fi e2`: shared with `J_Ctx_If_Else`, excluded by `no_step_from_post` | as above, `e2` false |
| `J_Loop_Enter` | source `•from…`: unique (the only rule on `CS_pre (Sloop …)`) | target `loop_from`: **shared with `J_Loop_Iter2`** (same target, same store); separated by `e1` true (Enter) vs `e1` false (Iter2) |
| `J_Loop_Do` | source `loop_from`: unique | target `loop_do(•s1)`: shared with `J_Ctx_Loop_Do`, excluded by `no_step_to_pre` |
| `J_Loop_DoDone` | source `loop_do(s1•)`: shared with `J_Ctx_Loop_Do`, excluded by `no_step_from_post` | target `loop_until`: unique |
| `J_Loop_Exit` | source `loop_until`: **shared with `J_Loop_Iter1`**; separated by `e2` true vs false | target `(from…)•`: unique |
| `J_Loop_Iter1` | as above, `e2` false | target `loop_loop(•s2)`: shared with `J_Ctx_Loop_Loop`, excluded by `no_step_to_pre` |
| `J_Loop_Iter2` | source `loop_loop(s2•)`: shared with `J_Ctx_Loop_Loop`, excluded by `no_step_from_post` | target `loop_from`: shared with `J_Loop_Enter`, separated by `e1` (see above) |
| `J_Call_Enter` | source `•call p`: unique | target `call p ⟨•(Γ p)⟩`: shared with `J_Ctx_Call`, excluded by `no_step_to_pre` |
| `J_Call_Exit` | source `call p ⟨(Γ p)•⟩`: shared with `J_Ctx_Call`, excluded by `no_step_from_post` | target `(call p)•`: unique |
| `J_Uncall_Enter` | source `•uncall p`: unique | target `uncall p ⟨•(inv (Γ p))⟩`: shared with `J_Ctx_Uncall`, excluded by `no_step_to_pre` |
| `J_Uncall_Exit` | source `uncall p ⟨(inv (Γ p))•⟩`: shared with `J_Ctx_Uncall`, excluded by `no_step_from_post` | target `(uncall p)•`: unique |
| `J_Ctx_*` (8 rules) | the outer constructor fixes the rule; the base rule sharing the source pattern is excluded by `no_step_from_post`; the inner step is unique by IH | the outer constructor fixes the rule; the base rule sharing the target pattern is excluded by `no_step_to_pre`; the inner source is unique by IH (backward IH needs `wf_cs` of the inner configuration, obtained by inverting `wf_cs` of the outer one) |

Pairs sharing a **source** pattern, and the separating guard: `J_If_True`/`J_If_False` (`e1`);
`J_Loop_Exit`/`J_Loop_Iter1` (`e2`); every base-vs-congruence pair (`no_step_from_post`).
Pairs sharing a **target** pattern: `J_Fi_True`/`J_Fi_False` (`e2`, evaluated in the common
target store, which equals both source stores); `J_Loop_Enter`/`J_Loop_Iter2` (`e1`, likewise);
every base-vs-congruence pair (`no_step_to_pre`). `J_Asn` shares no pattern with anything but
needs `x ∉ e` to be injective on stores.

Because the guards are evaluated in a store that the rule does not change, "true vs false in the
same store" is a genuine dichotomy on `Z` (`eval s e <> 0` vs `eval s e = 0`); no partiality
argument is needed anywhere, in contrast to `proofs.v` where the `S_Asn`/`S_Asn` case has to
thread `eval_expr … = Some …` and `odot … = Some …` equations.

---

## 6. Well-formedness and the theorems

```
nf_expr x e     x does not occur in e
wf_stmt s       every assignment  x op= e  in s has  nf_expr x e
wf_penv Γ       forall p, wf_stmt (Γ p)
wf_cs cs        every statement embedded in cs is wf_stmt (and recursively wf_cs in the hole)
```

All three are decidable: `nf_expr_dec`, `wf_stmt_dec`, `wf_cs_dec` (as `nf_expr_dec`,
`wf_cmd_dec`, `wf_cc_dec` in `proofs.v`).

| Result in `janus/janus.v` | Statement | Ancestor in `proofs.v` |
|---|---|---|
| `jstep_deterministic` | `jstep Γ cfg cfg1 -> jstep Γ cfg cfg2 -> cfg1 = cfg2` — **no hypothesis** | `ss_step_deterministic` (L368) |
| `wf_cs_step_preserved` | `wf_penv Γ -> jstep Γ (cs,s) (cs',s') -> wf_cs cs -> wf_cs cs'` | `wf_cc_step_preserved` (L539) |
| `wf_cs_step_reflected` | `wf_penv Γ -> jstep Γ (cs,s) (cs',s') -> wf_cs cs' -> wf_cs cs` | `wf_cc_step_reflected` (L2581) |
| `jstep_bwd_deterministic` | `wf_cs (fst cfg1) -> wf_cs (fst cfg2) -> jstep Γ cfg1 cfg -> jstep Γ cfg2 cfg -> cfg1 = cfg2` | `ss_bwd_deterministic` (L582) |
| `jstep_bwd_deterministic_tgt` | `wf_penv Γ -> wf_cs (fst cfg) -> jstep Γ cfg1 cfg -> jstep Γ cfg2 cfg -> cfg1 = cfg2` (via reflection) | `ss_bwd_deterministic_tgt` (L2605) |
| `asn_step_injective` | the `J_Asn` case of backward determinism, isolated: two `J_Asn` steps into the same `(CS_post (Sass x op e), s')` with `nf_expr x e` have the same source | the `S_Asn`/`S_Asn` bullet inside `ss_bwd_deterministic` (not a separate lemma there) |
| `apply_upd_injective` | `apply_upd op d1 v = apply_upd op d2 v -> d1 = d2` | `odot_left_injective` (L289) |
| `inv_involutive`, `wf_stmt_inv` | `inv (inv s) = s`; `wf_stmt s -> wf_stmt (inv s)` | `inv_involutive` (L2142), `wf_cmd_inv` (L2265) |
| `cs_inv_involutive`, `wf_cs_cs_inv` | `cs_inv (cs_inv cs) = cs`; `wf_cs cs -> wf_cs (cs_inv cs)` | `cc_inv_involutive` (L4757), `wf_cc_cc_inv` (L4940) |
| `inv_step_reverses` | `wf_cs cs -> jstep Γ (cs,s) (cs',s') -> jstep Γ (cs_inv cs', s') (cs_inv cs, s)` — a forward step of a program is a backward step of its inverse at the `cs_inv`-mirrored token position. `wf_cs cs` is needed only for the `J_Asn` case (`eval s' e = eval s e` requires `nf_expr x e`); no `wf_penv` | `inv_step_reverses` (L4772; hypothesis `wf_cc (fst cfg)`) |
| `inv_step_reverses_iff` | `wf_cs cs -> wf_cs cs' -> (jstep Γ (cs,s) (cs',s') <-> jstep Γ (cs_inv cs', s') (cs_inv cs, s))` — with both endpoints well-formed, a step is a forward step iff the reversed step of the inverse program is (the converse direction is `inv_step_reverses` applied to the inverse, via `wf_cs_cs_inv` and `cs_inv_involutive`) | — |
| `bstep` | `bstep Γ cfg cfg' := jstep Γ cfg' cfg` | `bstep` (L4950) |
| `bstep_deterministic` | `wf_penv Γ -> wf_cs (fst cfg) -> bstep Γ cfg cfg1 -> bstep Γ cfg cfg2 -> cfg1 = cfg2` | `bstep_deterministic` (L4954) |
| `bstep_is_fwd_of_inv` | `wf_cs cs -> wf_cs cs' -> (bstep Γ (cs,s) (cs',s') <-> jstep Γ (cs_inv cs, s) (cs_inv cs', s'))` — the backward relation is the forward relation of the inverted program | `bstep_fun` / `bstep_fun_correct` (L4964–4970) state this through the executable stepper |
| `step_fun`, `step_fun_correct` | `step_fun Γ cs s = Some (cs', s') <-> jstep Γ (cs, s) (cs', s')` — the relation is executable (`step_fun_sound` / `step_fun_complete` are the two directions; `step_fun_post_is_none` checks that `s•` is stuck) | `step_fun` (L4514), `step_fun_correct` (L4560) |
| `update_cancel` | `update (update s x v) x (s x) = s` — restoring the old value at `x` undoes an update (used in the `J_Asn` case of `inv_step_reverses`) | — |
| `apply_upd_inv` | `apply_upd (inv_upd op) (apply_upd op d v) v = d` — the inverted operator undoes the update; with `inv_upd_involutive` this is why `inv (Sass x op e)` reverses `J_Asn` | — |
| `j_example_run` (Example) | `jnsteps Γ0 7 (CS_pre ex_prog, zero_store) (CS_post ex_prog, ex_final)` — a 7-step run of `ex_prog = X0 += 1; if X0 then X1 ^= 3 else skip fi X0` from the zero store to `X0 = 1, X1 = 3` (`J_Seq_Enter`; `J_Asn` under `J_Ctx_Seq_L`; `J_Seq_Mid`; `J_If_True` under `J_Ctx_Seq_R`; `J_Asn` under `J_Ctx_Seq_R`/`J_Ctx_If_Then`; `J_Fi_True` under `J_Ctx_Seq_R`; `J_Seq_Exit`) | — |
| `wf_stmt_rename`, `wf_inst` | a renaming injective on `vars st` preserves `wf_stmt`; hence `wf_penv Γ -> call_ok (Γ p) ys = true -> wf_stmt (inst (Γ p) ys)` | — (R-CORE has no procedures) |
| `inst_no_params`, `call_ok_no_params` | formals `[]`, actuals `[]`: the body runs unchanged and the call is accepted (conservative extension) | — |
| `j_call_by_reference`, `j_uncall_undoes_call` (Examples) | `X2 += 5; call 0(X3, X2)` with `proc 0(a, b) = a += b` sets `X3 = 5`; `uncall 0(X3, X2)` restores `X3 = 0` (computed with `run` over `step_fun`) | — |
| `j_alias_actuals_stuck`, `j_alias_global_stuck`, `alias_breaks_wf` (Examples) | `call 0(X2, X2)` and `call 1(X1)` (with `proc 1(a) = a ^= X1`) are stuck; the latter would instantiate the ill-formed `X1 ^= X1` | — |
| `local_enter_injective`, `local_exit_injective` | partial injectivity of rules 28 and 29 (the latter under `x ∉ e2`) | — |
| `j_local_shadows`, `j_local_inverse` (Examples) | `local X0 = X1+1; X2 += X0; delocal X0 = X1+1` from `X0 = 7, X1 = 3` ends with `X2 = 4` and the outer `X0 = 7` restored; the inverse block restores the start store | — |
| `j_delocal_mismatch_stuck`, `j_delocal_mismatch_no_step`, `local_bwd_needs_nf` (Examples) | a failed delocal is stuck; `delocal x = x` breaks backward determinism, so `wf_cs` must require `x ∉ e2` | — |
| `aasn_step_injective`, `eval_aupdate_invariant`, `eval_aagree`, `aupdate_cancel` | partial injectivity of rule 31; an update of `a` does not change an `a`-free expression; undoing the cell update | — |
| `j_array_run`, `j_array_inverse`, `j_array_out_of_bounds_stuck`, `aasn_bwd_needs_anf` (Examples) | `X0 += 3; A0[X0] += 5; A0[X0+1] ^= A0[X0]` and its inverse; index 8 and −1 are stuck; `a ∉ e2` is necessary | — |
| `exec`, `loop_from`, `loop_until` | big-step semantics (mutual inductive; the two loop relations start at the from-point and the until-point) | `ds` (big-step of the paper) |
| `exec_iff_jstar` | `exec Γ s σ σ' <-> jstar Γ (•s, σ) (s•, σ')` — the big-step semantics is exactly the runs of `jstep` from entry to exit. `→` by mutual induction (`exec_jstar_mut`, lifting runs through contexts with `jstar_lift`); `←` via the remaining-execution relation `cexec` on token positions, preserved backwards by every step (`cexec_step_back`, using `top_step`) | `semantic_equivalence` (R-CORE, ds ↔ ss) |
| `exec_deterministic` | big-step determinism, derived from `jstep_deterministic` and terminality of `s•` (`jstar_deterministic_terminal`) | `ds_deterministic` |
| `exec_inv`, `exec_inv_iff` | `wf_penv Γ -> wf_stmt s -> (exec Γ s σ σ' <-> exec Γ (inv s) σ' σ)` — correctness of the program inverter for the big-step semantics, **derived** from step-level reversibility: a run reverses position by position into a run of the inverse (`jstar_inv`, from `inv_step_reverses` and `wf_cs_step_preserved`) | — |
| `run_jstar`, `exec_call_by_reference`, `exec_call_inverted` | the bounded runner produces `jstar` runs; a call-by-reference program as a big-step judgement, and its inverse via `exec_inv` | — |
| `nf_expr_dec`, `anf_expr_dec`, `wf_stmt_dec`, `wf_cs_dec` | decision procedures | `nf_expr_dec` (L419), `wf_cmd_dec` (L444), `wf_cc_dec` (L4365) |

Why `wf_penv Γ` appears where `proofs.v` had nothing: `J_Call_Enter` and `J_Uncall_Enter` bring
`inst (Γ p) ys` (resp. its inverse) *into* the controlled statement, so preservation needs the
instantiated bodies to be well-formed, and `J_Call_Exit` / `J_Uncall_Exit` take them out again, so
reflection needs the same. `wf_penv Γ` (every body well-formed) gives this through `wf_inst`,
which needs `call_ok`: renaming preserves `x ∉ e` only when it is injective on the body's
variables (`wf_stmt_rename`). Everything else is structural, as before; `jstep_deterministic`,
`jstep_bwd_deterministic` and `inv_step_reverses` needed only the call-rule premises threaded
through (`J_Uncall_*` are stated with `inv (inst …)`, so `rename_inv` is not used there; it is
proved for the record).

Why there is no reachability hypothesis anywhere: the only rule that can identify two distinct
predecessors is `J_Asn`, and only through `x ∈ e`; `wf_cs` excludes exactly that and is preserved
along runs (`wf_cs_step_preserved`), so backward determinism from a well-formed start is a
corollary rather than a separate theorem (cf. `ss_bwd_deterministic_reachable`, L3275).

---

## 7. Exclusions and next steps

Excluded from this core, in the order they should be added:

1. ~~**Arrays**~~ — **done 2026-09-25** (§1 "Arrays", rule 31).
2. ~~**`local x = e … delocal x = e`**~~ — **done 2026-09-24** (§1 "Local blocks", rules 28–30).
3. ~~**Procedure parameters**~~ — **done 2026-09-24** (§1 "Parameters"): `Γ : pid -> proc`,
   `CS_call`/`CS_uncall` record the actuals, the body is instantiated by renaming, and the
   no-aliasing rule is the decidable side condition `call_ok`.
4. **`/` and `%`**. Reintroduce partiality into `eval`, and with it the `Some`/`None` bookkeeping
   that the present development avoids.

Independent of the language extensions:

5. **`bstep_fun` and extraction.** `step_fun` / `step_fun_correct` are done (Sect. 6). What
   remains is `bstep_fun` (as in `proofs.v` L4964–4970: `step_fun` on the `cs_inv`-mirrored
   configuration, correct by `bstep_is_fwd_of_inv`) and adding `janus.v` to `extraction.v`, so
   the Janus semantics can be *run* (a small reversible debugger) rather than only reasoned about.
6. **The R-CORE embedding as a formal statement** (Sect. 4): a translation of `cmd` into `stmt`
   and of `cont_cmd` into `cont_stmt` (with `CC_mid_loop ↦ CS_loop_from` or `CS_loop_until`
   chosen by phase), plus a value translation, such that every `exec_ss` step is simulated by
   one `jstep` step followed by 0 or 3 administrative steps.
7. **A CFG / fss-style layer for Janus**, so that Lanese–Vidal's static Lemma 2
   (`flow⁻¹(s) = flow(I[[s]])`) can be stated on our side and compared rule by rule with
   `inv_step_reverses` (`LANESE_VIDAL.md` §3); the comparison needs the paper's rule figures
   (`LANESE_VIDAL.md` §5).
8. ~~**A big-step semantics and its equivalence with `jstep`**~~ — **done 2026-09-26**
   (`exec_iff_jstar`; §6).
7. **Connecting to the paper's `fss` layer**: a labelled-flowchart (CFG) semantics of Janus in the
   style of `fstep`/`pstep`, and the analogue of `semantic_equivalence_ss_fss`. This is also where
   a formal comparison with the Lanese–Vidal program-counter semantics would live; see
   `LANESE_VIDAL.md`.
8. ~~**Big-step semantics and `semantic_equivalence`**~~ — **done 2026-09-26** (`exec_iff_jstar`,
   with `exec_deterministic` and `exec_inv` as corollaries).
