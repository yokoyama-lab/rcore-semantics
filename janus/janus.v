(*
  janus/janus.v -- A control-token small-step semantics for a Janus core
  language, mechanized in Rocq 9.1.1, extending the R-CORE development of
  ../proofs.v (Makino & Yokoyama, "Small-Step Semantics with Meta-Level
  Reversibility for a Reversible Core Language", RC 2026, paper #11).

  Purpose.  Lanese & Vidal (RC 2026, paper #9) ask of the control-token
  style of small-step semantics "whether it scales to more complex
  languages like Janus".  This file answers the question for the Janus
  CORE: the single-token controlled-statement construction of proofs.v is
  carried over to a language with

      skip, reversible updates (+=, -=, ^=), sequencing,
      if e1 then s1 else s2 fi e2,
      from e1 do s1 loop s2 until e2,
      call p(ys) / uncall p(ys)   with call-by-reference parameters,
                          against a procedure environment Gamma,

  and the same package of theorems is re-established, axiom-free:

      forward determinism            [jstep_deterministic]
      invariance of well-formedness  [wf_cs_step_preserved],
                                     [wf_cs_step_reflected]
      backward determinism           [jstep_bwd_deterministic],
                                     [jstep_bwd_deterministic_tgt],
                                     [bstep_deterministic]
      meta-level reversibility       [inv_step_reverses],
        via the syntactic inverter   [inv_step_reverses_iff],
                                     [bstep_is_fwd_of_inv]
      executable semantics           [step_fun_correct]

  Scope.  This is Janus WITHOUT arrays, without local/delocal, and
  without the division-like operators / and % (whose partiality is
  orthogonal to the control-token question).  Procedures take
  call-by-reference parameters (section 3a); the no-aliasing rule is the
  decidable side condition [call_ok] of the call/uncall rules.  Values
  are unbounded integers (Z).  All expression evaluation is therefore
  total, and the only partiality of the semantics is in the loop guards
  and the call side condition.

  Design.  R-CORE's [from x loop c until y] is the Janus loop
  [from x do skip loop c until y].  R-CORE needs a single "mid-loop" token
  position because both of its guards are tested at the same program
  point.  Janus tests the entry/iterate guard e1 at the FROM-point (just
  before s1) and the exit/iterate guard e2 at the UNTIL-point (just after
  s1, before s2), so the controlled statements carry two token positions,
  [CS_loop_from] and [CS_loop_until].  Splitting the point is what makes
  the controlled-statement inverter [cs_inv] a purely syntactic
  involution: inverting a loop swaps the two points, exactly as the
  program inverter swaps the two guards.

  Relation to proofs.v.  Definitions and proof scripts mirror proofs.v
  section by section (store lemmas via [Vector.eq_nth_iff], the
  no-step lemmas, the [kill_post]/[use_IH] tactics, the S_Asn backward
  case via [update_injective_off_x]/[update_value_at_x]/[eval_agree]/
  [store_ext]).  This file is self-contained: it does not import
  proofs.v, and it introduces no axiom (see the audit section at the end,
  enforced by tools/audit.sh with SRC=janus/janus.v).

  Tested with Rocq 9.1.1.
*)

From Stdlib Require Import ZArith Lia List Bool.
From Stdlib Require Import Vectors.Vector Vectors.Fin Vectors.VectorSpec.
Set Implicit Arguments.

(* ================================================================= *)
(* 1. Syntax                                                          *)
(* ================================================================= *)

(* Ten variables X0..X9, as in proofs.v: [var := Fin.t 10]. *)
Definition var := Fin.t 10.

Definition X0 : var := Fin.F1.
Definition X1 : var := Fin.FS Fin.F1.
Definition X2 : var := Fin.FS (Fin.FS Fin.F1).
Definition X3 : var := Fin.FS (Fin.FS (Fin.FS Fin.F1)).
Definition X4 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Definition X5 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Definition X6 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
Definition X7 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))).
Definition X8 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))).
Definition X9 : var := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))).

(* Stores: a total map from the ten variables to integers. *)
Definition store := Vector.t Z 10.

Definition lookup (s : store) : var -> Z := Vector.nth (n:=10) s.
Coercion lookup : store >-> Funclass.

Definition update (s : store) (x : var) (v : Z) : store :=
  Vector.replace s x v.


Local Open Scope Z_scope.

(* Binary operators.  Band/Bor are bitwise; Bland/Blor are logical and the
   comparisons return 1 or 0.  Truth is "nonzero". *)
Inductive binop : Type :=
  | Bplus | Bminus | Btimes | Bxor | Band | Bor
  | Blt | Bgt | Beq | Bneq | Bland | Blor.

Inductive expr : Type :=
  | Econst (z : Z)
  | Evar   (x : var)
  | Ebin   (op : binop) (e1 e2 : expr).

(* Reversible update operators  x op= e. *)
Inductive updop : Type := Uadd | Usub | Uxor.

Definition apply_upd (op : updop) (d v : Z) : Z :=
  match op with
  | Uadd => d + v
  | Usub => d - v
  | Uxor => Z.lxor d v
  end.

Definition inv_upd (op : updop) : updop :=
  match op with
  | Uadd => Usub
  | Usub => Uadd
  | Uxor => Uxor
  end.

Definition pid := nat.

(* Sif e1 s1 s2 e2   =  if e1 then s1 else s2 fi e2
   Sloop e1 s1 s2 e2 =  from e1 do s1 loop s2 until e2 *)
Inductive stmt : Type :=
  | Sskip
  | Sass    (x : var) (op : updop) (e : expr)
  | Sseq    (s1 s2 : stmt)
  | Sif     (e1 : expr) (s1 s2 : stmt) (e2 : expr)
  | Sloop   (e1 : expr) (s1 s2 : stmt) (e2 : expr)
  | Scall   (p : pid) (args : list var)
  | Suncall (p : pid) (args : list var).

(* A procedure: its formal parameters and its body.  Parameters are passed
   by reference: [call p ys] runs the body with each formal renamed to the
   corresponding actual (see [ren] and [rename], section 3a).  A body may
   also read and write variables that are not formals: those are the
   globals. *)
Local Infix "+++" := List.app (right associativity, at level 60).

Record proc : Type := mkproc { formals : list var; body : stmt }.

(* Procedure environment Gamma.  It is an explicit parameter of the step
   relation throughout (never a section Parameter). *)
Definition penv := pid -> proc.

(* ================================================================= *)
(* 2. Expression evaluation (total)                                    *)
(* ================================================================= *)

Definition b2z (b : bool) : Z := if b then 1 else 0.

Definition apply_bin (op : binop) (a b : Z) : Z :=
  match op with
  | Bplus  => a + b
  | Bminus => a - b
  | Btimes => a * b
  | Bxor   => Z.lxor a b
  | Band   => Z.land a b
  | Bor    => Z.lor a b
  | Blt    => b2z (Z.ltb a b)
  | Bgt    => b2z (Z.ltb b a)
  | Beq    => b2z (Z.eqb a b)
  | Bneq   => b2z (negb (Z.eqb a b))
  | Bland  => b2z (negb (Z.eqb a 0) && negb (Z.eqb b 0))
  | Blor   => b2z (negb (Z.eqb a 0) || negb (Z.eqb b 0))
  end.

Fixpoint eval (s : store) (e : expr) : Z :=
  match e with
  | Econst z      => z
  | Evar x        => s x
  | Ebin op e1 e2 => apply_bin op (eval s e1) (eval s e2)
  end.

(* ================================================================= *)
(* 3. The syntactic program inverter                                  *)
(* ================================================================= *)

Fixpoint inv (st : stmt) : stmt :=
  match st with
  | Sskip             => Sskip
  | Sass x op e       => Sass x (inv_upd op) e
  | Sseq a b          => Sseq (inv b) (inv a)
  | Sif e1 a b e2     => Sif e2 (inv a) (inv b) e1
  | Sloop e1 a b e2   => Sloop e2 (inv a) (inv b) e1
  | Scall p ys        => Suncall p ys
  | Suncall p ys      => Scall p ys
  end.

(* ================================================================= *)
(* 3a. Parameter passing: renaming formals to actuals                  *)
(* ================================================================= *)

(* [ren xs ys v]: the actual bound to v if v is a formal, else v itself. *)
Fixpoint ren (xs ys : list var) (v : var) : var :=
  match xs, ys with
  | List.cons x xs', List.cons y ys' => if Fin.eq_dec v x then y else ren xs' ys' v
  | _, _ => v
  end.

Fixpoint rename_expr (ρ : var -> var) (e : expr) : expr :=
  match e with
  | Econst z      => Econst z
  | Evar x        => Evar (ρ x)
  | Ebin op e1 e2 => Ebin op (rename_expr ρ e1) (rename_expr ρ e2)
  end.

Fixpoint rename (ρ : var -> var) (st : stmt) : stmt :=
  match st with
  | Sskip           => Sskip
  | Sass x op e     => Sass (ρ x) op (rename_expr ρ e)
  | Sseq a b        => Sseq (rename ρ a) (rename ρ b)
  | Sif e1 a b e2   => Sif (rename_expr ρ e1) (rename ρ a) (rename ρ b) (rename_expr ρ e2)
  | Sloop e1 a b e2 => Sloop (rename_expr ρ e1) (rename ρ a) (rename ρ b) (rename_expr ρ e2)
  | Scall p ys      => Scall p (List.map ρ ys)
  | Suncall p ys    => Suncall p (List.map ρ ys)
  end.

(* The body that [call p ys] runs. *)
Definition inst (pr : proc) (ys : list var) : stmt :=
  rename (ren (formals pr) ys) (body pr).

(* Every variable occurring in an expression / a statement. *)
Fixpoint vars_expr (e : expr) : list var :=
  match e with
  | Econst _      => List.nil
  | Evar x        => List.cons x List.nil
  | Ebin _ e1 e2  => vars_expr e1 +++ vars_expr e2
  end.

Fixpoint vars (st : stmt) : list var :=
  match st with
  | Sskip           => List.nil
  | Sass x _ e      => x :: vars_expr e
  | Sseq a b        => vars a +++ vars b
  | Sif e1 a b e2   => vars_expr e1 +++ vars a +++ vars b +++ vars_expr e2
  | Sloop e1 a b e2 => vars_expr e1 +++ vars a +++ vars b +++ vars_expr e2
  | Scall _ ys      => ys
  | Suncall _ ys    => ys
  end.

Definition var_eqb (u w : var) : bool := if Fin.eq_dec u w then true else false.

Fixpoint nodupb (l : list var) : bool :=
  match l with
  | List.nil => true
  | List.cons x l' => negb (List.existsb (var_eqb x) l') && nodupb l'
  end.

(* ρ is injective on the list l. *)
Definition inj_on (ρ : var -> var) (l : list var) : Prop :=
  forall u w, List.In u l -> List.In w l -> ρ u = ρ w -> u = w.

Definition inj_onb (ρ : var -> var) (l : list var) : bool :=
  List.forallb (fun u => List.forallb (fun w => negb (var_eqb (ρ u) (ρ w)) || var_eqb u w) l) l.

(* The side condition of the four call/uncall rules: arities agree, the
   formals and the actuals are each duplicate-free, and the renaming is
   injective on the variables the body touches.  The last clause is
   Janus's no-aliasing rule: an actual may not coincide with a global the
   body uses (nor with another actual).  A call violating it is stuck. *)
Definition call_ok (pr : proc) (ys : list var) : bool :=
  Nat.eqb (List.length (formals pr)) (List.length ys)
  && nodupb (formals pr) && nodupb ys
  && inj_onb (ren (formals pr) ys) (vars (body pr)).

(* ================================================================= *)
(* 4. Controlled statements: one control token                        *)
(* ================================================================= *)

Inductive cont_stmt : Type :=
  | CS_pre        (st : stmt)                                          (* •s  *)
  | CS_post       (st : stmt)                                          (* s•  *)
  | CS_seq_L      (cs : cont_stmt) (s2 : stmt)
  | CS_seq_R      (s1 : stmt) (cs : cont_stmt)
  | CS_if_then    (e1 : expr) (cs : cont_stmt) (s2 : stmt) (e2 : expr)
  | CS_if_else    (e1 : expr) (s1 : stmt) (cs : cont_stmt) (e2 : expr)
  | CS_loop_from  (e1 : expr) (s1 s2 : stmt) (e2 : expr)
      (* token at the from-point, just before s1 *)
  | CS_loop_do    (e1 : expr) (cs : cont_stmt) (s2 : stmt) (e2 : expr)
      (* token inside s1 *)
  | CS_loop_until (e1 : expr) (s1 s2 : stmt) (e2 : expr)
      (* token at the until-point, after s1, before testing e2 *)
  | CS_loop_loop  (e1 : expr) (s1 : stmt) (cs : cont_stmt) (e2 : expr)
      (* token inside s2 *)
  | CS_call       (p : pid) (ys : list var) (cs : cont_stmt)
      (* token inside inst (Gamma p) ys *)
  | CS_uncall     (p : pid) (ys : list var) (cs : cont_stmt).
      (* token inside inv (inst (Gamma p) ys) *)

(* ================================================================= *)
(* 5. Small-step semantics                                            *)
(* ================================================================= *)

(* Guards: [eval s e <> 0] is "e is true", [eval s e = 0] is "e is false".
   The store is unchanged except in J_Asn. *)
Inductive jstep (Γ : penv) : cont_stmt * store -> cont_stmt * store -> Prop :=
  | J_Skip : forall s,
      jstep Γ (CS_pre Sskip, s) (CS_post Sskip, s)
  | J_Asn : forall x op e s,
      jstep Γ (CS_pre (Sass x op e), s)
              (CS_post (Sass x op e), update s x (apply_upd op (s x) (eval s e)))
  | J_Seq_Enter : forall s1 s2 s,
      jstep Γ (CS_pre (Sseq s1 s2), s) (CS_seq_L (CS_pre s1) s2, s)
  | J_Seq_Mid : forall s1 s2 s,
      jstep Γ (CS_seq_L (CS_post s1) s2, s) (CS_seq_R s1 (CS_pre s2), s)
  | J_Seq_Exit : forall s1 s2 s,
      jstep Γ (CS_seq_R s1 (CS_post s2), s) (CS_post (Sseq s1 s2), s)
  | J_If_True : forall e1 s1 s2 e2 s,
      eval s e1 <> 0 ->
      jstep Γ (CS_pre (Sif e1 s1 s2 e2), s) (CS_if_then e1 (CS_pre s1) s2 e2, s)
  | J_If_False : forall e1 s1 s2 e2 s,
      eval s e1 = 0 ->
      jstep Γ (CS_pre (Sif e1 s1 s2 e2), s) (CS_if_else e1 s1 (CS_pre s2) e2, s)
  | J_Fi_True : forall e1 s1 s2 e2 s,
      eval s e2 <> 0 ->
      jstep Γ (CS_if_then e1 (CS_post s1) s2 e2, s) (CS_post (Sif e1 s1 s2 e2), s)
  | J_Fi_False : forall e1 s1 s2 e2 s,
      eval s e2 = 0 ->
      jstep Γ (CS_if_else e1 s1 (CS_post s2) e2, s) (CS_post (Sif e1 s1 s2 e2), s)
  | J_Loop_Enter : forall e1 s1 s2 e2 s,
      eval s e1 <> 0 ->
      jstep Γ (CS_pre (Sloop e1 s1 s2 e2), s) (CS_loop_from e1 s1 s2 e2, s)
  | J_Loop_Do : forall e1 s1 s2 e2 s,
      jstep Γ (CS_loop_from e1 s1 s2 e2, s) (CS_loop_do e1 (CS_pre s1) s2 e2, s)
  | J_Loop_DoDone : forall e1 s1 s2 e2 s,
      jstep Γ (CS_loop_do e1 (CS_post s1) s2 e2, s) (CS_loop_until e1 s1 s2 e2, s)
  | J_Loop_Exit : forall e1 s1 s2 e2 s,
      eval s e2 <> 0 ->
      jstep Γ (CS_loop_until e1 s1 s2 e2, s) (CS_post (Sloop e1 s1 s2 e2), s)
  | J_Loop_Iter1 : forall e1 s1 s2 e2 s,
      eval s e2 = 0 ->
      jstep Γ (CS_loop_until e1 s1 s2 e2, s) (CS_loop_loop e1 s1 (CS_pre s2) e2, s)
  | J_Loop_Iter2 : forall e1 s1 s2 e2 s,
      eval s e1 = 0 ->
      jstep Γ (CS_loop_loop e1 s1 (CS_post s2) e2, s) (CS_loop_from e1 s1 s2 e2, s)
  | J_Call_Enter : forall p ys s,
      call_ok (Γ p) ys = true ->
      jstep Γ (CS_pre (Scall p ys), s) (CS_call p ys (CS_pre (inst (Γ p) ys)), s)
  | J_Call_Exit : forall p ys s,
      call_ok (Γ p) ys = true ->
      jstep Γ (CS_call p ys (CS_post (inst (Γ p) ys)), s) (CS_post (Scall p ys), s)
  | J_Uncall_Enter : forall p ys s,
      call_ok (Γ p) ys = true ->
      jstep Γ (CS_pre (Suncall p ys), s)
              (CS_uncall p ys (CS_pre (inv (inst (Γ p) ys))), s)
  | J_Uncall_Exit : forall p ys s,
      call_ok (Γ p) ys = true ->
      jstep Γ (CS_uncall p ys (CS_post (inv (inst (Γ p) ys))), s)
              (CS_post (Suncall p ys), s)
  (* Context rules: one for each constructor with a cont_stmt hole. *)
  | J_Ctx_Seq_L : forall cs cs' s2 s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_seq_L cs s2, s) (CS_seq_L cs' s2, s')
  | J_Ctx_Seq_R : forall s1 cs cs' s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_seq_R s1 cs, s) (CS_seq_R s1 cs', s')
  | J_Ctx_If_Then : forall e1 cs cs' s2 e2 s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_if_then e1 cs s2 e2, s) (CS_if_then e1 cs' s2 e2, s')
  | J_Ctx_If_Else : forall e1 s1 cs cs' e2 s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_if_else e1 s1 cs e2, s) (CS_if_else e1 s1 cs' e2, s')
  | J_Ctx_Loop_Do : forall e1 cs cs' s2 e2 s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_loop_do e1 cs s2 e2, s) (CS_loop_do e1 cs' s2 e2, s')
  | J_Ctx_Loop_Loop : forall e1 s1 cs cs' e2 s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_loop_loop e1 s1 cs e2, s) (CS_loop_loop e1 s1 cs' e2, s')
  | J_Ctx_Call : forall p ys cs cs' s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_call p ys cs, s) (CS_call p ys cs', s')
  | J_Ctx_Uncall : forall p ys cs cs' s s',
      jstep Γ (cs, s) (cs', s') ->
      jstep Γ (CS_uncall p ys cs, s) (CS_uncall p ys cs', s').

(* Backward step: the converse relation. *)
Definition bstep (Γ : penv) (cfg1 cfg2 : cont_stmt * store) : Prop :=
  jstep Γ cfg2 cfg1.

(* ================================================================= *)
(* 6. Store and update-operator lemmas                                *)
(* ================================================================= *)

Lemma update_eq : forall s x v, update s x v x = v.
Proof. intros. unfold update, lookup. apply nth_replace_eq. Qed.

Lemma update_neq : forall s x y v, x <> y -> update s x v y = s y.
Proof.
  intros s x y v Hxy. unfold update, lookup.
  apply nth_replace_neq. auto.
Qed.

(* Pointwise => Leibniz equality on stores, constructively, from
   [Vector.eq_nth_iff]: no functional extensionality. *)
Lemma store_ext : forall s1 s2 : store, (forall y, s1 y = s2 y) -> s1 = s2.
Proof.
  intros s1 s2 H. apply eq_nth_iff. intros p1 p2 ->. apply H.
Qed.

Lemma update_injective_off_x :
  forall (s1 s2 : store) (x : var) (v1 v2 : Z),
    update s1 x v1 = update s2 x v2 ->
    forall y, y <> x -> s1 y = s2 y.
Proof.
  intros s1 s2 x v1 v2 Heq y Hy.
  assert (Hpoint : update s1 x v1 y = update s2 x v2 y) by (rewrite Heq; reflexivity).
  rewrite !update_neq in Hpoint by (intro; apply Hy; auto). exact Hpoint.
Qed.

Lemma update_value_at_x :
  forall (s1 s2 : store) (x : var) (v1 v2 : Z),
    update s1 x v1 = update s2 x v2 -> v1 = v2.
Proof.
  intros s1 s2 x v1 v2 Heq.
  assert (H : update s1 x v1 x = update s2 x v2 x) by (rewrite Heq; reflexivity).
  rewrite !update_eq in H. exact H.
Qed.

Lemma update_cancel : forall s x v, update (update s x v) x (s x) = s.
Proof.
  intros s x v; apply store_ext; intro y.
  destruct (Fin.eq_dec y x) as [->|Hy].
  - now rewrite update_eq.
  - now rewrite !update_neq by auto.
Qed.

(* Every update operator is injective in its destination argument. *)
Lemma apply_upd_injective :
  forall op d1 d2 v, apply_upd op d1 v = apply_upd op d2 v -> d1 = d2.
Proof.
  intros op d1 d2 v H; destruct op; simpl in H.
  - lia.
  - lia.
  - apply (f_equal (fun z => Z.lxor z v)) in H.
    rewrite !Z.lxor_assoc, Z.lxor_nilpotent, !Z.lxor_0_r in H. exact H.
Qed.

(* The inverse operator undoes the operator. *)
Lemma apply_upd_inv :
  forall op d v, apply_upd (inv_upd op) (apply_upd op d v) v = d.
Proof.
  intros op d v; destruct op; simpl.
  - lia.
  - lia.
  - rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity.
Qed.

Lemma inv_upd_involutive : forall op, inv_upd (inv_upd op) = op.
Proof. destruct op; reflexivity. Qed.

(* ================================================================= *)
(* 7. Well-formedness                                                 *)
(* ================================================================= *)

(* x does not occur in e. *)
Inductive nf_expr (x : var) : expr -> Prop :=
  | nf_Econst : forall z, nf_expr x (Econst z)
  | nf_Evar   : forall y, y <> x -> nf_expr x (Evar y)
  | nf_Ebin   : forall op e1 e2,
      nf_expr x e1 -> nf_expr x e2 -> nf_expr x (Ebin op e1 e2).

(* Assignments must not read their own destination; call/uncall are
   always well-formed here (the body's well-formedness is a property of
   Gamma, [wf_penv]). *)
Inductive wf_stmt : stmt -> Prop :=
  | wf_Sskip   : wf_stmt Sskip
  | wf_Sass    : forall x op e, nf_expr x e -> wf_stmt (Sass x op e)
  | wf_Sseq    : forall s1 s2, wf_stmt s1 -> wf_stmt s2 -> wf_stmt (Sseq s1 s2)
  | wf_Sif     : forall e1 s1 s2 e2,
      wf_stmt s1 -> wf_stmt s2 -> wf_stmt (Sif e1 s1 s2 e2)
  | wf_Sloop   : forall e1 s1 s2 e2,
      wf_stmt s1 -> wf_stmt s2 -> wf_stmt (Sloop e1 s1 s2 e2)
  | wf_Scall   : forall p ys, wf_stmt (Scall p ys)
  | wf_Suncall : forall p ys, wf_stmt (Suncall p ys).

Definition wf_penv (Γ : penv) : Prop := forall p, wf_stmt (body (Γ p)).

(* Well-formedness of a controlled statement: every statement inside it
   is well-formed.  For CS_call/CS_uncall only the inner controlled
   statement is constrained. *)
Inductive wf_cs : cont_stmt -> Prop :=
  | wf_cs_pre        : forall st, wf_stmt st -> wf_cs (CS_pre st)
  | wf_cs_post       : forall st, wf_stmt st -> wf_cs (CS_post st)
  | wf_cs_seq_L      : forall cs s2, wf_cs cs -> wf_stmt s2 -> wf_cs (CS_seq_L cs s2)
  | wf_cs_seq_R      : forall s1 cs, wf_stmt s1 -> wf_cs cs -> wf_cs (CS_seq_R s1 cs)
  | wf_cs_if_then    : forall e1 cs s2 e2,
      wf_cs cs -> wf_stmt s2 -> wf_cs (CS_if_then e1 cs s2 e2)
  | wf_cs_if_else    : forall e1 s1 cs e2,
      wf_stmt s1 -> wf_cs cs -> wf_cs (CS_if_else e1 s1 cs e2)
  | wf_cs_loop_from  : forall e1 s1 s2 e2,
      wf_stmt s1 -> wf_stmt s2 -> wf_cs (CS_loop_from e1 s1 s2 e2)
  | wf_cs_loop_do    : forall e1 cs s2 e2,
      wf_cs cs -> wf_stmt s2 -> wf_cs (CS_loop_do e1 cs s2 e2)
  | wf_cs_loop_until : forall e1 s1 s2 e2,
      wf_stmt s1 -> wf_stmt s2 -> wf_cs (CS_loop_until e1 s1 s2 e2)
  | wf_cs_loop_loop  : forall e1 s1 cs e2,
      wf_stmt s1 -> wf_cs cs -> wf_cs (CS_loop_loop e1 s1 cs e2)
  | wf_cs_call       : forall p ys cs, wf_cs cs -> wf_cs (CS_call p ys cs)
  | wf_cs_uncall     : forall p ys cs, wf_cs cs -> wf_cs (CS_uncall p ys cs).

Local Hint Constructors nf_expr wf_stmt wf_cs : core.

(* Decidability of well-formedness. *)
Fixpoint nf_expr_dec (x : var) (e : expr) : {nf_expr x e} + {~ nf_expr x e}.
Proof.
  destruct e as [z | y | op e1 e2].
  - left; constructor.
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + left; constructor; exact Hy.
  - destruct (nf_expr_dec x e1) as [H1 | H1].
    + destruct (nf_expr_dec x e2) as [H2 | H2].
      * left; constructor; assumption.
      * right; intro H; inversion H; subst; contradiction.
    + right; intro H; inversion H; subst; contradiction.
Defined.

Fixpoint wf_stmt_dec (st : stmt) : {wf_stmt st} + {~ wf_stmt st}.
Proof.
  destruct st as [ | x op e | a b | e1 a b e2 | e1 a b e2 | p ys | p ys].
  - left; constructor.
  - destruct (nf_expr_dec x e) as [H | H].
    + left; constructor; exact H.
    + right; intro Hw; inversion Hw; subst; contradiction.
  - destruct (wf_stmt_dec a) as [Ha | Ha].
    + destruct (wf_stmt_dec b) as [Hb | Hb].
      * left; constructor; assumption.
      * right; intro Hw; inversion Hw; subst; contradiction.
    + right; intro Hw; inversion Hw; subst; contradiction.
  - destruct (wf_stmt_dec a) as [Ha | Ha].
    + destruct (wf_stmt_dec b) as [Hb | Hb].
      * left; constructor; assumption.
      * right; intro Hw; inversion Hw; subst; contradiction.
    + right; intro Hw; inversion Hw; subst; contradiction.
  - destruct (wf_stmt_dec a) as [Ha | Ha].
    + destruct (wf_stmt_dec b) as [Hb | Hb].
      * left; constructor; assumption.
      * right; intro Hw; inversion Hw; subst; contradiction.
    + right; intro Hw; inversion Hw; subst; contradiction.
  - left; constructor.
  - left; constructor.
Defined.

Fixpoint wf_cs_dec (cs : cont_stmt) : {wf_cs cs} + {~ wf_cs cs}.
Proof.
  destruct cs as [st | st | cs s2 | s1 cs | e1 cs s2 e2 | e1 s1 cs e2
                 | e1 s1 s2 e2 | e1 cs s2 e2 | e1 s1 s2 e2 | e1 s1 cs e2
                 | p ys cs | p ys cs];
  repeat match goal with
  | [ st : stmt |- _ ] =>
      lazymatch goal with
      | [ H : wf_stmt st |- _ ] => fail
      | [ H : ~ wf_stmt st |- _ ] => fail
      | _ => destruct (wf_stmt_dec st)
      end
  | [ cs : cont_stmt |- _ ] =>
      lazymatch goal with
      | [ H : wf_cs cs |- _ ] => fail
      | [ H : ~ wf_cs cs |- _ ] => fail
      | _ => destruct (wf_cs_dec cs)
      end
  end;
  try (left; constructor; assumption);
  right; intro Hw; inversion Hw; subst; contradiction.
Defined.

(* ================================================================= *)
(* 8. Evaluation lemmas for x-free expressions                        *)
(* ================================================================= *)

Lemma eval_update_invariant :
  forall x e s v, nf_expr x e -> eval (update s x v) e = eval s e.
Proof.
  intros x e s v Hnf; induction Hnf; simpl.
  - reflexivity.
  - now rewrite update_neq by auto.
  - now rewrite IHHnf1, IHHnf2.
Qed.

Lemma eval_agree :
  forall x e (s s' : store),
    nf_expr x e ->
    (forall y, y <> x -> s y = s' y) ->
    eval s e = eval s' e.
Proof.
  intros x e s s' Hnf Hag; induction Hnf; simpl.
  - reflexivity.
  - now rewrite (Hag _ H).
  - now rewrite IHHnf1, IHHnf2.
Qed.

(* Partial injectivity of the J_Asn rule in the store: two pre-stores
   with the same post-store are equal, provided x is not read by e. *)
Lemma asn_step_injective :
  forall x op e (s1 s2 : store),
    nf_expr x e ->
    update s1 x (apply_upd op (s1 x) (eval s1 e))
      = update s2 x (apply_upd op (s2 x) (eval s2 e)) ->
    s1 = s2.
Proof.
  intros x op e s1 s2 Hnf Hupd.
  assert (Hoff : forall y, y <> x -> s1 y = s2 y)
    by (eapply update_injective_off_x; exact Hupd).
  assert (Hveq : apply_upd op (s1 x) (eval s1 e) = apply_upd op (s2 x) (eval s2 e))
    by (eapply update_value_at_x; exact Hupd).
  assert (Hev : eval s1 e = eval s2 e)
    by (eapply eval_agree; [exact Hnf | exact Hoff]).
  rewrite Hev in Hveq.
  apply apply_upd_injective in Hveq.
  apply store_ext; intro y.
  destruct (Fin.eq_dec y x) as [->|Hy].
  - exact Hveq.
  - apply Hoff; exact Hy.
Qed.

(* ================================================================= *)
(* 9. Stuckness: no step from s•, no step to •s                       *)
(* ================================================================= *)

Lemma no_step_from_post :
  forall Γ s st cfg, ~ jstep Γ (CS_post st, s) cfg.
Proof. intros Γ s st cfg H; inversion H. Qed.

Lemma no_step_to_pre :
  forall Γ s st cfg, ~ jstep Γ cfg (CS_pre st, s).
Proof. intros Γ s st cfg H; inversion H. Qed.

Ltac kill_post :=
  exfalso;
  match goal with
  | [ Hbad : jstep _ (CS_post _, _) _ |- _ ] =>
      eapply no_step_from_post; exact Hbad
  end.

Ltac kill_step_to_pre :=
  exfalso;
  match goal with
  | [ Hbad : jstep _ _ (CS_pre _, _) |- _ ] =>
      eapply no_step_to_pre; exact Hbad
  end.

(* ================================================================= *)
(* 10. Forward determinism                                            *)
(* ================================================================= *)

Ltac use_IH :=
  match goal with
  | [ IH : forall cfg2, jstep _ _ cfg2 -> _ = cfg2,
      Hinner : jstep _ _ ?cfg' |- _ ] =>
      let E := fresh "E" in
      pose proof (IH _ Hinner) as E; injection E as ? ?; subst; reflexivity
  end.

(* No well-formedness hypothesis is needed in the forward direction. *)
Theorem jstep_deterministic :
  forall Γ cfg cfg1 cfg2,
    jstep Γ cfg cfg1 -> jstep Γ cfg cfg2 -> cfg1 = cfg2.
Proof.
  intros Γ cfg cfg1 cfg2 H1; revert cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst;
    try reflexivity; try contradiction; try kill_post; try use_IH.
Qed.

(* ================================================================= *)
(* 11. Invariance of well-formedness                                  *)
(* ================================================================= *)

Ltac wf_inv :=
  repeat match goal with
  | [ H : wf_cs (CS_pre _)               |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_post _)              |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_seq_L _ _)           |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_seq_R _ _)           |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_if_then _ _ _ _)     |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_if_else _ _ _ _)     |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_loop_from _ _ _ _)   |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_loop_do _ _ _ _)     |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_loop_until _ _ _ _)  |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_loop_loop _ _ _ _)   |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_call _ _ _)          |- _ ] => inversion H; subst; clear H
  | [ H : wf_cs (CS_uncall _ _ _)        |- _ ] => inversion H; subst; clear H
  | [ H : wf_stmt (Sass _ _ _)           |- _ ] => inversion H; subst; clear H
  | [ H : wf_stmt (Sseq _ _)             |- _ ] => inversion H; subst; clear H
  | [ H : wf_stmt (Sif _ _ _ _)          |- _ ] => inversion H; subst; clear H
  | [ H : wf_stmt (Sloop _ _ _ _)        |- _ ] => inversion H; subst; clear H
  end.

Lemma inv_involutive : forall st, inv (inv st) = st.
Proof.
  induction st; simpl; try rewrite inv_upd_involutive; congruence.
Qed.

Lemma wf_stmt_inv : forall st, wf_stmt st -> wf_stmt (inv st).
Proof.
  induction st; intros H; inversion H; subst; simpl; auto.
Qed.

(* Renaming commutes with inversion. *)
Lemma rename_inv : forall ρ st, rename ρ (inv st) = inv (rename ρ st).
Proof. intros ρ st; induction st; simpl; congruence. Qed.

Lemma var_eqb_true : forall u w, var_eqb u w = true <-> u = w.
Proof.
  intros u w; unfold var_eqb; destruct (Fin.eq_dec u w); split; congruence.
Qed.

Lemma inj_onb_spec : forall ρ l, inj_onb ρ l = true -> inj_on ρ l.
Proof.
  unfold inj_onb, inj_on; intros ρ l H u w Hu Hw Hρ.
  rewrite List.forallb_forall in H. specialize (H u Hu).
  rewrite List.forallb_forall in H. specialize (H w Hw).
  apply orb_prop in H as [H | H].
  - rewrite Hρ in H. unfold var_eqb in H.
    destruct (Fin.eq_dec (ρ w) (ρ w)); [discriminate | contradiction].
  - apply var_eqb_true; exact H.
Qed.

Lemma inj_on_app_l : forall ρ l1 l2, inj_on ρ (l1 +++ l2) -> inj_on ρ l1.
Proof.
  unfold inj_on; intros ρ l1 l2 H u w Hu Hw; apply H; apply List.in_or_app; auto.
Qed.

Lemma inj_on_app_r : forall ρ l1 l2, inj_on ρ (l1 +++ l2) -> inj_on ρ l2.
Proof.
  unfold inj_on; intros ρ l1 l2 H u w Hu Hw; apply H; apply List.in_or_app; auto.
Qed.

(* An injective renaming keeps x out of e. *)
Lemma nf_expr_rename :
  forall ρ x e,
    nf_expr x e ->
    (forall y, List.In y (vars_expr e) -> ρ y = ρ x -> y = x) ->
    nf_expr (ρ x) (rename_expr ρ e).
Proof.
  intros ρ x e Hnf; induction Hnf; intros Hinj; simpl in *.
  - constructor.
  - constructor. intro Hc. apply H. apply Hinj; auto.
  - constructor.
    + apply IHHnf1. intros y Hy; apply Hinj; apply List.in_or_app; auto.
    + apply IHHnf2. intros y Hy; apply Hinj; apply List.in_or_app; auto.
Qed.

(* Renaming that is injective on the variables of st preserves
   well-formedness. *)
Lemma wf_stmt_rename :
  forall ρ st, wf_stmt st -> inj_on ρ (vars st) -> wf_stmt (rename ρ st).
Proof.
  intros ρ st Hwf; induction Hwf; intros Hinj; simpl in *.
  - constructor.
  - constructor. apply nf_expr_rename; [exact H |].
    intros y Hy Heq. apply (Hinj y x); simpl; auto.
  - apply wf_Sseq; [apply IHHwf1; exact (@inj_on_app_l _ _ _ Hinj)
                 | apply IHHwf2; exact (@inj_on_app_r _ _ _ Hinj)].
  - pose proof (@inj_on_app_l _ _ _ (@inj_on_app_r _ _ _ Hinj)) as H1.
    pose proof (@inj_on_app_l _ _ _ (@inj_on_app_r _ _ _ (@inj_on_app_r _ _ _ Hinj))) as H2.
    constructor; auto.
  - pose proof (@inj_on_app_l _ _ _ (@inj_on_app_r _ _ _ Hinj)) as H1.
    pose proof (@inj_on_app_l _ _ _ (@inj_on_app_r _ _ _ (@inj_on_app_r _ _ _ Hinj))) as H2.
    constructor; auto.
  - constructor.
  - constructor.
Qed.

(* The body a well-formed environment instantiates at an accepted call is
   well-formed. *)
Lemma wf_inst :
  forall Γ p ys, wf_penv Γ -> call_ok (Γ p) ys = true -> wf_stmt (inst (Γ p) ys).
Proof.
  intros Γ p ys HΓ Hok. unfold inst, call_ok in *.
  apply andb_prop in Hok as [_ Hinj].
  apply wf_stmt_rename; [apply HΓ | apply inj_onb_spec; exact Hinj].
Qed.

Local Hint Resolve wf_inst wf_stmt_inv : core.

Lemma wf_cs_step_preserved_cfg :
  forall Γ cfg cfg',
    wf_penv Γ -> jstep Γ cfg cfg' -> wf_cs (fst cfg) -> wf_cs (fst cfg').
Proof.
  intros Γ cfg cfg' HΓ H; induction H; intros Hwf; simpl in *; wf_inv;
    eauto 6 using wf_stmt_inv, wf_inst.
Qed.

Lemma wf_cs_step_reflected_cfg :
  forall Γ cfg cfg',
    wf_penv Γ -> jstep Γ cfg cfg' -> wf_cs (fst cfg') -> wf_cs (fst cfg).
Proof.
  intros Γ cfg cfg' HΓ H; induction H; intros Hwf; simpl in *; wf_inv;
    eauto 6 using wf_stmt_inv, wf_inst.
Qed.

(* Forward direction of invariance. *)
Lemma wf_cs_step_preserved :
  forall Γ cs s cs' s',
    wf_penv Γ -> jstep Γ (cs, s) (cs', s') -> wf_cs cs -> wf_cs cs'.
Proof.
  intros Γ cs s cs' s' HΓ H Hwf.
  exact (wf_cs_step_preserved_cfg (cfg := (cs, s)) (cfg' := (cs', s')) HΓ H Hwf).
Qed.

(* Backward direction of invariance. *)
Lemma wf_cs_step_reflected :
  forall Γ cs s cs' s',
    wf_penv Γ -> jstep Γ (cs, s) (cs', s') -> wf_cs cs' -> wf_cs cs.
Proof.
  intros Γ cs s cs' s' HΓ H Hwf.
  exact (wf_cs_step_reflected_cfg (cfg := (cs, s)) (cfg' := (cs', s')) HΓ H Hwf).
Qed.

(* ================================================================= *)
(* 12. Backward determinism                                           *)
(* ================================================================= *)

Ltac bwd_ctx IH cs s :=
  match goal with
  | [ Hinner : jstep _ (?cs'', ?s0) _ |- _ ] =>
      let E := fresh "E" in
      assert (E : (cs, s) = (cs'', s0))
        by (eapply IH; [eassumption | eassumption | exact Hinner]);
      injection E as ? ?; subst; reflexivity
  end.

(* Paper-faithful form: well-formedness of both predecessors. *)
Theorem jstep_bwd_deterministic :
  forall Γ cfg1 cfg2 cfg,
    wf_cs (fst cfg1) -> wf_cs (fst cfg2) ->
    jstep Γ cfg1 cfg -> jstep Γ cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros Γ cfg1 cfg2 cfg Hwf1 Hwf2 H1; revert cfg2 Hwf1 Hwf2.
  induction H1; intros cfg2 Hwf1 Hwf2 H2; simpl in *; inversion H2; subst;
    try reflexivity;
    try contradiction;
    try kill_post;
    try kill_step_to_pre.
  - (* J_Asn vs J_Asn: recover the pre-store from the common post-store. *)
    assert (Hnf : nf_expr x e) by (wf_inv; assumption).
    match goal with
    | [ Hupd : update ?sa x _ = update ?sb x _ |- _ ] =>
        assert (Hss : sa = sb)
          by (eapply asn_step_injective; [exact Hnf | exact Hupd]);
        subst; reflexivity
    end.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
  - inversion Hwf1; subst; inversion Hwf2; subst; bwd_ctx IHjstep cs s.
Qed.

(* Single-hypothesis form: well-formedness of the common target,
   transported to the predecessors by reflection. *)
Theorem jstep_bwd_deterministic_tgt :
  forall Γ cfg1 cfg2 cfg,
    wf_penv Γ -> wf_cs (fst cfg) ->
    jstep Γ cfg1 cfg -> jstep Γ cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros Γ [cs1 s1] [cs2 s2] [cs s] HΓ Hwf H1 H2.
  apply jstep_bwd_deterministic with (Γ := Γ) (cfg := (cs, s)); simpl in *; try assumption.
  - eapply wf_cs_step_reflected; [exact HΓ | exact H1 | exact Hwf].
  - eapply wf_cs_step_reflected; [exact HΓ | exact H2 | exact Hwf].
Qed.

Theorem bstep_deterministic :
  forall Γ cfg cfg1 cfg2,
    wf_penv Γ -> wf_cs (fst cfg) ->
    bstep Γ cfg cfg1 -> bstep Γ cfg cfg2 -> cfg1 = cfg2.
Proof.
  unfold bstep; intros Γ cfg cfg1 cfg2 HΓ Hwf H1 H2.
  eapply jstep_bwd_deterministic_tgt; eassumption.
Qed.

(* ================================================================= *)
(* 13. The inverter on controlled statements                          *)
(* ================================================================= *)

(* Where the same point of execution sits in the inverted program.  Note
   the from-point and the until-point swap, as do the two guards. *)
Fixpoint cs_inv (cs : cont_stmt) : cont_stmt :=
  match cs with
  | CS_pre st                 => CS_post (inv st)
  | CS_post st                => CS_pre (inv st)
  | CS_seq_L cs1 s2           => CS_seq_R (inv s2) (cs_inv cs1)
  | CS_seq_R s1 cs2           => CS_seq_L (cs_inv cs2) (inv s1)
  | CS_if_then e1 cs1 s2 e2   => CS_if_then e2 (cs_inv cs1) (inv s2) e1
  | CS_if_else e1 s1 cs2 e2   => CS_if_else e2 (inv s1) (cs_inv cs2) e1
  | CS_loop_from e1 s1 s2 e2  => CS_loop_until e2 (inv s1) (inv s2) e1
  | CS_loop_until e1 s1 s2 e2 => CS_loop_from e2 (inv s1) (inv s2) e1
  | CS_loop_do e1 cs1 s2 e2   => CS_loop_do e2 (cs_inv cs1) (inv s2) e1
  | CS_loop_loop e1 s1 cs2 e2 => CS_loop_loop e2 (inv s1) (cs_inv cs2) e1
  | CS_call p ys cs1          => CS_uncall p ys (cs_inv cs1)
  | CS_uncall p ys cs1        => CS_call p ys (cs_inv cs1)
  end.

Lemma cs_inv_involutive : forall cs, cs_inv (cs_inv cs) = cs.
Proof. induction cs; simpl; rewrite ?inv_involutive; congruence. Qed.

Lemma wf_cs_cs_inv : forall cs, wf_cs cs -> wf_cs (cs_inv cs).
Proof.
  induction cs; intros H; inversion H; subst; simpl; auto using wf_stmt_inv.
Qed.

(* A form of J_Asn whose post-store is stated by an equation. *)
Lemma J_Asn' :
  forall Γ x op e s s',
    s' = update s x (apply_upd op (s x) (eval s e)) ->
    jstep Γ (CS_pre (Sass x op e), s) (CS_post (Sass x op e), s').
Proof. intros; subst; constructor. Qed.

(* Meta-level reversibility, realized syntactically: one forward step of
   cs is one forward step of [cs_inv cs] taken in the opposite direction.
   Well-formedness of the source is needed exactly where backward
   determinism needs it: in the assignment case. *)
Lemma inv_step_reverses_cfg :
  forall Γ cfg cfg',
    jstep Γ cfg cfg' -> wf_cs (fst cfg) ->
    jstep Γ (cs_inv (fst cfg'), snd cfg') (cs_inv (fst cfg), snd cfg).
Proof.
  intros Γ cfg cfg' H; induction H; intros Hwf; simpl in *.
  - apply J_Skip.
  - assert (Hnf : nf_expr x e) by (wf_inv; assumption).
    apply J_Asn'.
    rewrite update_eq, eval_update_invariant by exact Hnf.
    rewrite apply_upd_inv, update_cancel. reflexivity.
  - apply J_Seq_Exit.
  - apply J_Seq_Mid.
  - apply J_Seq_Enter.
  - apply J_Fi_True; exact H.
  - apply J_Fi_False; exact H.
  - apply J_If_True; exact H.
  - apply J_If_False; exact H.
  - apply J_Loop_Exit; exact H.
  - apply J_Loop_DoDone.
  - apply J_Loop_Do.
  - apply J_Loop_Enter; exact H.
  - apply J_Loop_Iter2; exact H.
  - apply J_Loop_Iter1; exact H.
  - apply J_Uncall_Exit; exact H.
  - apply J_Uncall_Enter; exact H.
  - rewrite inv_involutive. apply J_Call_Exit; exact H.
  - rewrite inv_involutive. apply J_Call_Enter; exact H.
  - apply J_Ctx_Seq_R;     apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_Seq_L;     apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_If_Then;   apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_If_Else;   apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_Loop_Do;   apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_Loop_Loop; apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_Uncall;    apply IHjstep; wf_inv; assumption.
  - apply J_Ctx_Call;      apply IHjstep; wf_inv; assumption.
Qed.

Theorem inv_step_reverses :
  forall Γ cs s cs' s',
    wf_cs cs ->
    jstep Γ (cs, s) (cs', s') -> jstep Γ (cs_inv cs', s') (cs_inv cs, s).
Proof.
  intros Γ cs s cs' s' Hwf H.
  exact (inv_step_reverses_cfg (cfg := (cs, s)) (cfg' := (cs', s')) H Hwf).
Qed.

Theorem inv_step_reverses_iff :
  forall Γ cs s cs' s',
    wf_cs cs -> wf_cs cs' ->
    (jstep Γ (cs, s) (cs', s') <-> jstep Γ (cs_inv cs', s') (cs_inv cs, s)).
Proof.
  intros Γ cs s cs' s' Hwf Hwf'; split; intros H.
  - eapply inv_step_reverses; [exact Hwf | exact H].
  - assert (Hwf'' : wf_cs (cs_inv cs')) by (apply wf_cs_cs_inv; exact Hwf').
    apply (fun H0 => inv_step_reverses Hwf'' H0) in H.
    rewrite !cs_inv_involutive in H. exact H.
Qed.

(* Backward execution of cs is forward execution of [cs_inv cs]. *)
Theorem bstep_is_fwd_of_inv :
  forall Γ cs s cs' s',
    wf_cs cs -> wf_cs cs' ->
    (bstep Γ (cs, s) (cs', s') <-> jstep Γ (cs_inv cs, s) (cs_inv cs', s')).
Proof.
  intros Γ cs s cs' s' Hwf Hwf'; unfold bstep.
  apply inv_step_reverses_iff; assumption.
Qed.

(* ================================================================= *)
(* 14. Executable semantics                                           *)
(* ================================================================= *)

(* Decidable equality on statements, needed to test "the token has reached
   the end of the body Gamma p" executably. *)
Definition binop_eq_dec (a b : binop) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition updop_eq_dec (a b : updop) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition expr_eq_dec (a b : expr) : {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply Z.eq_dec.
  - apply Fin.eq_dec.
  - apply binop_eq_dec.
Defined.

Definition stmt_eq_dec (a b : stmt) : {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply expr_eq_dec.
  - apply updop_eq_dec.
  - apply Fin.eq_dec.
  - apply expr_eq_dec.
  - apply expr_eq_dec.
  - apply expr_eq_dec.
  - apply expr_eq_dec.
  - apply (list_eq_dec (@Fin.eq_dec 10)).
  - apply Nat.eq_dec.
  - apply (list_eq_dec (@Fin.eq_dec 10)).
  - apply Nat.eq_dec.
Defined.

(* In each context case the inner step is tried first; if the inner
   statement is stuck (in particular, if it is s•) the top-level rule for
   that position applies. *)
Fixpoint step_fun (Γ : penv) (cs : cont_stmt) (s : store)
  : option (cont_stmt * store) :=
  match cs with
  | CS_pre Sskip => Some (CS_post Sskip, s)
  | CS_pre (Sass x op e) =>
      Some (CS_post (Sass x op e), update s x (apply_upd op (s x) (eval s e)))
  | CS_pre (Sseq s1 s2) => Some (CS_seq_L (CS_pre s1) s2, s)
  | CS_pre (Sif e1 s1 s2 e2) =>
      if Z.eqb (eval s e1) 0
      then Some (CS_if_else e1 s1 (CS_pre s2) e2, s)
      else Some (CS_if_then e1 (CS_pre s1) s2 e2, s)
  | CS_pre (Sloop e1 s1 s2 e2) =>
      if Z.eqb (eval s e1) 0 then None else Some (CS_loop_from e1 s1 s2 e2, s)
  | CS_pre (Scall p ys) =>
      if call_ok (Γ p) ys then Some (CS_call p ys (CS_pre (inst (Γ p) ys)), s) else None
  | CS_pre (Suncall p ys) =>
      if call_ok (Γ p) ys
      then Some (CS_uncall p ys (CS_pre (inv (inst (Γ p) ys))), s) else None
  | CS_post _ => None
  | CS_seq_L cs1 s2 =>
      match step_fun Γ cs1 s with
      | Some (c, t) => Some (CS_seq_L c s2, t)
      | None => match cs1 with
                | CS_post s1 => Some (CS_seq_R s1 (CS_pre s2), s)
                | _ => None
                end
      end
  | CS_seq_R s1 cs2 =>
      match step_fun Γ cs2 s with
      | Some (c, t) => Some (CS_seq_R s1 c, t)
      | None => match cs2 with
                | CS_post s2 => Some (CS_post (Sseq s1 s2), s)
                | _ => None
                end
      end
  | CS_if_then e1 cs1 s2 e2 =>
      match step_fun Γ cs1 s with
      | Some (c, t) => Some (CS_if_then e1 c s2 e2, t)
      | None => match cs1 with
                | CS_post s1 =>
                    if Z.eqb (eval s e2) 0 then None
                    else Some (CS_post (Sif e1 s1 s2 e2), s)
                | _ => None
                end
      end
  | CS_if_else e1 s1 cs2 e2 =>
      match step_fun Γ cs2 s with
      | Some (c, t) => Some (CS_if_else e1 s1 c e2, t)
      | None => match cs2 with
                | CS_post s2 =>
                    if Z.eqb (eval s e2) 0
                    then Some (CS_post (Sif e1 s1 s2 e2), s) else None
                | _ => None
                end
      end
  | CS_loop_from e1 s1 s2 e2 => Some (CS_loop_do e1 (CS_pre s1) s2 e2, s)
  | CS_loop_do e1 cs1 s2 e2 =>
      match step_fun Γ cs1 s with
      | Some (c, t) => Some (CS_loop_do e1 c s2 e2, t)
      | None => match cs1 with
                | CS_post s1 => Some (CS_loop_until e1 s1 s2 e2, s)
                | _ => None
                end
      end
  | CS_loop_until e1 s1 s2 e2 =>
      if Z.eqb (eval s e2) 0
      then Some (CS_loop_loop e1 s1 (CS_pre s2) e2, s)
      else Some (CS_post (Sloop e1 s1 s2 e2), s)
  | CS_loop_loop e1 s1 cs2 e2 =>
      match step_fun Γ cs2 s with
      | Some (c, t) => Some (CS_loop_loop e1 s1 c e2, t)
      | None => match cs2 with
                | CS_post s2 =>
                    if Z.eqb (eval s e1) 0
                    then Some (CS_loop_from e1 s1 s2 e2, s) else None
                | _ => None
                end
      end
  | CS_call p ys cs1 =>
      match step_fun Γ cs1 s with
      | Some (c, t) => Some (CS_call p ys c, t)
      | None => match cs1 with
                | CS_post b => if stmt_eq_dec b (inst (Γ p) ys)
                               then if call_ok (Γ p) ys
                                    then Some (CS_post (Scall p ys), s) else None
                               else None
                | _ => None
                end
      end
  | CS_uncall p ys cs1 =>
      match step_fun Γ cs1 s with
      | Some (c, t) => Some (CS_uncall p ys c, t)
      | None => match cs1 with
                | CS_post b => if stmt_eq_dec b (inv (inst (Γ p) ys))
                               then if call_ok (Γ p) ys
                                    then Some (CS_post (Suncall p ys), s) else None
                               else None
                | _ => None
                end
      end
  end.

(* Soundness: whatever step_fun computes is a step. *)
Lemma step_fun_sound :
  forall Γ cs s cs' s',
    step_fun Γ cs s = Some (cs', s') -> jstep Γ (cs, s) (cs', s').
Proof.
  intros Γ cs; induction cs; intros s cs' s' H; simpl in H.
  - (* CS_pre *)
    destruct st as [ | x op e | a b | e1 a b e2 | e1 a b e2 | p ys | p ys].
    + injection H as ? ?; subst; constructor.
    + injection H as ? ?; subst; constructor.
    + injection H as ? ?; subst; constructor.
    + destruct (Z.eqb (eval s e1) 0) eqn:E; injection H as ? ?; subst; constructor.
      * apply Z.eqb_eq; exact E.
      * apply Z.eqb_neq; exact E.
    + destruct (Z.eqb (eval s e1) 0) eqn:E; [discriminate |].
      injection H as ? ?; subst; constructor. apply Z.eqb_neq; exact E.
    + destruct (call_ok (Γ p) ys) eqn:Ok; [| discriminate].
      injection H as ? ?; subst; constructor; exact Ok.
    + destruct (call_ok (Γ p) ys) eqn:Ok; [| discriminate].
      injection H as ? ?; subst; constructor; exact Ok.
  - (* CS_post *) discriminate.
  - (* CS_seq_L *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Seq_L. apply IHcs; exact E.
    + destruct cs; try discriminate. injection H as ? ?; subst; constructor.
  - (* CS_seq_R *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Seq_R. apply IHcs; exact E.
    + destruct cs; try discriminate. injection H as ? ?; subst; constructor.
  - (* CS_if_then *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_If_Then. apply IHcs; exact E.
    + destruct cs; try discriminate.
      destruct (Z.eqb (eval s e2) 0) eqn:E2; [discriminate |].
      injection H as ? ?; subst; constructor. apply Z.eqb_neq; exact E2.
  - (* CS_if_else *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_If_Else. apply IHcs; exact E.
    + destruct cs; try discriminate.
      destruct (Z.eqb (eval s e2) 0) eqn:E2; [| discriminate].
      injection H as ? ?; subst; constructor. apply Z.eqb_eq; exact E2.
  - (* CS_loop_from *) injection H as ? ?; subst; constructor.
  - (* CS_loop_do *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Loop_Do. apply IHcs; exact E.
    + destruct cs; try discriminate. injection H as ? ?; subst; constructor.
  - (* CS_loop_until *)
    destruct (Z.eqb (eval s e2) 0) eqn:E; injection H as ? ?; subst; constructor.
    + apply Z.eqb_eq; exact E.
    + apply Z.eqb_neq; exact E.
  - (* CS_loop_loop *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Loop_Loop. apply IHcs; exact E.
    + destruct cs; try discriminate.
      destruct (Z.eqb (eval s e1) 0) eqn:E2; [| discriminate].
      injection H as ? ?; subst; constructor. apply Z.eqb_eq; exact E2.
  - (* CS_call *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Call. apply IHcs; exact E.
    + destruct cs; try discriminate.
      destruct (stmt_eq_dec st (inst (Γ p) ys)) as [-> | Hne]; [| discriminate].
      destruct (call_ok (Γ p) ys) eqn:Ok; [| discriminate].
      injection H as ? ?; subst; constructor; exact Ok.
  - (* CS_uncall *)
    destruct (step_fun Γ cs s) as [[c t]|] eqn:E.
    + injection H as ? ?; subst. apply J_Ctx_Uncall. apply IHcs; exact E.
    + destruct cs; try discriminate.
      destruct (stmt_eq_dec st (inv (inst (Γ p) ys))) as [-> | Hne]; [| discriminate].
      destruct (call_ok (Γ p) ys) eqn:Ok; [| discriminate].
      injection H as ? ?; subst; constructor; exact Ok.
Qed.

(* Completeness: every step is computed by step_fun. *)
Lemma step_fun_complete :
  forall Γ cfg cfg',
    jstep Γ cfg cfg' -> step_fun Γ (fst cfg) (snd cfg) = Some cfg'.
Proof.
  intros Γ cfg cfg' H; induction H; simpl in *;
    try reflexivity;
    try (rewrite IHjstep; reflexivity);
    try (apply Z.eqb_neq in H; rewrite H; reflexivity);
    try (apply Z.eqb_eq in H; rewrite H; reflexivity);
    try (rewrite H; reflexivity).
  all: match goal with
       | [ |- context [stmt_eq_dec ?a ?b] ] =>
           destruct (stmt_eq_dec a b) as [_ | Hne];
           [rewrite H; reflexivity | exfalso; apply Hne; reflexivity]
       end.
Qed.

Theorem step_fun_correct :
  forall Γ cs s cs' s',
    step_fun Γ cs s = Some (cs', s') <-> jstep Γ (cs, s) (cs', s').
Proof.
  intros Γ cs s cs' s'; split.
  - apply step_fun_sound.
  - intros H. exact (step_fun_complete (cfg := (cs, s)) (cfg' := (cs', s')) H).
Qed.

Example step_fun_post_is_none :
  forall Γ st s, step_fun Γ (CS_post st) s = None.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* 15. Embedding sanity: running a small Janus program                *)
(* ================================================================= *)

Inductive jnsteps (Γ : penv) : nat -> cont_stmt * store -> cont_stmt * store -> Prop :=
  | JN_refl : forall cfg, jnsteps Γ O cfg cfg
  | JN_step : forall n cfg1 cfg2 cfg3,
      jstep Γ cfg1 cfg2 -> jnsteps Γ n cfg2 cfg3 -> jnsteps Γ (S n) cfg1 cfg3.

Definition zero_store : store := Vector.const 0 10%nat.
Definition Γ0 : penv := fun _ => mkproc List.nil Sskip.

(*  X0 += 1;  if X0 then X1 ^= 3 else skip fi X0  *)
Definition ex_prog : stmt :=
  Sseq (Sass X0 Uadd (Econst 1))
       (Sif (Evar X0) (Sass X1 Uxor (Econst 3)) Sskip (Evar X0)).

Definition ex_final : store := update (update zero_store X0 1) X1 3.

Example j_example_run :
  jnsteps Γ0 7%nat (CS_pre ex_prog, zero_store) (CS_post ex_prog, ex_final).
Proof.
  unfold ex_prog.
  eapply JN_step. { apply J_Seq_Enter. }
  eapply JN_step. { apply J_Ctx_Seq_L. apply J_Asn. }
  eapply JN_step. { apply J_Seq_Mid. }
  eapply JN_step. { apply J_Ctx_Seq_R. apply J_If_True. cbv; discriminate. }
  eapply JN_step. { apply J_Ctx_Seq_R. apply J_Ctx_If_Then. apply J_Asn. }
  eapply JN_step. { apply J_Ctx_Seq_R. apply J_Fi_True. cbv; discriminate. }
  eapply JN_step. { apply J_Seq_Exit. }
  apply JN_refl.
Qed.

(* ---- 15a. Parameters: conservative extension and worked examples ---- *)

Lemma rename_expr_id : forall e, rename_expr (fun v => v) e = e.
Proof. induction e; simpl; congruence. Qed.

Lemma map_id_var : forall l : list var, List.map (fun v => v) l = l.
Proof. induction l; simpl; congruence. Qed.

Lemma rename_id : forall st, rename (fun v => v) st = st.
Proof.
  induction st; simpl; rewrite ?rename_expr_id, ?map_id_var; congruence.
Qed.

Lemma inj_onb_id : forall l, inj_onb (fun v => v) l = true.
Proof.
  intro l; unfold inj_onb; apply List.forallb_forall; intros u _.
  apply List.forallb_forall; intros w _.
  unfold var_eqb; destruct (Fin.eq_dec u w); reflexivity.
Qed.

(* A parameterless procedure called with no arguments runs its body
   unchanged, and the call is always accepted: the parameterless fragment
   of the previous version of this file is the special case formals = []. *)
Lemma inst_no_params : forall b, inst (mkproc List.nil b) List.nil = b.
Proof. intro b; unfold inst; simpl; apply rename_id. Qed.

Lemma call_ok_no_params : forall b, call_ok (mkproc List.nil b) List.nil = true.
Proof. intro b; unfold call_ok; simpl; apply inj_onb_id. Qed.

(* A bounded runner over the verified stepper. *)
Fixpoint run (Γ : penv) (n : nat) (cfg : cont_stmt * store) : cont_stmt * store :=
  match n with
  | O => cfg
  | S n' => match step_fun Γ (fst cfg) (snd cfg) with
            | Some cfg' => run Γ n' cfg'
            | None => cfg
            end
  end.

(* procedure 0 (a, b):  a += b      with formals a = X0, b = X1
   procedure 1 (a)   :  a ^= X1     X1 is a global *)
Definition Γ1 : penv := fun p =>
  match p with
  | O => mkproc (X0 :: X1 :: List.nil) (Sass X0 Uadd (Evar X1))
  | _ => mkproc (X0 :: List.nil) (Sass X0 Uxor (Evar X1))
  end.

Lemma wf_penv_Γ1 : wf_penv Γ1.
Proof.
  intros [|p]; simpl; constructor; constructor; intro H; discriminate H.
Qed.

(*  X2 += 5;  call 0 (X3, X2)  : X3 is updated through the formal a. *)
Definition ex_call : stmt :=
  Sseq (Sass X2 Uadd (Econst 5)) (Scall 0%nat (X3 :: X2 :: List.nil)).

Example j_call_by_reference :
  run Γ1 10%nat (CS_pre ex_call, zero_store)
  = (CS_post ex_call, update (update zero_store X2 5) X3 5).
Proof. vm_compute. reflexivity. Qed.

(* uncall 0 (X3, X2) from that store undoes the call: X3 is back to 0. *)
Example j_uncall_undoes_call :
  run Γ1 10%nat (CS_pre (Suncall 0%nat (X3 :: X2 :: List.nil)),
             update (update zero_store X2 5) X3 5)
  = (CS_post (Suncall 0%nat (X3 :: X2 :: List.nil)), update zero_store X2 5).
Proof. vm_compute. reflexivity. Qed.

(* Aliasing between two actuals: call 0 (X2, X2) is stuck. *)
Example j_alias_actuals_stuck :
  step_fun Γ1 (CS_pre (Scall 0%nat (X2 :: X2 :: List.nil))) zero_store = None.
Proof. vm_compute. reflexivity. Qed.

(* Aliasing between an actual and a global the body uses: call 1 (X1)
   would run X1 ^= X1, which is not well-formed; the call is stuck. *)
Example j_alias_global_stuck :
  step_fun Γ1 (CS_pre (Scall 1%nat (X1 :: List.nil))) zero_store = None.
Proof. vm_compute. reflexivity. Qed.

(* The side condition is not decorative: without it, a well-formed
   environment would instantiate a body that is not well-formed, and
   backward determinism would fail inside the call. *)
Example alias_breaks_wf :
  wf_penv Γ1 /\ ~ wf_stmt (inst (Γ1 1%nat) (X1 :: List.nil)).
Proof.
  split; [exact wf_penv_Γ1 |].
  vm_compute. intro H; inversion H; subst.
  match goal with [ Hn : nf_expr _ _ |- _ ] => inversion Hn; subst end.
  match goal with [ Hne : ?a <> ?a |- _ ] => apply Hne; reflexivity end.
Qed.

(* ================================================================= *)
(* 16. Axiom audit                                                    *)
(* ================================================================= *)

(* Every top-level result of this file.  tools/audit.sh (with
   SRC=janus/janus.v) checks that this block is complete and that every
   line prints "Closed under the global context". *)
Print Assumptions update_eq.
Print Assumptions update_neq.
Print Assumptions store_ext.
Print Assumptions update_injective_off_x.
Print Assumptions update_value_at_x.
Print Assumptions update_cancel.
Print Assumptions apply_upd_injective.
Print Assumptions apply_upd_inv.
Print Assumptions inv_upd_involutive.
Print Assumptions eval_update_invariant.
Print Assumptions eval_agree.
Print Assumptions asn_step_injective.
Print Assumptions no_step_from_post.
Print Assumptions no_step_to_pre.
Print Assumptions jstep_deterministic.
Print Assumptions inv_involutive.
Print Assumptions wf_stmt_inv.
Print Assumptions wf_cs_step_preserved_cfg.
Print Assumptions wf_cs_step_reflected_cfg.
Print Assumptions wf_cs_step_preserved.
Print Assumptions wf_cs_step_reflected.
Print Assumptions jstep_bwd_deterministic.
Print Assumptions jstep_bwd_deterministic_tgt.
Print Assumptions bstep_deterministic.
Print Assumptions cs_inv_involutive.
Print Assumptions wf_cs_cs_inv.
Print Assumptions J_Asn'.
Print Assumptions inv_step_reverses_cfg.
Print Assumptions inv_step_reverses.
Print Assumptions inv_step_reverses_iff.
Print Assumptions bstep_is_fwd_of_inv.
Print Assumptions step_fun_sound.
Print Assumptions step_fun_complete.
Print Assumptions step_fun_correct.
Print Assumptions step_fun_post_is_none.
Print Assumptions j_example_run.
Print Assumptions rename_inv.
Print Assumptions var_eqb_true.
Print Assumptions inj_onb_spec.
Print Assumptions inj_on_app_l.
Print Assumptions inj_on_app_r.
Print Assumptions nf_expr_rename.
Print Assumptions wf_stmt_rename.
Print Assumptions wf_inst.
Print Assumptions rename_expr_id.
Print Assumptions map_id_var.
Print Assumptions rename_id.
Print Assumptions inj_onb_id.
Print Assumptions inst_no_params.
Print Assumptions call_ok_no_params.
Print Assumptions wf_penv_Γ1.
Print Assumptions j_call_by_reference.
Print Assumptions j_uncall_undoes_call.
Print Assumptions j_alias_actuals_stuck.
Print Assumptions j_alias_global_stuck.
Print Assumptions alias_breaks_wf.
