(*
  proofs.v -- Coq/Rocq formalization of the small-step reversible operational
  semantics for R-CORE, together with a proof of

      RC2026:Lem 1 (Reversibility of controlled command evaluation)

  from

      "Small-Step Semantics with Meta-Level Reversibility for a Reversible
       Core Language" (Makino & Yokoyama, RC 2026, submission 7435).

  Two documents are referred to throughout this file.  RC2026 is the
  paper above; Letter is the companion IEICE letter "A Machine-Checked
  Formalization of the Meta-Level Reversible Small-Step Semantics of
  the Reversible Core Language R-CORE" (Ebisu, Makino & Yokoyama).
  Claims are cited as RC2026:Lem 1 / Letter:Thm 1, with the LaTeX label
  of the corresponding source given in brackets where it helps.

  We prove both implications stated in the paper:

     RC2026:Lem 1, forward  [lem:rev_com]   forward determinism
        (C,sigma)->(C',sigma') /\ (C,sigma)->(C'',sigma'')
          => C' = C'' /\ sigma' = sigma''

     RC2026:Lem 1, backward [lem:rev_com2]  backward determinism
        (C,sigma)<-(C',sigma') /\ (C,sigma)<-(C'',sigma'')
          => C' = C'' /\ sigma' = sigma''

  Correspondence with the Letter, whose numbering is independent:

     Letter:Thm 1 [thm:fwd]   forward determinism
                              = [ss_step_deterministic] / [rev_com_forward]
     Letter:Lem 1 [lem:refl]  reflection of well-formedness
                              = [wf_cc_step_reflected]      (Sect. 32)
     Letter:Thm 2 [thm:bwd]   backward determinism, hypothesising
                              well-formedness of the single COMMON TARGET
                              = [ss_bwd_deterministic_tgt]  (Sect. 32)
     Letter:Lem 2 [lem:pres]  preservation of well-formedness
                              = [wf_cc_step_preserved]      (Sect. 8)
     Letter:Thm 3 [thm:equiv] equivalence of ds, ss and fss
                              = [semantic_equivalence_p]    (Sect. 39)
                              in the fixed-position reading of fss that
                              the Letter states; [semantic_equivalence]
                              (Sect. 27) is the same equivalence for the
                              residual-flowchart reading.

  Note that Letter:Thm 2 is NOT [ss_bwd_deterministic] (Sect. 8), which
  is the paper-faithful form hypothesising well-formedness of both
  predecessors.  The two are equivalent by [wf_cc_step_reflected].

  As discussed in the paper (Section 3, Asn rules), an R-CORE assignment
  "X ^= E" is well-formed only when X does not occur free in E (otherwise
  the assignment is not a partial injection).  Forward determinism does not
  need this restriction, but backward determinism does.  We capture the
  side condition via a well-formedness predicate [wf_cmd] and prove the
  backward direction relative to it.

  Tested with Coq/Rocq 8.20+/9.1.1.
*)

From Stdlib Require Import Arith List Bool.
From Stdlib Require Import Vectors.Vector Vectors.Fin Vectors.VectorSpec.
Set Implicit Arguments.

(* This development is fully axiom-free.  In particular, [store_ext] —
   the pointwise => Leibniz [=] bridge on stores — is derived
   constructively from [Vector.eq_nth_iff], avoiding the need for
   functional_extensionality.  The paper's 10-variable convention
   ([Variables ::= X0 | X1 | ... | X9], main.tex:367) is realized at
   the type level via [var := Fin.t 10] and [store := Vector.t val 10]. *)

(* ================================================================= *)
(* 1. Syntax                                                          *)
(* ================================================================= *)

(* Variables.  The paper (main.tex:367) fixes the 10-variable convention
   [Variables ::= X0 | X1 | ... | X9]; this formalization realizes that
   convention at the type level via [Fin.t 10] (a finite type with
   exactly 10 inhabitants).  Design decision: switch from the earlier
   [var := nat] encoding to [var := Fin.t 10] in order to eliminate
   the last [functional_extensionality] dependency. *)
Definition var := Fin.t 10.

Inductive val : Type :=
  | Vnil  : val
  | Vpair : val -> val -> val.

Fixpoint val_eq_dec (v1 v2 : val) : {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Defined.

Inductive expr : Type :=
  | Evar  (x : var)
  | Enil
  | Ehd   (x : var)
  | Etl   (x : var)
  | Econs (x y : var)
  | Eeq   (x y : var).

Inductive cmd : Type :=
  | Cass  (x : var) (e : expr)
  | Cseq  (c1 c2 : cmd)
  | Cloop (x : var) (c : cmd) (y : var).

(* Surface-syntax notations matching the paper's R-CORE.
   - [x ^= e]            for [Cass x e]   (reversible assignment)
   - [c1 ; c2]           for [Cseq c1 c2] (sequence)
   - [from x loop c until y] for [Cloop x c y]
   Declared in a dedicated [rcore_scope] and opened by default for the
   rest of the file; both parsing and printing use the surface forms. *)
Declare Scope rcore_scope.
Delimit Scope rcore_scope with rcore.
Bind Scope rcore_scope with cmd.
Bind Scope rcore_scope with var.   (* makes the [X0..X9] names the
                                       printer's default for [var]-typed
                                       positions ([var := Fin.t 10]). *)

Notation "x '^=' e" := (Cass x e)
  (at level 75, no associativity) : rcore_scope.
Notation "c1 ; c2" := (Cseq c1 c2)
  (at level 90, right associativity) : rcore_scope.
Notation "'from' x 'loop' c 'until' y" := (Cloop x c y)
  (at level 80, x at level 0, y at level 0) : rcore_scope.

(* Paper-style variable names — the 10 paper variables [X0..X9] are
   realized as Definitions over [Fin.t 10].  Because they are
   first-class names (not Notations), Coq's printer prefers them in
   [var]-typed positions automatically. *)
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

Open Scope rcore_scope.

(* Controlled commands: a command tree with exactly one control token. *)
Inductive cont_cmd : Type :=
  | CC_at_pre   (c  : cmd)
  | CC_at_post  (c  : cmd)
  | CC_mid_loop (x  : var) (c : cmd) (y : var)
  | CC_seq_L    (cc : cont_cmd) (c2 : cmd)
  | CC_seq_R    (c1 : cmd) (cc : cont_cmd)
  | CC_in_loop  (x  : var) (cc : cont_cmd) (y : var).

(* Surface notation for the controlled command (the paper's evaluation
   context E with explicit token position, main.tex L1249/1269).  We
   use Unicode [•] for the control token, matching the paper's
   [\bullet], and angle brackets [⟨ ⟩] to mark "the side that holds
   the hole" in the compositional cases (since [;] alone cannot tell
   [CC_seq_L cc c] apart from [CC_seq_R c cc]).

     paper                       Rocq surface         constructor
     ----------------------------------------------------------------
     •c                          •c                   CC_at_pre  c
     c•                          c •                  CC_at_post c
     •from X loop c until Y      •from x loop c until y   CC_mid_loop x c y
     E ; D    (token in E)       cc ;▷ c              CC_seq_L cc c
     D ; E    (token in E)       c ◁; cc              CC_seq_R c cc
     from X loop E until Y       from x loop ⟨ cc ⟩ until y   CC_in_loop x cc y

   The [▷]/[◁] arrows point at the side that holds the active hole.    *)

Bind Scope rcore_scope with cont_cmd.

Notation "'•' c" := (CC_at_pre c)
  (at level 35, c at level 35, no associativity) : rcore_scope.
Notation "c '•'" := (CC_at_post c)
  (at level 35, no associativity) : rcore_scope.
Notation "'•from' x 'loop' c 'until' y" := (CC_mid_loop x c y)
  (at level 80, x at level 0, y at level 0) : rcore_scope.
Notation "cc ';▷' c" := (CC_seq_L cc c)
  (at level 90, right associativity) : rcore_scope.
Notation "c '◁;' cc" := (CC_seq_R c cc)
  (at level 90, right associativity) : rcore_scope.
Notation "'from' x 'loop' '⟨' cc '⟩' 'until' y" := (CC_in_loop x cc y)
  (at level 80, x at level 0, y at level 0) : rcore_scope.

(* ================================================================= *)
(* 2. Stores and semantic auxiliaries                                 *)
(* ================================================================= *)

Definition store := Vector.t val 10.

(* A store can be APPLIED as a function via the [lookup] coercion, so
   the existing semantic code [s x] keeps working without change. *)
Definition lookup (s : store) : var -> val := Vector.nth (n:=10) s.
Coercion lookup : store >-> Funclass.

Definition update (s : store) (x : var) (v : val) : store :=
  Vector.replace s x v.

(* Default the names [s], [s'] to type [store] in untyped binders.
   Coq extends [Implicit Types] to numeric variants ([s1], [s2], ...)
   automatically; the prefixes [s_pre], [s_mid], etc. are introduced
   when needed by explicit annotation. *)
Implicit Type s : store.

Definition eval_expr (s : store) (e : expr) : option val :=
  match e with
  | Evar x   => Some (s x)
  | Enil     => Some Vnil
  | Ehd x    => match s x with Vpair a _ => Some a | _ => None end
  | Etl x    => match s x with Vpair _ b => Some b | _ => None end
  | Econs x y => Some (Vpair (s x) (s y))
  | Eeq x y  => if val_eq_dec (s x) (s y)
                then Some (Vpair Vnil Vnil) else Some Vnil
  end.

(* Reversible update operator d (+) e, as in paper Eq.~odot. *)
Definition odot (d e : val) : option val :=
  match d with
  | Vnil => Some e
  | _    => if val_eq_dec d e then Some Vnil else None
  end.

(* ================================================================= *)
(* 3. Small-step semantics                                            *)
(* ================================================================= *)

Inductive exec_ss : cont_cmd * store -> cont_cmd * store -> Prop :=
  | S_Asn       : forall x e s v_e v_new,
      eval_expr s e = Some v_e ->
      odot (s x) v_e = Some v_new ->
      exec_ss (CC_at_pre  (Cass x e), s)
           (CC_at_post (Cass x e), update s x v_new)
  | S_LoopEnter : forall x c y s,
      s x <> Vnil ->
      exec_ss (CC_at_pre (Cloop x c y), s) (CC_mid_loop x c y, s)
  | S_LoopExit  : forall x c y s,
      s y <> Vnil ->
      exec_ss (CC_mid_loop x c y, s) (CC_at_post (Cloop x c y), s)
  | S_LoopIter1 : forall x c y s,
      s y = Vnil ->
      exec_ss (CC_mid_loop x c y, s) (CC_in_loop x (CC_at_pre c) y, s)
  | S_LoopIter2 : forall x c y s,
      s x = Vnil ->
      exec_ss (CC_in_loop x (CC_at_post c) y, s) (CC_mid_loop x c y, s)
  | S_Seq_Enter : forall c1 c2 s,
      exec_ss (CC_at_pre (Cseq c1 c2), s) (CC_seq_L (CC_at_pre c1) c2, s)
  | S_Seq_Mid   : forall c1 c2 s,
      exec_ss (CC_seq_L (CC_at_post c1) c2, s) (CC_seq_R c1 (CC_at_pre c2), s)
  | S_Seq_Exit  : forall c1 c2 s,
      exec_ss (CC_seq_R c1 (CC_at_post c2), s) (CC_at_post (Cseq c1 c2), s)
  | S_Ctx_Seq_L : forall cc cc' c2 s s',
      exec_ss (cc, s) (cc', s') ->
      exec_ss (CC_seq_L cc c2, s) (CC_seq_L cc' c2, s')
  | S_Ctx_Seq_R : forall c1 cc cc' s s',
      exec_ss (cc, s) (cc', s') ->
      exec_ss (CC_seq_R c1 cc, s) (CC_seq_R c1 cc', s')
  | S_Ctx_Loop  : forall x cc cc' y s s',
      exec_ss (cc, s) (cc', s') ->
      exec_ss (CC_in_loop x cc y, s) (CC_in_loop x cc' y, s').

(* ================================================================= *)
(* 4. Basic store and operator lemmas                                 *)
(* ================================================================= *)

Lemma update_eq : forall s x v, update s x v x = v.
Proof. intros. unfold update, lookup. apply nth_replace_eq. Qed.

Lemma update_neq : forall s x y v, x <> y -> update s x v y = s y.
Proof.
  intros s x y v Hxy. unfold update, lookup.
  apply nth_replace_neq. auto.
Qed.

(* Reversibility of odot: applying (-)(+)e twice yields the original d. *)
Lemma odot_inv : forall d e v, odot d e = Some v -> odot v e = Some d.
Proof.
  intros d e v H. unfold odot in *.
  destruct d as [|d1 d2].
  - (* d = Vnil; H : Some e = Some v, so v = e. *)
    injection H as H'. subst v. destruct e as [|v1 v2].
    + reflexivity.
    + destruct (val_eq_dec (Vpair v1 v2) (Vpair v1 v2)) as [_|N]; [reflexivity|now elim N].
  - (* d = Vpair d1 d2. *)
    destruct (val_eq_dec (Vpair d1 d2) e) as [Heq|Hne].
    + (* d = e, so v = Vnil. *)
      injection H as H'. subst v. subst e. reflexivity.
    + discriminate H.
Qed.

(* Injectivity of (\d. odot d e) on its domain: this is the property that
   makes the merged S_Asn rule backward-deterministic in the d component. *)
Lemma odot_left_injective :
  forall d1 d2 e v,
    odot d1 e = Some v ->
    odot d2 e = Some v ->
    d1 = d2.
Proof.
  intros d1 d2 e v H1 H2. unfold odot in H1, H2.
  destruct d1 as [|a1 a2]; destruct d2 as [|b1 b2].
  - reflexivity.
  - (* d1 = Vnil, d2 = Vpair b1 b2 *)
    injection H1 as H1'. subst v.
    destruct (val_eq_dec (Vpair b1 b2) e) as [Heq|Hne]; [|discriminate].
    injection H2 as H2'. subst e. discriminate.
  - (* d1 = Vpair a1 a2, d2 = Vnil *)
    injection H2 as H2'. subst v.
    destruct (val_eq_dec (Vpair a1 a2) e) as [Heq|Hne]; [|discriminate].
    injection H1 as H1'. subst e. discriminate.
  - (* d1 = Vpair a1 a2, d2 = Vpair b1 b2 *)
    destruct (val_eq_dec (Vpair a1 a2) e) as [Ha|Ha]; [|discriminate].
    destruct (val_eq_dec (Vpair b1 b2) e) as [Hb|Hb]; [|discriminate].
    subst e. now rewrite <- Hb.
Qed.

(* When the AsnSet/AsnClear premise of S_Asn applies, the destination
   store overwrites the variable, so the original value of x is forgotten
   except through [odot].  This lemma will let us recover the original
   store from the post-state. *)
Lemma update_injective_off_x :
  forall (s1 s2 : store) (x : var) (v1 v2 : val),
    update s1 x v1 = update s2 x v2 ->
    forall y, y <> x -> s1 y = s2 y.
Proof.
  intros s1 s2 x v1 v2 Heq y Hy.
  assert (Hpoint : update s1 x v1 y = update s2 x v2 y) by (rewrite Heq; reflexivity).
  rewrite !update_neq in Hpoint by (intro; apply Hy; auto). exact Hpoint.
Qed.

Lemma update_value_at_x :
  forall (s1 s2 : store) (x : var) (v1 v2 : val),
    update s1 x v1 = update s2 x v2 -> v1 = v2.
Proof.
  intros s1 s2 x v1 v2 Heq.
  assert (H : update s1 x v1 x = update s2 x v2 x) by (rewrite Heq; reflexivity).
  rewrite !update_eq in H. exact H.
Qed.

(* ================================================================= *)
(* 5. "No step from C bullet" -- terminal configurations are stuck.   *)
(* ================================================================= *)

(* CC_at_post c is terminal: no inference rule lists it as an LHS at the
   top level, and no congruence rule applies because CC_at_post has no
   internal cont_cmd.  *)
Lemma no_step_from_at_post :
  forall c s cfg, ~ exec_ss (CC_at_post c, s) cfg.
Proof.
  intros c s cfg Hstep. inversion Hstep.
Qed.

(* ================================================================= *)
(* 6. Forward determinism (RC2026:Lem 1 forward; Letter:Thm 1)       *)
(* ================================================================= *)

Ltac kill_post :=
  exfalso;
  match goal with
  | [ Hbad : exec_ss (CC_at_post _, _) _ |- _ ] =>
      eapply no_step_from_at_post; exact Hbad
  end.

Ltac use_IH :=
  match goal with
  | [ IH : forall cfg2, exec_ss _ cfg2 -> _ = cfg2,
      Hinner : exec_ss _ ?cfg' |- _ ] =>
      let E := fresh "E" in
      pose proof (IH _ Hinner) as E; injection E as ? ?; subst; reflexivity
  end.

(* Letter:Thm 1 (Forward determinism); RC2026:Lem 1, forward. *)
Theorem ss_step_deterministic :
  forall cfg cfg1 cfg2,
    exec_ss cfg cfg1 -> exec_ss cfg cfg2 -> cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1; revert cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst;
    try reflexivity; try contradiction; try kill_post; try use_IH.
  (* Only S_Asn vs. S_Asn remains: unify v_e and v_new. *)
  match goal with
  | [ He : eval_expr ?s ?e = Some _ |- _ ] =>
      rewrite H in He; injection He; intros; subst
  end.
  match goal with
  | [ Ho : odot _ _ = Some _ |- _ ] =>
      rewrite H0 in Ho; injection Ho; intros; subst
  end.
  reflexivity.
Qed.

(* ================================================================= *)
(* 7. Well-formedness for backward determinism                         *)
(* ================================================================= *)

(* x does not occur in expression e.  This corresponds to the standard
   R-CORE / Janus syntactic restriction that the variable being updated
   does not appear free in the right-hand side. *)
Inductive nf_expr (x : var) : expr -> Prop :=
  | nf_Evar  : forall y, y <> x -> nf_expr x (Evar y)
  | nf_Enil  : nf_expr x Enil
  | nf_Ehd   : forall y, y <> x -> nf_expr x (Ehd y)
  | nf_Etl   : forall y, y <> x -> nf_expr x (Etl y)
  | nf_Econs : forall y z, y <> x -> z <> x -> nf_expr x (Econs y z)
  | nf_Eeq   : forall y z, y <> x -> z <> x -> nf_expr x (Eeq y z).

Inductive wf_cmd : cmd -> Prop :=
  | wf_Cass  : forall x e, nf_expr x e -> wf_cmd (Cass x e)
  | wf_Cseq  : forall c1 c2, wf_cmd c1 -> wf_cmd c2 -> wf_cmd (Cseq c1 c2)
  | wf_Cloop : forall x c y, wf_cmd c -> wf_cmd (Cloop x c y).

(* The self-assignment [X ^= X] the Conclusion points to as the source
   of backward-nondeterminism (it collapses every value to [nil]) is
   exactly what [nf_expr] excludes: no [x] is free of itself. *)
Lemma nf_expr_not_self : forall x, ~ nf_expr x (Evar x).
Proof. intros x H; inversion H; congruence. Qed.

(* Well-formedness is decidable: [nf_expr] and [wf_cmd] reduce to
   disequality tests on [var := Fin.t 10], which is itself decidable.
   This gives the syntactic check a reversible interpreter or debugger
   performs once per program (Sect.~7 of the letter) an actual
   decision procedure, not just a proposition. *)
Definition nf_expr_dec (x : var) (e : expr) : {nf_expr x e} + {~ nf_expr x e}.
Proof.
  destruct e as [y | | y | y | y z | y z].
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + left; constructor; exact Hy.
  - left; constructor.
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + left; constructor; exact Hy.
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + left; constructor; exact Hy.
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + destruct (Fin.eq_dec z x) as [-> | Hz].
      * right; intro H; inversion H; congruence.
      * left; constructor; assumption.
  - destruct (Fin.eq_dec y x) as [-> | Hy].
    + right; intro H; inversion H; congruence.
    + destruct (Fin.eq_dec z x) as [-> | Hz].
      * right; intro H; inversion H; congruence.
      * left; constructor; assumption.
Defined.

Fixpoint wf_cmd_dec (c : cmd) : {wf_cmd c} + {~ wf_cmd c}.
Proof.
  destruct c as [x e | c1 c2 | x c y].
  - destruct (nf_expr_dec x e) as [Hnf | Hnf].
    + left; constructor; exact Hnf.
    + right; intro H; inversion H; subst; contradiction.
  - destruct (wf_cmd_dec c1) as [Hwf1 | Hwf1].
    + destruct (wf_cmd_dec c2) as [Hwf2 | Hwf2].
      * left; constructor; assumption.
      * right; intro H; inversion H; subst; contradiction.
    + right; intro H; inversion H; subst; contradiction.
  - destruct (wf_cmd_dec c) as [Hwf | Hwf].
    + left; constructor; exact Hwf.
    + right; intro H; inversion H; subst; contradiction.
Defined.

(* eval_expr is unaffected by updates at variables not free in e. *)
Lemma eval_expr_update_invariant :
  forall x e s v,
    nf_expr x e ->
    eval_expr (update s x v) e = eval_expr s e.
Proof.
  intros x e s v Hnf. destruct Hnf; simpl; try reflexivity.
  - now rewrite update_neq by auto.
  - now rewrite update_neq by auto.
  - now rewrite update_neq by auto.
  - now rewrite !update_neq by auto.
  - now rewrite !update_neq by auto.
Qed.

(* If two stores agree everywhere except possibly at x and evaluating
   an x-free expression on either gives the same answer. *)
Lemma eval_expr_agree :
  forall x e s s',
    nf_expr x e ->
    (forall y, y <> x -> s y = s' y) ->
    eval_expr s e = eval_expr s' e.
Proof.
  intros x e s s' Hnf Hag. destruct Hnf; simpl.
  - now rewrite (Hag _ H).
  - reflexivity.
  - now rewrite (Hag _ H).
  - now rewrite (Hag _ H).
  - now rewrite (Hag _ H), (Hag _ H0).
  - now rewrite (Hag _ H), (Hag _ H0).
Qed.

(* ------------------------------------------------------------------ *
   Pointwise => Leibniz [=] for stores — derived constructively.

   With [store := Vector.t val 10], two stores that agree at every
   index are Leibniz-equal: this is [VectorSpec.eq_nth_iff] applied to
   the finite vector representation.  No axiom needed.

   (Earlier formalizations used [store := var -> val] and required
   [functional_extensionality_dep]; that axiom was removed in the
   vector-store refactor.) *)
Lemma store_ext : forall s1 s2 : store, (forall y, s1 y = s2 y) -> s1 = s2.
Proof.
  intros s1 s2 H. apply eq_nth_iff. intros p1 p2 ->. apply H.
Qed.

(* ================================================================= *)
(* 8. Backward determinism (RC2026:Lem 1 backward), modulo wf        *)
(*    For the Letter's form (Letter:Thm 2), see Sect. 32.            *)
(* ================================================================= *)

(* In the backward direction we case-analyse on the *target* configuration
   and use injectivity (no two source configurations produce the same
   target).  We carry a [wf_cmd] hypothesis attached to the *top-level*
   command of the source so that the AsnSet/AsnClear case can apply
   [odot_left_injective] under the assumption that the variable does not
   appear in the right-hand side. *)

(* Well-formedness of a controlled command: just well-formedness of
   every cmd inside it. *)
Inductive wf_cc : cont_cmd -> Prop :=
  | wf_pre   : forall c, wf_cmd c -> wf_cc (CC_at_pre c)
  | wf_post  : forall c, wf_cmd c -> wf_cc (CC_at_post c)
  | wf_mid   : forall x c y, wf_cmd c -> wf_cc (CC_mid_loop x c y)
  | wf_seq_L : forall cc c2, wf_cc cc -> wf_cmd c2 -> wf_cc (CC_seq_L cc c2)
  | wf_seq_R : forall c1 cc, wf_cmd c1 -> wf_cc cc -> wf_cc (CC_seq_R c1 cc)
  | wf_in_lp : forall x cc y, wf_cc cc -> wf_cc (CC_in_loop x cc y).

Hint Constructors wf_cmd wf_cc nf_expr : core.
Hint Constructors exec_ss : r_db.

(* Surface notation for single-step transitions:  [cfg1 ==> cfg2]
   denotes [exec_ss cfg1 cfg2].  Each [cfg] is a pair [(cc, s)].
   We use [==>] rather than the more paper-faithful [=>] because the
   single-arrow form clashes irreparably with Coq's [fun .. => ..] syntax. *)
Notation "cfg1 '==>' cfg2" := (exec_ss cfg1 cfg2)
  (at level 70, no associativity) : rcore_scope.

(* Steps preserve well-formedness (Letter:Lem 2). *)
Lemma wf_cc_step_preserved :
  forall cc s cc' s', exec_ss (cc, s) (cc', s') -> wf_cc cc -> wf_cc cc'.
Proof.
  intros cc s cc' s' Hstep Hwf.
  remember (cc, s) as cfg eqn:E1; remember (cc', s') as cfg' eqn:E2.
  revert cc s cc' s' E1 E2 Hwf.
  induction Hstep; intros; inversion E1; inversion E2; subst; clear E1 E2;
    repeat match goal with
    | [ H : wf_cc (CC_at_pre _)   |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_at_post _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_mid_loop _ _ _) |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_seq_L _ _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_seq_R _ _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_in_loop _ _ _) |- _ ] => inversion H; subst; clear H
    | [ H : wf_cmd (Cass _ _)     |- _ ] => inversion H; subst; clear H
    | [ H : wf_cmd (Cseq _ _)     |- _ ] => inversion H; subst; clear H
    | [ H : wf_cmd (Cloop _ _ _)  |- _ ] => inversion H; subst; clear H
    end;
    try (econstructor; eauto; fail);
    (* Context rule cases: use IH. *)
    try (constructor; [eapply IHHstep; eauto | eauto]);
    try (constructor; [eauto | eapply IHHstep; eauto]);
    try (constructor; eapply IHHstep; eauto).
Qed.

(* Lemma: no rule of [exec_ss] has [CC_at_pre c] as its RHS.
   Useful to discharge "ctx step ends at CC_at_pre" obligations. *)
Lemma no_step_to_at_pre :
  forall c s cfg, ~ exec_ss cfg (CC_at_pre c, s).
Proof.
  intros c s cfg Hstep. inversion Hstep.
Qed.

Ltac kill_step_to_at_pre :=
  exfalso;
  match goal with
  | [ Hbad : exec_ss _ (CC_at_pre _, _) |- _ ] =>
      eapply no_step_to_at_pre; exact Hbad
  end.

(* Backward determinism, the paper-faithful form (RC2026:Lem 1
   backward).  Both predecessors are hypothesised; for the Letter's
   single-hypothesis form see [ss_bwd_deterministic_tgt] in Sect. 32. *)
Theorem ss_bwd_deterministic :
  forall cfg1 cfg2 cfg,
    wf_cc (fst cfg1) -> wf_cc (fst cfg2) ->
    exec_ss cfg1 cfg -> exec_ss cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros cfg1 cfg2 cfg Hwf1 Hwf2 H1; revert cfg2 Hwf1 Hwf2.
  induction H1; intros cfg2 Hwf1 Hwf2 H2; simpl in *; inversion H2; subst;
    try reflexivity;
    try contradiction;
    try kill_post;
    try kill_step_to_at_pre.
  - (* S_Asn vs. S_Asn.  Recover the post-store equation [update s0 x v_new0
       = update s x v_new] coming out of [inversion H2; subst], plus the
       primed [eval_expr] and [odot] hypotheses. *)
    assert (Hnf : nf_expr x e).
    { inversion Hwf1 as
        [c0 Hwfc0
        | c0 Hwfc0
        | x0 c0 y0 Hwfc0
        | cc0 c0 Hwfc0 Hwfc0'
        | c0 cc0 Hwfc0 Hwfc0'
        | x0 cc0 y0 Hwfc0]; subst; inversion Hwfc0; subst; assumption. }
    (* Recover the pre-store equality: off-x agreement comes from
       [update_injective_off_x], the written values coincide by
       [update_value_at_x], the x-free RHS evaluates identically on both
       pre-stores ([eval_expr_agree]), so [odot_left_injective] pins the
       value at x itself; constructive [store_ext] then closes pointwise
       agreement into Leibniz equality. *)
    match goal with
    | [ Hupd : update ?sa x ?vna = update ?sb x ?vnb |- _ ] =>
        let Hoff := fresh "Hoff" in
        let Hveq := fresh "Hveq" in
        let Hagr := fresh "Hagr" in
        let Hx   := fresh "Hx"   in
        let Hss  := fresh "Hss"  in
        pose proof (update_injective_off_x _ _ _ _ Hupd) as Hoff;
        pose proof (update_value_at_x _ _ _ _ _ Hupd) as Hveq;
        subst vna;
        pose proof (eval_expr_agree _ _ Hnf Hoff) as Hagr;
        match goal with
        | [ Hea : eval_expr sa e = Some _, Heb : eval_expr sb e = Some _ |- _ ] =>
            rewrite Hea, Heb in Hagr; injection Hagr as ->
        end;
        assert (Hx : sa x = sb x) by (eapply odot_left_injective; eauto);
        assert (Hss : sa = sb)
          by (apply store_ext; intros y;
              destruct (Fin.eq_dec y x) as [->|Hy]; [exact Hx | apply Hoff; exact Hy]);
        subst sa; reflexivity
    end.
  - (* S_Ctx_Seq_L vs. S_Ctx_Seq_L *)
    inversion Hwf1; subst. inversion Hwf2; subst.
    match goal with
    | [ Hinner : exec_ss (?cc'', ?s0) _ |- _ ] =>
        let E := fresh "E" in
        assert (E : (cc, s) = (cc'', s0))
          by (eapply IHexec_ss; [eassumption|eassumption|exact Hinner]);
        injection E as Hcc Hs; subst; reflexivity
    end.
  - (* S_Ctx_Seq_R vs. S_Ctx_Seq_R *)
    inversion Hwf1; subst. inversion Hwf2; subst.
    match goal with
    | [ Hinner : exec_ss (?cc'', ?s0) _ |- _ ] =>
        let E := fresh "E" in
        assert (E : (cc, s) = (cc'', s0))
          by (eapply IHexec_ss; [eassumption|eassumption|exact Hinner]);
        injection E as Hcc Hs; subst; reflexivity
    end.
  - (* S_Ctx_Loop vs. S_Ctx_Loop *)
    inversion Hwf1; subst. inversion Hwf2; subst.
    match goal with
    | [ Hinner : exec_ss (?cc'', ?s0) _ |- _ ] =>
        let E := fresh "E" in
        assert (E : (cc, s) = (cc'', s0))
          by (eapply IHexec_ss; [eassumption|eassumption|exact Hinner]);
        injection E as Hcc Hs; subst; reflexivity
    end.
Qed.

(* ================================================================= *)
(* 9. Reversibility of controlled command evaluation (RC2026:Lem 1)  *)
(* ================================================================= *)

(* The paper's statement, packaged.  Backward determinism comes with the
   well-formedness hypothesis (X not free in E for every X ^= E inside). *)
Theorem rev_com_forward :
  forall cc s cc' s' cc'' s'',
    exec_ss (cc, s) (cc',  s') ->
    exec_ss (cc, s) (cc'', s'') ->
    cc' = cc'' /\ s' = s''.
Proof.
  intros cc s cc' s' cc'' s'' H1 H2.
  pose proof (ss_step_deterministic H1 H2) as E. injection E as -> ->. auto.
Qed.

Theorem rev_com_backward :
  forall cc s cc' s' cc'' s'',
    wf_cc cc' -> wf_cc cc'' ->
    exec_ss (cc',  s')  (cc, s) ->
    exec_ss (cc'', s'') (cc, s) ->
    cc' = cc'' /\ s' = s''.
Proof.
  intros cc s cc' s' cc'' s'' Hwf1 Hwf2 H1 H2.
  pose proof (ss_bwd_deterministic (cfg1 := (cc',s')) (cfg2 := (cc'',s'')) (cfg := (cc,s))
                Hwf1 Hwf2 H1 H2) as E.
  injection E as -> ->. auto.
Qed.

(* ================================================================= *)
(* 10. Multi-step relation and context lifting                        *)
(* ================================================================= *)

(* Reflexive/transitive closure of [exec_ss]. *)
Inductive exec_ss_star : cont_cmd * store -> cont_cmd * store -> Prop :=
  | exec_ss_star_refl  : forall cfg, exec_ss_star cfg cfg
  | steps_cons  : forall cfg1 cfg2 cfg3,
      exec_ss  cfg1 cfg2 -> exec_ss_star cfg2 cfg3 -> exec_ss_star cfg1 cfg3.
Hint Constructors exec_ss_star : r_db.

Lemma exec_ss_star_trans :
  forall cfg1 cfg2 cfg3, exec_ss_star cfg1 cfg2 -> exec_ss_star cfg2 cfg3 -> exec_ss_star cfg1 cfg3.
Proof.
  intros cfg1 cfg2 cfg3 H1 H2. induction H1 as [|? ? ? Hstep _ IH].
  - exact H2.
  - eapply steps_cons; [exact Hstep | apply IH; exact H2].
Qed.

(* Generic context-lifting lemma on raw configurations; the three
   concrete liftings below are immediate corollaries. *)
Section CtxLift.

Variable F : cont_cmd * store -> cont_cmd * store.
Hypothesis F_step :
  forall cfg cfg', exec_ss cfg cfg' -> exec_ss (F cfg) (F cfg').

Lemma steps_lift :
  forall cfg cfg', exec_ss_star cfg cfg' -> exec_ss_star (F cfg) (F cfg').
Proof.
  intros cfg cfg' H. induction H as [|? ? ? Hstep _ IH].
  - apply exec_ss_star_refl.
  - eapply steps_cons; [apply F_step; exact Hstep | exact IH].
Qed.

End CtxLift.

Lemma steps_ctx_seq_L :
  forall cc s cc' s' c2,
    exec_ss_star (cc, s) (cc', s') ->
    exec_ss_star (CC_seq_L cc c2, s) (CC_seq_L cc' c2, s').
Proof.
  intros cc s cc' s' c2 H.
  pose (F := fun cfg : cont_cmd * store => (CC_seq_L (fst cfg) c2, snd cfg)).
  change (exec_ss_star (F (cc, s)) (F (cc', s'))).
  apply (steps_lift F); [|exact H].
  intros [a sa] [b sb] Hst; simpl. apply S_Ctx_Seq_L. exact Hst.
Qed.

Lemma steps_ctx_seq_R :
  forall cc s cc' s' c1,
    exec_ss_star (cc, s) (cc', s') ->
    exec_ss_star (CC_seq_R c1 cc, s) (CC_seq_R c1 cc', s').
Proof.
  intros cc s cc' s' c1 H.
  pose (F := fun cfg : cont_cmd * store => (CC_seq_R c1 (fst cfg), snd cfg)).
  change (exec_ss_star (F (cc, s)) (F (cc', s'))).
  apply (steps_lift F); [|exact H].
  intros [a sa] [b sb] Hst; simpl. apply S_Ctx_Seq_R. exact Hst.
Qed.

Lemma steps_ctx_loop :
  forall cc s cc' s' x y,
    exec_ss_star (cc, s) (cc', s') ->
    exec_ss_star (CC_in_loop x cc y, s) (CC_in_loop x cc' y, s').
Proof.
  intros cc s cc' s' x y H.
  pose (F := fun cfg : cont_cmd * store => (CC_in_loop x (fst cfg) y, snd cfg)).
  change (exec_ss_star (F (cc, s)) (F (cc', s'))).
  apply (steps_lift F); [|exact H].
  intros [a sa] [b sb] Hst; simpl. apply S_Ctx_Loop. exact Hst.
Qed.

(* ================================================================= *)
(* 11. Denotational semantics                                         *)
(* ================================================================= *)

(* Big-step "denotational" relation for commands, together with the
   auxiliary loop relation, as in Fig.~\ref{fig:ds} of the paper.
   We follow the encoding from the earlier draft `proof1.v` but state
   the loop in a form that matches the paper's `LEntry/LExit/Loop`
   schema more directly. *)
Inductive exec_ds : cmd -> store -> store -> Prop :=
  | D_Asn  : forall x e s v_e v_new,
      eval_expr s e = Some v_e ->
      odot (s x) v_e = Some v_new ->
      exec_ds (Cass x e) s (update s x v_new)
  | D_Seq  : forall c1 c2 s s1 s2,
      exec_ds c1 s s1 -> exec_ds c2 s1 s2 ->
      exec_ds (Cseq c1 c2) s s2
  | D_Loop : forall x c y s s',
      s x <> Vnil ->          (* entry assertion: X is true *)
      loop_sem x c y s s' ->
      exec_ds (Cloop x c y) s s'

with loop_sem : var -> cmd -> var -> store -> store -> Prop :=
  | L_Base : forall x c y s,
      s y <> Vnil ->          (* exit test: Y is true *)
      loop_sem x c y s s
  | L_Rec  : forall x c y s s1 s2,
      s y = Vnil ->           (* Y is false: enter body *)
      exec_ds c s s1 ->
      s1 x = Vnil ->          (* after body, X is false *)
      loop_sem x c y s1 s2 ->
      loop_sem x c y s s2.
Hint Constructors exec_ds loop_sem : eval_db.

Scheme eval_denote_mut := Induction for exec_ds Sort Prop
  with loop_sem_mut    := Induction for loop_sem    Sort Prop.

Combined Scheme exec_ds_loop_mut from eval_denote_mut, loop_sem_mut.

(* ================================================================= *)
(* 12. Theorem 1 (Semantic Equivalence), direction ds -> ss            *)
(* ================================================================= *)

(* Item (1) -> (2) of Theorem~\ref{thm:semantic_equivalence}:
   every denotational evaluation of a command corresponds to a finite
   small-step derivation from the pre-token configuration to the
   post-token configuration. *)
Theorem ds_implies_ss :
  forall c s s',
    exec_ds c s s' ->
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s').
Proof.
  apply (eval_denote_mut
           (fun c s s' _ =>
              exec_ss_star (CC_at_pre c, s) (CC_at_post c, s'))
           (fun x c y s s' _ =>
              exec_ss_star (CC_mid_loop x c y, s) (CC_at_post (Cloop x c y), s'))).
  - (* D_Asn *) intros; eauto with r_db.
  - (* D_Seq *)
    intros c1 c2 s s1 s2 _ IH1 _ IH2.
    eapply steps_cons; [apply S_Seq_Enter|].
    eapply exec_ss_star_trans; [apply steps_ctx_seq_L; exact IH1|].
    eapply steps_cons; [apply S_Seq_Mid|].
    eapply exec_ss_star_trans; [apply steps_ctx_seq_R; exact IH2|].
    eauto with r_db.
  - (* D_Loop *) intros x c y s s' Hx _ IHloop; eauto with r_db.
  - (* L_Base *) intros; eauto with r_db.
  - (* L_Rec *)
    intros x c y s s1 s2 Hyf _ IHbody Hx _ IHrest.
    eapply steps_cons; [apply S_LoopIter1; exact Hyf|].
    eapply exec_ss_star_trans; [apply steps_ctx_loop; exact IHbody|].
    eauto with r_db.
Qed.

(* ================================================================= *)
(* 13. Shape lemmas (for the ss -> ds direction)                       *)
(* ================================================================= *)

(* From CC_at_post c, [exec_ss_star] terminates immediately. *)
Lemma steps_from_at_post :
  forall c s cfg, exec_ss_star (CC_at_post c, s) cfg -> cfg = (CC_at_post c, s).
Proof.
  intros c s cfg H. inversion H as [|cfg1 cfg2 cfg3 Hst]; subst.
  - reflexivity.
  - exfalso. eapply no_step_from_at_post; exact Hst.
Qed.

(* Shape of a single step out of CC_seq_L. *)
Lemma step_from_seq_L_shape :
  forall cc c2 s cfg,
    exec_ss (CC_seq_L cc c2, s) cfg ->
    (exists cc' s', cfg = (CC_seq_L cc' c2, s') /\ exec_ss (cc, s) (cc', s')) \/
    (exists c1, cc = CC_at_post c1 /\ cfg = (CC_seq_R c1 (CC_at_pre c2), s)).
Proof.
  intros cc c2 s cfg Hst. inversion Hst; subst.
  - right. eexists; split; reflexivity.
  - left.  do 2 eexists; split; [reflexivity|assumption].
Qed.

Lemma step_from_seq_R_shape :
  forall c1 cc s cfg,
    exec_ss (CC_seq_R c1 cc, s) cfg ->
    (exists cc' s', cfg = (CC_seq_R c1 cc', s') /\ exec_ss (cc, s) (cc', s')) \/
    (exists c2, cc = CC_at_post c2 /\ cfg = (CC_at_post (Cseq c1 c2), s)).
Proof.
  intros c1 cc s cfg Hst. inversion Hst; subst.
  - right. eexists; split; reflexivity.
  - left. do 2 eexists; split; [reflexivity|assumption].
Qed.

Lemma step_from_in_loop_shape :
  forall x cc y s cfg,
    exec_ss (CC_in_loop x cc y, s) cfg ->
    (exists cc' s', cfg = (CC_in_loop x cc' y, s') /\ exec_ss (cc, s) (cc', s')) \/
    (exists c, cc = CC_at_post c /\ cfg = (CC_mid_loop x c y, s) /\ s x = Vnil).
Proof.
  intros x cc y s cfg Hst. inversion Hst; subst.
  - right. eexists; split; [reflexivity|split; [reflexivity|assumption]].
  - left. do 2 eexists; split; [reflexivity|assumption].
Qed.

(* "[exec_ss_star] inside CC_seq_L stays in CC_seq_L (and unlifts) until it
   leaves via [S_Seq_Mid]."  We capture the unlifting half here: if the
   start and the end are both [CC_seq_L _ c2], the surrounding shape
   never changed, so the inner cont_cmds form a [exec_ss_star] of their own. *)
(* "Shape" of any cfg reachable from CC_seq_R c1 _.  Useful to derive
   that the CC_seq_L shape cannot occur downstream. *)
Inductive seq_R_reach (c1 : cmd) : cont_cmd * store -> Prop :=
  | SR_inner : forall cc s, seq_R_reach c1 (CC_seq_R c1 cc, s)
  | SR_done  : forall c2 s, seq_R_reach c1 (CC_at_post (Cseq c1 c2), s).

Lemma steps_from_seq_R_shape :
  forall c1 cc s cfg,
    exec_ss_star (CC_seq_R c1 cc, s) cfg ->
    seq_R_reach c1 cfg.
Proof.
  intros c1 cc s cfg H.
  remember (CC_seq_R c1 cc, s) as cfg0 eqn:E.
  revert cc s E.
  induction H as [|cfg1 cfg2 cfg3 Hst Hrest IH]; intros cc s E; subst.
  - apply SR_inner.
  - destruct (step_from_seq_R_shape Hst) as [(cc' & s' & -> & _)|(c2 & -> & ->)].
    + apply (IH cc' s'); reflexivity.
    + pose proof (steps_from_at_post Hrest) as Eend. rewrite Eend.
      apply SR_done.
Qed.

(* ================================================================= *)
(* 14. Factorization lemmas for Cseq derivations                       *)
(* ================================================================= *)

(* A complete CC_seq_L (CC_at_pre c1) c2 -> CC_at_post (Cseq c1 c2)
   derivation factors as: body 1, S_Seq_Mid, body 2, S_Seq_Exit. *)
Lemma factor_seq_R :
  forall c1 cc s c2 s_final,
    exec_ss_star (CC_seq_R c1 cc, s) (CC_at_post (Cseq c1 c2), s_final) ->
    exec_ss_star (cc, s) (CC_at_post c2, s_final).
Proof.
  intros c1 cc s c2 s_final H.
  remember (CC_seq_R c1 cc, s) as cfg1 eqn:E1.
  remember (CC_at_post (Cseq c1 c2), s_final) as cfg2 eqn:E2.
  revert cc s E1.
  induction H as [cfg_end | cfg1' cfg_mid cfg2' Hst Hrest IH]; intros cc s E1.
  - subst cfg_end. discriminate.
  - subst cfg1'.
    destruct (step_from_seq_R_shape Hst) as [(cc1 & s1 & Hcfg & Hinner) | (c2' & -> & Hcfg)].
    + subst cfg_mid. eapply steps_cons; [exact Hinner|].
      apply (IH E2 cc1 s1 eq_refl).
    + subst cfg_mid.
      pose proof (steps_from_at_post Hrest) as Eend.
      rewrite E2 in Eend. injection Eend as <- <-.
      apply exec_ss_star_refl.
Qed.

Lemma factor_seq_L :
  forall cc c2 s c1 s_final,
    exec_ss_star (CC_seq_L cc c2, s) (CC_at_post (Cseq c1 c2), s_final) ->
    exists s_mid,
      exec_ss_star (cc, s) (CC_at_post c1, s_mid) /\
      exec_ss_star (CC_at_pre c2, s_mid) (CC_at_post c2, s_final).
Proof.
  intros cc c2 s c1 s_final H.
  remember (CC_seq_L cc c2, s) as cfg1 eqn:E1.
  remember (CC_at_post (Cseq c1 c2), s_final) as cfg2 eqn:E2.
  revert cc s E1.
  induction H as [cfg_end | cfg1' cfg_mid cfg2' Hst Hrest IH]; intros cc s E1.
  - subst cfg_end. discriminate.
  - subst cfg1'.
    destruct (step_from_seq_L_shape Hst) as [(cc1 & s1 & Hcfg & Hinner) | (c1' & -> & Hcfg)].
    + subst cfg_mid.
      specialize (IH E2 cc1 s1 eq_refl) as (s_mid & Hbody1 & Hbody2).
      exists s_mid. split; [|exact Hbody2].
      eapply steps_cons; [exact Hinner|exact Hbody1].
    + (* S_Seq_Mid: cc = CC_at_post c1'.  The rest factors via seq_R. *)
      subst cfg_mid.
      pose proof (steps_from_seq_R_shape Hrest) as Hsh.
      subst cfg2'.
      (* Hsh : seq_R_reach c1' (CC_at_post (Cseq c1 c2), s_final).
         The only matching constructor is SR_done, giving c1' = c1. *)
      assert (Hc1eq : c1' = c1)
        by (inversion Hsh; subst; reflexivity).
      subst c1'.
      exists s. split; [apply exec_ss_star_refl|].
      apply (factor_seq_R Hrest).
Qed.

(* ================================================================= *)
(* 15. Length-indexed multi-step relation and strong induction        *)
(* ================================================================= *)

Inductive nsteps : nat -> cont_cmd * store -> cont_cmd * store -> Prop :=
  | nsteps_O : forall cfg, nsteps 0 cfg cfg
  | nsteps_S : forall n cfg1 cfg2 cfg3,
      exec_ss cfg1 cfg2 -> nsteps n cfg2 cfg3 -> nsteps (S n) cfg1 cfg3.

Lemma steps_to_nsteps :
  forall cfg cfg', exec_ss_star cfg cfg' -> exists n, nsteps n cfg cfg'.
Proof.
  intros cfg cfg' H. induction H as [|? ? ? Hst Hrest [n IH]].
  - exists 0; apply nsteps_O.
  - exists (S n); econstructor; eauto.
Qed.

Lemma nsteps_to_steps :
  forall n cfg cfg', nsteps n cfg cfg' -> exec_ss_star cfg cfg'.
Proof.
  induction 1 as [|? ? ? ? Hst _ IH].
  - apply exec_ss_star_refl.
  - eapply steps_cons; eauto.
Qed.

Lemma nsteps_zero_eq : forall cfg cfg', nsteps 0 cfg cfg' -> cfg = cfg'.
Proof. intros cfg cfg' H. inversion H. reflexivity. Qed.

(* "Pull out" the last step of a non-empty derivation. *)
Lemma nsteps_split_last :
  forall n cfg1 cfg3,
    nsteps (S n) cfg1 cfg3 ->
    exists cfg2, nsteps n cfg1 cfg2 /\ exec_ss cfg2 cfg3.
Proof.
  induction n; intros cfg1 cfg3 H; inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
  - inversion Hrest; subst. exists cfg1. split; [apply nsteps_O|assumption].
  - specialize (IHn _ _ Hrest) as (cfg2 & Hns & Hst2).
    exists cfg2. split; [econstructor; eauto|assumption].
Qed.

(* Strong induction (well-founded recursion) on derivation length, packaged
   for convenient use below. *)
Lemma nsteps_strong_ind :
  forall (P : nat -> cont_cmd * store -> cont_cmd * store -> Prop),
    (forall n cfg cfg',
       nsteps n cfg cfg' ->
       (forall m cfgA cfgB, m < n -> nsteps m cfgA cfgB -> P m cfgA cfgB) ->
       P n cfg cfg') ->
    forall n cfg cfg', nsteps n cfg cfg' -> P n cfg cfg'.
Proof.
  intros P Hstep n.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros cfg cfg' Hns. apply Hstep; auto.
Qed.

(* ================================================================= *)
(* 16. Loop body factorization (via strong induction)                  *)
(* ================================================================= *)

(* Key auxiliary: a derivation that starts in [CC_in_loop x cc y] and
   reaches [CC_mid_loop x c y] proceeds by ctx-steps inside the loop
   body until the inner reaches [CC_at_post c0], then a single
   [S_LoopIter2] step.  This is the *first-exit* version. *)
From Stdlib Require Import Lia.

(* The "root command" of a controlled command: the underlying cmd in
   which the control token currently sits.  Every [exec_ss] preserves the
   root cmd. *)
Fixpoint root_cmd (cc : cont_cmd) : cmd :=
  match cc with
  | CC_at_pre   c          => c
  | CC_at_post  c          => c
  | CC_mid_loop x c y      => Cloop x c y
  | CC_seq_L    cc' c2     => Cseq (root_cmd cc') c2
  | CC_seq_R    c1 cc'     => Cseq c1 (root_cmd cc')
  | CC_in_loop  x cc' y    => Cloop x (root_cmd cc') y
  end.

Lemma step_preserves_root :
  forall cc s cc' s',
    exec_ss (cc, s) (cc', s') -> root_cmd cc = root_cmd cc'.
Proof.
  intros cc s cc' s' H.
  remember (cc, s) as cfg1; remember (cc', s') as cfg2.
  revert cc s cc' s' Heqcfg1 Heqcfg2.
  induction H; intros; inversion Heqcfg1; inversion Heqcfg2; subst; simpl;
    try reflexivity; f_equal; eapply IHexec_ss; reflexivity.
Qed.

Lemma steps_preserves_root_cfg :
  forall cfg cfg',
    exec_ss_star cfg cfg' -> root_cmd (fst cfg) = root_cmd (fst cfg').
Proof.
  intros cfg cfg' H. induction H as [|cfg1 cfg_m cfg2 Hst _ IH].
  - reflexivity.
  - destruct cfg1 as [cc1 s1]. destruct cfg_m as [cc_m s_m]. simpl in *.
    transitivity (root_cmd cc_m); [|exact IH].
    eapply step_preserves_root; exact Hst.
Qed.

Lemma steps_preserves_root :
  forall cc s cc' s',
    exec_ss_star (cc, s) (cc', s') -> root_cmd cc = root_cmd cc'.
Proof.
  intros cc s cc' s' H. exact (steps_preserves_root_cfg H).
Qed.

Lemma mid_loop_params_unique :
  forall x c y x' c' y' s s',
    exec_ss_star (CC_mid_loop x c y, s) (CC_mid_loop x' c' y', s') ->
    x = x' /\ c = c' /\ y = y'.
Proof.
  intros x c y x' c' y' s s' H.
  pose proof (steps_preserves_root H) as Eroot.
  simpl in Eroot. injection Eroot as -> -> ->. auto.
Qed.

(* Generic factor lemma for CC_in_loop -> END derivations, parameterized
   on the endpoint constructor.  Both endpoints we care about
   ([CC_mid_loop x c y] and [CC_at_post (Cloop x c y)]) are NOT
   [CC_in_loop], which forces [n >= 1].  We capture this via the
   disjunction.  The S_LoopIter2 case derives c0 = c uniformly via
   [steps_preserves_root]. *)
Lemma factor_in_loop_via :
  forall n x cc y s c end_cc s_end,
    (end_cc = CC_mid_loop x c y \/ end_cc = CC_at_post (Cloop x c y)) ->
    nsteps n (CC_in_loop x cc y, s) (end_cc, s_end) ->
    exists m s_body,
      m < n /\
      nsteps m (cc, s) (CC_at_post c, s_body) /\
      s_body x = Vnil /\
      nsteps (n - S m) (CC_mid_loop x c y, s_body) (end_cc, s_end).
Proof.
  intros n.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros x cc y s c end_cc s_end Hend H.
  destruct n as [|n'].
  - apply nsteps_zero_eq in H. destruct Hend; subst end_cc;
    injection H as Hbad _; discriminate.
  - inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
    destruct (step_from_in_loop_shape Hst)
      as [(cc1 & s1 & Hcfg & Hinner)|(c0 & -> & Hcfg & Hx)].
    + (* still inside the loop: ctx step *)
      subst cfg_mid.
      specialize (IH n' (Nat.lt_succ_diag_r _) x cc1 y s1 c end_cc s_end Hend Hrest)
        as (m & s_body & Hlt & Hbody & Hxnil & Hrest').
      exists (S m), s_body.
      split; [lia|]. split; [econstructor; eauto|].
      split; [exact Hxnil|].
      replace (S n' - S (S m)) with (n' - S m) by lia.
      exact Hrest'.
    + (* S_LoopIter2: cc = CC_at_post c0.  Derive c0 = c via root preservation. *)
      subst cfg_mid.
      pose proof (steps_preserves_root (nsteps_to_steps Hrest)) as Eroot.
      simpl in Eroot.
      assert (Hc : c0 = c).
      { destruct Hend; subst end_cc; simpl in Eroot;
          injection Eroot as Hc; exact Hc. }
      subst c0.
      exists 0, s.
      split; [lia|]. split; [apply nsteps_O|]. split; [exact Hx|].
      replace (S n' - 1) with n' by lia. exact Hrest.
Qed.

Lemma factor_in_loop_first_exit :
  forall n x cc y s c s_end,
    nsteps n (CC_in_loop x cc y, s) (CC_mid_loop x c y, s_end) ->
    exists m s_body,
      m < n /\
      nsteps m (cc, s) (CC_at_post c, s_body) /\
      s_body x = Vnil /\
      nsteps (n - S m) (CC_mid_loop x c y, s_body)
                       (CC_mid_loop x c y, s_end).
Proof. intros; eapply factor_in_loop_via; [left; reflexivity|eassumption]. Qed.

Lemma factor_in_loop_to_post :
  forall n x cc y s c s_end,
    nsteps n (CC_in_loop x cc y, s) (CC_at_post (Cloop x c y), s_end) ->
    exists m s_body,
      m < n /\
      nsteps m (cc, s) (CC_at_post c, s_body) /\
      s_body x = Vnil /\
      nsteps (n - S m) (CC_mid_loop x c y, s_body)
                       (CC_at_post (Cloop x c y), s_end).
Proof. intros; eapply factor_in_loop_via; [right; reflexivity|eassumption]. Qed.

(* From this we extract the [exec_ss_star]-level factorization. *)
Lemma factor_loop_body :
  forall x c y s s_end,
    exec_ss_star (CC_in_loop x (CC_at_pre c) y, s) (CC_mid_loop x c y, s_end) ->
    exists s_body,
      exec_ss_star (CC_at_pre c, s) (CC_at_post c, s_body) /\
      s_body x = Vnil /\
      exec_ss_star (CC_mid_loop x c y, s_body) (CC_mid_loop x c y, s_end).
Proof.
  intros x c y s s_end H.
  apply steps_to_nsteps in H as [n Hn].
  pose proof (factor_in_loop_first_exit Hn)
    as (m & s_body & _ & Hbody & Hxnil & Hrest).
  exists s_body. repeat split.
  - apply nsteps_to_steps in Hbody. exact Hbody.
  - exact Hxnil.
  - apply nsteps_to_steps in Hrest. exact Hrest.
Qed.

(* ================================================================= *)
(* 17. Theorem 1 (Semantic Equivalence), direction ss -> ds            *)
(* ================================================================= *)

(* Mid-loop derivations correspond to [loop_sem].  Note that the body's
   cmd [c] is fixed by [root_cmd] preservation, so we only need a
   denotational hypothesis at *this* [c]. *)
Lemma mid_loop_implies_loop_sem :
  forall n x c y s s_end,
    nsteps n (CC_mid_loop x c y, s) (CC_at_post (Cloop x c y), s_end) ->
    (forall m s0 s0',
       m < n ->
       nsteps m (CC_at_pre c, s0) (CC_at_post c, s0') ->
       exec_ds c s0 s0') ->
    loop_sem x c y s s_end.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros x c y s s_end H Hbody_ind.
  destruct n as [|n'].
  - apply nsteps_zero_eq in H. discriminate.
  - inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
    inversion Hst; subst.
    + (* S_LoopExit *)
      apply nsteps_to_steps in Hrest as Hsteps.
      pose proof (steps_from_at_post Hsteps) as Eend.
      injection Eend as Eend. subst s_end.
      apply L_Base. assumption.
    + (* S_LoopIter1 *)
      destruct (factor_in_loop_to_post Hrest)
        as (m & s_body & Hlt & Hbody_inner & Hxnil & Hrest_post).
      eapply L_Rec with (s1 := s_body); try eassumption.
      * eapply (Hbody_ind m); [lia|exact Hbody_inner].
      * eapply (IH (n' - S m)); [lia|exact Hrest_post|].
        intros k s0 s0' Hk Hk_st.
        eapply (Hbody_ind k); [lia|exact Hk_st].
Qed.

(* Main theorem: any small-step derivation from CC_at_pre to CC_at_post
   of the same cmd is matched by a denotational evaluation.  This is
   Theorem~\ref{thm:semantic_equivalence}, direction (2) -> (1). *)
Theorem ss_implies_ds :
  forall c s s',
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') ->
    exec_ds c s s'.
Proof.
  intros c. induction c as [x e | c1 IH1 c2 IH2 | x cbody IHbody y];
    intros s s' H; apply steps_to_nsteps in H as [n Hn].
  - (* Cass *)
    destruct n as [|n'].
    + apply nsteps_zero_eq in Hn. discriminate.
    + inversion Hn as [|? ? cfg_mid ? Hst Hrest]; subst.
      inversion Hst; subst.
      pose proof (nsteps_to_steps Hrest) as Hsteps.
      pose proof (steps_from_at_post Hsteps) as Eend.
      injection Eend as Eend.
      subst s'.
      eapply D_Asn; eassumption.
  - (* Cseq *)
    destruct n as [|n']; [apply nsteps_zero_eq in Hn; discriminate|].
    (* The first step is S_Seq_Enter. *)
    inversion Hn as [|? ? cfg_mid ? Hst Hrest]; subst.
    inversion Hst; subst.
    pose proof (nsteps_to_steps Hrest) as Hrest_s.
    destruct (factor_seq_L Hrest_s) as (s_mid & Hbody1 & Hbody2).
    apply IH1 in Hbody1.
    apply IH2 in Hbody2.
    eapply D_Seq; eassumption.
  - (* Cloop *)
    destruct n as [|n']; [apply nsteps_zero_eq in Hn; discriminate|].
    inversion Hn as [|? ? cfg_mid ? Hst Hrest]; subst.
    inversion Hst; subst.
    apply D_Loop; [assumption|].
    eapply mid_loop_implies_loop_sem; [exact Hrest|].
    intros k s0 s0' _ Hk_st. apply IHbody.
    eapply nsteps_to_steps. exact Hk_st.
Qed.

(* ================================================================= *)
(* 18. Theorem 1, packaged as a biconditional                          *)
(* ================================================================= *)

Theorem semantic_equivalence_ds_ss :
  forall c s s',
    exec_ds c s s' <->
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s').
Proof.
  split.
  - apply ds_implies_ss.
  - apply ss_implies_ds.
Qed.

(* ================================================================= *)
(* 19. fss syntax: atomic nodes, flowcharts, controlled flowcharts    *)
(* ================================================================= *)

(* Atomic node types (constructors only -- the "syntax" of nodes).
   Each program is built from these:
     A_step X E   : a reversible assignment step "X ^= E"
     A_test  Y    : a test on variable Y (1 in-edge, 2 out-edges t/f)
     A_assert X   : an assertion on variable X (2 in-edges t/f, 1 out-edge)
     A_begin X    : the program's initial terminal "read X"
     A_end   X    : the program's final terminal "write X"  *)
Inductive atom : Type :=
  | A_step   : var -> expr -> atom
  | A_test   : var -> atom
  | A_assert : var -> atom
  | A_begin  : var -> atom
  | A_end    : var -> atom.

(* Flowchart bodies built from atoms.  [F_nil] marks the "fall-through" /
   end of a body (also: the position just before [write X] in a program).
   [F_loop X body Y rest] is the standard reversible loop topology:
   the assertion X on entry, the body, the test Y on exit, then [rest].
   The back-edge from body to assertion is implicit in the constructor. *)
Inductive flowchart : Type :=
  | F_nil  : flowchart
  | F_step : var -> expr -> flowchart -> flowchart
  | F_loop : var -> flowchart -> var -> flowchart -> flowchart.

(* A whole program is "read X; F; write X". *)
Inductive flow_program : Type :=
  | FProg : var -> flowchart -> flow_program.

(* Controlled flowchart bodies: a flowchart with one control token.
   The token's position is encoded by the constructor choice:
   - [CF_pre F]      : token at the input edge of [F] (about to fire the first atom)
   - [CF_mid x body y rest] : token between assertion X and test Y of a loop
                              (loop body and continuation are kept for record)
   - [CF_in_loop x body cc y rest] : token within the loop body, [cc] holds the
                              inner position; the surrounding loop is kept *)
Inductive ctrl_flow : Type :=
  | CF_pre     : flowchart -> ctrl_flow
  | CF_mid     : var -> flowchart -> var -> flowchart -> ctrl_flow
  | CF_in_loop : var -> flowchart -> ctrl_flow -> var -> flowchart -> ctrl_flow.

(* Controlled flow program. *)
Inductive ctrl_flow_prog : Type :=
  | CFP_pre_read   : var -> flowchart -> ctrl_flow_prog
  | CFP_in_body    : var -> ctrl_flow -> ctrl_flow_prog
  | CFP_post_write : var -> ctrl_flow_prog.

(* ================================================================= *)
(* 20. fss step relation                                              *)
(* ================================================================= *)

(* Each transition is one traversal of an edge incident to an atomic
   node.  The rules are named after the underlying atomic operation
   plus the truth value that selects the edge:
   - FS_Asn        : crossing a step node (AsnSet / AsnClear combined via [odot]).
   - FS_AssertT    : entering a loop via the assertion's t-input.
   - FS_AssertF    : returning to the loop's assertion via its f-input
                     (back-edge from the body to the assertion).
   - FS_TestT      : exiting a loop via the test's t-output.
   - FS_TestF      : entering a loop body via the test's f-output.
   - FS_Ctx        : lifting a step that takes place inside a loop body. *)
Inductive fstep : ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | FS_Asn : forall x e F s v_e v_new,
      eval_expr s e = Some v_e ->
      odot (s x) v_e = Some v_new ->
      fstep (CF_pre (F_step x e F), s)
            (CF_pre F, update s x v_new)
  | FS_AssertT : forall x body y rest s,
      s x <> Vnil ->
      fstep (CF_pre (F_loop x body y rest), s)
            (CF_mid x body y rest, s)
  | FS_AssertF : forall x body y rest s,
      s x = Vnil ->
      fstep (CF_in_loop x body (CF_pre F_nil) y rest, s)
            (CF_mid x body y rest, s)
  | FS_TestT : forall x body y rest s,
      s y <> Vnil ->
      fstep (CF_mid x body y rest, s) (CF_pre rest, s)
  | FS_TestF : forall x body y rest s,
      s y = Vnil ->
      fstep (CF_mid x body y rest, s)
            (CF_in_loop x body (CF_pre body) y rest, s)
  | FS_Ctx : forall x body cc cc' y rest s s',
      fstep (cc, s) (cc', s') ->
      fstep (CF_in_loop x body cc y rest, s)
            (CF_in_loop x body cc' y rest, s').

(* Multi-step closure. *)
Inductive fsteps : ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | fsteps_refl : forall cfg, fsteps cfg cfg
  | fsteps_cons : forall cfg1 cfg2 cfg3,
      fstep cfg1 cfg2 -> fsteps cfg2 cfg3 -> fsteps cfg1 cfg3.

Hint Constructors fstep fsteps : r_db.

Lemma fsteps_trans :
  forall cfg1 cfg2 cfg3,
    fsteps cfg1 cfg2 -> fsteps cfg2 cfg3 -> fsteps cfg1 cfg3.
Proof.
  intros cfg1 cfg2 cfg3 H1 H2.
  induction H1 as [|? ? ? Hst Hr IH]; [exact H2|].
  eapply fsteps_cons; [exact Hst|apply IH; exact H2].
Qed.

(* Program-level fss steps including begin/end. *)
Inductive fpstep : ctrl_flow_prog * store -> ctrl_flow_prog * store -> Prop :=
  | FP_Begin : forall x F s,
      fpstep (CFP_pre_read x F, s) (CFP_in_body x (CF_pre F), s)
  | FP_Body  : forall x cc cc' s s',
      fstep (cc, s) (cc', s') ->
      fpstep (CFP_in_body x cc, s) (CFP_in_body x cc', s')
  | FP_End : forall x s,
      fpstep (CFP_in_body x (CF_pre F_nil), s) (CFP_post_write x, s).

(* Lifting fsteps into a CF_in_loop context. *)
Lemma fsteps_lift_loop :
  forall x body cc cc' y rest s s',
    fsteps (cc, s) (cc', s') ->
    fsteps (CF_in_loop x body cc y rest, s)
           (CF_in_loop x body cc' y rest, s').
Proof.
  intros x body cc cc' y rest s s' H.
  remember (cc, s) as cfg1 eqn:E1.
  remember (cc', s') as cfg2 eqn:E2.
  revert cc s cc' s' E1 E2.
  induction H as [cfg_end | cfg1' cfg_mid cfg2' Hst Hrest IH];
    intros cc s cc' s' E1 E2.
  - subst cfg_end. injection E2 as -> ->. apply fsteps_refl.
  - subst cfg1'. destruct cfg_mid as [ccm sm].
    eapply fsteps_cons; [apply FS_Ctx; exact Hst|].
    apply (IH ccm sm cc' s'); [reflexivity|exact E2].
Qed.

(* ================================================================= *)
(* 21. Translation cmd -> flowchart and cont_cmd -> ctrl_flow         *)
(* ================================================================= *)

(* [translate c rest] prepends c's flowchart in front of [rest]. *)
Fixpoint translate (c : cmd) (rest : flowchart) : flowchart :=
  match c with
  | Cass x e        => F_step x e rest
  | Cseq c1 c2      => translate c1 (translate c2 rest)
  | Cloop x cb y    => F_loop x (translate cb F_nil) y rest
  end.

(* Translation of a controlled command, parameterized by the surrounding
   flowchart [rest] (= what comes "after" the controlled command). *)
Fixpoint translate_ctrl (cc : cont_cmd) (rest : flowchart) : ctrl_flow :=
  match cc with
  | CC_at_pre  c           => CF_pre (translate c rest)
  | CC_at_post c           => CF_pre rest
  | CC_mid_loop x cb y     => CF_mid x (translate cb F_nil) y rest
  | CC_seq_L cc1 c2        => translate_ctrl cc1 (translate c2 rest)
  | CC_seq_R c1 cc2        => translate_ctrl cc2 rest
  | CC_in_loop x cc' y     =>
      CF_in_loop x (translate (root_cmd cc') F_nil)
                   (translate_ctrl cc' F_nil) y rest
  end.

(* Sanity: translate_ctrl agrees on root_cmd via the body-position invariant.
   Specifically, for any cont_cmd whose underlying cmd is [c], the
   translation places [translate c rest] (or [rest]) under [CF_pre _]. *)

(* ================================================================= *)
(* 22. ss -> fss simulation                                           *)
(* ================================================================= *)

Lemma ss_step_implies_fss_steps_cfg :
  forall cfg1 cfg2,
    exec_ss cfg1 cfg2 ->
    forall rest, fsteps (translate_ctrl (fst cfg1) rest, snd cfg1)
                        (translate_ctrl (fst cfg2) rest, snd cfg2).
Proof.
  intros cfg1 cfg2 H. induction H; intros rest; simpl;
    try (eauto with r_db; fail).
  (* S_Ctx_Loop alone needs the root-cmd rewrite to align bodies. *)
  rewrite (step_preserves_root H).
  apply fsteps_lift_loop. apply IHexec_ss.
Qed.

Lemma ss_step_implies_fss_steps :
  forall cc s cc' s',
    exec_ss (cc, s) (cc', s') ->
    forall rest, fsteps (translate_ctrl cc rest, s)
                        (translate_ctrl cc' rest, s').
Proof.
  intros cc s cc' s' H rest.
  exact (ss_step_implies_fss_steps_cfg H rest).
Qed.

Lemma ss_steps_implies_fss_steps :
  forall cc s cc' s' rest,
    exec_ss_star (cc, s) (cc', s') ->
    fsteps (translate_ctrl cc rest, s) (translate_ctrl cc' rest, s').
Proof.
  intros cc s cc' s' rest H.
  remember (cc, s) as cfg1 eqn:E1.
  remember (cc', s') as cfg2 eqn:E2.
  revert cc s cc' s' E1 E2.
  induction H as [cfg_end | cfg1' cfg_mid cfg2' Hst Hrest IH];
    intros cc s cc' s' E1 E2.
  - subst cfg_end. injection E2 as -> ->. apply fsteps_refl.
  - subst cfg1'. destruct cfg_mid as [ccm sm].
    eapply fsteps_trans.
    + apply (ss_step_implies_fss_steps Hst).
    + apply (IH ccm sm cc' s'); [reflexivity|exact E2].
Qed.

(* Main ss -> fss correspondence at the body level. *)
Theorem ss_implies_fss :
  forall c s s',
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') ->
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s').
Proof.
  intros c s s' H.
  exact (ss_steps_implies_fss_steps F_nil H).
Qed.

(* Composition: ds implies fss. *)
Theorem ds_implies_fss :
  forall c s s',
    exec_ds c s s' ->
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s').
Proof.
  intros c s s' H.
  apply ss_implies_fss.
  apply ds_implies_ss. exact H.
Qed.

(* ================================================================= *)
(* 23. Length-indexed fss derivations                                 *)
(* ================================================================= *)

Inductive fnsteps : nat -> ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | fnsteps_O : forall cfg, fnsteps 0 cfg cfg
  | fnsteps_S : forall n cfg1 cfg2 cfg3,
      fstep cfg1 cfg2 -> fnsteps n cfg2 cfg3 -> fnsteps (S n) cfg1 cfg3.

Lemma fsteps_to_fnsteps :
  forall cfg cfg', fsteps cfg cfg' -> exists n, fnsteps n cfg cfg'.
Proof.
  intros cfg cfg' H. induction H as [|? ? ? Hst Hrest [n IH]].
  - exists 0; apply fnsteps_O.
  - exists (S n); econstructor; eauto.
Qed.

Lemma fnsteps_to_fsteps :
  forall n cfg cfg', fnsteps n cfg cfg' -> fsteps cfg cfg'.
Proof.
  induction 1 as [|? ? ? ? Hst _ IH].
  - apply fsteps_refl.
  - eapply fsteps_cons; eauto.
Qed.

Lemma fnsteps_zero_eq : forall cfg cfg', fnsteps 0 cfg cfg' -> cfg = cfg'.
Proof. intros cfg cfg' H. inversion H. reflexivity. Qed.

(* ================================================================= *)
(* 24. Outer-rest measure and the no-cycle property                    *)
(* ================================================================= *)

(* The "outer rest" of a controlled flowchart: the trailing flowchart
   that the token will eventually reach as a CF_pre.  This is the part
   of the original flowchart that is yet to enter the control-flow
   "frontier" of the token's traversal. *)
Definition outer_rest (cc : ctrl_flow) : flowchart :=
  match cc with
  | CF_pre F => F
  | CF_mid _ _ _ rest => rest
  | CF_in_loop _ _ _ _ rest => rest
  end.

(* The "suffix" partial order on flowcharts: [sub_flow F G] iff [F] is
   reachable from [G] by stripping the top [F_step] or [F_loop] wrappers.
   Equivalently, [F] is what remains after consuming a prefix of [G]'s
   trailing path. *)
Inductive sub_flow : flowchart -> flowchart -> Prop :=
  | sub_refl : forall F, sub_flow F F
  | sub_step : forall F x e F', sub_flow F F' -> sub_flow F (F_step x e F')
  | sub_loop : forall F x body y F',
      sub_flow F F' -> sub_flow F (F_loop x body y F').
Hint Constructors sub_flow : sub_db.

Lemma sub_flow_trans :
  forall F1 F2 F3, sub_flow F1 F2 -> sub_flow F2 F3 -> sub_flow F1 F3.
Proof.
  intros F1 F2 F3 H1 H2. revert F1 H1. induction H2; intros F1 H1.
  - exact H1.
  - apply sub_step. apply IHsub_flow. exact H1.
  - apply sub_loop. apply IHsub_flow. exact H1.
Qed.

(* Counting structural atoms (steps + loops counted once each) bounds
   sub_flow: it is monotone, strict on non-refl derivations. *)
Fixpoint flow_size (F : flowchart) : nat :=
  match F with
  | F_nil => 0
  | F_step _ _ F' => S (flow_size F')
  | F_loop _ body _ F' => S (flow_size body + flow_size F')
  end.

Lemma sub_flow_size :
  forall F1 F2, sub_flow F1 F2 -> flow_size F1 <= flow_size F2.
Proof. induction 1; simpl; lia. Qed.

(* [translate c R] is strictly larger than [R], hence never equal to it. *)
Lemma translate_grows :
  forall c R, flow_size R < flow_size (translate c R).
Proof.
  induction c; intros R; simpl.
  - lia.
  - pose proof (IHc1 (translate c2 R)). pose proof (IHc2 R). lia.
  - lia.
Qed.

Lemma translate_neq_self :
  forall c R, translate c R <> R.
Proof.
  intros c R Heq. pose proof (translate_grows c R). rewrite Heq in *. lia.
Qed.

Lemma sub_flow_strict_size :
  forall F1 F2, sub_flow F1 F2 -> F1 = F2 \/ flow_size F1 < flow_size F2.
Proof.
  induction 1.
  - left; reflexivity.
  - right. pose proof (sub_flow_size H). simpl. lia.
  - right. pose proof (sub_flow_size H). simpl. lia.
Qed.

Lemma sub_flow_antisym :
  forall F1 F2, sub_flow F1 F2 -> sub_flow F2 F1 -> F1 = F2.
Proof.
  intros F1 F2 H1 H2.
  pose proof (sub_flow_size H1).
  pose proof (sub_flow_size H2).
  destruct (sub_flow_strict_size H1) as [-> | Hlt]; auto. lia.
Qed.

(* The key observation: every fstep weakly decreases [outer_rest] under
   [sub_flow], and the first step out of [CF_pre F] strictly decreases. *)
Lemma fstep_outer_rest_sub :
  forall cc s cc' s', fstep (cc, s) (cc', s') ->
                       sub_flow (outer_rest cc') (outer_rest cc).
Proof. intros cc s cc' s' H. inversion H; simpl; subst; eauto with sub_db. Qed.

Lemma fnsteps_outer_rest_sub :
  forall n cfg cfg', fnsteps n cfg cfg' ->
                      sub_flow (outer_rest (fst cfg')) (outer_rest (fst cfg)).
Proof.
  induction 1 as [|? [cc s] [cc' s'] ? Hst _ IH].
  - apply sub_refl.
  - simpl in *. eapply sub_flow_trans; [exact IH|].
    eapply fstep_outer_rest_sub; eauto.
Qed.

(* The first fstep out of [CF_pre F] strictly shrinks the outer-rest. *)
Lemma fstep_pre_strict :
  forall F s cc' s',
    fstep (CF_pre F, s) (cc', s') ->
    flow_size (outer_rest cc') < flow_size F.
Proof.
  intros F s cc' s' H. inversion H; simpl; subst; lia.
Qed.

(* No-cycle: a derivation that returns to its starting [CF_pre F] must
   be empty.  Proof: the first step would strictly shrink the
   outer-rest, but subsequent steps only weakly shrink, so the original
   [F] is never reached again. *)
Theorem fnsteps_pre_no_cycle :
  forall n F s s', fnsteps n (CF_pre F, s) (CF_pre F, s') -> n = 0 /\ s = s'.
Proof.
  intros n F s s' H. inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
  - auto.
  - exfalso. destruct cfg_mid as [cc_mid s_mid].
    pose proof (fstep_pre_strict Hst) as Hstrict. simpl in Hstrict.
    pose proof (fnsteps_outer_rest_sub Hrest) as Hsub. simpl in Hsub.
    pose proof (sub_flow_size Hsub) as Hsize. lia.
Qed.

(* ================================================================= *)
(* 25. Factor lemma: every complete fss derivation through [translate c R]
       passes through [CF_pre R] at a unique split point, witnessing
       [exec_ds c] for the prefix.                                  *)
(* ================================================================= *)

(* For a loop, the body's [translate cb F_nil] -> [CF_pre F_nil] segment
   captures a single iteration; we factor the entire CF_mid -> CF_pre R
   stretch into loop_sem.  This mirrors [mid_loop_implies_loop_sem] from
   ss. *)

(* Factor any CF_in_loop -> CF_pre F_end derivation through the first
   AssertF transition. *)
Lemma fnsteps_in_loop_to_pre :
  forall n x body cc y rest s F_end s_end,
    fnsteps n (CF_in_loop x body cc y rest, s) (CF_pre F_end, s_end) ->
    exists m s_body,
      m < n /\
      fnsteps m (cc, s) (CF_pre F_nil, s_body) /\
      s_body x = Vnil /\
      fnsteps (n - S m) (CF_mid x body y rest, s_body) (CF_pre F_end, s_end).
Proof.
  intros n.
  induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros x body cc y rest s F_end s_end H.
  destruct n as [|n']; [apply fnsteps_zero_eq in H; discriminate|].
  inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
  inversion Hst; subst.
  - exists 0, s. split; [lia|]. split; [apply fnsteps_O|].
    split; [assumption|]. replace (S n' - 1) with n' by lia. exact Hrest.
  - specialize (IH n' (Nat.lt_succ_diag_r _) x body cc' y rest s' F_end s_end Hrest)
      as (m & s_body & Hlt & Hbody & Hxnil & Hrest').
    exists (S m), s_body. split; [lia|]. split; [econstructor; eauto|].
    split; [exact Hxnil|]. replace (S n' - S (S m)) with (n' - S m) by lia.
    exact Hrest'.
Qed.

(* CF_mid -> CF_pre rest derivation factors into a loop_sem trace.
   The body cmd cb is recovered from the assumed body shape, and the
   inductive hypothesis on body sub-derivations witnesses [exec_ds cb]. *)
Lemma fnsteps_mid_implies_loop_sem :
  forall n x cb y rest s s_end,
    fnsteps n (CF_mid x (translate cb F_nil) y rest, s) (CF_pre rest, s_end) ->
    (forall m s0 s0',
       m < n ->
       fnsteps m (CF_pre (translate cb F_nil), s0) (CF_pre F_nil, s0') ->
       exec_ds cb s0 s0') ->
    loop_sem x cb y s s_end.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros x cb y rest s s_end H Hbody_ind.
  destruct n as [|n']; [apply fnsteps_zero_eq in H; discriminate|].
  inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
  inversion Hst; subst.
  - (* FS_TestT: exit. The remaining derivation is at CF_pre rest -> CF_pre rest,
       which must be empty by no-cycle. *)
    pose proof (fnsteps_pre_no_cycle Hrest) as [_ <-].
    apply L_Base; assumption.
  - (* FS_TestF: enter body. *)
    destruct (fnsteps_in_loop_to_pre Hrest)
      as (m & s_body & Hlt & Hbody_run & Hxnil & Hrest_post).
    eapply L_Rec with (s1 := s_body); try eassumption.
    + eapply (Hbody_ind m); [lia|exact Hbody_run].
    + eapply (IH (n' - S m)); [lia|exact Hrest_post|].
      intros k s0 s0' Hk Hk_st.
      apply (Hbody_ind k); [lia|exact Hk_st].
Qed.

(* ================================================================= *)
(* 26. Main constructive theorem (fss -> ds)                           *)
(* ================================================================= *)

(* We prove [fss_complete_to_pre] by strong induction on derivation
   length [n], combined with structural induction on [c].  The Cseq
   case is handled by a structural induction on [c1], using the
   re-association of [translate c1 (translate c2 R)] across [Cseq].
   The Cloop case uses [fnsteps_mid_implies_loop_sem] plus a
   factoring of the post-loop fnsteps tail. *)

(* Auxiliary factor: a CF_mid -> CF_pre F_end derivation factors
   into loop_sem (for the [cb] body, witnessed by [Hbody_ind]) plus
   a continuation from [CF_pre rest] to [CF_pre F_end].  We use this
   for the Cloop case of fss_complete_to_pre. *)
Lemma fnsteps_mid_split :
  forall n x cb y rest s F_end s_final,
    fnsteps n (CF_mid x (translate cb F_nil) y rest, s) (CF_pre F_end, s_final) ->
    (forall m s0 s0',
       m < n ->
       fnsteps m (CF_pre (translate cb F_nil), s0) (CF_pre F_nil, s0') ->
       exec_ds cb s0 s0') ->
    exists s_mid k,
      k < n /\
      loop_sem x cb y s s_mid /\
      fnsteps k (CF_pre rest, s_mid) (CF_pre F_end, s_final).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Nat.lt_wf_0).
  intros x cb y rest s F_end s_final H Hbody_ind.
  destruct n as [|n']; [apply fnsteps_zero_eq in H; discriminate|].
  inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
  inversion Hst; subst.
  - (* FS_TestT: exit via t-edge *)
    exists s, n'. split; [lia|]. split; [apply L_Base; assumption|exact Hrest].
  - (* FS_TestF: enter body *)
    destruct (fnsteps_in_loop_to_pre Hrest)
      as (m & s_body & Hlt & Hbody_run & Hxnil & Hrest_post).
    (* Now Hrest_post is from CF_mid again, length n' - S m.  Recurse via IH. *)
    pose (Hbody_ind' :=
      (fun j s0 s0' (Hj : j < n' - S m) Hj_st =>
         Hbody_ind j s0 s0' ltac:(lia) Hj_st)).
    destruct (IH (n' - S m) ltac:(lia) x cb y rest s_body F_end s_final
                Hrest_post Hbody_ind')
      as (s_mid_final & k_final & Hk_lt & Hloop_rest & Hcont).
    exists s_mid_final, k_final. split; [lia|]. split; [|exact Hcont].
    eapply L_Rec with (s1 := s_body); try eassumption.
    eapply (Hbody_ind m); [lia|exact Hbody_run].
Qed.

(* Structural factor for Cseq: derivation through [translate c1 (translate c2 R)]
   yields ds(c1) and a sub-derivation for c2; recurses structurally on c1. *)
Lemma fss_seq_factor :
  forall c1 n c2 R s s_final,
    (forall m c R' s' s'', m < n ->
       fnsteps m (CF_pre (translate c R'), s') (CF_pre R', s'') ->
       exec_ds c s' s'') ->
    fnsteps n (CF_pre (translate c1 (translate c2 R)), s) (CF_pre R, s_final) ->
    exists s_mid, exec_ds c1 s s_mid /\ exec_ds c2 s_mid s_final.
Proof.
  induction c1 as [x e | c1a IHc1a c1b IHc1b | x cb IHcb y];
    intros n c2 R s s_final IHn H.
  - (* Cass x e *)
    destruct n as [|n'].
    + exfalso. apply fnsteps_zero_eq in H. injection H as Heq _.
      pose proof (translate_grows c2 R) as Hg.
      assert (Hsize : flow_size (F_step x e (translate c2 R)) = flow_size R)
        by (rewrite Heq; reflexivity).
      simpl in Hsize. lia.
    + inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
      inversion Hst; subst.
      exists (update s x v_new). split.
      * eapply D_Asn; eassumption.
      * eapply (IHn n' c2 R); [lia|exact Hrest].
  - (* Cseq c1a c1b: re-associate, apply IHc1a with c2' := Cseq c1b c2. *)
    (* translate (Cseq c1a c1b) (translate c2 R) =
       translate c1a (translate c1b (translate c2 R)) =
       translate c1a (translate (Cseq c1b c2) R). *)
    simpl in H.
    change (translate c1b (translate c2 R)) with (translate (Cseq c1b c2) R) in H.
    specialize (IHc1a n (Cseq c1b c2) R s s_final IHn H)
      as (s_mid1 & Hc1a & Hcseq).
    inversion Hcseq as [| ? ? ? s_mid2 ? Hc1b Hc2 | ]; subst.
    exists s_mid2. split; [eapply D_Seq; eauto|exact Hc2].
  - (* Cloop x cb y *)
    destruct n as [|n'].
    + exfalso. apply fnsteps_zero_eq in H. injection H as Heq _.
      pose proof (translate_grows c2 R) as Hg.
      assert (Hsize : flow_size (F_loop x (translate cb F_nil) y (translate c2 R))
                      = flow_size R)
        by (rewrite Heq; reflexivity).
      simpl in Hsize. lia.
    + inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
      inversion Hst; subst.
      (* Hrest : fnsteps n' (CF_mid x body y (translate c2 R), s) (CF_pre R, s_final). *)
      pose proof (fnsteps_mid_split (rest := translate c2 R) Hrest
                   (fun m s0 s0' Hm Hm_st => IHn m _ _ s0 s0' ltac:(lia) Hm_st))
        as (s_mid_loop & k & Hk_lt & Hloop & Hc2_run).
      exists s_mid_loop. split.
      * apply D_Loop; assumption.
      * eapply (IHn k); [lia|exact Hc2_run].
Qed.

(* The main constructive theorem. *)
Theorem fss_complete_to_pre :
  forall n c R s s',
    fnsteps n (CF_pre (translate c R), s) (CF_pre R, s') ->
    exec_ds c s s'.
Proof.
  intros n. induction n as [n IHn] using (well_founded_induction Nat.lt_wf_0).
  intros c R s s' H.
  destruct c as [x e | c1 c2 | x cb y]; simpl in H.
  - (* Cass x e *)
    destruct n as [|n'].
    + exfalso. apply fnsteps_zero_eq in H. injection H as Heq _.
      assert (Hsize : flow_size (F_step x e R) = flow_size R)
        by (rewrite Heq; reflexivity).
      simpl in Hsize. lia.
    + inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
      inversion Hst; subst.
      pose proof (fnsteps_pre_no_cycle Hrest) as [_ <-].
      eapply D_Asn; eassumption.
  - (* Cseq c1 c2 *)
    edestruct (@fss_seq_factor c1 n c2 R s s')
      as (s_mid & Hc1 & Hc2).
    + intros m c R' s'' s''' Hm Hm_st. eapply (IHn m); [lia|exact Hm_st].
    + exact H.
    + eapply D_Seq; eauto.
  - (* Cloop x cb y *)
    destruct n as [|n'].
    + exfalso. apply fnsteps_zero_eq in H. injection H as Heq _.
      assert (Hsize : flow_size (F_loop x (translate cb F_nil) y R) = flow_size R)
        by (rewrite Heq; reflexivity).
      simpl in Hsize. lia.
    + inversion H as [|? ? cfg_mid ? Hst Hrest]; subst.
      inversion Hst; subst.
      apply D_Loop; [assumption|].
      eapply fnsteps_mid_implies_loop_sem; [exact Hrest|].
      intros k s0 s0' Hk Hk_st. eapply (IHn k); [lia|exact Hk_st].
Qed.

Theorem fss_implies_ds :
  forall c s s',
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s') ->
    exec_ds c s s'.
Proof.
  intros c s s' H.
  apply fsteps_to_fnsteps in H as [n Hn].
  eapply fss_complete_to_pre. exact Hn.
Qed.

(* ================================================================= *)
(* 27. Theorem 1 (Semantic Equivalence), full statement                *)
(* ================================================================= *)

(* fss -> ss via fss -> ds -> ss. *)
Theorem fss_implies_ss :
  forall c s s',
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s') ->
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s').
Proof.
  intros c s s' H.
  apply ds_implies_ss.
  apply fss_implies_ds. exact H.
Qed.

(* The full equivalence between ss and fss (Theorem 1 items 2 <-> 3). *)
Theorem semantic_equivalence_ss_fss :
  forall c s s',
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') <->
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s').
Proof.
  split.
  - apply ss_implies_fss.
  - apply fss_implies_ss.
Qed.

(* The full equivalence between ds and fss (Theorem 1 items 1 <-> 3). *)
Theorem semantic_equivalence_ds_fss :
  forall c s s',
    exec_ds c s s' <->
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s').
Proof.
  split.
  - apply ds_implies_fss.
  - apply fss_implies_ds.
Qed.

(* RC2026:Thm 1 / Letter:Thm 3, all three equivalences packaged. *)
Theorem semantic_equivalence :
  forall c s s',
    (exec_ds c s s' <-> exec_ss_star (CC_at_pre c, s) (CC_at_post c, s'))
    /\
    (exec_ds c s s' <-> fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s'))
    /\
    (exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') <->
     fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s')).
Proof.
  intros c s s'. repeat split.
  - apply ds_implies_ss.
  - apply ss_implies_ds.
  - apply ds_implies_fss.
  - intros H. apply fss_implies_ds. exact H.
  - apply ss_implies_fss.
  - apply fss_implies_ss.
Qed.

(* ================================================================= *)
(* 28. Executable interpreter (fuel-based)                            *)
(* ================================================================= *)

(* A fuel-bounded denotational interpreter for R-CORE.  Returns [Some s']
   when the program terminates within [fuel] derivation steps and reaches
   final store [s']; [None] otherwise (fuel exhausted, stuck on assertion
   violation, or [eval_expr]/[odot] undefined).

   Mutually recursive with [eval_loop_fuel] over the loop body.  Both
   decrease [fuel] strictly, so the Fixpoint is structurally well-founded. *)

Fixpoint eval_cmd_fuel (fuel : nat) (c : cmd) (s : store) : option store :=
  match fuel with
  | 0 => None
  | S f =>
    match c with
    | Cass x e =>
        match eval_expr s e with
        | Some v_e =>
            match odot (s x) v_e with
            | Some v_new => Some (update s x v_new)
            | None => None
            end
        | None => None
        end
    | Cseq c1 c2 =>
        match eval_cmd_fuel f c1 s with
        | Some s1 => eval_cmd_fuel f c2 s1
        | None => None
        end
    | Cloop x c y =>
        (* Entry assertion: s x must be non-Vnil. *)
        match s x with
        | Vnil => None
        | _    => eval_loop_fuel f x c y s
        end
    end
  end
with eval_loop_fuel (fuel : nat) (x : var) (c : cmd) (y : var) (s : store) : option store :=
  match fuel with
  | 0 => None
  | S f =>
    match s y with
    | Vnil =>
        (* Y is false: run the body, then assert X = Vnil before next iter. *)
        match eval_cmd_fuel f c s with
        | Some s1 =>
            match s1 x with
            | Vnil => eval_loop_fuel f x c y s1
            | _    => None
            end
        | None => None
        end
    | _    => Some s     (* Y is true: exit loop *)
    end
  end.

(* Quick computational sanity check: the trivial program
     X ^= nil   (with σ(X) = nil initially)
   evaluates to a store where X = nil. *)
Example eval_cmd_fuel_test :
  let s0 := Vector.const Vnil 10 in
  eval_cmd_fuel 5 (X0 ^= Enil) s0 = Some (update s0 X0 Vnil).
Proof. reflexivity. Qed.

(* Soundness of the fuel-based interpreter against the denotational
   relation [exec_ds].  Proved together with the loop variant. *)
Lemma eval_cmd_loop_sound :
  forall fuel,
    (forall c s s', eval_cmd_fuel fuel c s = Some s' -> exec_ds c s s') /\
    (forall x c y s s',
       eval_loop_fuel fuel x c y s = Some s' -> loop_sem x c y s s').
Proof.
  induction fuel as [|f IH]; simpl; split; intros.
  - discriminate.
  - discriminate.
  - destruct IH as [IHc IHl].
    destruct c.
    + (* Cass *)
      destruct (eval_expr s e) as [v_e|] eqn:He; [|discriminate].
      destruct (odot (s x) v_e) as [v_new|] eqn:Ho; [|discriminate].
      injection H as <-. eapply D_Asn; eassumption.
    + (* Cseq *)
      destruct (eval_cmd_fuel f c1 s) as [s1|] eqn:Hc1; [|discriminate].
      apply IHc in Hc1. apply IHc in H. eapply D_Seq; eassumption.
    + (* Cloop *)
      destruct (s x) eqn:Hx; [discriminate|].
      apply IHl in H. apply D_Loop; [|exact H]. rewrite Hx. discriminate.
  - destruct IH as [IHc IHl].
    destruct (s y) eqn:Hy.
    + (* Y is false: body executes, recurse. *)
      destruct (eval_cmd_fuel f c s) as [s1|] eqn:Hbody; [|discriminate].
      destruct (s1 x) eqn:Hxn; [|discriminate].
      apply IHc in Hbody. apply IHl in H.
      eapply L_Rec with (s1 := s1); eassumption.
    + (* Y is true: exit. *)
      injection H as <-. apply L_Base. rewrite Hy. discriminate.
Qed.

Theorem eval_cmd_sound :
  forall fuel c s s',
    eval_cmd_fuel fuel c s = Some s' ->
    exec_ds c s s'.
Proof. intros fuel; apply (proj1 (eval_cmd_loop_sound fuel)). Qed.

Theorem eval_loop_sound :
  forall fuel x c y s s',
    eval_loop_fuel fuel x c y s = Some s' ->
    loop_sem x c y s s'.
Proof. intros fuel; apply (proj2 (eval_cmd_loop_sound fuel)). Qed.

(* Fuel monotonicity: more fuel never breaks a successful evaluation. *)
Lemma eval_cmd_loop_mono :
  forall fuel fuel',
    fuel <= fuel' ->
    (forall c s s', eval_cmd_fuel fuel c s = Some s' ->
                    eval_cmd_fuel fuel' c s = Some s') /\
    (forall x c y s s', eval_loop_fuel fuel x c y s = Some s' ->
                        eval_loop_fuel fuel' x c y s = Some s').
Proof.
  induction fuel as [|f IH]; intros fuel' Hle; split; intros.
  - discriminate.
  - discriminate.
  - destruct fuel' as [|f']; [lia|]. simpl in *.
    destruct c.
    + (* Cass *) exact H.
    + (* Cseq *)
      destruct (eval_cmd_fuel f c1 s) as [s1|] eqn:Hc1; [|discriminate].
      destruct (IH f' ltac:(lia)) as [IHc _].
      rewrite (IHc _ _ _ Hc1).
      apply (IHc _ _ _ H).
    + (* Cloop *)
      destruct (s x) eqn:Hx; [discriminate|];
        destruct (IH f' ltac:(lia)) as [_ IHl];
        apply (IHl _ _ _ _ _ H).
  - destruct fuel' as [|f']; [lia|]. simpl in *.
    destruct (s y) eqn:Hy.
    + destruct (eval_cmd_fuel f c s) as [s1|] eqn:Hbody; [|discriminate].
      destruct (s1 x) eqn:Hxn; [|discriminate].
      destruct (IH f' ltac:(lia)) as [IHc IHl].
      rewrite (IHc _ _ _ Hbody). rewrite Hxn. apply (IHl _ _ _ _ _ H).
    + exact H.
Qed.

Lemma eval_cmd_fuel_mono :
  forall fuel fuel' c s s',
    fuel <= fuel' ->
    eval_cmd_fuel fuel c s = Some s' ->
    eval_cmd_fuel fuel' c s = Some s'.
Proof. intros; apply (proj1 (eval_cmd_loop_mono H)); exact H0. Qed.

Lemma eval_loop_fuel_mono :
  forall fuel fuel' x c y s s',
    fuel <= fuel' ->
    eval_loop_fuel fuel x c y s = Some s' ->
    eval_loop_fuel fuel' x c y s = Some s'.
Proof. intros; apply (proj2 (eval_cmd_loop_mono H)); exact H0. Qed.

(* Completeness: every denotational derivation is captured by sufficient fuel. *)
Lemma eval_cmd_loop_complete :
  (forall c s s', exec_ds c s s' -> exists fuel, eval_cmd_fuel fuel c s = Some s') /\
  (forall x c y s s', loop_sem x c y s s' -> exists fuel, eval_loop_fuel fuel x c y s = Some s').
Proof.
  apply (exec_ds_loop_mut
           (fun c s s' _ => exists fuel, eval_cmd_fuel fuel c s = Some s')
           (fun x c y s s' _ => exists fuel, eval_loop_fuel fuel x c y s = Some s')).
  - (* D_Asn *) intros x e s v_e v_new He Ho.
    exists 1. simpl. rewrite He, Ho. reflexivity.
  - (* D_Seq *) intros c1 c2 s s1 s2 _ [f1 IH1] _ [f2 IH2].
    exists (S (Nat.max f1 f2)). simpl.
    pose proof (@eval_cmd_fuel_mono f1 (Nat.max f1 f2) c1 s s1 ltac:(lia) IH1) as H1.
    pose proof (@eval_cmd_fuel_mono f2 (Nat.max f1 f2) c2 s1 s2 ltac:(lia) IH2) as H2.
    rewrite H1. exact H2.
  - (* D_Loop *) intros x c y s s' Hx _ [fl IHloop].
    exists (S fl). simpl.
    destruct (s x); [contradiction|exact IHloop].
  - (* L_Base *) intros x c y s Hy.
    exists 1. simpl. destruct (s y); [contradiction|reflexivity].
  - (* L_Rec *) intros x c y s s1 s2 Hyf _ [fb IHbody] Hxn _ [fl IHloop].
    exists (S (Nat.max fb fl)). simpl.
    rewrite Hyf.
    pose proof (@eval_cmd_fuel_mono fb (Nat.max fb fl) c s s1 ltac:(lia) IHbody) as Hb.
    pose proof (@eval_loop_fuel_mono fl (Nat.max fb fl) x c y s1 s2 ltac:(lia) IHloop) as Hl.
    rewrite Hb, Hxn. exact Hl.
Qed.

Theorem eval_cmd_complete :
  forall c s s', exec_ds c s s' -> exists fuel, eval_cmd_fuel fuel c s = Some s'.
Proof. apply (proj1 eval_cmd_loop_complete). Qed.

Theorem eval_loop_complete :
  forall x c y s s', loop_sem x c y s s' -> exists fuel, eval_loop_fuel fuel x c y s = Some s'.
Proof. apply (proj2 eval_cmd_loop_complete). Qed.

(* The interpreter is correct: there exists fuel iff the program terminates. *)
Theorem eval_cmd_correct :
  forall c s s', (exists fuel, eval_cmd_fuel fuel c s = Some s') <-> exec_ds c s s'.
Proof.
  intros c s s'. split.
  - intros [fuel H]. eapply eval_cmd_sound; eauto.
  - apply eval_cmd_complete.
Qed.

(* ================================================================= *)
(* 29. Syntactic inverter and reversibility at the source level       *)
(* ================================================================= *)

(* For each R-CORE cmd [c], [inv c] is the cmd that runs the inverse
   computation: it consumes the output store and produces the input.
   Reversibility is structural:
   - Assignments are self-inverse (the value side flips via [odot]).
   - Sequences reverse order.
   - Loops swap the entry assertion and exit test variables. *)
Fixpoint inv (c : cmd) : cmd :=
  match c with
  | Cass x e    => Cass x e
  | Cseq c1 c2  => Cseq (inv c2) (inv c1)
  | Cloop x c y => Cloop y (inv c) x
  end.

Lemma inv_involutive : forall c, inv (inv c) = c.
Proof. induction c; simpl; congruence. Qed.

(* ------------------------------------------------------------------ *)
(* Auxiliary [loop_iters]: like [loop_sem] but without the L_Base exit. *)
(* This relation tracks "n iterations of the loop body, no exit yet".  *)
(* Right-extensible (proven below), which is what we need for inverse. *)
Inductive loop_iters : var -> cmd -> var -> store -> store -> Prop :=
  | LI_nil  : forall x c y s, loop_iters x c y s s
  | LI_cons : forall x c y s s1 s2,
      s y = Vnil ->
      exec_ds c s s1 ->
      s1 x = Vnil ->
      loop_iters x c y s1 s2 ->
      loop_iters x c y s s2.

Lemma loop_sem_iff_iters :
  forall x c y s s',
    loop_sem x c y s s' <-> (loop_iters x c y s s' /\ s' y <> Vnil).
Proof.
  intros. split.
  - induction 1.
    + split; [apply LI_nil|assumption].
    + destruct IHloop_sem as [Hiters Hexit].
      split; [|exact Hexit].
      eapply LI_cons; eauto.
  - intros [Hiters Hexit]. induction Hiters.
    + apply L_Base; assumption.
    + eapply L_Rec; eauto.
Qed.

(* Right-extension (snoc) for loop_iters. *)
Lemma loop_iters_snoc :
  forall x c y s s_mid,
    loop_iters x c y s s_mid ->
    forall s_pre,
      s_mid y = Vnil ->
      exec_ds c s_mid s_pre ->
      s_pre x = Vnil ->
      loop_iters x c y s s_pre.
Proof.
  intros x c y s s_mid H. induction H; intros s_pre Hy Hbody Hx_pre.
  - eapply LI_cons; eauto. apply LI_nil.
  - eapply LI_cons; eauto.
Qed.

(* The key inverse lemma for loop_iters (no exit-assertion needed). *)
Lemma loop_iters_inv :
  forall x c y s s',
    loop_iters x c y s s' ->
    (forall s0 s0', exec_ds c s0 s0' -> exec_ds (inv c) s0' s0) ->
    loop_iters y (inv c) x s' s.
Proof.
  intros x c y s s' H Pbody. induction H.
  - apply LI_nil.
  - (* LI_cons: s y = nil, body s s1, s1 x = nil, loop_iters x c y s1 s2.
       IH: loop_iters y (inv c) x s2 s1.  Want: loop_iters y (inv c) x s2 s. *)
    eapply loop_iters_snoc; eauto.
Qed.

(* Inverse for loop_sem (needs the outer entry assertion s x <> Vnil). *)
Lemma loop_sem_inv :
  forall x c y s s',
    loop_sem x c y s s' ->
    s x <> Vnil ->
    (forall s0 s0', exec_ds c s0 s0' -> exec_ds (inv c) s0' s0) ->
    loop_sem y (inv c) x s' s.
Proof.
  intros x c y s s' Hloop Hx Pbody.
  apply loop_sem_iff_iters in Hloop. destruct Hloop as [Hiters _].
  apply loop_sem_iff_iters. split.
  - eapply loop_iters_inv; eauto.
  - exact Hx.
Qed.

(* ------------------------------------------------------------------ *)
(* Main correctness theorem for the syntactic inverter.
   Reversibility requires well-formedness (assertion-variable
   non-free in expression) — exactly the side condition the paper
   imposes. *)

Theorem inv_correct :
  forall c, wf_cmd c -> forall s s', exec_ds c s s' -> exec_ds (inv c) s' s.
Proof.
  induction c; intros Hwf s s' H.
  - (* Cass x e *)
    inversion Hwf as [x' e' Hnf | |]; subst.
    inversion H as [x_ e_ s_ v_e v_new Heval Hod | |]; subst.
    simpl.
    (* Want: exec_ds (Cass x e) (update s x v_new) s. *)
    pose proof (@eval_expr_update_invariant x e s v_new Hnf) as Heval'.
    rewrite Heval in Heval'.
    apply odot_inv in Hod.
    (* D_Asn produces [update (update s x v_new) x (s x)], which agrees
       pointwise with [s]; we close via [store_ext] (now axiom-free,
       backed by [Vector.eq_nth_iff]). *)
    replace s with (update (update s x v_new) x (s x)) at 2.
    + apply D_Asn with (v_e := v_e).
      * exact Heval'.
      * rewrite update_eq. exact Hod.
    + apply store_ext. intros y. destruct (Fin.eq_dec y x) as [Hy|Hy].
      * subst y. now rewrite update_eq.
      * now rewrite !update_neq by auto.
  - (* Cseq c1 c2 *)
    inversion Hwf; subst.
    inversion H; subst.
    simpl. eapply D_Seq.
    + apply IHc2; eassumption.
    + apply IHc1; eassumption.
  - (* Cloop x c y *)
    inversion Hwf as [| |x_ c_ y_ Hwfc]; subst.
    inversion H as [| |x_ c_ y_ s_ s'_ Hx Hloop]; subst.
    simpl. apply D_Loop.
    + (* Need: s' y <> Vnil.  From loop_sem exit invariant. *)
      apply loop_sem_iff_iters in Hloop. destruct Hloop as [_ Hexit]. exact Hexit.
    + eapply loop_sem_inv; try eassumption.
      intros s0 s0' Hbody. apply IHc; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Corollaries: dagger laws.                                          *)

(* Well-formedness is preserved by inversion. *)
Lemma wf_cmd_inv : forall c, wf_cmd c -> wf_cmd (inv c).
Proof.
  induction 1; simpl.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

(* The "iff" form of inv_correct: under wf, forward and backward are
   the same up to swapping source and target. *)
Theorem inv_correct_iff :
  forall c, wf_cmd c -> forall s s', exec_ds c s s' <-> exec_ds (inv c) s' s.
Proof.
  intros c Hwf s s'. split.
  - apply inv_correct; assumption.
  - intros H.
    apply inv_correct in H; [|apply wf_cmd_inv; assumption].
    rewrite inv_involutive in H. exact H.
Qed.

(* Dagger law 1: (c1 ; c2)† = c2† ; c1†.  This is by definition. *)
Lemma inv_seq : forall c1 c2, inv (Cseq c1 c2) = Cseq (inv c2) (inv c1).
Proof. reflexivity. Qed.

(* Dagger law 2: (c†)† = c.  This is [inv_involutive]. *)

(* Dagger law 3: running [c] then [c†] is the identity (on well-formed
   programs with terminating runs).  This is "compose-id".  We state
   it semantically: any forward run is exactly undone by inv c. *)
Theorem inv_compose_id :
  forall c, wf_cmd c -> forall s s',
    exec_ds c s s' ->
    exec_ds (Cseq c (inv c)) s s.
Proof.
  intros c Hwf s s' H.
  eapply D_Seq.
  - exact H.
  - apply inv_correct; assumption.
Qed.

(* Symmetric form: inv c then c is also the identity. *)
Theorem inv_compose_id_sym :
  forall c, wf_cmd c -> forall s s',
    exec_ds (inv c) s s' ->
    exec_ds (Cseq (inv c) c) s s.
Proof.
  intros c Hwf s s' H.
  eapply D_Seq.
  - exact H.
  - apply inv_correct_iff; assumption.
Qed.

(* ================================================================= *)
(* 30. Full Abstraction: contextual <-> denotational equivalence       *)
(* ================================================================= *)

(* Single-hole program contexts. *)
Inductive ctx : Type :=
  | C_Hole  : ctx
  | C_SeqL  : ctx -> cmd -> ctx
  | C_SeqR  : cmd -> ctx -> ctx
  | C_LoopC : var -> ctx -> var -> ctx.

Fixpoint ctx_fill (C : ctx) (c : cmd) : cmd :=
  match C with
  | C_Hole         => c
  | C_SeqL  C' c2  => Cseq (ctx_fill C' c) c2
  | C_SeqR  c1 C'  => Cseq c1 (ctx_fill C' c)
  | C_LoopC x C' y => Cloop x (ctx_fill C' c) y
  end.

(* Denotational equivalence: same store-to-store relation. *)
Definition denot_eq (c1 c2 : cmd) : Prop :=
  forall s s', exec_ds c1 s s' <-> exec_ds c2 s s'.

(* Contextual equivalence: same observational behavior under every context. *)
Definition cxt_eq (c1 c2 : cmd) : Prop :=
  forall C s s', exec_ds (ctx_fill C c1) s s' <-> exec_ds (ctx_fill C c2) s s'.

(* Equivalence-relation properties for denot_eq. *)
Lemma denot_eq_refl : forall c, denot_eq c c.
Proof. intros c s s'. reflexivity. Qed.

Lemma denot_eq_sym : forall c1 c2, denot_eq c1 c2 -> denot_eq c2 c1.
Proof. intros c1 c2 Heq s s'. symmetry. apply Heq. Qed.

Lemma denot_eq_trans :
  forall c1 c2 c3, denot_eq c1 c2 -> denot_eq c2 c3 -> denot_eq c1 c3.
Proof. intros c1 c2 c3 H12 H23 s s'. etransitivity; eauto. Qed.

(* Body-equivalence is preserved by [loop_sem]. *)
Lemma loop_sem_compat :
  forall x y c1 c2 s s',
    denot_eq c1 c2 -> (loop_sem x c1 y s s' <-> loop_sem x c2 y s s').
Proof.
  intros x y c1 c2 s s' Heq. split; intros H.
  - induction H.
    + apply L_Base; assumption.
    + eapply L_Rec; eauto. apply Heq; assumption.
  - induction H.
    + apply L_Base; assumption.
    + eapply L_Rec; eauto. apply Heq; assumption.
Qed.

(* Congruence under each context frame. *)
Lemma denot_eq_compat_seq_l :
  forall c1 c2 c, denot_eq c1 c2 -> denot_eq (Cseq c1 c) (Cseq c2 c).
Proof.
  intros c1 c2 c Heq s s''. split; intros H; inversion H; subst;
    eapply D_Seq; try eassumption; apply Heq; assumption.
Qed.

Lemma denot_eq_compat_seq_r :
  forall c c1 c2, denot_eq c1 c2 -> denot_eq (Cseq c c1) (Cseq c c2).
Proof.
  intros c c1 c2 Heq s s''. split; intros H; inversion H; subst;
    eapply D_Seq; try eassumption; apply Heq; assumption.
Qed.

Lemma denot_eq_compat_loop :
  forall x c1 c2 y, denot_eq c1 c2 -> denot_eq (Cloop x c1 y) (Cloop x c2 y).
Proof.
  intros x c1 c2 y Heq s s'. split.
  - intros H. inversion H; subst.
    apply D_Loop; [assumption|].
    pose proof (@loop_sem_compat x y c1 c2 s s' Heq) as [Hf _]. apply Hf; assumption.
  - intros H. inversion H; subst.
    apply D_Loop; [assumption|].
    pose proof (@loop_sem_compat x y c1 c2 s s' Heq) as [_ Hb]. apply Hb; assumption.
Qed.

(* SOUNDNESS: denotational equivalence implies contextual equivalence. *)
Theorem fa_soundness : forall c1 c2, denot_eq c1 c2 -> cxt_eq c1 c2.
Proof.
  intros c1 c2 Heq C.
  induction C as [|C IH c2'|c1' C IH|x C IH y]; simpl.
  - intros s s'. apply Heq.
  - intros s s'. eapply denot_eq_compat_seq_l. exact IH.
  - intros s s'. eapply denot_eq_compat_seq_r. exact IH.
  - intros s s'. eapply denot_eq_compat_loop. exact IH.
Qed.

(* COMPLETENESS: empty context already witnesses equivalence. *)
Theorem fa_completeness : forall c1 c2, cxt_eq c1 c2 -> denot_eq c1 c2.
Proof. intros c1 c2 Heq s s'. apply (Heq C_Hole). Qed.

(* FULL ABSTRACTION. *)
Theorem full_abstraction :
  forall c1 c2, denot_eq c1 c2 <-> cxt_eq c1 c2.
Proof. split; [apply fa_soundness | apply fa_completeness]. Qed.

(* ================================================================= *)
(* 31. Categorical (Dagger) Semantics                                  *)
(* ================================================================= *)

(* The category we build:
   - Objects: store (the type of variable maps).  Conceptually all R-CORE
     programs share the same store type, so we have a one-object category
     in the strict sense; the "type" of a morphism is determined by its
     domain of definition.
   - Morphisms: binary relations [store -> store -> Prop].  R-CORE
     denotations are partial injective functions, so they sit inside this
     larger category as a sub-collection.
   - Identity, composition, dagger: defined below.

   We verify the standard dagger-category axioms unconditionally on
   relations, then show R-CORE syntax forms a dagger functor into this
   category (Cseq -> composition, inv -> dagger). *)

Definition denot : Type := store -> store -> Prop.

Definition denot_id : denot := fun s s' => s = s'.

Definition denot_comp (f g : denot) : denot :=
  fun s s'' => exists s', f s s' /\ g s' s''.

Definition denot_dagger (f : denot) : denot := fun s s' => f s' s.

Definition denot_eqv (f g : denot) : Prop := forall s s', f s s' <-> g s s'.

(* Equivalence-relation properties. *)
Lemma denot_eqv_refl : forall f, denot_eqv f f.
Proof. intros f s s'. reflexivity. Qed.

Lemma denot_eqv_sym : forall f g, denot_eqv f g -> denot_eqv g f.
Proof. intros f g H s s'. symmetry. apply H. Qed.

Lemma denot_eqv_trans :
  forall f g h, denot_eqv f g -> denot_eqv g h -> denot_eqv f h.
Proof. intros f g h Hfg Hgh s s'. etransitivity; eauto. Qed.

(* --- Category axioms --- *)

Lemma denot_comp_id_l : forall f, denot_eqv (denot_comp denot_id f) f.
Proof.
  intros f s s'. unfold denot_comp, denot_id. split.
  - intros [s_ [Heq Hf]]; subst; assumption.
  - intros Hf. exists s. split; [reflexivity|assumption].
Qed.

Lemma denot_comp_id_r : forall f, denot_eqv (denot_comp f denot_id) f.
Proof.
  intros f s s'. unfold denot_comp, denot_id. split.
  - intros [s_ [Hf Heq]]; subst; assumption.
  - intros Hf. exists s'. split; [assumption|reflexivity].
Qed.

Lemma denot_comp_assoc : forall f g h,
  denot_eqv (denot_comp (denot_comp f g) h) (denot_comp f (denot_comp g h)).
Proof.
  intros f g h s s'''. unfold denot_comp. split.
  - intros [s'' [[s' [Hf Hg]] Hh]]. exists s'. split; [assumption|].
    exists s''. split; assumption.
  - intros [s' [Hf [s'' [Hg Hh]]]]. exists s''. split; [|assumption].
    exists s'. split; assumption.
Qed.

(* --- Dagger axioms --- *)

Lemma denot_dagger_involutive : forall f, denot_eqv (denot_dagger (denot_dagger f)) f.
Proof. intros f s s'. unfold denot_dagger. reflexivity. Qed.

Lemma denot_dagger_id : denot_eqv (denot_dagger denot_id) denot_id.
Proof.
  intros s s'. unfold denot_dagger, denot_id. split; intros; subst; reflexivity.
Qed.

Lemma denot_dagger_comp : forall f g,
  denot_eqv (denot_dagger (denot_comp f g))
            (denot_comp (denot_dagger g) (denot_dagger f)).
Proof.
  intros f g s s''. unfold denot_dagger, denot_comp. split.
  - intros [s' [Hf Hg]]. exists s'. split; assumption.
  - intros [s' [Hg Hf]]. exists s'. split; assumption.
Qed.

(* --- R-CORE denotation as a dagger functor into [denot] --- *)

Definition cmd_denot (c : cmd) : denot := exec_ds c.

(* Functoriality wrt composition: cmd_denot (Cseq c1 c2) = c1 ; c2 in [denot]. *)
Theorem cmd_denot_seq : forall c1 c2,
  denot_eqv (cmd_denot (Cseq c1 c2)) (denot_comp (cmd_denot c1) (cmd_denot c2)).
Proof.
  intros c1 c2 s s''. unfold cmd_denot, denot_comp. split.
  - intros H. inversion H; subst. exists s1. split; assumption.
  - intros [s' [H1 H2]]. eapply D_Seq; eassumption.
Qed.

(* Functoriality wrt dagger: cmd_denot (inv c) = (cmd_denot c)†, under wf. *)
Theorem cmd_denot_dagger : forall c, wf_cmd c ->
  denot_eqv (cmd_denot (inv c)) (denot_dagger (cmd_denot c)).
Proof.
  intros c Hwf s s'. unfold cmd_denot, denot_dagger.
  symmetry. apply (@inv_correct_iff c Hwf).
Qed.

(* Compatibility of cmd_denot with denot_eq (semantic-syntactic bridge). *)
Lemma cmd_denot_eq_iff_eqv :
  forall c1 c2, denot_eq c1 c2 <-> denot_eqv (cmd_denot c1) (cmd_denot c2).
Proof. unfold denot_eq, denot_eqv, cmd_denot. tauto. Qed.

(* The image of [cmd_denot] is closed under dagger: every R-CORE program
   has a syntactic inverse whose denotation is the dagger.  This is a
   "dagger subcategory" statement, witnessed by [inv]. *)
Theorem cmd_denot_dagger_image :
  forall c, wf_cmd c -> exists c', wf_cmd c' /\
    denot_eqv (cmd_denot c') (denot_dagger (cmd_denot c)).
Proof.
  intros c Hwf. exists (inv c). split.
  - apply wf_cmd_inv; assumption.
  - apply cmd_denot_dagger; assumption.
Qed.

(* [denot_eqv]-respecting dagger, needed to chain [cmd_denot_seq] and
   [denot_dagger_comp] below. *)
Lemma denot_dagger_proper :
  forall f g, denot_eqv f g -> denot_eqv (denot_dagger f) (denot_dagger g).
Proof. intros f g H s s'. apply H. Qed.

(* The syntactic inverter is an anti-homomorphism for sequencing at the
   semantic level too, not just syntactically ([inv_seq]): the dagger
   of a composition is the composition of the daggers, reversed.  This
   instantiates the abstract dagger-category law [denot_dagger_comp]
   at [cmd_denot]. *)
Corollary cmd_denot_inv_seq :
  forall c1 c2, wf_cmd c1 -> wf_cmd c2 ->
    denot_eqv (cmd_denot (inv (Cseq c1 c2)))
              (denot_comp (denot_dagger (cmd_denot c2)) (denot_dagger (cmd_denot c1))).
Proof.
  intros c1 c2 Hwf1 Hwf2.
  assert (Hwf : wf_cmd (Cseq c1 c2)) by (constructor; assumption).
  pose proof (cmd_denot_dagger Hwf) as Step1.
  pose proof (denot_dagger_proper (cmd_denot_seq c1 c2)) as Step2.
  pose proof (denot_dagger_comp (cmd_denot c1) (cmd_denot c2)) as Step3.
  eapply denot_eqv_trans; [exact Step1 |].
  eapply denot_eqv_trans; [exact Step2 | exact Step3].
Qed.

(* ================================================================= *)
(* 32. Backward preservation of well-formedness, and the single-      *)
(*     hypothesis form of backward determinism.                       *)
(*                                                                    *)
(*  A step moves the control token but never changes the underlying   *)
(*  command content, so [wf_cc] is invariant in BOTH directions.      *)
(*  [wf_cc_step_preserved] (section 8) is the forward direction; here *)
(*  is the mirror.  Consequently backward determinism can hypothesize *)
(*  well-formedness of the single COMMON TARGET configuration instead *)
(*  of both predecessors ([ss_bwd_deterministic_tgt]).                *)
(*                                                                    *)
(*  In the Letter these are Letter:Lem 1 (reflection) and Letter:Thm 2 *)
(*  (backward determinism); Letter:Lem 2 (preservation) is            *)
(*  [wf_cc_step_preserved] in Sect. 8.                                *)
(* ================================================================= *)

(* Letter:Lem 1 (Reflection of well-formedness). *)
Lemma wf_cc_step_reflected :
  forall cc s cc' s', exec_ss (cc, s) (cc', s') -> wf_cc cc' -> wf_cc cc.
Proof.
  intros cc s cc' s' Hstep Hwf.
  remember (cc, s) as cfg eqn:E1; remember (cc', s') as cfg' eqn:E2.
  revert cc s cc' s' E1 E2 Hwf.
  induction Hstep; intros; inversion E1; inversion E2; subst; clear E1 E2;
    repeat match goal with
    | [ H : wf_cc (CC_at_pre _)   |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_at_post _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_mid_loop _ _ _) |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_seq_L _ _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_seq_R _ _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cc (CC_in_loop _ _ _) |- _ ] => inversion H; subst; clear H
    | [ H : wf_cmd (Cseq _ _)  |- _ ] => inversion H; subst; clear H
    | [ H : wf_cmd (Cloop _ _ _) |- _ ] => inversion H; subst; clear H
    end;
    eauto 6 using wf_pre, wf_post, wf_mid, wf_seq_L, wf_seq_R, wf_in_lp,
                  wf_Cass, wf_Cseq, wf_Cloop.
Qed.

(* Letter:Thm 2 (Backward determinism).  A single hypothesis: the
   well-formedness of the common target.  Equivalent to
   [ss_bwd_deterministic] by the two-directional invariance of [wf_cc]. *)
Theorem ss_bwd_deterministic_tgt :
  forall cfg1 cfg2 cfg,
    wf_cc (fst cfg) ->
    exec_ss cfg1 cfg -> exec_ss cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros [cc1 s1] [cc2 s2] [cc s] Hwf H1 H2.
  apply ss_bwd_deterministic with (cfg := (cc, s)); simpl in *; try assumption.
  - exact (wf_cc_step_reflected H1 Hwf).
  - exact (wf_cc_step_reflected H2 Hwf).
Qed.

Print Assumptions wf_cc_step_reflected.
Print Assumptions ss_bwd_deterministic_tgt.

(* ================================================================= *)
(* 33. Determinism of the finer-grained semantics (fss)               *)
(* ================================================================= *)

(* Forward determinism of [fstep] holds unconditionally, exactly as for
   ss.  The only structural fact needed is that the fall-through position
   [CF_pre F_nil] is stuck, which separates the FS_AssertF and FS_Ctx
   rules on an in-loop configuration. *)

Lemma fstep_nil_stuck : forall s cfg, ~ fstep (CF_pre F_nil, s) cfg.
Proof. intros s cfg H. inversion H. Qed.

Theorem fstep_forward_deterministic :
  forall cfg cfg1 cfg2, fstep cfg cfg1 -> fstep cfg cfg2 -> cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1. revert cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst;
    try reflexivity; try congruence.
  - (* FS_AssertF vs FS_Ctx: the inner token is at CF_pre F_nil, stuck *)
    match goal with
    | [ Hin : fstep (CF_pre F_nil, _) _ |- _ ] =>
        exfalso; exact (fstep_nil_stuck Hin)
    end.
  - (* FS_Ctx vs FS_AssertF: same, from the other side *)
    exfalso; exact (fstep_nil_stuck H1).
  - (* FS_Ctx vs FS_Ctx *)
    match goal with
    | [ Hin : fstep (?cc0, ?s0) _ |- _ ] =>
        let E := fresh "E" in
        assert (E : (cc', s') = (cc'0, s'0)) by (apply IHfstep; exact Hin);
        injection E as -> ->; reflexivity
    end.
Qed.

(* Well-formedness at the flowchart level: every assignment atom
   satisfies the same "assigned variable not free in the RHS" side
   condition as [wf_cmd], lifted through loop bodies and continuations. *)

Inductive wf_flow : flowchart -> Prop :=
  | wf_F_nil  : wf_flow F_nil
  | wf_F_step : forall x e F,
      nf_expr x e -> wf_flow F -> wf_flow (F_step x e F)
  | wf_F_loop : forall x body y rest,
      wf_flow body -> wf_flow rest -> wf_flow (F_loop x body y rest).

Inductive wf_cf : ctrl_flow -> Prop :=
  | wf_CF_pre : forall F, wf_flow F -> wf_cf (CF_pre F)
  | wf_CF_mid : forall x body y rest,
      wf_flow body -> wf_flow rest -> wf_cf (CF_mid x body y rest)
  | wf_CF_in_loop : forall x body cc y rest,
      wf_flow body -> wf_cf cc -> wf_flow rest ->
      wf_cf (CF_in_loop x body cc y rest).

(* Backward determinism FAILS for the raw [fstep] relation, even under
   well-formedness.  The reason is structural, not data-related: a
   [ctrl_flow] records only the REMAINING flowchart, so the executed
   prefix is forgotten, and two configurations of different programs can
   step onto the same target.  Concretely, both a step atom and a loop
   exit can land on the fall-through position [CF_pre F_nil] with the
   same store.  (Contrast ss: a [cont_cmd] carries the whole program,
   which is what makes [ss_bwd_deterministic_tgt] provable.) *)

Definition cex_store : store :=
  update (Vector.const Vnil 10) X1 (Vpair Vnil Vnil).

Theorem fstep_not_backward_deterministic :
  exists cfg1 cfg2 cfg,
    wf_cf (fst cfg1) /\ wf_cf (fst cfg2) /\
    fstep cfg1 cfg /\ fstep cfg2 cfg /\ cfg1 <> cfg2.
Proof.
  exists (CF_pre (F_step X0 Enil F_nil), cex_store).
  exists (CF_mid X0 F_nil X1 F_nil, cex_store).
  exists (CF_pre F_nil, cex_store).
  repeat split.
  - (* wf of the assignment source: X0 not free in Enil *)
    constructor. constructor; constructor.
  - constructor; constructor.
  - (* the assignment fires and rewrites nil to nil in place *)
    assert (Hupd : update cex_store X0 Vnil = cex_store) by reflexivity.
    rewrite <- Hupd at 2.
    apply FS_Asn with (v_e := Vnil); reflexivity.
  - (* the loop exit fires: cex_store X1 <> Vnil *)
    apply FS_TestT. discriminate.
  - discriminate.
Qed.

(* What DOES hold backward is the local invertibility of each atom
   traversal: with the control component of the source fixed, the
   pre-store is uniquely determined by the target.  Only the assignment
   case has content; it is the fss counterpart of the assignment case
   of [ss_bwd_deterministic_tgt].  The hypothesis is the MINIMAL one:
   only the atom currently under the token needs the "assigned variable
   not free in the RHS" condition ([nf_head]); full [wf_cf] is not
   required and is recovered as a corollary below. *)

Fixpoint nf_head (cc : ctrl_flow) : Prop :=
  match cc with
  | CF_pre (F_step x e _)  => nf_expr x e
  | CF_in_loop _ _ cc' _ _ => nf_head cc'
  | _                      => True
  end.

Theorem fstep_backward_store_deterministic_nf :
  forall cc s1 s2 cfg,
    nf_head cc ->
    fstep (cc, s1) cfg -> fstep (cc, s2) cfg -> s1 = s2.
Proof.
  intros cc s1 s2 cfg Hwf H1. revert s2.
  remember (cc, s1) as src eqn:Esrc.
  revert cc s1 Hwf Esrc.
  induction H1; intros cc0 s1 Hwf Esrc s2 H2;
    injection Esrc as E1 E2; subst; inversion H2; subst; try reflexivity.
  - (* FS_Asn vs FS_Asn *)
    simpl in Hwf. rename Hwf into Hnf.
    match goal with
    | [ Hupd : update ?sb x ?vnb = update ?sa x ?vna |- ?sa = ?sb ] =>
        let Hoff := fresh "Hoff" in
        let Hveq := fresh "Hveq" in
        let Hagr := fresh "Hagr" in
        let Hx   := fresh "Hx"   in
        pose proof (update_injective_off_x _ _ _ _ Hupd) as Hoff;
        pose proof (update_value_at_x _ _ _ _ _ Hupd) as Hveq;
        subst vnb;
        pose proof (eval_expr_agree _ _ Hnf Hoff) as Hagr;
        match goal with
        | [ Hea : eval_expr sb e = Some _, Heb : eval_expr sa e = Some _ |- _ ] =>
            rewrite Hea, Heb in Hagr; injection Hagr as ->
        end;
        assert (Hx : sb x = sa x) by (eapply odot_left_injective; eauto);
        apply store_ext; intros y;
        destruct (Fin.eq_dec y x) as [->|Hy];
        [ symmetry; exact Hx | symmetry; apply Hoff; exact Hy ]
    end.
  - (* FS_Ctx vs FS_Ctx *)
    simpl in Hwf.
    eapply IHfstep; eauto.
Qed.

Lemma wf_cf_nf_head : forall cc, wf_cf cc -> nf_head cc.
Proof.
  intros cc H; induction H; simpl; auto.
  destruct F as [|x e K|x b y K]; simpl; auto.
  match goal with
  | [ W : wf_flow (F_step _ _ _) |- _ ] => inversion W; assumption
  end.
Qed.

Corollary fstep_backward_store_deterministic :
  forall cc s1 s2 cfg,
    wf_cf cc ->
    fstep (cc, s1) cfg -> fstep (cc, s2) cfg -> s1 = s2.
Proof.
  intros cc s1 s2 cfg Hwf.
  apply fstep_backward_store_deterministic_nf, wf_cf_nf_head, Hwf.
Qed.

Print Assumptions fstep_forward_deterministic.
Print Assumptions fstep_not_backward_deterministic.
Print Assumptions fstep_backward_store_deterministic.

(* ----------------------------------------------------------------- *)
(* 34. Backward determinism of fss over the positions of a fixed      *)
(*      program                                                       *)
(* ----------------------------------------------------------------- *)

(* The counterexample above mixes positions of DIFFERENT programs.  The
   intended reading of fss is a control token moving over one fixed
   flowchart, so the right statement restricts both predecessors to
   token positions of the same program F.  The engine is a structural
   fact: within one flowchart, every suffix has a unique parent (the
   suffix chain is linear and sizes strictly decrease), so the target
   position pins down the atom that was crossed; the store is then
   recovered by the local invertibility proved above. *)

Fixpoint fsize (F : flowchart) : nat :=
  match F with
  | F_nil          => 1
  | F_step _ _ K   => S (fsize K)
  | F_loop _ b _ K => S (fsize b + fsize K)
  end.

Definition fchild (F : flowchart) : option flowchart :=
  match F with
  | F_nil          => None
  | F_step _ _ K   => Some K
  | F_loop _ _ _ K => Some K
  end.

(* [tailf F G]: G is reached from F by descending continuations.
   Deliberately, [t_loop] does NOT descend into loop bodies: positions
   inside a body are represented by [CF_in_loop] and handled by the
   recursive occurrence of [posf] on the body, matching the shapes of
   [fstep] one-to-one.  On the continuation chain, sizes strictly
   decrease, so the chain is linear and each suffix occurs exactly
   once — the source of the unique-parent property below. *)
Inductive tailf : flowchart -> flowchart -> Prop :=
  | t_refl : forall F, tailf F F
  | t_step : forall x e K G, tailf K G -> tailf (F_step x e K) G
  | t_loop : forall x b y K G, tailf K G -> tailf (F_loop x b y K) G.

Lemma tailf_size : forall F G, tailf F G -> fsize G <= fsize F.
Proof. intros F G H; induction H; simpl; lia. Qed.

Lemma fchild_size : forall F G, fchild F = Some G -> fsize G < fsize F.
Proof. intros [|x e K|x b y K] G H; simpl in *; try discriminate;
       injection H as <-; lia. Qed.

(* A tail of K cannot have K itself as its child (size order). *)
Lemma tailf_child_absurd :
  forall K p, tailf K p -> fchild p = Some K -> False.
Proof.
  intros K p T C.
  pose proof (tailf_size T).
  assert (fsize K < fsize p) by (eapply fchild_size; eauto). lia.
Qed.

(* Unique-parent lemma: two tails of F with the same child coincide. *)
Lemma tailf_parent_unique :
  forall F p1 p2 G,
    tailf F p1 -> tailf F p2 ->
    fchild p1 = Some G -> fchild p2 = Some G -> p1 = p2.
Proof.
  induction F as [|x e K IH|x b IHb y K IH];
    intros p1 p2 G T1 T2 C1 C2;
    inversion T1; subst; inversion T2; subst;
    try reflexivity; simpl in C1; simpl in C2.
  - (* F_step: p1 = F (refl), p2 descends into K; child G = K *)
    injection C1 as <-. exfalso. eapply tailf_child_absurd; eauto.
  - (* F_step: p1 descends, p2 = F (refl) *)
    injection C2 as <-. exfalso. eapply tailf_child_absurd; eauto.
  - (* F_step: both descend *)
    eapply IH; eauto.
  - (* F_loop: p1 = F (refl), p2 descends into the continuation K *)
    injection C1 as <-. exfalso. eapply tailf_child_absurd; eauto.
  - (* F_loop: p1 descends, p2 = F (refl) *)
    injection C2 as <-. exfalso. eapply tailf_child_absurd; eauto.
  - (* F_loop: both descend *)
    eapply IH; eauto.
Qed.

Lemma wf_flow_tail : forall F G, tailf F G -> wf_flow F -> wf_flow G.
Proof.
  intros F G H; induction H; intros Hwf; auto; inversion Hwf; auto.
Qed.

(* Token positions of a fixed program F.  Note that [posf] is a
   syntactic over-approximation of reachability: it admits positions no
   execution visits (e.g. a mid-loop position of a loop whose guard
   never allows entry).  The determinism results below therefore hold
   on a superset of the reachable configurations, which is a strictly
   stronger statement. *)
Inductive posf : flowchart -> ctrl_flow -> Prop :=
  | pos_pre : forall F G, tailf F G -> posf F (CF_pre G)
  | pos_mid : forall F x b y rest,
      tailf F (F_loop x b y rest) -> posf F (CF_mid x b y rest)
  | pos_in  : forall F x b cc y rest,
      tailf F (F_loop x b y rest) -> posf b cc ->
      posf F (CF_in_loop x b cc y rest).

(* No step from a position of b lands on the entry position of the
   WHOLE body b (the fss mirror of "no transition lands on the position
   immediately before a command"): the would-be parent of b would have
   to be a tail of b itself, contradicting the size order. *)
Lemma posf_no_step_to_whole :
  forall b cc s s', posf b cc -> ~ fstep (cc, s) (CF_pre b, s').
Proof.
  intros b cc s s' Hpos Hst.
  inversion Hst; subst; inversion Hpos; subst.
  all: match goal with
       | [ T : tailf _ _ |- False ] =>
           (pose proof (tailf_size T) as HS; simpl in HS; lia)
       end.
Qed.

(* Packaged case lemmas for the main theorem, phrased so that every
   hypothesis can be discharged by [eauto] from the inverted context
   (no dependence on machine-generated hypothesis names). *)

Lemma fss_asn_asn_eq :
  forall F0 K x e x' e' s1 s2 v_e v_e' v1 v2,
    wf_flow F0 ->
    tailf F0 (F_step x e K) ->
    tailf F0 (F_step x' e' K) ->
    eval_expr s1 e = Some v_e ->
    odot (s1 x) v_e = Some v1 ->
    eval_expr s2 e' = Some v_e' ->
    odot (s2 x') v_e' = Some v2 ->
    update s2 x' v2 = update s1 x v1 ->
    (CF_pre (F_step x e K), s1) = (CF_pre (F_step x' e' K), s2).
Proof.
  intros F0 K x e x' e' s1 s2 v_e v_e' v1 v2 Hwf T1 T2 Hev1 Ho1 Hev2 Ho2 Hu.
  assert (P : F_step x e K = F_step x' e' K)
    by (eapply tailf_parent_unique; [exact T1|exact T2|reflexivity|reflexivity]).
  injection P as <- <-.
  assert (Hnf : nf_expr x e).
  { pose proof (wf_flow_tail T1 Hwf) as W. inversion W; assumption. }
  pose proof (update_injective_off_x _ _ _ _ (eq_sym Hu)) as Hoff.
  pose proof (eval_expr_agree _ _ Hnf Hoff) as Hagr.
  rewrite Hev1, Hev2 in Hagr. injection Hagr as <-.
  pose proof (update_value_at_x _ _ _ _ _ (eq_sym Hu)) as Hveq. subst v2.
  assert (Hx : s1 x = s2 x) by (eapply odot_left_injective; eauto).
  assert (Hs : s1 = s2).
  { apply store_ext; intros y.
    destruct (Fin.eq_dec y x) as [->|Hy]; [exact Hx|apply Hoff; exact Hy]. }
  now subst.
Qed.

Lemma fss_step_loop_absurd :
  forall (A : Prop) F0 x e x' b y' K,
    tailf F0 (F_step x e K) -> tailf F0 (F_loop x' b y' K) -> A.
Proof.
  intros A F0 x e x' b y' K T1 T2. exfalso.
  assert (P : F_step x e K = F_loop x' b y' K)
    by (eapply tailf_parent_unique; [exact T1|exact T2|reflexivity|reflexivity]).
  discriminate P.
Qed.

Lemma fss_loop_loop_eq :
  forall F0 x b y x' b' y' K (s : store),
    tailf F0 (F_loop x b y K) -> tailf F0 (F_loop x' b' y' K) ->
    (CF_mid x b y K, s) = (CF_mid x' b' y' K, s).
Proof.
  intros F0 x b y x' b' y' K s T1 T2.
  assert (P : F_loop x b y K = F_loop x' b' y' K)
    by (eapply tailf_parent_unique; [exact T1|exact T2|reflexivity|reflexivity]).
  injection P as <- <- <-. reflexivity.
Qed.

Lemma wf_flow_loop_body :
  forall F0 x b y K, tailf F0 (F_loop x b y K) -> wf_flow F0 -> wf_flow b.
Proof.
  intros F0 x b y K T Hwf.
  pose proof (wf_flow_tail T Hwf) as W. inversion W; assumption.
Qed.

(* Backward determinism of fss over the token positions of one fixed,
   well-formed program: the mixed cases die by parent uniqueness, the
   assignment case is closed by local invertibility, and the in-loop
   case recurses into the body. *)
Theorem fstep_backward_deterministic_pos :
  forall cc1 s1 tgt,
    fstep (cc1, s1) tgt ->
    forall F cc2 s2,
      wf_flow F -> posf F cc1 -> posf F cc2 ->
      fstep (cc2, s2) tgt ->
      (cc1, s1) = (cc2, s2).
Proof.
  intros cc1 s1 tgt H1.
  remember (cc1, s1) as src1 eqn:E1. revert cc1 s1 E1.
  induction H1; intros cc1 s1 E1 F0 cc2 s2 HwfF Hp1 Hp2 H2;
    injection E1 as E1a E1b; subst; inversion H2; subst.
  - (* FS_Asn vs FS_Asn *)
    inversion Hp1; subst; inversion Hp2; subst.
    eapply fss_asn_asn_eq; eauto.
  - (* FS_Asn vs FS_TestT *)
    inversion Hp1; subst; inversion Hp2; subst.
    eapply fss_step_loop_absurd; eauto.
  - (* FS_AssertT vs FS_AssertT *) reflexivity.
  - (* FS_AssertT vs FS_AssertF *) congruence.
  - (* FS_AssertF vs FS_AssertT *) congruence.
  - (* FS_AssertF vs FS_AssertF *) reflexivity.
  - (* FS_TestT vs FS_Asn *)
    inversion Hp1; subst; inversion Hp2; subst.
    eapply fss_step_loop_absurd; eauto.
  - (* FS_TestT vs FS_TestT *)
    inversion Hp1; subst; inversion Hp2; subst.
    eapply fss_loop_loop_eq; eauto.
  - (* FS_TestF vs FS_TestF *) reflexivity.
  - (* FS_TestF vs FS_Ctx *)
    inversion Hp2; subst.
    exfalso; eapply posf_no_step_to_whole; eauto.
  - (* FS_Ctx vs FS_TestF *)
    inversion Hp1; subst.
    exfalso; eapply posf_no_step_to_whole; eauto.
  - (* FS_Ctx vs FS_Ctx *)
    inversion Hp1; subst; inversion Hp2; subst.
    assert (Hwb : wf_flow body) by (eapply wf_flow_loop_body; eauto).
    match goal with
    | [ |- (CF_in_loop _ _ ?A _ _, ?SA) = (CF_in_loop _ _ ?B _ _, ?SB) ] =>
        (enough (E : (A, SA) = (B, SB)) by (injection E as <- <-; reflexivity));
        eapply IHfstep; eauto
    end.
Qed.

Print Assumptions fstep_backward_deterministic_pos.

(* ----------------------------------------------------------------- *)
(* 35. Invariance of posf and backward determinism along executions   *)
(* ----------------------------------------------------------------- *)

(* Descending one atom stays within the positions of F. *)
Lemma tailf_child :
  forall F p G, tailf F p -> fchild p = Some G -> tailf F G.
Proof.
  intros F p G T. revert G. induction T; intros G0 C.
  - destruct F as [|x e K|x b y K]; simpl in C; try discriminate;
      injection C as <-; constructor; constructor.
  - apply t_step; auto.
  - apply t_loop; auto.
Qed.

(* posf is preserved by steps: the token never leaves the program.
   (The REFLECTED direction fails, exactly as the raw counterexample
   shows: the target of a step can be a position of F while the source
   belongs to a different program.) *)
Lemma posf_step_preserved :
  forall cc s cc' s' F,
    posf F cc -> fstep (cc, s) (cc', s') -> posf F cc'.
Proof.
  intros cc s cc' s' F Hp Hst.
  revert F Hp.
  remember (cc, s) as src eqn:Es. remember (cc', s') as tgt eqn:Et.
  revert cc s cc' s' Es Et.
  induction Hst; intros cc0 s0 cc0' s0' Es Et F1 Hp;
    injection Es as <- <-; injection Et as <- <-;
    inversion Hp; subst.
  - (* FS_Asn *)
    apply pos_pre. eapply tailf_child; [eassumption|reflexivity].
  - (* FS_AssertT *)
    apply pos_mid. assumption.
  - (* FS_AssertF *)
    apply pos_mid. assumption.
  - (* FS_TestT *)
    apply pos_pre. eapply tailf_child; [eassumption|reflexivity].
  - (* FS_TestF *)
    apply pos_in; [assumption|apply pos_pre; apply t_refl].
  - (* FS_Ctx *)
    apply pos_in; [assumption|].
    eapply IHHst; eauto.
Qed.

Lemma posf_steps_preserved :
  forall F cc s cc' s',
    posf F cc -> fsteps (cc, s) (cc', s') -> posf F cc'.
Proof.
  intros F cc s cc' s' Hp Hst.
  remember (cc, s) as c1 eqn:E1. remember (cc', s') as c2 eqn:E2.
  revert cc s cc' s' Hp E1 E2.
  induction Hst as [cfg | cfg1 cfg2 cfg3 Hstep Hrest IH];
    intros cc s cc' s' Hp E1 E2; subst.
  - injection E2 as <- <-. exact Hp.
  - destruct cfg2 as [ccm sm].
    eapply IH; [|reflexivity|reflexivity].
    eapply posf_step_preserved; eauto.
Qed.

(* The side condition of [fstep_backward_deterministic_pos] is thereby
   discharged automatically along executions: any two predecessors of a
   common target that are reachable from the entry configuration of one
   well-formed program coincide. *)
Corollary fstep_backward_deterministic_reachable :
  forall F s0 cc1 s1 cc2 s2 tgt,
    wf_flow F ->
    fsteps (CF_pre F, s0) (cc1, s1) ->
    fsteps (CF_pre F, s0) (cc2, s2) ->
    fstep (cc1, s1) tgt -> fstep (cc2, s2) tgt ->
    (cc1, s1) = (cc2, s2).
Proof.
  intros F s0 cc1 s1 cc2 s2 tgt Hwf Hr1 Hr2 H1 H2.
  assert (Hp0 : posf F (CF_pre F)) by (apply pos_pre; apply t_refl).
  eapply fstep_backward_deterministic_pos; eauto using posf_steps_preserved.
Qed.

Print Assumptions posf_step_preserved.
Print Assumptions fstep_backward_deterministic_reachable.

(* ================================================================= *)
(* 36. Consequences of determinism                                    *)
(*                                                                    *)
(*  The three consequences reported in the companion letter, stated   *)
(*  as theorems rather than left to the reader: (1) uniqueness of     *)
(*  terminating runs, (2) determinism of the big-step semantics, and  *)
(*  (3) injectivity of the store map denoted by a well-formed         *)
(*  command.  Only (3) needs well-formedness, and it needs it only    *)
(*  through the program inverter [inv_correct].                       *)
(* ================================================================= *)

(* (1) Two runs out of a common start that both reach a stuck
   configuration reach the SAME one.  Forward determinism pins each
   step, and stuckness rules out one run stopping strictly earlier. *)
Lemma ss_run_unique_stuck :
  forall cfg cfg1 cfg2,
    exec_ss_star cfg cfg1 -> exec_ss_star cfg cfg2 ->
    (forall cfg', ~ exec_ss cfg1 cfg') ->
    (forall cfg', ~ exec_ss cfg2 cfg') ->
    cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1. revert cfg2.
  induction H1 as [cfg0 | cfga cfgm cfg1 Hstep Hstar IH];
    intros cfg2 H2 Hstuck1 Hstuck2.
  - inversion H2 as [|? cfgm2 ? Hstep2 Hstar2]; subst.
    + reflexivity.
    + exfalso; eapply Hstuck1; exact Hstep2.
  - inversion H2 as [|? cfgm2 ? Hstep2 Hstar2]; subst.
    + exfalso; eapply Hstuck2; exact Hstep.
    + assert (E : cfgm = cfgm2) by (eapply ss_step_deterministic; eauto).
      subst cfgm2. eapply IH; eauto.
Qed.

(* Terminal configurations are stuck ([no_step_from_at_post]), so a
   terminating run of a program is unique: the final store is. *)
Theorem ss_run_unique :
  forall c s s1 s2,
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s1) ->
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s2) ->
    s1 = s2.
Proof.
  intros c s s1 s2 H1 H2.
  assert (E : (CC_at_post c, s1) = (CC_at_post c, s2)).
  { eapply ss_run_unique_stuck; try exact H1; try exact H2;
      intros cfg' Hbad; eapply no_step_from_at_post; exact Hbad. }
  congruence.
Qed.

(* (1') The whole run, not just its final store, is determined by the
   starting configuration.  The letter's introduction says that one
   configuration determines the whole run, and [ss_run_unique] above
   pins only the terminal store, so the trace-level statement is proved
   here.  It has three parts: the configuration reached after a given
   number of steps is unique, a shorter run out of a configuration is a
   prefix of a longer one, and two maximal runs therefore agree in
   length as well as in endpoint.  Together they say that the run out of
   a configuration is one determined chain. *)

(* The configuration reached after [n] steps is unique. *)
Theorem ss_run_state_unique :
  forall n cfg cfg1 cfg2, nsteps n cfg cfg1 -> nsteps n cfg cfg2 -> cfg1 = cfg2.
Proof.
  induction n as [|n IH]; intros cfg cfg1 cfg2 H1 H2.
  - apply nsteps_zero_eq in H1; apply nsteps_zero_eq in H2; congruence.
  - inversion H1 as [|? ? cfgA ? Hst1 Hrest1]; subst.
    inversion H2 as [|? ? cfgB ? Hst2 Hrest2]; subst.
    assert (E : cfgA = cfgB) by (eapply ss_step_deterministic; eassumption).
    subst cfgB. eapply IH; eassumption.
Qed.

(* A shorter run is a prefix of a longer one out of the same
   configuration: the longer run passes through the endpoint of the
   shorter, and what remains is the difference of the two lengths. *)
Lemma ss_run_prefix :
  forall n m cfg cfg1 cfg2,
    n <= m -> nsteps n cfg cfg1 -> nsteps m cfg cfg2 -> nsteps (m - n) cfg1 cfg2.
Proof.
  induction n as [|n IH]; intros m cfg cfg1 cfg2 Hle H1 H2.
  - apply nsteps_zero_eq in H1. subst cfg1. rewrite Nat.sub_0_r. exact H2.
  - destruct m as [|m']; [lia|].
    inversion H1 as [|? ? cfgA ? Hst1 Hrest1]; subst.
    inversion H2 as [|? ? cfgB ? Hst2 Hrest2]; subst.
    assert (E : cfgA = cfgB) by (eapply ss_step_deterministic; eassumption).
    subst cfgB. simpl. eapply IH; [lia | eassumption | eassumption].
Qed.

(* Two maximal runs out of one configuration have the same length and
   the same endpoint, hence by [ss_run_state_unique] they agree at every
   intermediate step.  This is the trace-level form of "one
   configuration determines the whole run"; [ss_run_unique] is its
   store-level corollary for terminating programs. *)
Theorem ss_run_trace_unique :
  forall n m cfg cfg1 cfg2,
    nsteps n cfg cfg1 -> (forall cfg', ~ exec_ss cfg1 cfg') ->
    nsteps m cfg cfg2 -> (forall cfg', ~ exec_ss cfg2 cfg') ->
    n = m /\ cfg1 = cfg2.
Proof.
  intros n m cfg cfg1 cfg2 H1 Hs1 H2 Hs2.
  assert (Hnm : n = m).
  { destruct (Nat.le_ge_cases n m) as [Hle | Hge].
    - pose proof (ss_run_prefix Hle H1 H2) as Hp.
      remember (m - n) as k eqn:Ek. destruct k as [|k'].
      + lia.
      + inversion Hp; subst. exfalso.
        match goal with [ H : exec_ss cfg1 _ |- _ ] => eapply Hs1; exact H end.
    - pose proof (ss_run_prefix Hge H2 H1) as Hp.
      remember (n - m) as k eqn:Ek. destruct k as [|k'].
      + lia.
      + inversion Hp; subst. exfalso.
        match goal with [ H : exec_ss cfg2 _ |- _ ] => eapply Hs2; exact H end. }
  subst. split; [reflexivity | eapply ss_run_state_unique; eassumption].
Qed.

(* (2) Determinism of the big-step semantics, transported from ss
   through the equivalence.  No side condition. *)
Theorem ds_deterministic :
  forall c s s1 s2, exec_ds c s s1 -> exec_ds c s s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H1 H2.
  eapply ss_run_unique; apply ds_implies_ss; eassumption.
Qed.

(* (3) A well-formed command denotes an INJECTIVE partial store map.
   Determinism (2) says the map is a partial function; injectivity is
   the same statement for the syntactic inverse, which exists and is
   correct exactly for well-formed commands. *)
Theorem ds_injective :
  forall c, wf_cmd c ->
    forall s1 s2 s', exec_ds c s1 s' -> exec_ds c s2 s' -> s1 = s2.
Proof.
  intros c Hwf s1 s2 s' H1 H2.
  eapply ds_deterministic with (c := inv c) (s := s');
    apply inv_correct; assumption.
Qed.

(* Packaged denotationally: [cmd_denot c] is a partial injective map. *)
Corollary cmd_denot_partial_injective :
  forall c, wf_cmd c ->
    (forall s s1 s2, cmd_denot c s s1 -> cmd_denot c s s2 -> s1 = s2) /\
    (forall s1 s2 s', cmd_denot c s1 s' -> cmd_denot c s2 s' -> s1 = s2).
Proof.
  intros c Hwf. unfold cmd_denot. split.
  - intros s s1 s2; apply ds_deterministic.
  - intros s1 s2 s'; apply ds_injective; assumption.
Qed.

Print Assumptions ss_run_unique.
Print Assumptions ss_run_state_unique.
Print Assumptions ss_run_trace_unique.
Print Assumptions ds_deterministic.
Print Assumptions cmd_denot_partial_injective.

(* ================================================================= *)
(* 37. Well-formedness along executions                               *)
(*                                                                    *)
(*  Sections 8 and 22 show that [wf_cc] is invariant under a single   *)
(*  step, in both directions.  Closing this under multi-step          *)
(*  execution is what turns the side condition into a per-program     *)
(*  check: every configuration reachable from a well-formed program   *)
(*  is well-formed, so the hypothesis of [ss_bwd_deterministic_tgt]   *)
(*  is discharged automatically along an execution.  This mirrors     *)
(*  [posf_steps_preserved] / [fstep_backward_deterministic_reachable] *)
(*  on the fss side (Sect. 35).                                       *)
(* ================================================================= *)

Lemma wf_cc_steps_preserved :
  forall cfg cfg', exec_ss_star cfg cfg' -> wf_cc (fst cfg) -> wf_cc (fst cfg').
Proof.
  intros cfg cfg' H.
  induction H as [cfg0 | cfg1 cfg2 cfg3 Hstep Hstar IH]; intros Hwf.
  - exact Hwf.
  - apply IH.
    destruct cfg1 as [cc1 s1]; destruct cfg2 as [cc2 s2]; simpl in *.
    exact (wf_cc_step_preserved Hstep Hwf).
Qed.

Lemma wf_cc_steps_reflected :
  forall cfg cfg', exec_ss_star cfg cfg' -> wf_cc (fst cfg') -> wf_cc (fst cfg).
Proof.
  intros cfg cfg' H.
  induction H as [cfg0 | cfg1 cfg2 cfg3 Hstep Hstar IH]; intros Hwf.
  - exact Hwf.
  - destruct cfg1 as [cc1 s1]; destruct cfg2 as [cc2 s2]; simpl in *.
    exact (wf_cc_step_reflected Hstep (IH Hwf)).
Qed.

(* Backward determinism with no hypothesis on the two predecessors at
   all: it suffices that both are reachable from the entry of one
   well-formed program.  Along an execution, therefore, the transition
   relation is injective without further proof obligations. *)
Corollary ss_bwd_deterministic_reachable :
  forall cfg0 cfg1 cfg2 cfg,
    wf_cc (fst cfg0) ->
    exec_ss_star cfg0 cfg1 -> exec_ss_star cfg0 cfg2 ->
    exec_ss cfg1 cfg -> exec_ss cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros cfg0 cfg1 cfg2 cfg Hwf Hr1 Hr2 H1 H2.
  apply ss_bwd_deterministic with (cfg := cfg).
  - exact (wf_cc_steps_preserved Hr1 Hwf).
  - exact (wf_cc_steps_preserved Hr2 Hwf).
  - exact H1.
  - exact H2.
Qed.

Print Assumptions wf_cc_steps_preserved.
Print Assumptions ss_bwd_deterministic_reachable.

(* Backward determinism of a whole run, dual to [ss_run_state_unique]:
   two runs of the same length into a common well-formed target
   coincide at the start, not just that both single-step hypotheses of
   [ss_bwd_deterministic_tgt] can be discharged one step at a time.
   This grounds a reversible debugger's ability to step back through an
   execution one configuration at a time, not just to its own start. *)
Theorem ss_run_state_unique_bwd :
  forall n cfg1 cfg2 cfgT,
    wf_cc (fst cfgT) ->
    nsteps n cfg1 cfgT -> nsteps n cfg2 cfgT -> cfg1 = cfg2.
Proof.
  induction n as [|n IH]; intros cfg1 cfg2 cfgT Hwf H1 H2.
  - apply nsteps_zero_eq in H1; apply nsteps_zero_eq in H2; congruence.
  - inversion H1 as [|? ? cfgM1 ? Hst1 Hrest1]; subst.
    inversion H2 as [|? ? cfgM2 ? Hst2 Hrest2]; subst.
    assert (EM : cfgM1 = cfgM2) by (eapply IH; eassumption).
    subst cfgM2.
    assert (HwfM : wf_cc (fst cfgM1))
      by (eapply wf_cc_steps_reflected;
          [eapply nsteps_to_steps; exact Hrest1 | exact Hwf]).
    eapply ss_bwd_deterministic_tgt; eassumption.
Qed.

(* Once the two starts coincide, forward determinism pins every
   intermediate configuration too: the two runs are one and the same,
   traversed either direction. *)
Corollary ss_run_trace_unique_bwd :
  forall n cfg1 cfg2 cfgT,
    wf_cc (fst cfgT) ->
    nsteps n cfg1 cfgT -> nsteps n cfg2 cfgT ->
    forall k cfgA cfgB, nsteps k cfg1 cfgA -> nsteps k cfg2 cfgB -> cfgA = cfgB.
Proof.
  intros n cfg1 cfg2 cfgT Hwf H1 H2 k cfgA cfgB HA HB.
  assert (E : cfg1 = cfg2) by (eapply ss_run_state_unique_bwd; eassumption).
  subst cfg2. eapply ss_run_state_unique; eassumption.
Qed.

Print Assumptions ss_run_state_unique_bwd.
Print Assumptions ss_run_trace_unique_bwd.

(* ================================================================= *)
(* 38. Uniqueness of the inverse, and inverse correctness at the ss   *)
(*     and fss levels                                                 *)
(*                                                                    *)
(*  [inv_correct] (Sect. 29) states the correctness of the syntactic  *)
(*  inverter against the big-step semantics.  Two natural questions   *)
(*  are left open there: is [inv c] the ONLY inverse of [c], and does *)
(*  the same statement hold for the two small-step semantics?  Both   *)
(*  are settled here.                                                 *)
(* ================================================================= *)

(* Uniqueness.  Any command that inverts [c] pointwise agrees with
   [inv c] as a store relation: the inverse is unique up to
   denotational equality, which by full abstraction (Sect. 30) is the
   same as being indistinguishable in every context. *)
Theorem inv_unique :
  forall c c', wf_cmd c ->
    (forall s s', exec_ds c s s' <-> exec_ds c' s' s) ->
    denot_eq c' (inv c).
Proof.
  intros c c' Hwf Hinv s s'.
  rewrite <- (Hinv s' s).
  apply (inv_correct_iff Hwf).
Qed.

Corollary inv_unique_cxt :
  forall c c', wf_cmd c ->
    (forall s s', exec_ds c s s' <-> exec_ds c' s' s) ->
    cxt_eq c' (inv c).
Proof.
  intros c c' Hwf Hinv. apply fa_soundness, inv_unique; assumption.
Qed.

(* Inverse correctness at the ss level: a terminating run of [c] from
   [s] to [s'] is matched by a terminating run of [inv c] from [s']
   back to [s].  The proof goes through the equivalence of Sect. 27;
   the statement is about ss alone. *)
Theorem inv_correct_ss :
  forall c, wf_cmd c -> forall s s',
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') ->
    exec_ss_star (CC_at_pre (inv c), s') (CC_at_post (inv c), s).
Proof.
  intros c Hwf s s' H.
  apply ds_implies_ss, (inv_correct Hwf), ss_implies_ds, H.
Qed.

Corollary inv_correct_ss_iff :
  forall c, wf_cmd c -> forall s s',
    exec_ss_star (CC_at_pre c, s) (CC_at_post c, s') <->
    exec_ss_star (CC_at_pre (inv c), s') (CC_at_post (inv c), s).
Proof.
  intros c Hwf s s'. split.
  - apply inv_correct_ss; assumption.
  - intros H.
    pose proof (inv_correct_ss (wf_cmd_inv Hwf) H) as H'.
    rewrite inv_involutive in H'. exact H'.
Qed.

(* Same at the fss level, on the flowchart translated from [c]. *)
Theorem inv_correct_fss :
  forall c, wf_cmd c -> forall s s',
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s') ->
    fsteps (CF_pre (translate (inv c) F_nil), s') (CF_pre F_nil, s).
Proof.
  intros c Hwf s s' H.
  apply ds_implies_fss, (inv_correct Hwf), fss_implies_ds, H.
Qed.

Corollary inv_correct_fss_iff :
  forall c, wf_cmd c -> forall s s',
    fsteps (CF_pre (translate c F_nil), s) (CF_pre F_nil, s') <->
    fsteps (CF_pre (translate (inv c) F_nil), s') (CF_pre F_nil, s).
Proof.
  intros c Hwf s s'. split.
  - apply inv_correct_fss; assumption.
  - intros H.
    pose proof (inv_correct_fss (wf_cmd_inv Hwf) H) as H'.
    rewrite inv_involutive in H'. exact H'.
Qed.

(* ================================================================= *)
(* 39. The fss of the paper: a token moving over a FIXED flowchart    *)
(*                                                                    *)
(*  [fstep] (Sect. 20) rewrites the remaining flowchart, so the       *)
(*  executed prefix is forgotten and backward determinism fails       *)
(*  ([fstep_not_backward_deterministic]).  The paper presents fss     *)
(*  differently: the flowchart F is fixed once and for all and a      *)
(*  control token travels over it, just as the token of ss travels    *)
(*  over a fixed command.  A configuration is then a position of F    *)
(*  paired with a store, and the executed prefix is recoverable from  *)
(*  F.  With that reading, spelled out as [pstep F] below, backward   *)
(*  determinism holds, and it needs well-formedness of the program    *)
(*  only, not of any configuration.                                   *)
(* ================================================================= *)

Inductive pstep (F : flowchart)
  : ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | P_step : forall cf s cf' s',
      posf F cf -> fstep (cf, s) (cf', s') -> pstep F (cf, s) (cf', s').

Inductive psteps (F : flowchart)
  : ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | psteps_refl : forall cfg, psteps F cfg cfg
  | psteps_cons : forall cfg1 cfg2 cfg3,
      pstep F cfg1 cfg2 -> psteps F cfg2 cfg3 -> psteps F cfg1 cfg3.

(* The token enters at the head of F and leaves when the whole chart
   has been traversed; both are positions of F. *)
Definition pentry (F : flowchart) : ctrl_flow := CF_pre F.
Definition pexit : ctrl_flow := CF_pre F_nil.

Lemma posf_pentry : forall F, posf F (pentry F).
Proof. intros F. apply pos_pre, t_refl. Qed.

(* Forward determinism, unconditional, as for ss and for raw fss. *)
Lemma pstep_fstep :
  forall F cfg cfg', pstep F cfg cfg' -> fstep cfg cfg' /\ posf F (fst cfg).
Proof. intros F cfg cfg' H. inversion H; subst. split; assumption. Qed.

Theorem pstep_forward_deterministic :
  forall F cfg cfg1 cfg2,
    pstep F cfg cfg1 -> pstep F cfg cfg2 -> cfg1 = cfg2.
Proof.
  intros F cfg cfg1 cfg2 H1 H2.
  destruct (pstep_fstep H1) as [Hs1 _].
  destruct (pstep_fstep H2) as [Hs2 _].
  exact (fstep_forward_deterministic Hs1 Hs2).
Qed.

(* Backward determinism.  The counterexample of
   [fstep_not_backward_deterministic] mixes positions of two different
   programs and is therefore not a counterexample here. *)
Theorem pstep_backward_deterministic :
  forall F, wf_flow F ->
    forall cfg1 cfg2 cfg,
      pstep F cfg1 cfg -> pstep F cfg2 cfg -> cfg1 = cfg2.
Proof.
  intros F Hwf [cf1 s1] [cf2 s2] cfg H1 H2.
  destruct (pstep_fstep H1) as [Hs1 Hp1]; simpl in Hp1.
  destruct (pstep_fstep H2) as [Hs2 Hp2]; simpl in Hp2.
  eapply fstep_backward_deterministic_pos; eauto.
Qed.

(* Bridging with the remaining-flowchart presentation. *)
Lemma psteps_fsteps :
  forall F cfg cfg', psteps F cfg cfg' -> fsteps cfg cfg'.
Proof.
  intros F cfg cfg' H. induction H as [|cfg1 cfg2 cfg3 Hstep _ IH].
  - apply fsteps_refl.
  - destruct (pstep_fstep Hstep) as [Hs _].
    eapply fsteps_cons; eassumption.
Qed.

Lemma fsteps_psteps :
  forall F cfg cfg',
    posf F (fst cfg) -> fsteps cfg cfg' -> psteps F cfg cfg'.
Proof.
  intros F cfg cfg' Hp H. revert Hp.
  induction H as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps IH]; intros Hp.
  - apply psteps_refl.
  - destruct cfg1 as [cf1 s1]; destruct cfg2 as [cf2 s2]; simpl in Hp.
    eapply psteps_cons.
    + apply P_step; eassumption.
    + apply IH. simpl. exact (posf_step_preserved Hp Hstep).
Qed.

(* Well-formedness transfers from commands to flowcharts. *)
Lemma wf_flow_translate :
  forall c R, wf_cmd c -> wf_flow R -> wf_flow (translate c R).
Proof.
  induction c as [x e | c1 IH1 c2 IH2 | x cb IH y]; intros R Hc HR;
    inversion Hc; subst; simpl.
  - constructor; assumption.
  - apply IH1; [assumption | apply IH2; assumption].
  - constructor; [apply IH; [assumption | constructor] | assumption].
Qed.

(* Semantic equivalence in the paper's reading: a terminating big-step
   run of [c] is a traversal of its flowchart from entry to exit. *)
Theorem ds_iff_pfss :
  forall c s s',
    exec_ds c s s' <->
    psteps (translate c F_nil)
           (pentry (translate c F_nil), s) (pexit, s').
Proof.
  intros c s s'. unfold pentry, pexit. split.
  - intros H. apply fsteps_psteps; simpl;
      [apply posf_pentry | apply ds_implies_fss, H].
  - intros H. apply fss_implies_ds, (psteps_fsteps H).
Qed.

(* For a well-formed command, the traversal is deterministic in both
   directions. *)
Corollary pstep_deterministic_wf :
  forall c, wf_cmd c ->
    (forall cfg cfg1 cfg2,
       pstep (translate c F_nil) cfg cfg1 ->
       pstep (translate c F_nil) cfg cfg2 -> cfg1 = cfg2) /\
    (forall cfg1 cfg2 cfg,
       pstep (translate c F_nil) cfg1 cfg ->
       pstep (translate c F_nil) cfg2 cfg -> cfg1 = cfg2).
Proof.
  intros c Hwf. split.
  - intros; eapply pstep_forward_deterministic; eassumption.
  - apply pstep_backward_deterministic, wf_flow_translate;
      [assumption | constructor].
Qed.

(* Letter:Thm 3 (Semantic equivalence), in the paper's
   reading of fss: one name for
     <C,s> ⇓ s'  iff  (•C,s) →* (C•,s')  iff  (•F,s) →* (F•,s'). *)
Theorem semantic_equivalence_p :
  forall c s s',
    (exec_ds c s s' <->
       exec_ss_star (CC_at_pre c, s) (CC_at_post c, s')) /\
    (exec_ds c s s' <->
       psteps (translate c F_nil)
              (pentry (translate c F_nil), s) (pexit, s')).
Proof.
  intros c s s'. split.
  - apply semantic_equivalence_ds_ss.
  - apply ds_iff_pfss.
Qed.

Print Assumptions pstep_forward_deterministic.
Print Assumptions pstep_backward_deterministic.
Print Assumptions ds_iff_pfss.
Print Assumptions pstep_deterministic_wf.

(* ================================================================= *)
(* 40. Program level: the token traverses the flowchart from entry    *)
(*     to exit                                                        *)
(*                                                                    *)
(*  Theorem 1 of the paper is stated for a whole program              *)
(*  [read X; C; write X]: the ds semantics of the program is defined  *)
(*  on the input datum iff the control token traverses the underlying *)
(*  reversible flowchart from entry to exit.  The program-level token *)
(*  is [ctrl_flow_prog] (Sect. 19) and its transitions are [fpstep]   *)
(*  (Sect. 20): [FP_Begin] performs the read, [FP_Body] traverses the *)
(*  chart, [FP_End] performs the write.  The letter states its        *)
(*  results at the level of commands and stores; what follows is the  *)
(*  program-level reading, of which that is the engine.               *)
(* ================================================================= *)

Inductive fpsteps : ctrl_flow_prog * store -> ctrl_flow_prog * store -> Prop :=
  | fpsteps_refl : forall cfg, fpsteps cfg cfg
  | fpsteps_cons : forall cfg1 cfg2 cfg3,
      fpstep cfg1 cfg2 -> fpsteps cfg2 cfg3 -> fpsteps cfg1 cfg3.

Lemma no_fpstep_from_post_write :
  forall x s cfg, ~ fpstep (CFP_post_write x, s) cfg.
Proof. intros x s cfg H. inversion H. Qed.

Lemma fpsteps_body_inv_gen :
  forall a b, fpsteps a b ->
    forall x cc s s'',
      a = (CFP_in_body x cc, s) -> b = (CFP_post_write x, s'') ->
      fsteps (cc, s) (CF_pre F_nil, s'').
Proof.
  intros a b H.
  induction H as [cfg | cfg1 cfg2 cfg3 Hstep Hsteps IH];
    intros x cc s s'' Ea Eb.
  - subst. discriminate.
  - subst cfg1.
    inversion Hstep; subst.
    + (* FP_Body *)
      eapply fsteps_cons; [eassumption | eapply IH; reflexivity].
    + (* FP_End *)
      inversion Hsteps; subst.
      * apply fsteps_refl.
      * exfalso.
        match goal with
        | [ Hbad : fpstep (CFP_post_write _, _) _ |- _ ] =>
            eapply no_fpstep_from_post_write; exact Hbad
        end.
Qed.

Lemma fpsteps_trans :
  forall cfg1 cfg2 cfg3,
    fpsteps cfg1 cfg2 -> fpsteps cfg2 cfg3 -> fpsteps cfg1 cfg3.
Proof.
  intros cfg1 cfg2 cfg3 H1 H2. induction H1 as [|a b c Hs _ IH].
  - exact H2.
  - eapply fpsteps_cons; [exact Hs | apply IH; exact H2].
Qed.

Lemma fsteps_in_body :
  forall x cc s cc' s',
    fsteps (cc, s) (cc', s') ->
    fpsteps (CFP_in_body x cc, s) (CFP_in_body x cc', s').
Proof.
  intros x cc s cc' s' H.
  remember (cc, s) as a eqn:Ea; remember (cc', s') as b eqn:Eb.
  revert cc s cc' s' Ea Eb.
  induction H as [cfg | cfg1 cfg2 cfg3 Hstep Hsteps IH];
    intros cc s cc' s' Ea Eb; subst.
  - injection Eb as -> ->. apply fpsteps_refl.
  - destruct cfg2 as [cc2 s2].
    eapply fpsteps_cons.
    + apply FP_Body. exact Hstep.
    + apply IH; reflexivity.
Qed.

Lemma fpsteps_prog_inv :
  forall x F s s'',
    fpsteps (CFP_pre_read x F, s) (CFP_post_write x, s'') ->
    fsteps (CF_pre F, s) (CF_pre F_nil, s'').
Proof.
  intros x F s s'' H.
  inversion H; subst.
  match goal with
  | [ Hstep : fpstep (CFP_pre_read _ _, _) _,
      Hsteps : fpsteps _ _ |- _ ] =>
      inversion Hstep; subst;
      eapply fpsteps_body_inv_gen; [exact Hsteps | reflexivity | reflexivity]
  end.
Qed.

Theorem prog_traversal :
  forall x c s s',
    exec_ds c s s' <->
    fpsteps (CFP_pre_read x (translate c F_nil), s) (CFP_post_write x, s').
Proof.
  intros x c s s'. split.
  - intros H.
    eapply fpsteps_cons; [apply FP_Begin |].
    eapply fpsteps_trans.
    + apply fsteps_in_body, ds_implies_fss, H.
    + eapply fpsteps_cons; [apply FP_End | apply fpsteps_refl].
  - intros H. apply fss_implies_ds. eapply fpsteps_prog_inv. exact H.
Qed.

Definition init_store (x : var) (d : val) : store :=
  update (Vector.const Vnil 10) x d.

Corollary prog_traversal_data :
  forall x c d e,
    exec_ds c (init_store x d) (init_store x e) <->
    fpsteps (CFP_pre_read x (translate c F_nil), init_store x d)
            (CFP_post_write x, init_store x e).
Proof. intros. apply prog_traversal. Qed.

(* The data-level form of injectivity (2): [read X; C; write X] denotes
   a partial injective map on data, not just on stores.  This is
   [ds_injective] read off at the single variable [x] that [init_store]
   sets, the r-Turing-complete input/output view of \S 2. *)
Corollary prog_data_injective :
  forall x c d1 d2 e,
    wf_cmd c ->
    exec_ds c (init_store x d1) (init_store x e) ->
    exec_ds c (init_store x d2) (init_store x e) ->
    d1 = d2.
Proof.
  intros x c d1 d2 e Hwf H1 H2.
  assert (E : init_store x d1 = init_store x d2) by (eapply ds_injective; eauto).
  assert (Ed : init_store x d1 x = init_store x d2 x) by (rewrite E; reflexivity).
  unfold init_store in Ed. rewrite !update_eq in Ed. exact Ed.
Qed.

Print Assumptions prog_traversal.
Print Assumptions prog_traversal_data.
Print Assumptions prog_data_injective.

(* ================================================================= *)
(* 41. Divergences from the printed rules of RC 2026                  *)
(*                                                                    *)
(*  Part A: the gap in the printed assignment rules.                  *)
(*  Part B: the loop guards test equality with [t] and [f].           *)
(*  Part C: the structural congruence, recovered as token movements.  *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* 41A. The gap in the printed small-step assignment rules            *)
(*                                                                    *)
(*  The companion paper prints TWO small-step assignment rules:       *)
(*  AsnSet_ss, with the premise [e <> nil] on the value of the        *)
(*  right-hand side, and AsnClear_ss, with the premise [d <> nil] on  *)
(*  the current value of the target (Fig. 9b, p. 211 of LNCS 16626).  *)
(*  Neither fires when the target and the value of the right-hand     *)
(*  side are both [nil].  The denotational rule Asn_ds carries the    *)
(*  side condition [d = nil \/ (d = E[[E]]s /\ d <> nil)]             *)
(*  (Fig. 2c, p. 204), whose LEFT disjunct is satisfied in exactly    *)
(*  that case, and AsnClear_fss carries no [d <> nil] premise at all  *)
(*  (Fig. 11a, p. 214).  So there is a well-formed assignment that    *)
(*  ds denotes and fss traverses, and from which the printed          *)
(*  small-step rules cannot move: Theorem 1 of the paper              *)
(*  (ds <-> ss <-> fss) fails as printed.  The defect is localized    *)
(*  to AsnClear_ss, whose fss counterpart lacks the guard.            *)
(*  Rule references are to the published proceedings, Springer LNCS   *)
(*  16626, doi:10.1007/978-3-032-30839-9_12, pp. 201-218.             *)
(*                                                                    *)
(*  [exec_ss] above merges the two rules into [S_Asn], whose only     *)
(*  premises are the [eval_expr] and [odot] equations, and that       *)
(*  closes the gap; [semantic_equivalence_p] is proved for the        *)
(*  merged rule.  This section transcribes the printed rules under    *)
(*  the name [ss_paper_asn] and exhibits the counterexample, so that  *)
(*  the claim made in Sect. 2 of the letter is machine-checked        *)
(*  rather than argued in prose.                                      *)
(* ================================================================= *)

(* The paper's two assignment rules, transcribed with their premises. *)
Inductive ss_paper_asn : cont_cmd * store -> cont_cmd * store -> Prop :=
  | P_AsnSet   : forall x e s v_e,
      eval_expr s e = Some v_e ->
      v_e <> Vnil ->                    (* the paper's [e <> nil] *)
      s x = Vnil ->
      ss_paper_asn (CC_at_pre (Cass x e), s)
                   (CC_at_post (Cass x e), update s x v_e)
  | P_AsnClear : forall x e s v_e,
      eval_expr s e = Some v_e ->
      s x <> Vnil ->                    (* the paper's [d <> nil] *)
      s x = v_e ->
      ss_paper_asn (CC_at_pre (Cass x e), s)
                   (CC_at_post (Cass x e), update s x Vnil).

(* Only an assignment rule can apply to [•(x ^= e)]: every other
   constructor of [exec_ss] has a differently shaped source.  Hence
   showing that both printed assignment rules are blocked shows that
   the printed small-step relation as a whole is stuck there. *)
Lemma exec_ss_from_pre_asn_inv : forall x e s t,
    exec_ss (CC_at_pre (Cass x e), s) t ->
    exists v_e v_new,
      eval_expr s e = Some v_e /\
      odot (s x) v_e = Some v_new /\
      t = (CC_at_post (Cass x e), update s x v_new).
Proof. intros x e s t H; inversion H; subst; eauto. Qed.

Definition nil_store : store := Vector.const Vnil 10.

(* Witness 1: [X0 ^= nil] evaluated in the all-nil store. *)
Example gap_witness_wf : wf_cmd (X0 ^= Enil).
Proof. apply wf_Cass, nf_Enil. Qed.

Example gap_witness_ds : exec_ds (X0 ^= Enil) nil_store nil_store.
Proof.
  replace nil_store with (update nil_store X0 Vnil) at 2 by reflexivity.
  apply D_Asn with (v_e := Vnil); reflexivity.
Qed.

Example gap_witness_ss :
  exec_ss (CC_at_pre (X0 ^= Enil), nil_store)
          (CC_at_post (X0 ^= Enil), nil_store).
Proof.
  replace nil_store with (update nil_store X0 Vnil) at 2 by reflexivity.
  apply S_Asn with (v_e := Vnil); reflexivity.
Qed.

Example gap_witness_paper_stuck :
  forall t, ~ ss_paper_asn (CC_at_pre (X0 ^= Enil), nil_store) t.
Proof. intros t H; inversion H; subst; simpl in *; congruence. Qed.

(* Witness 2: the same trap with an equality test, [X0 ^= =? X1 X2]
   in a store where [X1] and [X2] differ, so the test yields [nil].
   This is why the gap is a common case and not a marginal one. *)
Definition neq_store : store := update nil_store X2 (Vpair Vnil Vnil).

Example gap_witness2_wf : wf_cmd (X0 ^= Eeq X1 X2).
Proof. apply wf_Cass, nf_Eeq; discriminate. Qed.

Example gap_witness2_ds : exec_ds (X0 ^= Eeq X1 X2) neq_store neq_store.
Proof.
  replace neq_store with (update neq_store X0 Vnil) at 2 by reflexivity.
  apply D_Asn with (v_e := Vnil); reflexivity.
Qed.

Example gap_witness2_paper_stuck :
  forall t, ~ ss_paper_asn (CC_at_pre (X0 ^= Eeq X1 X2), neq_store) t.
Proof. intros t H; inversion H; subst; simpl in *; congruence. Qed.

(* Theorem 1 of RC 2026, read literally, is false. *)
Theorem rc2026_theorem1_fails_as_printed :
  exists c s,
    wf_cmd c /\
    exec_ds c s s /\
    (forall t, ~ ss_paper_asn (CC_at_pre c, s) t) /\
    exec_ss (CC_at_pre c, s) (CC_at_post c, s).
Proof.
  exists (X0 ^= Enil), nil_store.
  repeat split;
    auto using gap_witness_wf, gap_witness_ds,
               gap_witness_paper_stuck, gap_witness_ss.
Qed.

Print Assumptions exec_ss_from_pre_asn_inv.
Print Assumptions rc2026_theorem1_fails_as_printed.


(* ----------------------------------------------------------------- *)
(* 41B. The loop guards                                               *)
(*                                                                    *)
(*  The printed loop rules (Fig. 9b, p. 211) test equality with [t]   *)
(*  and [f], where [f] abbreviates [nil] and [t] abbreviates          *)
(*  [(nil.nil)] (p. 204).  Since the data domain is all binary trees  *)
(*  over [nil], a variable can hold a value that is neither, and on   *)
(*  such a value the printed rules are stuck.  Our guards test only   *)
(*  whether a variable is [nil], so they agree with the printed ones  *)
(*  on [t] and [f] and additionally cover the remaining values.       *)
(*  The witness store is not contrived: a two-line well-formed        *)
(*  R-CORE program reaches it from the all-nil store.                 *)
(* ----------------------------------------------------------------- *)

Definition Vt : val := Vpair Vnil Vnil.  (* the paper's [t]; [f] is [Vnil] *)

(* The printed loop rules, transcribed with their [t]/[f] guards. *)
Inductive ss_paper_loop : cont_cmd * store -> cont_cmd * store -> Prop :=
  | P_LoopEnter : forall x c y s,
      s x = Vt ->
      ss_paper_loop (CC_at_pre (Cloop x c y), s) (CC_mid_loop x c y, s)
  | P_LoopExit  : forall x c y s,
      s y = Vt ->
      ss_paper_loop (CC_mid_loop x c y, s) (CC_at_post (Cloop x c y), s)
  | P_LoopIter1 : forall x c y s,
      s y = Vnil ->
      ss_paper_loop (CC_mid_loop x c y, s) (CC_in_loop x (CC_at_pre c) y, s)
  | P_LoopIter2 : forall x c y s,
      s x = Vnil ->
      ss_paper_loop (CC_in_loop x (CC_at_post c) y, s) (CC_mid_loop x c y, s).

(* [X0] holds [((nil.nil).nil)], which is neither [t] nor [f]. *)
Definition odd_store : store :=
  update (update nil_store X1 Vt) X0 (Vpair Vt Vnil).

Example odd_store_wf : wf_cmd (X1 ^= Eeq X2 X3 ; X0 ^= Econs X1 X4).
Proof.
  apply wf_Cseq; apply wf_Cass;
    [apply nf_Eeq | apply nf_Econs]; discriminate.
Qed.

Example odd_store_reachable :
  exec_ds (X1 ^= Eeq X2 X3 ; X0 ^= Econs X1 X4) nil_store odd_store.
Proof.
  eapply D_Seq.
  - apply D_Asn with (v_e := Vt); reflexivity.
  - apply D_Asn with (v_e := Vpair Vt Vnil); reflexivity.
Qed.

Example loop_gap_ss : forall c,
  exec_ss (CC_at_pre (Cloop X0 c X1), odd_store)
          (CC_mid_loop X0 c X1, odd_store).
Proof. intro c; apply S_LoopEnter; discriminate. Qed.

Example loop_gap_paper_stuck : forall c t,
  ~ ss_paper_loop (CC_at_pre (Cloop X0 c X1), odd_store) t.
Proof. intros c t H; inversion H; subst; discriminate. Qed.

Theorem rc2026_loop_guards_are_stricter :
  exists x c y s,
    (forall t, ~ ss_paper_loop (CC_at_pre (Cloop x c y), s) t) /\
    exec_ss (CC_at_pre (Cloop x c y), s) (CC_mid_loop x c y, s).
Proof.
  exists X0, (X5 ^= Enil), X1, odd_store.
  split; [apply loop_gap_paper_stuck | apply loop_gap_ss].
Qed.

Print Assumptions rc2026_loop_guards_are_stricter.

(* ----------------------------------------------------------------- *)
(* 41B'. The printed small-step relation as a whole                   *)
(*                                                                    *)
(*  [ss_paper_asn] alone shows that the two printed ASSIGNMENT rules  *)
(*  are blocked.  To conclude that the printed semantics is stuck we  *)
(*  need the whole relation, so we assemble it here: the assignment   *)
(*  rules, the loop rules, and the closure under evaluation contexts. *)
(*  There are deliberately no rules for [;]: the paper moves the      *)
(*  token across [;] with the structural congruence of Eq. (7), not   *)
(*  with transitions, and the witness below contains no [;] anyway,   *)
(*  so the congruence relates it only to itself.                      *)
(* ----------------------------------------------------------------- *)

Inductive ss_paper : cont_cmd * store -> cont_cmd * store -> Prop :=
  | SP_asn    : forall a b, ss_paper_asn a b -> ss_paper a b
  | SP_loop   : forall a b, ss_paper_loop a b -> ss_paper a b
  | SP_ctx_L  : forall cc cc' c2 s s',
      ss_paper (cc, s) (cc', s') ->
      ss_paper (CC_seq_L cc c2, s) (CC_seq_L cc' c2, s')
  | SP_ctx_R  : forall c1 cc cc' s s',
      ss_paper (cc, s) (cc', s') ->
      ss_paper (CC_seq_R c1 cc, s) (CC_seq_R c1 cc', s')
  | SP_ctx_lp : forall x cc cc' y s s',
      ss_paper (cc, s) (cc', s') ->
      ss_paper (CC_in_loop x cc y, s) (CC_in_loop x cc' y, s').

(* The witnesses of 41A are stuck in the printed relation as a whole,
   not merely in its assignment fragment. *)
Example gap_witness_paper_ss_stuck :
  forall t, ~ ss_paper (CC_at_pre (X0 ^= Enil), nil_store) t.
Proof.
  intros t H; inversion H; subst.
  - eapply gap_witness_paper_stuck; eauto.
  - match goal with Hl : ss_paper_loop _ _ |- _ => inversion Hl end.
Qed.

Example gap_witness2_paper_ss_stuck :
  forall t, ~ ss_paper (CC_at_pre (X0 ^= Eeq X1 X2), neq_store) t.
Proof.
  intros t H; inversion H; subst.
  - eapply gap_witness2_paper_stuck; eauto.
  - match goal with Hl : ss_paper_loop _ _ |- _ => inversion Hl end.
Qed.

(* The strengthened statement: ds denotes the command, the printed
   small-step relation cannot move at all, and the repaired relation
   makes exactly the step that closes the gap. *)
Theorem rc2026_theorem1_fails_as_printed_full :
  exists c s,
    wf_cmd c /\
    exec_ds c s s /\
    (forall t, ~ ss_paper (CC_at_pre c, s) t) /\
    exec_ss (CC_at_pre c, s) (CC_at_post c, s).
Proof.
  exists (X0 ^= Enil), nil_store.
  repeat split;
    auto using gap_witness_wf, gap_witness_ds,
               gap_witness_paper_ss_stuck, gap_witness_ss.
Qed.

Print Assumptions gap_witness_paper_ss_stuck.
Print Assumptions rc2026_theorem1_fails_as_printed_full.

(* ----------------------------------------------------------------- *)
(* 41B'. The printed fss assignment rules (Fig. 11a)                  *)
(*                                                                    *)
(*  The gap is diagnosed by comparing three printed rule sets, so the *)
(*  fss side is transcribed too.  Fig. 11a prints                     *)
(*                                                                    *)
(*     (E,s) -> (e,(E,s))       e <> nil                              *)
(*    ---------------------------------------------- (AsnSet_fss)     *)
(*     (Efss[.(X ^= E)], s + {X -> nil})                              *)
(*         -> (Efss[(X ^= E).], s + {X -> e})                         *)
(*                                                                    *)
(*     (E,s) -> (d,(E,s))                                             *)
(*    ---------------------------------------------- (AsnClear_fss)   *)
(*     (Efss[.(X ^= E)], s + {X -> d})                                *)
(*         -> (Efss[(X ^= E).], s + {X -> nil})                       *)
(*                                                                    *)
(*  AsnClear_fss carries no [d <> nil] premise, where AsnClear_ss of  *)
(*  Fig. 9b does.  That single asymmetry is what confines the defect  *)
(*  to the ss side, and it is the reason the printed fss traverses    *)
(*  the witnesses on which the printed ss cannot move at all.         *)
(*                                                                    *)
(*  Two readings are inherited from [ss_paper_asn] and are ours, not  *)
(*  the paper's: [E] is evaluated in the full store (the paper writes *)
(*  s + {X -> d} and evaluates in s), and the token positions are     *)
(*  encoded by [CF_pre].  On the well-formed witnesses below the two  *)
(*  evaluation readings agree, X being absent from E.                 *)
(* ----------------------------------------------------------------- *)

Inductive fstep_paper_asn : ctrl_flow * store -> ctrl_flow * store -> Prop :=
  | PF_AsnSet   : forall x e F s v_e,
      eval_expr s e = Some v_e ->
      v_e <> Vnil ->                    (* the paper's [e <> nil] *)
      s x = Vnil ->
      fstep_paper_asn (CF_pre (F_step x e F), s)
                      (CF_pre F, update s x v_e)
  | PF_AsnClear : forall x e F s d,
      eval_expr s e = Some d ->
      s x = d ->                        (* Fig. 11a prints no [d <> nil] *)
      fstep_paper_asn (CF_pre (F_step x e F), s)
                      (CF_pre F, update s x Vnil).

(* Witness 1 moves in the printed fss.  [X0 ^= nil] translates to a
   single step node, so reaching [CF_pre F_nil] is its whole traversal. *)
Example gap_witness_paper_fss_moves :
  fstep_paper_asn (CF_pre (translate (X0 ^= Enil) F_nil), nil_store)
                  (CF_pre F_nil, nil_store).
Proof.
  simpl.
  replace nil_store with (update nil_store X0 Vnil) at 2 by reflexivity.
  apply PF_AsnClear with (d := Vnil); reflexivity.
Qed.

(* Witness 2 likewise, the equality-test case. *)
Example gap_witness2_paper_fss_moves :
  fstep_paper_asn (CF_pre (translate (X0 ^= Eeq X1 X2) F_nil), neq_store)
                  (CF_pre F_nil, neq_store).
Proof.
  simpl.
  replace neq_store with (update neq_store X0 Vnil) at 2 by reflexivity.
  apply PF_AsnClear with (d := Vnil); reflexivity.
Qed.

(* The diagnosis, on one witness and in one statement: ds denotes the
   command, the printed ss admits no step at all, and the printed fss
   traverses it.  So the three printed semantics cannot be equivalent,
   and the one that stands apart is ss.  What is NOT mechanized, here
   as for [ss_paper], is that these inductive types reproduce the
   printed figures; that reading remains ours. *)
Theorem rc2026_printed_fss_moves_where_ss_is_stuck :
  exists c s,
    wf_cmd c /\
    exec_ds c s s /\
    (forall t, ~ ss_paper (CC_at_pre c, s) t) /\
    fstep_paper_asn (CF_pre (translate c F_nil), s) (CF_pre F_nil, s).
Proof.
  exists (X0 ^= Enil), nil_store.
  repeat split;
    auto using gap_witness_wf, gap_witness_ds,
               gap_witness_paper_ss_stuck, gap_witness_paper_fss_moves.
Qed.

Print Assumptions gap_witness_paper_fss_moves.
Print Assumptions gap_witness2_paper_fss_moves.
Print Assumptions rc2026_printed_fss_moves_where_ss_is_stuck.

(* ----------------------------------------------------------------- *)
(* 41C. The structural congruence                                     *)
(*                                                                    *)
(*  The paper reads [->] modulo the structural congruence of Eq. (7), *)
(*  p. 210, which moves the token across [;].  We do NOT quotient:    *)
(*  every member of a congruence class is a distinct [cont_cmd] and   *)
(*  the three equations are oriented as the transitions               *)
(*  [S_Seq_Enter], [S_Seq_Mid] and [S_Seq_Exit].  [cong_iff_admin]    *)
(*  shows the congruence is recovered exactly as the equivalence      *)
(*  closure of those transitions, so nothing is lost: the determinism *)
(*  results are stated with syntactic equality on a finer relation,   *)
(*  and one printed step becomes one of ours bracketed by token       *)
(*  movements.                                                        *)
(* ----------------------------------------------------------------- *)

(* The paper's structural congruence, Eq. (7). *)
Inductive cc_cong : cont_cmd -> cont_cmd -> Prop :=
  | CG_enter  : forall c1 c2,
      cc_cong (CC_at_pre (Cseq c1 c2)) (CC_seq_L (CC_at_pre c1) c2)
  | CG_mid    : forall c1 c2,
      cc_cong (CC_seq_L (CC_at_post c1) c2) (CC_seq_R c1 (CC_at_pre c2))
  | CG_exit   : forall c1 c2,
      cc_cong (CC_seq_R c1 (CC_at_post c2)) (CC_at_post (Cseq c1 c2))
  | CG_ctx_L  : forall cc cc' c2,
      cc_cong cc cc' -> cc_cong (CC_seq_L cc c2) (CC_seq_L cc' c2)
  | CG_ctx_R  : forall c1 cc cc',
      cc_cong cc cc' -> cc_cong (CC_seq_R c1 cc) (CC_seq_R c1 cc')
  | CG_ctx_lp : forall x cc cc' y,
      cc_cong cc cc' -> cc_cong (CC_in_loop x cc y) (CC_in_loop x cc' y)
  | CG_refl   : forall cc, cc_cong cc cc
  | CG_sym    : forall cc1 cc2, cc_cong cc1 cc2 -> cc_cong cc2 cc1
  | CG_trans  : forall cc1 cc2 cc3,
      cc_cong cc1 cc2 -> cc_cong cc2 cc3 -> cc_cong cc1 cc3.

(* The token movements of [exec_ss], as a relation on control alone. *)
Inductive admin_step : cont_cmd -> cont_cmd -> Prop :=
  | A_enter  : forall c1 c2,
      admin_step (CC_at_pre (Cseq c1 c2)) (CC_seq_L (CC_at_pre c1) c2)
  | A_mid    : forall c1 c2,
      admin_step (CC_seq_L (CC_at_post c1) c2) (CC_seq_R c1 (CC_at_pre c2))
  | A_exit   : forall c1 c2,
      admin_step (CC_seq_R c1 (CC_at_post c2)) (CC_at_post (Cseq c1 c2))
  | A_ctx_L  : forall cc cc' c2,
      admin_step cc cc' -> admin_step (CC_seq_L cc c2) (CC_seq_L cc' c2)
  | A_ctx_R  : forall c1 cc cc',
      admin_step cc cc' -> admin_step (CC_seq_R c1 cc) (CC_seq_R c1 cc')
  | A_ctx_lp : forall x cc cc' y,
      admin_step cc cc' -> admin_step (CC_in_loop x cc y) (CC_in_loop x cc' y).

(* Every token movement really is a step of our semantics, and it
   leaves the store untouched. *)
Lemma admin_step_is_ss : forall cc cc' s,
    admin_step cc cc' -> exec_ss (cc, s) (cc', s).
Proof.
  intros cc cc' s H; induction H;
    eauto using S_Seq_Enter, S_Seq_Mid, S_Seq_Exit,
                S_Ctx_Seq_L, S_Ctx_Seq_R, S_Ctx_Loop.
Qed.

Inductive admin_eq : cont_cmd -> cont_cmd -> Prop :=
  | AE_step  : forall cc cc', admin_step cc cc' -> admin_eq cc cc'
  | AE_refl  : forall cc, admin_eq cc cc
  | AE_sym   : forall cc1 cc2, admin_eq cc1 cc2 -> admin_eq cc2 cc1
  | AE_trans : forall cc1 cc2 cc3,
      admin_eq cc1 cc2 -> admin_eq cc2 cc3 -> admin_eq cc1 cc3.

Lemma admin_eq_ctx_L : forall cc cc' c2,
    admin_eq cc cc' -> admin_eq (CC_seq_L cc c2) (CC_seq_L cc' c2).
Proof. intros cc cc' c2 H; induction H; eauto using admin_eq, A_ctx_L. Qed.

Lemma admin_eq_ctx_R : forall c1 cc cc',
    admin_eq cc cc' -> admin_eq (CC_seq_R c1 cc) (CC_seq_R c1 cc').
Proof. intros c1 cc cc' H; induction H; eauto using admin_eq, A_ctx_R. Qed.

Lemma admin_eq_ctx_lp : forall x cc cc' y,
    admin_eq cc cc' -> admin_eq (CC_in_loop x cc y) (CC_in_loop x cc' y).
Proof. intros x cc cc' y H; induction H; eauto using admin_eq, A_ctx_lp. Qed.

Lemma admin_step_cong : forall cc cc',
    admin_step cc cc' -> cc_cong cc cc'.
Proof. intros cc cc' H; induction H; eauto using cc_cong. Qed.

Theorem cong_iff_admin : forall cc1 cc2,
    cc_cong cc1 cc2 <-> admin_eq cc1 cc2.
Proof.
  intros cc1 cc2; split; intro H; induction H;
    eauto using admin_eq, admin_step, cc_cong,
                admin_eq_ctx_L, admin_eq_ctx_R, admin_eq_ctx_lp,
                admin_step_cong.
Qed.

(* The congruence only moves the token: it never changes the program.
   Hence well-formedness, the side condition of backward determinism,
   is a property of the congruence class and not of the representative. *)
Fixpoint cc_erase (cc : cont_cmd) : cmd :=
  match cc with
  | CC_at_pre c       => c
  | CC_at_post c      => c
  | CC_mid_loop x c y => Cloop x c y
  | CC_seq_L cc c2    => Cseq (cc_erase cc) c2
  | CC_seq_R c1 cc    => Cseq c1 (cc_erase cc)
  | CC_in_loop x cc y => Cloop x (cc_erase cc) y
  end.

Theorem cc_cong_erase : forall cc1 cc2,
    cc_cong cc1 cc2 -> cc_erase cc1 = cc_erase cc2.
Proof. intros cc1 cc2 H; induction H; simpl; congruence. Qed.

Lemma wf_cc_iff_erase : forall cc, wf_cc cc <-> wf_cmd (cc_erase cc).
Proof.
  induction cc; simpl; split; intro H; inversion H; subst;
    eauto using wf_cc, wf_cmd;
    try (apply wf_Cseq; tauto);
    try (apply wf_seq_L; tauto);
    try (apply wf_seq_R; tauto);
    try (apply wf_Cloop; tauto);
    try (apply wf_in_lp; tauto).
Qed.

Theorem cc_cong_preserves_wf : forall cc1 cc2,
    cc_cong cc1 cc2 -> (wf_cc cc1 <-> wf_cc cc2).
Proof.
  intros cc1 cc2 H.
  rewrite (wf_cc_iff_erase cc1), (wf_cc_iff_erase cc2),
          (cc_cong_erase H).
  reflexivity.
Qed.

Print Assumptions admin_step_is_ss.
Print Assumptions cong_iff_admin.
Print Assumptions cc_cong_erase.
Print Assumptions cc_cong_preserves_wf.

(* ================================================================= *)
(* 42. Axiom audit: every top-level result, in one place            *)
(*                                                                    *)
(*  The per-section audits above document the results they follow;    *)
(*  this block checks EVERY top-level Theorem, Lemma, Corollary and   *)
(*  Example of the development, so the claim that the development is  *)
(*  axiom-free is reproducible in one run and cannot silently drift   *)
(*  as results are added.  Each line must print                       *)
(*  [Closed under the global context].  tools/audit.sh, run in CI,    *)
(*  checks that this list is complete and that every verdict is the   *)
(*  closed-world one.                                                 *)
(* ================================================================= *)

Print Assumptions update_eq.
Print Assumptions update_neq.
Print Assumptions odot_inv.
Print Assumptions odot_left_injective.
Print Assumptions update_injective_off_x.
Print Assumptions update_value_at_x.
Print Assumptions no_step_from_at_post.
Print Assumptions ss_step_deterministic.
Print Assumptions nf_expr_not_self.
Print Assumptions eval_expr_update_invariant.
Print Assumptions eval_expr_agree.
Print Assumptions store_ext.
Print Assumptions wf_cc_step_preserved.
Print Assumptions no_step_to_at_pre.
Print Assumptions ss_bwd_deterministic.
Print Assumptions rev_com_forward.
Print Assumptions rev_com_backward.
Print Assumptions exec_ss_star_trans.
Print Assumptions steps_lift.
Print Assumptions steps_ctx_seq_L.
Print Assumptions steps_ctx_seq_R.
Print Assumptions steps_ctx_loop.
Print Assumptions ds_implies_ss.
Print Assumptions steps_from_at_post.
Print Assumptions step_from_seq_L_shape.
Print Assumptions step_from_seq_R_shape.
Print Assumptions step_from_in_loop_shape.
Print Assumptions steps_from_seq_R_shape.
Print Assumptions factor_seq_R.
Print Assumptions factor_seq_L.
Print Assumptions steps_to_nsteps.
Print Assumptions nsteps_to_steps.
Print Assumptions nsteps_zero_eq.
Print Assumptions nsteps_split_last.
Print Assumptions nsteps_strong_ind.
Print Assumptions step_preserves_root.
Print Assumptions steps_preserves_root_cfg.
Print Assumptions steps_preserves_root.
Print Assumptions mid_loop_params_unique.
Print Assumptions factor_in_loop_via.
Print Assumptions factor_in_loop_first_exit.
Print Assumptions factor_in_loop_to_post.
Print Assumptions factor_loop_body.
Print Assumptions mid_loop_implies_loop_sem.
Print Assumptions ss_implies_ds.
Print Assumptions semantic_equivalence_ds_ss.
Print Assumptions fsteps_trans.
Print Assumptions fsteps_lift_loop.
Print Assumptions ss_step_implies_fss_steps_cfg.
Print Assumptions ss_step_implies_fss_steps.
Print Assumptions ss_steps_implies_fss_steps.
Print Assumptions ss_implies_fss.
Print Assumptions ds_implies_fss.
Print Assumptions fsteps_to_fnsteps.
Print Assumptions fnsteps_to_fsteps.
Print Assumptions fnsteps_zero_eq.
Print Assumptions sub_flow_trans.
Print Assumptions sub_flow_size.
Print Assumptions translate_grows.
Print Assumptions translate_neq_self.
Print Assumptions sub_flow_strict_size.
Print Assumptions sub_flow_antisym.
Print Assumptions fstep_outer_rest_sub.
Print Assumptions fnsteps_outer_rest_sub.
Print Assumptions fstep_pre_strict.
Print Assumptions fnsteps_pre_no_cycle.
Print Assumptions fnsteps_in_loop_to_pre.
Print Assumptions fnsteps_mid_implies_loop_sem.
Print Assumptions fnsteps_mid_split.
Print Assumptions fss_seq_factor.
Print Assumptions fss_complete_to_pre.
Print Assumptions fss_implies_ds.
Print Assumptions fss_implies_ss.
Print Assumptions semantic_equivalence_ss_fss.
Print Assumptions semantic_equivalence_ds_fss.
Print Assumptions semantic_equivalence.
Print Assumptions eval_cmd_fuel_test.
Print Assumptions eval_cmd_loop_sound.
Print Assumptions eval_cmd_sound.
Print Assumptions eval_loop_sound.
Print Assumptions eval_cmd_loop_mono.
Print Assumptions eval_cmd_fuel_mono.
Print Assumptions eval_loop_fuel_mono.
Print Assumptions eval_cmd_loop_complete.
Print Assumptions eval_cmd_complete.
Print Assumptions eval_loop_complete.
Print Assumptions eval_cmd_correct.
Print Assumptions inv_involutive.
Print Assumptions loop_sem_iff_iters.
Print Assumptions loop_iters_snoc.
Print Assumptions loop_iters_inv.
Print Assumptions loop_sem_inv.
Print Assumptions inv_correct.
Print Assumptions wf_cmd_inv.
Print Assumptions inv_correct_iff.
Print Assumptions inv_seq.
Print Assumptions inv_compose_id.
Print Assumptions inv_compose_id_sym.
Print Assumptions denot_eq_refl.
Print Assumptions denot_eq_sym.
Print Assumptions denot_eq_trans.
Print Assumptions loop_sem_compat.
Print Assumptions denot_eq_compat_seq_l.
Print Assumptions denot_eq_compat_seq_r.
Print Assumptions denot_eq_compat_loop.
Print Assumptions fa_soundness.
Print Assumptions fa_completeness.
Print Assumptions full_abstraction.
Print Assumptions denot_eqv_refl.
Print Assumptions denot_eqv_sym.
Print Assumptions denot_eqv_trans.
Print Assumptions denot_comp_id_l.
Print Assumptions denot_comp_id_r.
Print Assumptions denot_comp_assoc.
Print Assumptions denot_dagger_involutive.
Print Assumptions denot_dagger_id.
Print Assumptions denot_dagger_comp.
Print Assumptions cmd_denot_seq.
Print Assumptions cmd_denot_dagger.
Print Assumptions cmd_denot_eq_iff_eqv.
Print Assumptions cmd_denot_dagger_image.
Print Assumptions denot_dagger_proper.
Print Assumptions cmd_denot_inv_seq.
Print Assumptions wf_cc_step_reflected.
Print Assumptions ss_bwd_deterministic_tgt.
Print Assumptions fstep_nil_stuck.
Print Assumptions fstep_forward_deterministic.
Print Assumptions fstep_not_backward_deterministic.
Print Assumptions fstep_backward_store_deterministic_nf.
Print Assumptions wf_cf_nf_head.
Print Assumptions fstep_backward_store_deterministic.
Print Assumptions tailf_size.
Print Assumptions fchild_size.
Print Assumptions tailf_child_absurd.
Print Assumptions tailf_parent_unique.
Print Assumptions wf_flow_tail.
Print Assumptions posf_no_step_to_whole.
Print Assumptions fss_asn_asn_eq.
Print Assumptions fss_step_loop_absurd.
Print Assumptions fss_loop_loop_eq.
Print Assumptions wf_flow_loop_body.
Print Assumptions fstep_backward_deterministic_pos.
Print Assumptions tailf_child.
Print Assumptions posf_step_preserved.
Print Assumptions posf_steps_preserved.
Print Assumptions fstep_backward_deterministic_reachable.
Print Assumptions ss_run_unique_stuck.
Print Assumptions ss_run_unique.
Print Assumptions ss_run_state_unique.
Print Assumptions ss_run_prefix.
Print Assumptions ss_run_trace_unique.
Print Assumptions ds_deterministic.
Print Assumptions ds_injective.
Print Assumptions cmd_denot_partial_injective.
Print Assumptions wf_cc_steps_preserved.
Print Assumptions wf_cc_steps_reflected.
Print Assumptions ss_bwd_deterministic_reachable.
Print Assumptions ss_run_state_unique_bwd.
Print Assumptions ss_run_trace_unique_bwd.
Print Assumptions inv_unique.
Print Assumptions inv_unique_cxt.
Print Assumptions inv_correct_ss.
Print Assumptions inv_correct_ss_iff.
Print Assumptions inv_correct_fss.
Print Assumptions inv_correct_fss_iff.
Print Assumptions posf_pentry.
Print Assumptions pstep_fstep.
Print Assumptions pstep_forward_deterministic.
Print Assumptions pstep_backward_deterministic.
Print Assumptions psteps_fsteps.
Print Assumptions fsteps_psteps.
Print Assumptions wf_flow_translate.
Print Assumptions ds_iff_pfss.
Print Assumptions pstep_deterministic_wf.
Print Assumptions semantic_equivalence_p.
Print Assumptions no_fpstep_from_post_write.
Print Assumptions fpsteps_body_inv_gen.
Print Assumptions fpsteps_trans.
Print Assumptions fsteps_in_body.
Print Assumptions fpsteps_prog_inv.
Print Assumptions prog_traversal.
Print Assumptions prog_traversal_data.
Print Assumptions prog_data_injective.
Print Assumptions exec_ss_from_pre_asn_inv.
Print Assumptions gap_witness_wf.
Print Assumptions gap_witness_ds.
Print Assumptions gap_witness_ss.
Print Assumptions gap_witness_paper_stuck.
Print Assumptions gap_witness2_wf.
Print Assumptions gap_witness2_ds.
Print Assumptions gap_witness2_paper_stuck.
Print Assumptions rc2026_theorem1_fails_as_printed.
Print Assumptions odd_store_wf.
Print Assumptions odd_store_reachable.
Print Assumptions loop_gap_ss.
Print Assumptions loop_gap_paper_stuck.
Print Assumptions rc2026_loop_guards_are_stricter.
Print Assumptions gap_witness_paper_ss_stuck.
Print Assumptions gap_witness2_paper_ss_stuck.
Print Assumptions rc2026_theorem1_fails_as_printed_full.
Print Assumptions admin_step_is_ss.
Print Assumptions admin_eq_ctx_L.
Print Assumptions admin_eq_ctx_R.
Print Assumptions admin_eq_ctx_lp.
Print Assumptions admin_step_cong.
Print Assumptions cong_iff_admin.
Print Assumptions cc_cong_erase.
Print Assumptions wf_cc_iff_erase.
Print Assumptions cc_cong_preserves_wf.
