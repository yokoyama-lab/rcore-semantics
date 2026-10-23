(*
  janus/embed.v -- R-CORE's control-token semantics (../proofs.v) as an
  instance of the Janus control-token semantics (janus.v).

  R-CORE's [from x loop c until y] is Janus's [from x do skip loop c until y]
  (janus.v, Design).  The two languages differ in their data: R-CORE's
  values are binary trees with hd/tl/cons/=? and the partial update (+),
  Janus's are integers with arithmetic.  No integer encoding of trees makes
  hd and tl single Janus expressions under the usual pairings (they need a
  square root or a logarithm), so a step-for-step simulation through a
  value translation is not available.  This file states the embedding
  through the data layer instead:

    gstep act test     the rules of [jstep] for skip, x op= e, sequencing
                       and loops (rules 1-3, 8-14, 20-21, 24-25 of
                       RULES.md), with the premise of the assignment rule
                       ([act]) and the value of a guard ([test]) as
                       parameters.

    Theorem A          with Janus's [act]/[test] (eval, update, truth),
    [jstep_gstep_iff]  [gstep] is exactly [jstep] on the fragment: every
                       [jstep] from an embedded configuration is the image
                       of a [gstep], and conversely.

    Theorem B          with R-CORE's [act]/[test] (eval_expr, (+), "is
    [adm_step],        not nil"), [gstep] on the translated program is a
    [rcore_sim],       stuttering bisimulation of [exec_ss]: an R-CORE
    [rcore_embed_runs] step is one [gstep] followed by 0 or 3
                       administrative steps (3 after S_LoopEnter and
                       S_LoopIter2, which enter the from-point, run
                       [skip] and reach the until-point), every [gstep]
                       from a related configuration is either such an
                       administrative step or the image of an R-CORE step,
                       and runs between translated configurations are
                       exactly R-CORE runs.

  So the Janus rules restricted to R-CORE's constructs, with R-CORE's data
  in place of integers, are R-CORE's rules up to the three administrative
  steps of the empty do-part.  Axiom-free (audit at the end).
*)

From Stdlib Require Import ZArith List Lia.
From RCore Require proofs.
From RCore.janus Require janus.
Set Implicit Arguments.

(* ================================================================= *)
(* 1. The fragment with its data layer as a parameter                 *)
(* ================================================================= *)

Section Generic.
Variables (St A G : Type).
(* [act s a s']: the assignment [a] can run from s and yields s'. *)
Variable act : St -> A -> St -> Prop.
(* [test s g]: the truth value of the guard g in s, if it has one. *)
Variable test : St -> G -> option bool.

Inductive gstmt : Type :=
  | GSkip
  | GAsn  (a : A)
  | GSeq  (s1 s2 : gstmt)
  | GLoop (g1 : G) (s1 s2 : gstmt) (g2 : G).      (* from g1 do s1 loop s2 until g2 *)

Inductive gcs : Type :=
  | GC_pre        (st : gstmt)
  | GC_post       (st : gstmt)
  | GC_seq_L      (c : gcs) (s2 : gstmt)
  | GC_seq_R      (s1 : gstmt) (c : gcs)
  | GC_loop_from  (g1 : G) (s1 s2 : gstmt) (g2 : G)
  | GC_loop_do    (g1 : G) (c : gcs) (s2 : gstmt) (g2 : G)
  | GC_loop_until (g1 : G) (s1 s2 : gstmt) (g2 : G)
  | GC_loop_loop  (g1 : G) (s1 : gstmt) (c : gcs) (g2 : G).

(* The rules of jstep for these constructors, in the same order and with
   the same premises, except that J_Asn's premise is [act] and a guard's
   value is [test]. *)
Inductive gstep : gcs * St -> gcs * St -> Prop :=
  | G_Skip : forall s, gstep (GC_pre GSkip, s) (GC_post GSkip, s)
  | G_Asn : forall a s s', act s a s' -> gstep (GC_pre (GAsn a), s) (GC_post (GAsn a), s')
  | G_Seq_Enter : forall s1 s2 s, gstep (GC_pre (GSeq s1 s2), s) (GC_seq_L (GC_pre s1) s2, s)
  | G_Seq_Mid : forall s1 s2 s, gstep (GC_seq_L (GC_post s1) s2, s) (GC_seq_R s1 (GC_pre s2), s)
  | G_Seq_Exit : forall s1 s2 s, gstep (GC_seq_R s1 (GC_post s2), s) (GC_post (GSeq s1 s2), s)
  | G_Loop_Enter : forall g1 s1 s2 g2 s,
      test s g1 = Some true ->
      gstep (GC_pre (GLoop g1 s1 s2 g2), s) (GC_loop_from g1 s1 s2 g2, s)
  | G_Loop_Do : forall g1 s1 s2 g2 s,
      gstep (GC_loop_from g1 s1 s2 g2, s) (GC_loop_do g1 (GC_pre s1) s2 g2, s)
  | G_Loop_DoDone : forall g1 s1 s2 g2 s,
      gstep (GC_loop_do g1 (GC_post s1) s2 g2, s) (GC_loop_until g1 s1 s2 g2, s)
  | G_Loop_Exit : forall g1 s1 s2 g2 s,
      test s g2 = Some true ->
      gstep (GC_loop_until g1 s1 s2 g2, s) (GC_post (GLoop g1 s1 s2 g2), s)
  | G_Loop_Iter1 : forall g1 s1 s2 g2 s,
      test s g2 = Some false ->
      gstep (GC_loop_until g1 s1 s2 g2, s) (GC_loop_loop g1 s1 (GC_pre s2) g2, s)
  | G_Loop_Iter2 : forall g1 s1 s2 g2 s,
      test s g1 = Some false ->
      gstep (GC_loop_loop g1 s1 (GC_post s2) g2, s) (GC_loop_from g1 s1 s2 g2, s)
  | G_Ctx_Seq_L : forall c c' s2 s s',
      gstep (c, s) (c', s') -> gstep (GC_seq_L c s2, s) (GC_seq_L c' s2, s')
  | G_Ctx_Seq_R : forall s1 c c' s s',
      gstep (c, s) (c', s') -> gstep (GC_seq_R s1 c, s) (GC_seq_R s1 c', s')
  | G_Ctx_Loop_Do : forall g1 c c' s2 g2 s s',
      gstep (c, s) (c', s') -> gstep (GC_loop_do g1 c s2 g2, s) (GC_loop_do g1 c' s2 g2, s')
  | G_Ctx_Loop_Loop : forall g1 s1 c c' g2 s s',
      gstep (c, s) (c', s') -> gstep (GC_loop_loop g1 s1 c g2, s) (GC_loop_loop g1 s1 c' g2, s').

Inductive gnsteps : nat -> gcs * St -> gcs * St -> Prop :=
  | GN_refl : forall cfg, gnsteps 0 cfg cfg
  | GN_step : forall n cfg1 cfg2 cfg3,
      gstep cfg1 cfg2 -> gnsteps n cfg2 cfg3 -> gnsteps (Datatypes.S n) cfg1 cfg3.

Lemma gnsteps_trans :
  forall m n c1 c2 c3, gnsteps m c1 c2 -> gnsteps n c2 c3 -> gnsteps (m + n) c1 c3.
Proof.
  intros m n c1 c2 c3 H1; induction H1; intro H2; simpl; [exact H2 |].
  eapply GN_step; [exact H | apply IHgnsteps; exact H2].
Qed.

Lemma no_gstep_from_post : forall st s cfg, ~ gstep (GC_post st, s) cfg.
Proof. intros st s cfg H; inversion H. Qed.

(* gstep is deterministic as soon as the assignment premise is (the
   proof is that of jstep_deterministic). *)
Lemma gstep_deterministic :
  (forall s a s1 s2, act s a s1 -> act s a s2 -> s1 = s2) ->
  forall cfg cfg1 cfg2, gstep cfg cfg1 -> gstep cfg cfg2 -> cfg1 = cfg2.
Proof.
  intros Hact cfg cfg1 cfg2 H1; revert cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst; try reflexivity; try congruence;
    try (exfalso; eapply no_gstep_from_post; eassumption);
    try match goal with
        | [ Ha : act ?s ?a ?s1, Hb : act ?s ?a ?s2 |- _ ] =>
            rewrite (Hact _ _ _ _ Ha Hb); reflexivity
        | [ IH : forall cfg2, gstep _ cfg2 -> _ = cfg2, Hi : gstep _ _ |- _ ] =>
            let E := fresh "E" in
            pose proof (IH _ Hi) as E; injection E as ? ?; subst; reflexivity
        end.
Qed.

End Generic.

Arguments GSkip {A G}.
Arguments GAsn {A G} a.
Arguments GSeq {A G} s1 s2.
Arguments GLoop {A G} g1 s1 s2 g2.
Arguments GC_pre {A G} st.
Arguments GC_post {A G} st.
Arguments GC_seq_L {A G} c s2.
Arguments GC_seq_R {A G} s1 c.
Arguments GC_loop_from {A G} g1 s1 s2 g2.
Arguments GC_loop_do {A G} g1 c s2 g2.
Arguments GC_loop_until {A G} g1 s1 s2 g2.
Arguments GC_loop_loop {A G} g1 s1 c g2.

(* ================================================================= *)
(* 2. Theorem A: with Janus's data, gstep is jstep on the fragment    *)
(* ================================================================= *)

Section JanusInstance.
Context {nv na asize : nat}.

Definition jasn : Type := (@janus.var nv * janus.updop * @janus.expr nv na)%type.

Definition jact (s : @janus.store nv na asize) (a : jasn) (s' : @janus.store nv na asize) : Prop :=
  let '(x, op, e) := a in
  exists v, janus.eval s e = Some v
            /\ s' = janus.update s x (janus.apply_upd op (janus.lookup s x) v).

Definition jtest (s : @janus.store nv na asize) (e : @janus.expr nv na) : option bool :=
  janus.truth s e.

Notation jstmt := (gstmt jasn (@janus.expr nv na)).
Notation jgcs := (gcs jasn (@janus.expr nv na)).

Fixpoint emb (g : jstmt) : @janus.stmt nv na :=
  match g with
  | GSkip => janus.Sskip
  | GAsn (x, op, e) => janus.Sass x op e
  | GSeq a b => janus.Sseq (emb a) (emb b)
  | GLoop e1 a b e2 => janus.Sloop e1 (emb a) (emb b) e2
  end.

Fixpoint embc (c : jgcs) : @janus.cont_stmt nv na :=
  match c with
  | GC_pre st => janus.CS_pre (emb st)
  | GC_post st => janus.CS_post (emb st)
  | GC_seq_L c s2 => janus.CS_seq_L (embc c) (emb s2)
  | GC_seq_R s1 c => janus.CS_seq_R (emb s1) (embc c)
  | GC_loop_from e1 s1 s2 e2 => janus.CS_loop_from e1 (emb s1) (emb s2) e2
  | GC_loop_do e1 c s2 e2 => janus.CS_loop_do e1 (embc c) (emb s2) e2
  | GC_loop_until e1 s1 s2 e2 => janus.CS_loop_until e1 (emb s1) (emb s2) e2
  | GC_loop_loop e1 s1 c e2 => janus.CS_loop_loop e1 (emb s1) (embc c) e2
  end.

Lemma gstep_jstep_cfg :
  forall Γ cfg cfg', gstep jact jtest cfg cfg' ->
    janus.jstep Γ (embc (fst cfg), snd cfg) (embc (fst cfg'), snd cfg').
Proof.
  intros Γ cfg cfg' H; induction H; simpl in *.
  - apply janus.J_Skip.
  - destruct a as [[x op] e]; destruct H as [v [Hv ->]]. apply janus.J_Asn; exact Hv.
  - apply janus.J_Seq_Enter.
  - apply janus.J_Seq_Mid.
  - apply janus.J_Seq_Exit.
  - apply janus.J_Loop_Enter; exact H.
  - apply janus.J_Loop_Do.
  - apply janus.J_Loop_DoDone.
  - apply janus.J_Loop_Exit; exact H.
  - apply janus.J_Loop_Iter1; exact H.
  - apply janus.J_Loop_Iter2; exact H.
  - apply janus.J_Ctx_Seq_L; exact IHgstep.
  - apply janus.J_Ctx_Seq_R; exact IHgstep.
  - apply janus.J_Ctx_Loop_Do; exact IHgstep.
  - apply janus.J_Ctx_Loop_Loop; exact IHgstep.
Qed.

(* Inverting [emb] and [embc] at a constructor. *)
Ltac inv_emb :=
  repeat match goal with
  | [ H : emb ?g = _ |- _ ] =>
      is_var g; destruct g as [ | [[? ?] ?] | ? ? | ? ? ? ?]; simpl in H;
      try discriminate H; inversion H; clear H; subst
  | [ H : _ = emb ?g |- _ ] => symmetry in H
  | [ H : embc ?c = _ |- _ ] =>
      is_var c; destruct c; simpl in H; try discriminate H; inversion H; clear H; subst
  end.

Lemma jstep_gstep_cfg :
  forall Γ cfg cfg', janus.jstep Γ cfg cfg' ->
    forall c, fst cfg = embc c ->
    exists c', fst cfg' = embc c' /\ gstep jact jtest (c, snd cfg) (c', snd cfg').
Proof.
  intros Γ cfg cfg' H; induction H; intros c0 E; simpl in *; symmetry in E; inv_emb.
  - exists (GC_post GSkip); split; [reflexivity | apply G_Skip].
  - eexists (GC_post (GAsn (_, _, _))); split; [reflexivity |].
    apply G_Asn; exists v; split; [exact H | reflexivity].
  - eexists (GC_seq_L (GC_pre _) _); split; [reflexivity | apply G_Seq_Enter].
  - eexists (GC_seq_R _ (GC_pre _)); split; [reflexivity | apply G_Seq_Mid].
  - eexists (GC_post (GSeq _ _)); split; [reflexivity | apply G_Seq_Exit].
  - eexists (GC_loop_from _ _ _ _); split; [reflexivity | apply G_Loop_Enter; exact H].
  - eexists (GC_loop_do _ (GC_pre _) _ _); split; [reflexivity | apply G_Loop_Do].
  - eexists (GC_loop_until _ _ _ _); split; [reflexivity | apply G_Loop_DoDone].
  - eexists (GC_post (GLoop _ _ _ _)); split; [reflexivity | apply G_Loop_Exit; exact H].
  - eexists (GC_loop_loop _ _ (GC_pre _) _); split; [reflexivity | apply G_Loop_Iter1; exact H].
  - eexists (GC_loop_from _ _ _ _); split; [reflexivity | apply G_Loop_Iter2; exact H].
  - destruct (IHjstep _ eq_refl) as [c' [-> Hg]].
    eexists (GC_seq_L c' _); split; [reflexivity | apply G_Ctx_Seq_L; exact Hg].
  - destruct (IHjstep _ eq_refl) as [c' [-> Hg]].
    eexists (GC_seq_R _ c'); split; [reflexivity | apply G_Ctx_Seq_R; exact Hg].
  - destruct (IHjstep _ eq_refl) as [c' [-> Hg]].
    eexists (GC_loop_do _ c' _ _); split; [reflexivity | apply G_Ctx_Loop_Do; exact Hg].
  - destruct (IHjstep _ eq_refl) as [c' [-> Hg]].
    eexists (GC_loop_loop _ _ c' _); split; [reflexivity | apply G_Ctx_Loop_Loop; exact Hg].
Qed.

(* Theorem A. *)
Theorem jstep_gstep_iff :
  forall Γ c s cs' s',
    janus.jstep Γ (embc c, s) (cs', s')
    <-> exists c', cs' = embc c' /\ gstep jact jtest (c, s) (c', s').
Proof.
  intros Γ c s cs' s'; split.
  - intro H. exact (jstep_gstep_cfg H c eq_refl).
  - intros [c' [-> Hg]]. exact (gstep_jstep_cfg Γ Hg).
Qed.

End JanusInstance.

(* ================================================================= *)
(* 3. Theorem B: with R-CORE's data, gstep is R-CORE up to stuttering  *)
(* ================================================================= *)

Definition rasn : Type := (proofs.var * proofs.expr)%type.

Definition ract (σ : proofs.store) (a : rasn) (σ' : proofs.store) : Prop :=
  let '(x, e) := a in
  exists ve vn, proofs.eval_expr σ e = Some ve
                /\ proofs.odot (proofs.lookup σ x) ve = Some vn
                /\ σ' = proofs.update σ x vn.

(* An R-CORE guard is a variable; it is true when its value is not nil. *)
Definition rtest (σ : proofs.store) (x : proofs.var) : option bool :=
  Some (match proofs.lookup σ x with proofs.Vnil => false | _ => true end).

Notation rstmt := (gstmt rasn proofs.var).
Notation rgcs := (gcs rasn proofs.var).
Notation rstep := (gstep ract rtest).
Notation rnsteps := (gnsteps ract rtest).

(* from x loop c until y  =  from x do skip loop c until y *)
Fixpoint T (c : proofs.cmd) : rstmt :=
  match c with
  | proofs.Cass x e => GAsn (x, e)
  | proofs.Cseq c1 c2 => GSeq (T c1) (T c2)
  | proofs.Cloop x c y => GLoop x GSkip (T c) y
  end.

(* R-CORE's mid-loop position is the until-point: both test y next. *)
Fixpoint Tc (cc : proofs.cont_cmd) : rgcs :=
  match cc with
  | proofs.CC_at_pre c => GC_pre (T c)
  | proofs.CC_at_post c => GC_post (T c)
  | proofs.CC_mid_loop x c y => GC_loop_until x GSkip (T c) y
  | proofs.CC_seq_L cc c2 => GC_seq_L (Tc cc) (T c2)
  | proofs.CC_seq_R c1 cc => GC_seq_R (T c1) (Tc cc)
  | proofs.CC_in_loop x cc y => GC_loop_loop x GSkip (Tc cc) y
  end.

(* [adm cc c k]: c reaches Tc cc by k administrative steps.  The only
   positions with k > 0 are the three between the from-point and the
   until-point of a translated loop (before skip, after skip). *)
Inductive adm : proofs.cont_cmd -> rgcs -> nat -> Prop :=
  | adm_tc : forall cc, adm cc (Tc cc) 0
  | adm_from : forall x c y, adm (proofs.CC_mid_loop x c y) (GC_loop_from x GSkip (T c) y) 3
  | adm_do_pre : forall x c y,
      adm (proofs.CC_mid_loop x c y) (GC_loop_do x (GC_pre GSkip) (T c) y) 2
  | adm_do_post : forall x c y,
      adm (proofs.CC_mid_loop x c y) (GC_loop_do x (GC_post GSkip) (T c) y) 1
  | adm_seq_L : forall cc g k c2, adm cc g k -> adm (proofs.CC_seq_L cc c2) (GC_seq_L g (T c2)) k
  | adm_seq_R : forall c1 cc g k, adm cc g k -> adm (proofs.CC_seq_R c1 cc) (GC_seq_R (T c1) g) k
  | adm_loop : forall x cc g k y,
      adm cc g k -> adm (proofs.CC_in_loop x cc y) (GC_loop_loop x GSkip g y) k.

Local Hint Constructors adm gstep gnsteps : core.

Lemma T_inj : forall c c', T c = T c' -> c = c'.
Proof.
  induction c; intros [] H; simpl in H; try discriminate H; injection H; intros; subst;
    try (f_equal; auto).
Qed.

Lemma Tc_inj : forall cc cc', Tc cc = Tc cc' -> cc = cc'.
Proof.
  induction cc; intros [] H; simpl in H; try discriminate H; injection H; intros; subst;
    try (f_equal; auto using T_inj).
Qed.

Lemma Tc_post : forall cc g, Tc cc = GC_post g -> exists c, cc = proofs.CC_at_post c /\ g = T c.
Proof. intros [] g H; simpl in H; try discriminate H; injection H; intros; subst; eauto. Qed.

(* The images of Tc are the positions with k = 0. *)
Lemma adm_0_tc : forall cc c k, adm cc c k -> k = 0 -> c = Tc cc.
Proof.
  intros cc c k H; induction H; intro Ek; try discriminate Ek; simpl; try reflexivity;
    rewrite IHadm by exact Ek; reflexivity.
Qed.

Lemma ract_det : forall σ a σ1 σ2, ract σ a σ1 -> ract σ a σ2 -> σ1 = σ2.
Proof.
  unfold ract; intros σ [x e] σ1 σ2 [v1 [w1 [Hv1 [Ho1 ->]]]] [v2 [w2 [Hv2 [Ho2 ->]]]].
  rewrite Hv1 in Hv2; injection Hv2 as <-. rewrite Ho1 in Ho2; injection Ho2 as <-.
  reflexivity.
Qed.

(* The value of an R-CORE guard. *)
Lemma rtest_true : forall σ x, rtest σ x = Some true <-> proofs.lookup σ x <> proofs.Vnil.
Proof.
  intros σ x; unfold rtest; destruct (proofs.lookup σ x); split; intro H;
    try discriminate; try congruence.
Qed.

Lemma rtest_false : forall σ x, rtest σ x = Some false <-> proofs.lookup σ x = proofs.Vnil.
Proof.
  intros σ x; unfold rtest; destruct (proofs.lookup σ x); split; intro H;
    try discriminate; try congruence.
Qed.

(* Every R-CORE step is one gstep, after which the token is k
   administrative steps away from the image (k = 3 after S_LoopEnter and
   S_LoopIter2, 0 otherwise). *)
Theorem rcore_sim :
  forall cfg cfg', proofs.exec_ss cfg cfg' ->
    exists c' k, rstep (Tc (fst cfg), snd cfg) (c', snd cfg')
                 /\ adm (fst cfg') c' k /\ (k = 0 \/ k = 3).
Proof.
  intros cfg cfg' H; induction H; simpl.
  - exists (GC_post (GAsn (x, e))), 0; split; [| split; [apply adm_tc | auto]].
    apply G_Asn. unfold ract. exists v_e, v_new; auto.
  - exists (GC_loop_from x GSkip (T c) y), 3; split; [| split; [apply adm_from | auto]].
    apply G_Loop_Enter. apply rtest_true; exact H.
  - exists (GC_post (GLoop x GSkip (T c) y)), 0;
      split; [| split; [apply adm_tc | auto]].
    apply G_Loop_Exit. apply rtest_true; exact H.
  - exists (GC_loop_loop x GSkip (GC_pre (T c)) y), 0;
      split; [| split; [apply adm_tc | auto]].
    apply G_Loop_Iter1. apply rtest_false; exact H.
  - exists (GC_loop_from x GSkip (T c) y), 3; split; [| split; [apply adm_from | auto]].
    apply G_Loop_Iter2. apply rtest_false; exact H.
  - exists (GC_seq_L (GC_pre (T c1)) (T c2)), 0;
      split; [apply G_Seq_Enter | split; [apply adm_tc | auto]].
  - exists (GC_seq_R (T c1) (GC_pre (T c2))), 0;
      split; [apply G_Seq_Mid | split; [apply adm_tc | auto]].
  - exists (GC_post (GSeq (T c1) (T c2))), 0;
      split; [apply G_Seq_Exit | split; [apply adm_tc | auto]].
  - destruct IHexec_ss as [c' [k [Hs [Ha Hk]]]].
    exists (GC_seq_L c' (T c2)), k; split; [apply G_Ctx_Seq_L; exact Hs | split; [apply adm_seq_L; exact Ha | exact Hk]].
  - destruct IHexec_ss as [c' [k [Hs [Ha Hk]]]].
    exists (GC_seq_R (T c1) c'), k; split; [apply G_Ctx_Seq_R; exact Hs | split; [apply adm_seq_R; exact Ha | exact Hk]].
  - destruct IHexec_ss as [c' [k [Hs [Ha Hk]]]].
    exists (GC_loop_loop x GSkip c' y), k; split; [apply G_Ctx_Loop_Loop; exact Hs | split; [apply adm_loop; exact Ha | exact Hk]].
Qed.

(* An administrative position always moves, without touching the store,
   one step closer to the image. *)
Lemma adm_progress :
  forall cc c k, adm cc c (Datatypes.S k) -> forall σ, exists c', rstep (c, σ) (c', σ) /\ adm cc c' k.
Proof.
  intros cc c k0 H; remember (Datatypes.S k0) as k eqn:Ek; revert k0 Ek.
  induction H; intros k0 Ek σ; try discriminate Ek; try (injection Ek as <-).
  - exists (GC_loop_do x (GC_pre GSkip) (T c) y); split; [apply G_Loop_Do | apply adm_do_pre].
  - exists (GC_loop_do x (GC_post GSkip) (T c) y); split;
      [apply G_Ctx_Loop_Do; apply G_Skip | apply adm_do_post].
  - exists (GC_loop_until x GSkip (T c) y); split;
      [apply G_Loop_DoDone | apply adm_tc].
  - destruct (IHadm k0 Ek σ) as [c' [Hs Ha]].
    exists (GC_seq_L c' (T c2)); split; [apply G_Ctx_Seq_L; exact Hs | apply adm_seq_L; exact Ha].
  - destruct (IHadm k0 Ek σ) as [c' [Hs Ha]].
    exists (GC_seq_R (T c1) c'); split; [apply G_Ctx_Seq_R; exact Hs | apply adm_seq_R; exact Ha].
  - destruct (IHadm k0 Ek σ) as [c' [Hs Ha]].
    exists (GC_loop_loop x GSkip c' y); split; [apply G_Ctx_Loop_Loop; exact Hs | apply adm_loop; exact Ha].
Qed.

Lemma adm_run : forall k cc c σ, adm cc c k -> rnsteps k (c, σ) (Tc cc, σ).
Proof.
  induction k; intros cc c σ H.
  - rewrite (adm_0_tc H eq_refl). apply GN_refl.
  - destruct (adm_progress H σ) as [c' [Hs Ha]].
    eapply GN_step; [exact Hs | apply IHk; exact Ha].
Qed.

(* From an image Tc cc, a gstep is the image of an R-CORE step. *)
Ltac tc_post :=
  match goal with
  | [ E : Tc _ = GC_post _ |- _ ] => destruct (@Tc_post _ _ E) as [? [-> ->]]
  | [ E : GC_post _ = Tc _ |- _ ] => symmetry in E; destruct (@Tc_post _ _ E) as [? [-> ->]]
  end.

Lemma tc_step :
  forall cc σ c' σ', rstep (Tc cc, σ) (c', σ') ->
    exists cc' k, proofs.exec_ss (cc, σ) (cc', σ') /\ adm cc' c' k.
Proof.
  induction cc as [c | c | x c y | cc IH c2 | c1 cc IH | x cc IH y]; intros σ c' σ' H; simpl in H.
  - destruct c as [x e | c1 c2 | x c y]; simpl in H; inversion H; subst.
    + match goal with [ Hr : ract _ _ _ |- _ ] =>
        unfold ract in Hr; destruct Hr as [ve [vn [Hv [Ho ->]]]] end.
      exists (proofs.CC_at_post (proofs.Cass x e)), 0; split;
        [eapply proofs.S_Asn; eassumption | apply adm_tc].
    + exists (proofs.CC_seq_L (proofs.CC_at_pre c1) c2), 0; split;
        [apply proofs.S_Seq_Enter | apply adm_tc].
    + exists (proofs.CC_mid_loop x c y), 3; split;
        [apply proofs.S_LoopEnter; apply rtest_true; assumption | apply adm_from].
  - exfalso; exact (no_gstep_from_post H).
  - inversion H; subst.
    + exists (proofs.CC_at_post (proofs.Cloop x c y)), 0; split;
        [apply proofs.S_LoopExit; apply rtest_true; assumption | apply adm_tc].
    + exists (proofs.CC_in_loop x (proofs.CC_at_pre c) y), 0; split;
        [apply proofs.S_LoopIter1; apply rtest_false; assumption | apply adm_tc].
  - inversion H; subst.
    + tc_post. eexists (proofs.CC_seq_R _ (proofs.CC_at_pre c2)), 0; split;
        [apply proofs.S_Seq_Mid | apply adm_tc].
    + match goal with [ Hi : gstep _ _ (Tc cc, _) _ |- _ ] =>
        destruct (IH _ _ _ Hi) as [cc' [k [He Ha]]] end.
      exists (proofs.CC_seq_L cc' c2), k; split;
        [apply proofs.S_Ctx_Seq_L; exact He | apply adm_seq_L; exact Ha].
  - inversion H; subst.
    + tc_post. eexists (proofs.CC_at_post (proofs.Cseq c1 _)), 0; split;
        [apply proofs.S_Seq_Exit | apply adm_tc].
    + match goal with [ Hi : gstep _ _ (Tc cc, _) _ |- _ ] =>
        destruct (IH _ _ _ Hi) as [cc' [k [He Ha]]] end.
      exists (proofs.CC_seq_R c1 cc'), k; split;
        [apply proofs.S_Ctx_Seq_R; exact He | apply adm_seq_R; exact Ha].
  - inversion H; subst.
    + tc_post. eexists (proofs.CC_mid_loop x _ y), 3; split;
        [apply proofs.S_LoopIter2; apply rtest_false; assumption | apply adm_from].
    + match goal with [ Hi : gstep _ _ (Tc cc, _) _ |- _ ] =>
        destruct (IH _ _ _ Hi) as [cc' [k [He Ha]]] end.
      exists (proofs.CC_in_loop x cc' y), k; split;
        [apply proofs.S_Ctx_Loop; exact He | apply adm_loop; exact Ha].
Qed.

(* Every gstep from a position related to cc is either an administrative
   step (k > 0: the store is unchanged and the token one step closer to
   Tc cc) or, at the image itself (k = 0), the image of an R-CORE step. *)
Theorem adm_step :
  forall cc c k σ c' σ', adm cc c k -> rstep (c, σ) (c', σ') ->
    (exists k0, k = Datatypes.S k0 /\ σ' = σ /\ adm cc c' k0)
    \/ (k = 0 /\ exists cc' k', proofs.exec_ss (cc, σ) (cc', σ') /\ adm cc' c' k').
Proof.
  intros cc c k σ c' σ' Ha Hs. destruct k as [| k0].
  - right; split; [reflexivity |]. rewrite (adm_0_tc Ha eq_refl) in Hs. eapply tc_step; exact Hs.
  - left; exists k0; split; [reflexivity |].
    destruct (adm_progress Ha σ) as [c'' [Hs' Ha']].
    pose proof (gstep_deterministic ract_det Hs Hs') as E. injection E as -> ->.
    split; [reflexivity | exact Ha'].
Qed.

(* One R-CORE step is 1 or 4 gsteps between the images. *)
Corollary rcore_sim_tc :
  forall cc σ cc' σ', proofs.exec_ss (cc, σ) (cc', σ') ->
    exists n, (n = 1 \/ n = 4) /\ rnsteps n (Tc cc, σ) (Tc cc', σ').
Proof.
  intros cc σ cc' σ' H. destruct (rcore_sim H) as [c' [k [Hs [Ha Hk]]]]; simpl in *.
  exists (1 + k); split; [destruct Hk as [-> | ->]; auto |].
  eapply GN_step; [exact Hs | apply adm_run; exact Ha].
Qed.

(* No image is an administrative position. *)
Lemma adm_tc_0 : forall k cc cc', adm cc (Tc cc') k -> k = 0.
Proof.
  intros k cc cc' H; remember (Tc cc') as c eqn:Ec; revert cc' Ec.
  induction H; intros cc' Ec; try reflexivity;
    destruct cc'; simpl in Ec; try discriminate Ec; injection Ec; intros; subst; eauto.
Qed.

Lemma runs_back :
  forall n cfg cfg', rnsteps n cfg cfg' ->
    forall cc0 k cc1, adm cc0 (fst cfg) k -> fst cfg' = Tc cc1 ->
    proofs.exec_ss_star (cc0, snd cfg) (cc1, snd cfg').
Proof.
  intros n cfg cfg' H; induction H as [cfg | n cfg1 cfg2 cfg3 Hs Hn IH];
    intros cc0 k cc1 Ha E.
  - destruct cfg as [c σ]; simpl in *; subst c.
    pose proof (@adm_tc_0 _ _ _ Ha) as Hk; subst k.
    pose proof (adm_0_tc Ha eq_refl) as E'. apply Tc_inj in E'; subst.
    apply proofs.exec_ss_star_refl.
  - destruct cfg1 as [c1 σ1], cfg2 as [c2 σ2]; simpl in *.
    destruct (adm_step Ha Hs) as [[k0 [_ [-> Ha']]] | [_ [cc' [k' [He Ha']]]]].
    + exact (IH _ _ _ Ha' E).
    + eapply proofs.steps_cons; [exact He | exact (IH _ _ _ Ha' E)].
Qed.

Lemma runs_fwd :
  forall cfg cfg', proofs.exec_ss_star cfg cfg' ->
    exists n, rnsteps n (Tc (fst cfg), snd cfg) (Tc (fst cfg'), snd cfg').
Proof.
  intros cfg cfg' H; induction H as [cfg | cfg1 cfg2 cfg3 Hs Hn IH].
  - exists 0; apply GN_refl.
  - destruct cfg1 as [cc1 σ1], cfg2 as [cc2 σ2]; simpl in *.
    destruct (rcore_sim_tc Hs) as [n1 [_ H1]].
    destruct IH as [n2 H2].
    exists (n1 + n2); eapply gnsteps_trans; eassumption.
Qed.

(* Runs between images are exactly R-CORE runs. *)
Theorem rcore_embed_runs :
  forall cc σ cc' σ',
    proofs.exec_ss_star (cc, σ) (cc', σ') <-> exists n, rnsteps n (Tc cc, σ) (Tc cc', σ').
Proof.
  intros cc σ cc' σ'; split.
  - intro H. exact (runs_fwd H).
  - intros [n Hn].
    exact (@runs_back n (Tc cc, σ) (Tc cc', σ') Hn cc 0 cc' (adm_tc cc) eq_refl).
Qed.

(* ================================================================= *)
(* 4. Axiom audit                                                     *)
(* ================================================================= *)

(* Every top-level result of this file.  tools/audit.sh (with
   SRC=janus/embed.v) checks that this block is complete and that every
   line prints "Closed under the global context". *)
Print Assumptions gnsteps_trans.
Print Assumptions no_gstep_from_post.
Print Assumptions gstep_deterministic.
Print Assumptions gstep_jstep_cfg.
Print Assumptions jstep_gstep_cfg.
Print Assumptions jstep_gstep_iff.
Print Assumptions T_inj.
Print Assumptions Tc_inj.
Print Assumptions Tc_post.
Print Assumptions adm_0_tc.
Print Assumptions ract_det.
Print Assumptions rtest_true.
Print Assumptions rtest_false.
Print Assumptions rcore_sim.
Print Assumptions adm_progress.
Print Assumptions adm_run.
Print Assumptions tc_step.
Print Assumptions adm_step.
Print Assumptions rcore_sim_tc.
Print Assumptions adm_tc_0.
Print Assumptions runs_back.
Print Assumptions runs_fwd.
Print Assumptions rcore_embed_runs.
