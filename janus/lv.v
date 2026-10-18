(*
  janus/lv.v -- The program-counter semantics of Lanese and Vidal,
  "A Reversible Semantics for Janus" (RC 2026, LNCS 16626, pp. 184-200;
  extended version arXiv:2602.16913), mechanized and related rule by rule
  to the control-token semantics [jstep] of janus/janus.v.

  What is formalized.  Their configurations <sigma, l, l', pi> (store, last
  executed label, next label, stack) and the forward rules of their
  Figs. 11-12 (LNCS numbering; Figs. 12-13 in the arXiv version) and the
  backward rules of Figs. 14-15 (arXiv: 16-17), over the common fragment
  of the two languages: no local blocks and no procedure parameters
  ([frag], [lv_penv]).

  Labels.  Their labels name the elementary blocks of a labelled program
  (assignments, skip, call, uncall, start, stop, and the two expressions of
  each conditional and loop).  Here a label is the position of the block:
  the root it belongs to (the main program, procedure q, or the inverse
  procedure q^-1) and the path from the root to the block, so that labels
  are unique by construction and [block], [ctx], [entry], [exit] and
  [flow] (their Figs. 8-9) are functions of the syntax.  A stack element
  loop1(l1, s1, l2, s2) is represented by its two labels, from which s1
  and s2 are recovered by [node] (labels are unique).

  Errata.  Read literally, three side conditions of the published rules
  do not say what the surrounding text says; the switch [fixed] selects
  either the rules as printed ([fixed = false]) or the repaired ones:
    (E1) forward LoopBase requires l2' <> entry(s1); entry(s1) is never a
         successor of l2, so the rule may also leave the loop towards
         entry(s2).  The repaired rule requires l2' <> entry(s2).
    (E2) forward LoopMain has no condition on the last label, so at the
         iteration point (last label exit(s2), loop2 on the stack) a true
         e1 re-enters the loop, where Janus and their own stack semantics
         (Fig. 5, LoopMain_S) are stuck.  The repaired rule requires
         l <> exit(s2), the condition of their backward LoopMain.
    (E3) backward AssVar, AssArr and Skip test l' -> l'' but leave the
         recovered last label l unconstrained.  The repaired rules also
         require l -> l', as backward Call does.
  Section 4 shows each erratum on a three-line program.

  Tested with Rocq 9.1.1.
*)

From Stdlib Require Import ZArith Lia List Bool.
From Stdlib Require Import Vectors.Vector Vectors.Fin.
From RCore.janus Require Import janus.
Import ListNotations.
Set Implicit Arguments.

(* ================================================================= *)
(* 1. Labels, the control-flow graph and the configurations           *)
(* ================================================================= *)

(* A step from a statement to one of its sub-statements. *)
Inductive dir : Type := DL | DR | DThen | DElse | DDo | DLoop.
Definition path := list dir.

(* A point of the CFG inside one root: an elementary block, the first or
   second expression of a conditional or loop, or start / stop. *)
Inductive pt : Type :=
  | PBlk (p : path)
  | PT1 (p : path)
  | PT2 (p : path)
  | PStart
  | PStop.

Inductive root : Type := RMain | RProc (q : pid) | RInv (q : pid).

Definition label : Type := (root * pt)%type.

Definition pfx (P : path) (x : pt) : pt :=
  match x with
  | PBlk p => PBlk (P ++ p)
  | PT1 p => PT1 (P ++ p)
  | PT2 p => PT2 (P ++ p)
  | PStart => PStart
  | PStop => PStop
  end.

Definition path_of (x : pt) : option path :=
  match x with
  | PBlk p | PT1 p | PT2 p => Some p
  | PStart | PStop => None
  end.

Section LV.
Context {nv na asize : nat}.

Local Notation stmt := (@janus.stmt nv na).
Local Notation expr := (@janus.expr nv na).
Local Notation store := (@janus.store nv na asize).
Local Notation penv := (@janus.penv nv na).
Local Notation cont_stmt := (@janus.cont_stmt nv na).

(* entry(s) and exit(s) of their Fig. 8, relative to s. *)
Fixpoint entry_pt (st : stmt) : pt :=
  match st with
  | Sseq a _ => pfx [DL] (entry_pt a)
  | Sif _ _ _ _ | Sloop _ _ _ _ => PT1 []
  | _ => PBlk []
  end.

Fixpoint exit_pt (st : stmt) : pt :=
  match st with
  | Sseq _ b => pfx [DR] (exit_pt b)
  | Sif _ _ _ _ | Sloop _ _ _ _ => PT2 []
  | _ => PBlk []
  end.

(* The sub-statement at a path. *)
Fixpoint node (st : stmt) (P : path) {struct P} : option stmt :=
  match P with
  | [] => Some st
  | d :: P' =>
      match d, st with
      | DL, Sseq a _ => node a P'
      | DR, Sseq _ b => node b P'
      | DThen, Sif _ a _ _ => node a P'
      | DElse, Sif _ _ b _ => node b P'
      | DDo, Sloop _ a _ _ => node a P'
      | DLoop, Sloop _ _ b _ => node b P'
      | _, _ => None
      end
  end.

(* flow(s) of their Fig. 9, relative to s. *)
Inductive flow : stmt -> pt -> pt -> Prop :=
  | F_Seq : forall a b,
      flow (Sseq a b) (pfx [DL] (exit_pt a)) (pfx [DR] (entry_pt b))
  | F_Seq_L : forall a b x y, flow a x y -> flow (Sseq a b) (pfx [DL] x) (pfx [DL] y)
  | F_Seq_R : forall a b x y, flow b x y -> flow (Sseq a b) (pfx [DR] x) (pfx [DR] y)
  | F_If_T1 : forall e1 a b e2, flow (Sif e1 a b e2) (PT1 []) (pfx [DThen] (entry_pt a))
  | F_If_T2 : forall e1 a b e2, flow (Sif e1 a b e2) (pfx [DThen] (exit_pt a)) (PT2 [])
  | F_If_E1 : forall e1 a b e2, flow (Sif e1 a b e2) (PT1 []) (pfx [DElse] (entry_pt b))
  | F_If_E2 : forall e1 a b e2, flow (Sif e1 a b e2) (pfx [DElse] (exit_pt b)) (PT2 [])
  | F_If_L : forall e1 a b e2 x y,
      flow a x y -> flow (Sif e1 a b e2) (pfx [DThen] x) (pfx [DThen] y)
  | F_If_R : forall e1 a b e2 x y,
      flow b x y -> flow (Sif e1 a b e2) (pfx [DElse] x) (pfx [DElse] y)
  | F_Loop_1 : forall e1 a b e2, flow (Sloop e1 a b e2) (PT1 []) (pfx [DDo] (entry_pt a))
  | F_Loop_2 : forall e1 a b e2, flow (Sloop e1 a b e2) (pfx [DDo] (exit_pt a)) (PT2 [])
  | F_Loop_3 : forall e1 a b e2, flow (Sloop e1 a b e2) (PT2 []) (pfx [DLoop] (entry_pt b))
  | F_Loop_4 : forall e1 a b e2, flow (Sloop e1 a b e2) (pfx [DLoop] (exit_pt b)) (PT1 [])
  | F_Loop_L : forall e1 a b e2 x y,
      flow a x y -> flow (Sloop e1 a b e2) (pfx [DDo] x) (pfx [DDo] y)
  | F_Loop_R : forall e1 a b e2 x y,
      flow b x y -> flow (Sloop e1 a b e2) (pfx [DLoop] x) (pfx [DLoop] y).

(* Stack elements of their Figs. 11-12. *)
Inductive frame : Type :=
  | Fift (l1 l2 : label)          (* if_true(l1, l2) *)
  | Fiff (l1 l2 : label)          (* if_false(l1, l2) *)
  | Floop1 (l1 l2 : label)        (* loop1(l1, s1, l2, s2) *)
  | Floop2 (l1 l2 : label)        (* loop2(l1, s1, l2, s2) *)
  | Fcall (l : label)             (* call(l) *)
  | Funcall (l : label).          (* uncall(l) *)

Record lvcfg : Type := mkcfg {
  lst : store; llast : label; lnext : label; lstk : list frame }.

Variables (Γ : penv) (main : stmt).

(* The statement of each root: the main program, the body of procedure q,
   and the body of its inverse q^-1 (their I[[s]], start and stop swapped,
   which here are not part of the statement but the points PStart/PStop). *)
Definition rstmt (r : root) : stmt :=
  match r with
  | RMain => main
  | RProc q => body (Γ q)
  | RInv q => inv (body (Γ q))
  end.

(* The CFG of each root: flow, plus start -> entry and exit -> stop. *)
Inductive edge : label -> label -> Prop :=
  | E_flow : forall r x y, flow (rstmt r) x y -> edge (r, x) (r, y)
  | E_start : forall r, edge (r, PStart) (r, entry_pt (rstmt r))
  | E_stop : forall r, edge (r, exit_pt (rstmt r)) (r, PStop).

(* block(l) for statements, and for expressions of conditionals and loops. *)
Definition stmt_at (l : label) : option stmt :=
  match snd l with PBlk p => node (rstmt (fst l)) p | _ => None end.

Definition test_at (l : label) : option expr :=
  match snd l with
  | PT1 p => match node (rstmt (fst l)) p with
             | Some (Sif e1 _ _ _) | Some (Sloop e1 _ _ _) => Some e1
             | _ => None
             end
  | PT2 p => match node (rstmt (fst l)) p with
             | Some (Sif _ _ _ e2) | Some (Sloop _ _ _ e2) => Some e2
             | _ => None
             end
  | _ => None
  end.

Definition is_start (l : label) : Prop := snd l = PStart.

(* ================================================================= *)
(* 2. The forward rules  -->  (their Figs. 11-12)                      *)
(* ================================================================= *)

(* [fixed = false]: the rules as printed.  [fixed = true]: (E1) and (E2)
   repaired.  The loop rules read ctx(l1) / the stack element through the
   path p of the loop: l1 = (r, PT1 p), l2 = (r, PT2 p). *)
Inductive lvf (fixed : bool) : lvcfg -> lvcfg -> Prop :=
  | LF_AssVar : forall s l l' l'' x op e v π,
      stmt_at l' = Some (Sass x op e) -> eval s e = Some v -> edge l' l'' ->
      lvf fixed (mkcfg s l l' π) (mkcfg (update s x (apply_upd op (s x) v)) l' l'' π)
  | LF_AssArr : forall s l l' l'' a e1 op e2 z i w π,
      stmt_at l' = Some (Saass a e1 op e2) ->
      eval s e1 = Some z -> idx z = Some i -> eval s e2 = Some w -> edge l' l'' ->
      lvf fixed (mkcfg s l l' π)
              (mkcfg (aupdate s a i (apply_upd op (aget s a i) w)) l' l'' π)
  | LF_Call : forall s l l' l'' q π,
      stmt_at l' = Some (Scall q []) -> edge (RProc q, PStart) l'' ->
      lvf fixed (mkcfg s l l' π) (mkcfg s (RProc q, PStart) l'' (Fcall l' :: π))
  | LF_Return1 : forall s l r l'' l''' π,
      edge l'' l''' ->
      lvf fixed (mkcfg s l (r, PStop) (Fcall l'' :: π)) (mkcfg s l'' l''' π)
  | LF_UnCall : forall s l l' l'' q π,
      stmt_at l' = Some (Suncall q []) -> edge (RInv q, PStart) l'' ->
      lvf fixed (mkcfg s l l' π) (mkcfg s (RInv q, PStart) l'' (Funcall l' :: π))
  | LF_Return2 : forall s l r l'' l''' π,
      edge l'' l''' ->
      lvf fixed (mkcfg s l (r, PStop) (Funcall l'' :: π)) (mkcfg s l'' l''' π)
  | LF_Skip : forall s l l' l'' π,
      stmt_at l' = Some Sskip -> edge l' l'' ->
      lvf fixed (mkcfg s l l' π) (mkcfg s l' l'' π)
  | LF_IfTrue1 : forall s l r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sif e1 s1 s2 e2) -> truth s e1 = Some true ->
      lvf fixed (mkcfg s l (r, PT1 p) π)
              (mkcfg s (r, PT1 p) (r, pfx (p ++ [DThen]) (entry_pt s1))
                     (Fift (r, PT1 p) (r, PT2 p) :: π))
  | LF_IfTrue2 : forall s l l1 l2 l2' e2 π,
      test_at l2 = Some e2 -> truth s e2 = Some true -> edge l2 l2' ->
      lvf fixed (mkcfg s l l2 (Fift l1 l2 :: π)) (mkcfg s l2 l2' π)
  | LF_IfFalse1 : forall s l r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sif e1 s1 s2 e2) -> truth s e1 = Some false ->
      lvf fixed (mkcfg s l (r, PT1 p) π)
              (mkcfg s (r, PT1 p) (r, pfx (p ++ [DElse]) (entry_pt s2))
                     (Fiff (r, PT1 p) (r, PT2 p) :: π))
  | LF_IfFalse2 : forall s l l1 l2 l2' e2 π,
      test_at l2 = Some e2 -> truth s e2 = Some false -> edge l2 l2' ->
      lvf fixed (mkcfg s l l2 (Fiff l1 l2 :: π)) (mkcfg s l2 l2' π)
  | LF_LoopMain : forall s l r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e1 = Some true ->
      (fixed = true -> l <> (r, pfx (p ++ [DLoop]) (exit_pt s2))) ->         (* E2 *)
      lvf fixed (mkcfg s l (r, PT1 p) π)
              (mkcfg s (r, PT1 p) (r, pfx (p ++ [DDo]) (entry_pt s1))
                     (Floop1 (r, PT1 p) (r, PT2 p) :: π))
  | LF_LoopBase : forall s l r p e1 s1 s2 e2 l2' π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e2 = Some true ->
      edge (r, PT2 p) l2' ->
      l2' <> (if fixed then (r, pfx (p ++ [DLoop]) (entry_pt s2))         (* E1 *)
              else (r, pfx (p ++ [DDo]) (entry_pt s1))) ->
      lvf fixed (mkcfg s l (r, PT2 p) (Floop1 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s (r, PT2 p) l2' π)
  | LF_Loop1 : forall s l r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e2 = Some false ->
      lvf fixed (mkcfg s l (r, PT2 p) (Floop1 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s (r, PT2 p) (r, pfx (p ++ [DLoop]) (entry_pt s2))
                     (Floop2 (r, PT1 p) (r, PT2 p) :: π))
  | LF_Loop2 : forall s l r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e1 = Some false ->
      lvf fixed (mkcfg s l (r, PT1 p) (Floop2 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s (r, PT1 p) (r, pfx (p ++ [DDo]) (entry_pt s1))
                     (Floop1 (r, PT1 p) (r, PT2 p) :: π)).

(* ================================================================= *)
(* 3. The backward rules  <--  (their Figs. 14-15)                     *)
(* ================================================================= *)

(* [lvb fixed c' c] is their  c' <-- c.  [fixed = true] repairs (E3). *)
Inductive lvb (fixed : bool) : lvcfg -> lvcfg -> Prop :=
  | LB_AssVar : forall s l l' l'' x op e v π,
      stmt_at l' = Some (Sass x op e) -> eval s e = Some v -> edge l' l'' ->
      (fixed = true -> edge l l') ->                                       (* E3 *)
      lvb fixed (mkcfg s l' l'' π) (mkcfg (update s x (apply_upd (inv_upd op) (s x) v)) l l' π)
  | LB_AssArr : forall s l l' l'' a e1 op e2 z i w π,
      stmt_at l' = Some (Saass a e1 op e2) ->
      eval s e1 = Some z -> idx z = Some i -> eval s e2 = Some w -> edge l' l'' ->
      (fixed = true -> edge l l') ->                                       (* E3 *)
      lvb fixed (mkcfg s l' l'' π)
              (mkcfg (aupdate s a i (apply_upd (inv_upd op) (aget s a i) w)) l l' π)
  | LB_Call : forall s ls l l' l'' π,
      is_start ls -> edge l l' ->
      lvb fixed (mkcfg s ls l'' (Fcall l' :: π)) (mkcfg s l l' π)
  | LB_Return1 : forall s l l'' l''' q π,
      stmt_at l'' = Some (Scall q []) -> edge l (RProc q, PStop) ->
      lvb fixed (mkcfg s l'' l''' π) (mkcfg s l (RProc q, PStop) (Fcall l'' :: π))
  | LB_UnCall : forall s ls l l' l'' π,
      is_start ls -> edge l l' ->
      lvb fixed (mkcfg s ls l'' (Funcall l' :: π)) (mkcfg s l l' π)
  | LB_Return2 : forall s l l'' l''' q π,
      stmt_at l'' = Some (Suncall q []) -> edge l (RInv q, PStop) ->
      lvb fixed (mkcfg s l'' l''' π) (mkcfg s l (RInv q, PStop) (Funcall l'' :: π))
  | LB_Skip : forall s l l' l'' π,
      stmt_at l' = Some Sskip -> edge l' l'' ->
      (fixed = true -> edge l l') ->                                       (* E3 *)
      lvb fixed (mkcfg s l' l'' π) (mkcfg s l l' π)
  | LB_IfTrue1 : forall s l l1 l1' l2 e1 π,
      test_at l1 = Some e1 -> truth s e1 = Some true -> edge l l1 ->
      lvb fixed (mkcfg s l1 l1' (Fift l1 l2 :: π)) (mkcfg s l l1 π)
  | LB_IfTrue2 : forall s r p e1 s1 s2 e2 l2' π,
      node (rstmt r) p = Some (Sif e1 s1 s2 e2) -> truth s e2 = Some true ->
      lvb fixed (mkcfg s (r, PT2 p) l2' π)
              (mkcfg s (r, pfx (p ++ [DThen]) (exit_pt s1)) (r, PT2 p)
                     (Fift (r, PT1 p) (r, PT2 p) :: π))
  | LB_IfFalse1 : forall s l l1 l1' l2 e1 π,
      test_at l1 = Some e1 -> truth s e1 = Some false -> edge l l1 ->
      lvb fixed (mkcfg s l1 l1' (Fiff l1 l2 :: π)) (mkcfg s l l1 π)
  | LB_IfFalse2 : forall s r p e1 s1 s2 e2 l2' π,
      node (rstmt r) p = Some (Sif e1 s1 s2 e2) -> truth s e2 = Some false ->
      lvb fixed (mkcfg s (r, PT2 p) l2' π)
              (mkcfg s (r, pfx (p ++ [DElse]) (exit_pt s2)) (r, PT2 p)
                     (Fiff (r, PT1 p) (r, PT2 p) :: π))
  | LB_LoopMain : forall s l l' r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e1 = Some true ->
      edge l (r, PT1 p) -> l <> (r, pfx (p ++ [DLoop]) (exit_pt s2)) ->
      lvb fixed (mkcfg s (r, PT1 p) l' (Floop1 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s l (r, PT1 p) π)
  | LB_LoopBase : forall s r p e1 s1 s2 e2 l2' π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e2 = Some true ->
      lvb fixed (mkcfg s (r, PT2 p) l2' π)
              (mkcfg s (r, pfx (p ++ [DDo]) (exit_pt s1)) (r, PT2 p)
                     (Floop1 (r, PT1 p) (r, PT2 p) :: π))
  | LB_Loop1 : forall s l' r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e2 = Some false ->
      lvb fixed (mkcfg s (r, PT2 p) l' (Floop2 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s (r, pfx (p ++ [DDo]) (exit_pt s1)) (r, PT2 p)
                     (Floop1 (r, PT1 p) (r, PT2 p) :: π))
  | LB_Loop2 : forall s l' r p e1 s1 s2 e2 π,
      node (rstmt r) p = Some (Sloop e1 s1 s2 e2) -> truth s e1 = Some false ->
      lvb fixed (mkcfg s (r, PT1 p) l' (Floop1 (r, PT1 p) (r, PT2 p) :: π))
              (mkcfg s (r, pfx (p ++ [DLoop]) (exit_pt s2)) (r, PT1 p)
                     (Floop2 (r, PT1 p) (r, PT2 p) :: π)).

(* Every point of flow(s) lies inside s: it has a path. *)
Lemma path_of_pfx : forall P x, path_of (pfx P x) = option_map (app P) (path_of x).
Proof. intros P [p|p|p| |]; reflexivity. Qed.

Lemma path_entry : forall st, path_of (entry_pt st) <> None.
Proof.
  induction st; simpl; try discriminate.
  rewrite path_of_pfx. destruct (path_of (entry_pt st1)); [discriminate | contradiction].
Qed.

Lemma path_exit : forall st, path_of (exit_pt st) <> None.
Proof.
  induction st; simpl; try discriminate.
  rewrite path_of_pfx. destruct (path_of (exit_pt st2)); [discriminate | contradiction].
Qed.

Lemma flow_paths : forall st x y, flow st x y -> path_of x <> None /\ path_of y <> None.
Proof.
  intros st x y H; induction H; rewrite ?path_of_pfx; simpl;
    repeat match goal with
           | [ |- context [path_of (entry_pt ?t)] ] =>
               destruct (path_of (entry_pt t)) eqn:?; [| exfalso; eapply path_entry; eassumption]
           | [ |- context [path_of (exit_pt ?t)] ] =>
               destruct (path_of (exit_pt t)) eqn:?; [| exfalso; eapply path_exit; eassumption]
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- context [path_of ?x] ] =>
               lazymatch goal with
               | [ H : path_of x <> None |- _ ] => destruct (path_of x); [| contradiction]
               end
           end;
    split; discriminate.
Qed.

Inductive lvf_star (fixed : bool) : lvcfg -> lvcfg -> Prop :=
  | LFS_refl : forall c, lvf_star fixed c c
  | LFS_step : forall c1 c2 c3, lvf fixed c1 c2 -> lvf_star fixed c2 c3 -> lvf_star fixed c1 c3.

End LV.

(* ================================================================= *)
(* 4. The errata on three small programs                              *)
(* ================================================================= *)

Section Errata.
Local Open Scope Z_scope.

(* One variable Y, one array of length 1 (unused), no procedures. *)
Definition Y : Fin.t 1 := Fin.F1.
Definition s0 : @store 1 1 1 :=
  mkstore (Vector.const 0 1%nat) (Vector.const (Vector.const 0 1%nat) 1%nat).
Definition s1 : @store 1 1 1 := update s0 Y 1.
Definition Γe : @penv 1 1 := fun _ => mkproc [] Sskip.

Lemma s0_neq_s1 : s0 <> s1.
Proof. intro H. apply (f_equal (fun s => lookup s Y)) in H. vm_compute in H. discriminate. Qed.

Ltac edge_flow := apply E_flow; simpl; constructor.

(* After inverting a step of a concrete program: unfold the program and
   split the equations between looked-up statements. *)
Ltac clean :=
  simpl in *;
  repeat match goal with
         | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
         end;
  subst; simpl in *.

(* ---- (E1) LoopBase:  from 1 do skip loop Y += 1 until 1 ----
   Janus runs it once and leaves Y = 0.  With the printed LoopBase the
   machine may also leave the loop towards s2 = (Y += 1), dropping the
   loop1 element, come back to l1, re-enter the loop with LoopMain and
   stop with Y = 1. *)
Definition main1 : @stmt 1 1 := Sloop (Econst 1) Sskip (Sass Y Uadd (Econst 1)) (Econst 1).

Definition init1 : @lvcfg 1 1 1 := mkcfg s0 (RMain, PStart) (RMain, PT1 []) [].
Definition lf1 : frame := Floop1 (RMain, PT1 []) (RMain, PT2 []).

(* The common prefix: LoopMain, then skip. *)
Lemma e1_prefix :
  forall fixed,
    lvf_star Γe main1 fixed init1 (mkcfg s0 (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1]).
Proof.
  intro fixed.
  eapply LFS_step.
  { apply (@LF_LoopMain 1 1 1 Γe main1 fixed s0 (RMain, PStart) RMain [] (Econst 1)
             Sskip (Sass Y Uadd (Econst 1)) (Econst 1) []); [reflexivity | reflexivity |].
    intros _ H; discriminate H. }
  eapply LFS_step; [| apply LFS_refl].
  apply LF_Skip; [reflexivity | edge_flow].
Qed.

(* From the end of s1 the printed LoopBase may go to stop ... *)
Lemma e1_exit :
  forall fixed (s : @store 1 1 1),
    lvf Γe main1 fixed (mkcfg s (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1])
                       (mkcfg s (RMain, PT2 []) (RMain, PStop) []).
Proof.
  intros fixed s.
  apply (@LF_LoopBase 1 1 1 Γe main1 fixed s (RMain, PBlk [DDo]) RMain [] (Econst 1)
           Sskip (Sass Y Uadd (Econst 1)) (Econst 1) (RMain, PStop) []);
    [reflexivity | reflexivity | apply E_stop | destruct fixed; discriminate].
Qed.

(* ... or, as printed, to entry(s2), dropping the loop1 element. *)
Lemma e1_escape :
  lvf Γe main1 false (mkcfg s0 (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1])
                     (mkcfg s0 (RMain, PT2 []) (RMain, PBlk [DLoop]) []).
Proof.
  apply (@LF_LoopBase 1 1 1 Γe main1 false s0 (RMain, PBlk [DDo]) RMain [] (Econst 1)
           Sskip (Sass Y Uadd (Econst 1)) (Econst 1) (RMain, PBlk [DLoop]) []);
    [reflexivity | reflexivity | edge_flow | discriminate].
Qed.

Example e1_printed_two_results :
  lvf_star Γe main1 false init1 (mkcfg s0 (RMain, PT2 []) (RMain, PStop) [])
  /\ lvf_star Γe main1 false init1 (mkcfg s1 (RMain, PT2 []) (RMain, PStop) []).
Proof.
  split.
  - (* the intended run: Y = 0 *)
    pose proof (e1_prefix false) as Hp.
    remember (mkcfg s0 (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1]) as c2.
    induction Hp; subst.
    + eapply LFS_step; [apply e1_exit | apply LFS_refl].
    + eapply LFS_step; [eassumption | apply IHHp; reflexivity].
  - (* the spurious run: Y = 1 *)
    pose proof (e1_prefix false) as Hp.
    remember (mkcfg s0 (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1]) as c2.
    induction Hp; subst.
    + eapply LFS_step; [apply e1_escape |].
      eapply LFS_step.
      { apply (@LF_AssVar 1 1 1 Γe main1 false s0 (RMain, PT2 []) (RMain, PBlk [DLoop])
                 (RMain, PT1 []) Y Uadd (Econst 1) 1 []); [reflexivity | reflexivity | edge_flow]. }
      eapply LFS_step.
      { apply (@LF_LoopMain 1 1 1 Γe main1 false s1 (RMain, PBlk [DLoop]) RMain [] (Econst 1)
                 Sskip (Sass Y Uadd (Econst 1)) (Econst 1) []); [reflexivity | reflexivity |].
        intro H; discriminate H. }
      eapply LFS_step; [apply LF_Skip; [reflexivity | edge_flow] |].
      eapply LFS_step; [apply e1_exit | apply LFS_refl].
    + eapply LFS_step; [eassumption | apply IHHp; reflexivity].
Qed.

(* Janus gives one result, Y = 0, so the printed rules contradict their
   equivalence with the stack semantics (LNCS Lemma 1, arXiv Lemma 3). *)
Example e1_janus_one_result :
  exec Γe main1 s0 s0 /\ ~ exec Γe main1 s0 s1.
Proof.
  assert (H : exec Γe main1 s0 s0).
  { apply exec_iff_jstar.
    assert (E : run Γe 20%nat (CS_pre main1, s0) = (CS_post main1, s0))
      by (vm_compute; reflexivity).
    rewrite <- E. apply run_jstar. }
  split; [exact H |].
  intro H1. apply s0_neq_s1. exact (exec_deterministic H H1).
Qed.

(* The repaired LoopBase cannot leave towards entry(s2). *)
Example e1_fixed_no_escape :
  ~ lvf Γe main1 true (mkcfg s0 (RMain, PBlk [DDo]) (RMain, PT2 []) [lf1])
                      (mkcfg s0 (RMain, PT2 []) (RMain, PBlk [DLoop]) []).
Proof.
  intro H; inversion H; subst; unfold main1 in *; clean; try discriminate; congruence.
Qed.

(* ---- (E2) LoopMain:  from Y = 0 do skip loop skip until Y = 1 ----
   From Y = 0 the first iteration ends at l1 with Y = 0, so the entry
   assertion is true where it must be false: Janus is stuck.  The printed
   LoopMain re-enters the loop, and the step cannot be undone: the Loop
   Lemma (LNCS Lemma 2, arXiv Lemma 5) fails at this reachable
   configuration. *)
Definition main2 : @stmt 1 1 :=
  Sloop (Ebin Beq (Evar Y) (Econst 0)) Sskip Sskip (Ebin Beq (Evar Y) (Econst 1)).

Definition init2 : @lvcfg 1 1 1 := mkcfg s0 (RMain, PStart) (RMain, PT1 []) [].
Definition lf2 : frame := Floop2 (RMain, PT1 []) (RMain, PT2 []).
Definition c2 : @lvcfg 1 1 1 := mkcfg s0 (RMain, PBlk [DLoop]) (RMain, PT1 []) [lf2].
Definition c2' : @lvcfg 1 1 1 := mkcfg s0 (RMain, PT1 []) (RMain, PBlk [DDo]) [lf1; lf2].

Lemma e2_reachable : forall fixed, lvf_star Γe main2 fixed init2 c2.
Proof.
  intro fixed.
  eapply LFS_step.
  { apply (@LF_LoopMain 1 1 1 Γe main2 fixed s0 (RMain, PStart) RMain []
             (Ebin Beq (Evar Y) (Econst 0)) Sskip Sskip (Ebin Beq (Evar Y) (Econst 1)) []);
      [reflexivity | reflexivity |].
    intros _ H; discriminate H. }
  eapply LFS_step; [apply LF_Skip; [reflexivity | edge_flow] |].
  eapply LFS_step.
  { apply (@LF_Loop1 1 1 1 Γe main2 fixed s0 (RMain, PBlk [DDo]) RMain []
             (Ebin Beq (Evar Y) (Econst 0)) Sskip Sskip (Ebin Beq (Evar Y) (Econst 1)) []);
      reflexivity. }
  eapply LFS_step; [apply LF_Skip; [reflexivity | edge_flow] | apply LFS_refl].
Qed.

Example e2_printed_loop_lemma_fails :
  lvf_star Γe main2 false init2 c2 /\ lvf Γe main2 false c2 c2' /\ ~ lvb Γe main2 false c2' c2.
Proof.
  split; [apply e2_reachable |]. split.
  - apply (@LF_LoopMain 1 1 1 Γe main2 false s0 (RMain, PBlk [DLoop]) RMain []
             (Ebin Beq (Evar Y) (Econst 0)) Sskip Sskip (Ebin Beq (Evar Y) (Econst 1)) [lf2]);
      [reflexivity | reflexivity |].
    intro H; discriminate H.
  - intro H; inversion H; subst; unfold main2 in *; clean; try discriminate; congruence.
Qed.

(* Janus is stuck there, and so is the repaired machine. *)
Example e2_fixed_stuck :
  lvf_star Γe main2 true init2 c2 /\ (forall d, ~ lvf Γe main2 true c2 d)
  /\ step_fun Γe (CS_loop_loop (Ebin Beq (Evar Y) (Econst 0)) Sskip (CS_post Sskip)
                               (Ebin Beq (Evar Y) (Econst 1))) s0 = None.
Proof.
  split; [apply e2_reachable |]. split; [| vm_compute; reflexivity].
  intros d H; inversion H; subst; unfold main2 in *; clean; try discriminate.
  all: first
    [ match goal with
      | [ Hn : true = true -> _ <> _ |- _ ] => apply (Hn eq_refl); reflexivity
      end
    | match goal with
      | [ Ht : truth _ _ = Some false |- _ ] => vm_compute in Ht; discriminate Ht
      end ].
Qed.

(* ---- (E3) backward Skip:  Y += 1; skip ----
   From the final configuration the printed backward Skip may recover any
   last label; with l = start the backward run is stuck before it can undo
   Y += 1. *)
Definition main3 : @stmt 1 1 := Sseq (Sass Y Uadd (Econst 1)) Sskip.
Definition fin3 : @lvcfg 1 1 1 := mkcfg s1 (RMain, PBlk [DR]) (RMain, PStop) [].
Definition bad3 : @lvcfg 1 1 1 := mkcfg s1 (RMain, PStart) (RMain, PBlk [DR]) [].

Example e3_printed_backward_lost :
  lvb Γe main3 false fin3 bad3 /\ (forall d, ~ lvb Γe main3 false bad3 d).
Proof.
  split.
  - apply LB_Skip; [reflexivity | apply E_stop | intro H; discriminate H].
  - intros d H; inversion H; subst; simpl in *; discriminate.
Qed.

Example e3_fixed_rejects :
  ~ lvb Γe main3 true fin3 bad3.
Proof.
  intro H; inversion H; subst; try discriminate.
  match goal with
  | [ He : true = true -> edge _ _ (RMain, PStart) (RMain, PBlk [DR]) |- _ ] =>
      specialize (He eq_refl); inversion He; subst
  end.
  all: match goal with
       | [ Hf : flow _ PStart _ |- _ ] =>
           apply flow_paths in Hf; destruct Hf as [Hf _]; apply Hf; reflexivity
       end.
Qed.

End Errata.
(* ================================================================= *)
(* 5. From token positions to configurations                          *)
(* ================================================================= *)

Section Sim.
Context {nv na asize : nat}.

Local Notation stmt := (@janus.stmt nv na).
Local Notation store := (@janus.store nv na asize).
Local Notation penv := (@janus.penv nv na).
Local Notation cont_stmt := (@janus.cont_stmt nv na).
Local Notation lvcfg := (@lvcfg nv na asize).

Variables (Γ : penv) (main : stmt).

Local Notation rstmt := (rstmt Γ main).
Local Notation edge := (edge Γ main).

(* phi r P pred succ stk cs: the control <l, l', pi> of the configuration
   whose token sits at cs, where cs is the statement at path P of root r,
   pred is the label executed just before entering it, succ the label
   that follows it, and stk the stack of the enclosing constructs.  The
   last executed label and the stack are read off the context spine of
   the token, the next label off its position. *)
Fixpoint phi (r : root) (P : path) (pred succ : label) (stk : list frame)
             (cs : cont_stmt) : label * label * list frame :=
  match cs with
  | CS_pre st => (pred, (r, pfx P (entry_pt st)), stk)
  | CS_post st => ((r, pfx P (exit_pt st)), succ, stk)
  | CS_seq_L c s2 => phi r (P ++ [DL]) pred (r, pfx (P ++ [DR]) (entry_pt s2)) stk c
  | CS_seq_R s1 c => phi r (P ++ [DR]) (r, pfx (P ++ [DL]) (exit_pt s1)) succ stk c
  | CS_if_then _ c _ _ =>
      phi r (P ++ [DThen]) (r, PT1 P) (r, PT2 P) (Fift (r, PT1 P) (r, PT2 P) :: stk) c
  | CS_if_else _ _ c _ =>
      phi r (P ++ [DElse]) (r, PT1 P) (r, PT2 P) (Fiff (r, PT1 P) (r, PT2 P) :: stk) c
  | CS_loop_from _ s1 _ _ =>
      ((r, PT1 P), (r, pfx (P ++ [DDo]) (entry_pt s1)), Floop1 (r, PT1 P) (r, PT2 P) :: stk)
  | CS_loop_do _ c _ _ =>
      phi r (P ++ [DDo]) (r, PT1 P) (r, PT2 P) (Floop1 (r, PT1 P) (r, PT2 P) :: stk) c
  | CS_loop_until _ s1 _ _ =>
      ((r, pfx (P ++ [DDo]) (exit_pt s1)), (r, PT2 P), Floop1 (r, PT1 P) (r, PT2 P) :: stk)
  | CS_loop_loop _ _ c _ =>
      phi r (P ++ [DLoop]) (r, PT2 P) (r, PT1 P) (Floop2 (r, PT1 P) (r, PT2 P) :: stk) c
  | CS_call q _ c =>
      phi (RProc q) [] (RProc q, PStart) (RProc q, PStop) (Fcall (r, PBlk P) :: stk) c
  | CS_uncall q _ c =>
      phi (RInv q) [] (RInv q, PStart) (RInv q, PStop) (Funcall (r, PBlk P) :: stk) c
  | CS_local _ _ _ c _ => phi r P pred succ stk c          (* outside the fragment *)
  end.

Definition to_cfg (s : store) (t : label * label * list frame) : lvcfg :=
  let '(a, b, k) := t in mkcfg s a b k.

(* The whole program: the token in main, which runs from start to stop. *)
Definition Phi (cs : cont_stmt) (s : store) : lvcfg :=
  to_cfg s (phi RMain [] (RMain, PStart) (RMain, PStop) [] cs).

(* The fragment the two languages share: no local blocks, no arguments. *)
Inductive frag : stmt -> Prop :=
  | fr_skip : frag Sskip
  | fr_ass : forall x op e, frag (Sass x op e)
  | fr_aass : forall a e1 op e2, frag (Saass a e1 op e2)
  | fr_seq : forall a b, frag a -> frag b -> frag (Sseq a b)
  | fr_if : forall e1 a b e2, frag a -> frag b -> frag (Sif e1 a b e2)
  | fr_loop : forall e1 a b e2, frag a -> frag b -> frag (Sloop e1 a b e2)
  | fr_call : forall q, frag (Scall q [])
  | fr_uncall : forall q, frag (Suncall q []).

Definition lv_penv : Prop := forall q, formals (Γ q) = [] /\ frag (body (Γ q)).

(* Token positions in the fragment whose call frames run the procedure
   bodies (as every reachable position does, cs_ok_step below). *)
Inductive cs_ok : cont_stmt -> Prop :=
  | ok_pre : forall st, frag st -> cs_ok (CS_pre st)
  | ok_post : forall st, frag st -> cs_ok (CS_post st)
  | ok_seq_L : forall c b, cs_ok c -> frag b -> cs_ok (CS_seq_L c b)
  | ok_seq_R : forall a c, frag a -> cs_ok c -> cs_ok (CS_seq_R a c)
  | ok_if_then : forall e1 c b e2, cs_ok c -> frag b -> cs_ok (CS_if_then e1 c b e2)
  | ok_if_else : forall e1 a c e2, frag a -> cs_ok c -> cs_ok (CS_if_else e1 a c e2)
  | ok_loop_from : forall e1 a b e2, frag a -> frag b -> cs_ok (CS_loop_from e1 a b e2)
  | ok_loop_do : forall e1 c b e2, cs_ok c -> frag b -> cs_ok (CS_loop_do e1 c b e2)
  | ok_loop_until : forall e1 a b e2, frag a -> frag b -> cs_ok (CS_loop_until e1 a b e2)
  | ok_loop_loop : forall e1 a c e2, frag a -> cs_ok c -> cs_ok (CS_loop_loop e1 a c e2)
  | ok_call : forall q c, top c = body (Γ q) -> cs_ok c -> cs_ok (CS_call q [] c)
  | ok_uncall : forall q c, top c = inv (body (Γ q)) -> cs_ok c -> cs_ok (CS_uncall q [] c).

(* A label lies outside the subtree at path P of root r. *)
Definition outside (r : root) (P : path) (l : label) : Prop :=
  fst l <> r \/ forall q, path_of (snd l) <> Some (P ++ q).

(* The context of a token position agrees with the program: st is the
   statement at P, pred -> entry(st) and exit(st) -> succ are edges, and
   pred and succ lie outside st. *)
Record frame_ok (r : root) (P : path) (pred succ : label) (st : stmt) : Prop := {
  fo_node : node (rstmt r) P = Some st;
  fo_in : edge pred (r, pfx P (entry_pt st));
  fo_out : edge (r, pfx P (exit_pt st)) succ;
  fo_pred : outside r P pred;
  fo_succ : outside r P succ }.

(* ---- 5a. Paths ---- *)

Lemma pfx_app : forall P Q x, pfx P (pfx Q x) = pfx (P ++ Q) x.
Proof. intros P Q [p|p|p| |]; simpl; rewrite ?app_assoc; reflexivity. Qed.

Lemma pfx_nil : forall x, pfx [] x = x.
Proof. intros [p|p|p| |]; reflexivity. Qed.

Lemma node_app :
  forall P Q (st : stmt),
    node st (P ++ Q) = match node st P with Some t => node t Q | None => None end.
Proof.
  induction P as [|d P IH]; intros Q st; [reflexivity |].
  destruct d, st; simpl; try reflexivity; apply IH.
Qed.

Lemma node_snoc :
  forall P d (st t : stmt), node st P = Some t -> node st (P ++ [d]) = node t [d].
Proof. intros P d st t H. rewrite node_app, H. reflexivity. Qed.

Lemma flow_lift :
  forall P (st t : stmt) x y, node st P = Some t -> flow t x y -> flow st (pfx P x) (pfx P y).
Proof.
  induction P as [|d P IH]; intros st t x y Hn Hf.
  - simpl in Hn. injection Hn as ->. rewrite !pfx_nil. exact Hf.
  - change (d :: P) with ([d] ++ P). rewrite <- !pfx_app.
    destruct d, st; simpl in Hn; try discriminate; constructor; eapply IH; eassumption.
Qed.

Lemma edge_lift :
  forall r P t x y, node (rstmt r) P = Some t -> flow t x y -> edge (r, pfx P x) (r, pfx P y).
Proof. intros. apply E_flow. eapply flow_lift; eassumption. Qed.

Lemma outside_ext : forall r P Q l, outside r P l -> outside r (P ++ Q) l.
Proof.
  intros r P Q l [H | H]; [left; exact H | right; intros q Hq].
  apply (H (Q ++ q)). rewrite app_assoc. exact Hq.
Qed.

Lemma outside_sib :
  forall r P d d' x, d <> d' -> outside r (P ++ [d]) (r, pfx (P ++ [d']) x).
Proof.
  intros r P d d' x Hd. right. intros q Hq. simpl in Hq.
  rewrite path_of_pfx in Hq. destruct (path_of x) as [p|]; [| discriminate].
  injection Hq as Hq. rewrite <- !app_assoc in Hq. apply app_inv_head in Hq.
  injection Hq as Hq _. congruence.
Qed.

Lemma outside_up : forall r P d, outside r (P ++ [d]) (r, PT1 P) /\ outside r (P ++ [d]) (r, PT2 P).
Proof.
  intros r P d. split; right; intros q Hq; simpl in Hq; injection Hq as Hq;
    apply (f_equal (@length dir)) in Hq; rewrite !length_app in Hq; simpl in Hq; lia.
Qed.

Lemma outside_neq :
  forall r P l Q x, outside r P l -> path_of x <> None -> l <> (r, pfx (P ++ Q) x).
Proof.
  intros r P l Q x [H | H] Hx Heq; subst l; simpl in H; [congruence |].
  rewrite path_of_pfx in H. destruct (path_of x) as [p|] eqn:E; [| contradiction].
  apply (H (Q ++ p)). simpl. rewrite app_assoc. reflexivity.
Qed.

Lemma outside_root : forall r P q x, r <> q -> outside r P (q, x).
Proof. intros. left. simpl. congruence. Qed.

Lemma outside_nopath : forall r P l, path_of (snd l) = None -> outside r P l.
Proof. intros r P l H. right. intros q Hq. congruence. Qed.

(* ---- 5b. Frames of the sub-positions ---- *)

Lemma fo_root : forall r, frame_ok r [] (r, PStart) (r, PStop) (rstmt r).
Proof.
  intro r. constructor.
  - reflexivity.
  - rewrite pfx_nil. apply E_start.
  - rewrite pfx_nil. apply E_stop.
  - apply outside_nopath; reflexivity.
  - apply outside_nopath; reflexivity.
Qed.

Lemma fo_seq_L :
  forall r P pred succ a b, frame_ok r P pred succ (Sseq a b) ->
    frame_ok r (P ++ [DL]) pred (r, pfx (P ++ [DR]) (entry_pt b)) a.
Proof.
  intros r P pred succ a b [Hn Hi Ho Hp Hs]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - simpl in Hi. rewrite pfx_app in Hi. exact Hi.
  - rewrite <- !pfx_app. eapply edge_lift; [exact Hn | apply F_Seq].
  - apply outside_ext; exact Hp.
  - apply outside_sib; discriminate.
Qed.

Lemma fo_seq_R :
  forall r P pred succ a b, frame_ok r P pred succ (Sseq a b) ->
    frame_ok r (P ++ [DR]) (r, pfx (P ++ [DL]) (exit_pt a)) succ b.
Proof.
  intros r P pred succ a b [Hn Hi Ho Hp Hs]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - rewrite <- !pfx_app. eapply edge_lift; [exact Hn | apply F_Seq].
  - simpl in Ho. rewrite pfx_app in Ho. exact Ho.
  - apply outside_sib; discriminate.
  - apply outside_ext; exact Hs.
Qed.

(* The two labels of a conditional or loop at P. *)
Lemma pt1_at : forall P, pfx P (PT1 []) = PT1 P.
Proof. intro P. simpl. rewrite app_nil_r. reflexivity. Qed.
Lemma pt2_at : forall P, pfx P (PT2 []) = PT2 P.
Proof. intro P. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma fo_then :
  forall r P pred succ e1 a b e2, frame_ok r P pred succ (Sif e1 a b e2) ->
    frame_ok r (P ++ [DThen]) (r, PT1 P) (r, PT2 P) a.
Proof.
  intros r P pred succ e1 a b e2 [Hn _ _ _ _]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - rewrite <- (pt1_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_If_T1].
  - rewrite <- (pt2_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_If_T2].
  - apply outside_up.
  - apply outside_up.
Qed.

Lemma fo_else :
  forall r P pred succ e1 a b e2, frame_ok r P pred succ (Sif e1 a b e2) ->
    frame_ok r (P ++ [DElse]) (r, PT1 P) (r, PT2 P) b.
Proof.
  intros r P pred succ e1 a b e2 [Hn _ _ _ _]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - rewrite <- (pt1_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_If_E1].
  - rewrite <- (pt2_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_If_E2].
  - apply outside_up.
  - apply outside_up.
Qed.

Lemma fo_do :
  forall r P pred succ e1 a b e2, frame_ok r P pred succ (Sloop e1 a b e2) ->
    frame_ok r (P ++ [DDo]) (r, PT1 P) (r, PT2 P) a.
Proof.
  intros r P pred succ e1 a b e2 [Hn _ _ _ _]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - rewrite <- (pt1_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_Loop_1].
  - rewrite <- (pt2_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_Loop_2].
  - apply outside_up.
  - apply outside_up.
Qed.

Lemma fo_loop :
  forall r P pred succ e1 a b e2, frame_ok r P pred succ (Sloop e1 a b e2) ->
    frame_ok r (P ++ [DLoop]) (r, PT2 P) (r, PT1 P) b.
Proof.
  intros r P pred succ e1 a b e2 [Hn _ _ _ _]. constructor.
  - rewrite (node_snoc _ _ _ Hn). reflexivity.
  - rewrite <- (pt2_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_Loop_3].
  - rewrite <- (pt1_at P), <- pfx_app. eapply edge_lift; [exact Hn | apply F_Loop_4].
  - apply outside_up.
  - apply outside_up.
Qed.

(* ---- 5c. One token step is zero or one machine step ---- *)

Lemma inst_nil : lv_penv -> forall q, inst (Γ q) [] = body (Γ q).
Proof. intros H q. unfold inst. rewrite (proj1 (H q)). exact (rename_id _). Qed.

Lemma stmt_at_P :
  forall r P (st : stmt), node (rstmt r) P = Some st -> stmt_at Γ main (r, PBlk P) = Some st.
Proof. intros r P st H. exact H. Qed.

Lemma test2_at :
  forall r P e1 (a b : stmt) e2,
    node (rstmt r) P = Some (Sif e1 a b e2) \/ node (rstmt r) P = Some (Sloop e1 a b e2) ->
    test_at Γ main (r, PT1 P) = Some e1 /\ test_at Γ main (r, PT2 P) = Some e2.
Proof. intros r P e1 a b e2 [H | H]; unfold test_at; simpl; rewrite H; split; reflexivity. Qed.

Lemma frag_inv : forall st, frag st -> frag (inv st).
Proof. intros st H; induction H; simpl; constructor; assumption. Qed.

Ltac not_frag :=
  match goal with
  | [ H : cs_ok (CS_local _ _ _ _ _) |- _ ] => inversion H
  | [ H : cs_ok (CS_pre (Slocal _ _ _ _)) |- _ ] =>
      let H' := fresh in inversion H as [? H' | | | | | | | | | | |]; subst; inversion H'
  end.

(* The administrative token steps (sequence enter/mid/exit, loop do and
   do-done) leave the configuration unchanged; every other step is one
   step of the machine, as printed or repaired. *)
Theorem lv_fwd_sim :
  forall fixed, lv_penv ->
  forall cfg cfg', jstep Γ cfg cfg' ->
  forall r P pred succ stk,
    frame_ok r P pred succ (top (fst cfg)) -> cs_ok (fst cfg) ->
    (snd cfg = snd cfg' /\ phi r P pred succ stk (fst cfg) = phi r P pred succ stk (fst cfg'))
    \/ lvf Γ main fixed (to_cfg (snd cfg) (phi r P pred succ stk (fst cfg)))
                        (to_cfg (snd cfg') (phi r P pred succ stk (fst cfg'))).
Proof.
  intros fixed HΓ cfg cfg' H; induction H; intros r P pred succ stk Hf Hok; simpl in *;
    try not_frag.
  (* congruence rules: the inner position, in the inner frame *)
  all: try (apply IHjstep; inversion Hok; subst;
            first [ eapply fo_seq_L; eassumption | eapply fo_seq_R; eassumption
                  | eapply fo_then; eassumption | eapply fo_else; eassumption
                  | eapply fo_do; eassumption | eapply fo_loop; eassumption
                  | assumption
                  | match goal with
                    | [ Ht : top _ = _ |- _ ] => rewrite Ht; apply fo_root
                    end ]; fail).
  all: try (apply IHjstep; inversion Hok; subst; assumption; fail).
  all: destruct Hf as [Hn Hi Ho Hp Hs].
  (* administrative steps *)
  all: try (left; split; [reflexivity | rewrite ?pfx_app; reflexivity]; fail).
  all: right; simpl in Hi, Ho; rewrite ?app_nil_r in *.
  - apply LF_Skip; [apply stmt_at_P; exact Hn | exact Ho].
  - eapply LF_AssVar; [apply stmt_at_P; exact Hn | exact H | exact Ho].
  - eapply LF_IfTrue1; [exact Hn | exact H].
  - eapply LF_IfFalse1; [exact Hn | exact H].
  - eapply LF_IfTrue2; [unfold test_at; simpl; rewrite Hn; reflexivity | exact H | exact Ho].
  - eapply LF_IfFalse2; [unfold test_at; simpl; rewrite Hn; reflexivity | exact H | exact Ho].
  - eapply LF_LoopMain; [exact Hn | exact H |].
    intros _. apply outside_neq; [exact Hp | apply path_exit].
  - eapply LF_LoopBase; [exact Hn | exact H | exact Ho |].
    destruct fixed; (apply outside_neq; [exact Hs | apply path_entry]).
  - eapply LF_Loop1; [exact Hn | exact H].
  - eapply LF_Loop2; [exact Hn | exact H].
  - inversion Hok as [? Hfr | | | | | | | | | | |]; subst; inversion Hfr; subst.
    rewrite pfx_nil, (inst_nil HΓ).
    apply LF_Call; [apply stmt_at_P; exact Hn | exact (E_start Γ main (RProc p))].
  - inversion Hok; subst. apply LF_Return1. exact Ho.
  - inversion Hok as [? Hfr | | | | | | | | | | |]; subst; inversion Hfr; subst.
    rewrite pfx_nil, (inst_nil HΓ).
    apply LF_UnCall; [apply stmt_at_P; exact Hn | exact (E_start Γ main (RInv p))].
  - inversion Hok; subst. apply LF_Return2. exact Ho.
  - eapply LF_AssArr; [apply stmt_at_P; exact Hn | eassumption | eassumption | eassumption | exact Ho].
Qed.

(* Forms of the backward assignment rules whose recovered store is given
   by an equation. *)
Lemma lb_assvar :
  forall fixed (s s0 : store) l l' l'' x op e v π,
    stmt_at Γ main l' = Some (Sass x op e) -> eval s e = Some v -> edge l' l'' ->
    (fixed = true -> edge l l') -> s0 = update s x (apply_upd (inv_upd op) (s x) v) ->
    lvb Γ main fixed (mkcfg s l' l'' π) (mkcfg s0 l l' π).
Proof. intros; subst; eapply LB_AssVar; eassumption. Qed.

Lemma lb_assarr :
  forall fixed (s s0 : store) l l' l'' a e1 op e2 z i w π,
    stmt_at Γ main l' = Some (Saass a e1 op e2) ->
    eval s e1 = Some z -> idx z = Some i -> eval s e2 = Some w -> edge l' l'' ->
    (fixed = true -> edge l l') ->
    s0 = aupdate s a i (apply_upd (inv_upd op) (aget s a i) w) ->
    lvb Γ main fixed (mkcfg s l' l'' π) (mkcfg s0 l l' π).
Proof. intros; subst; eapply LB_AssArr; eassumption. Qed.

(* Each non-administrative token step, read backwards, is one backward
   step of the machine (as printed or repaired).  Well-formedness is
   needed where inv_step_reverses needs it: to recover the store. *)
Theorem lv_bwd_sim :
  forall fixed, lv_penv ->
  forall cfg cfg', jstep Γ cfg cfg' ->
  forall r P pred succ stk,
    frame_ok r P pred succ (top (fst cfg)) -> cs_ok (fst cfg) -> wf_cs (fst cfg) ->
    (snd cfg = snd cfg' /\ phi r P pred succ stk (fst cfg) = phi r P pred succ stk (fst cfg'))
    \/ lvb Γ main fixed (to_cfg (snd cfg') (phi r P pred succ stk (fst cfg')))
                        (to_cfg (snd cfg) (phi r P pred succ stk (fst cfg))).
Proof.
  intros fixed HΓ cfg cfg' H; induction H; intros r P pred succ stk Hf Hok Hwf; simpl in *;
    try not_frag.
  all: try (apply IHjstep; inversion Hok; subst; inversion Hwf; subst;
            first [ eapply fo_seq_L; eassumption | eapply fo_seq_R; eassumption
                  | eapply fo_then; eassumption | eapply fo_else; eassumption
                  | eapply fo_do; eassumption | eapply fo_loop; eassumption
                  | assumption
                  | match goal with
                    | [ Ht : top _ = _ |- _ ] => rewrite Ht; apply fo_root
                    end ]; fail).
  all: try (apply IHjstep; inversion Hok; subst; inversion Hwf; subst; assumption; fail).
  all: destruct Hf as [Hn Hi Ho Hp Hs].
  all: try (left; split; [reflexivity | rewrite ?pfx_app; reflexivity]; fail).
  all: right; simpl in Hi, Ho; rewrite ?app_nil_r in *.
  - apply LB_Skip; [apply stmt_at_P; exact Hn | exact Ho | intros _; exact Hi].
  - inversion Hwf as [? Hw | | | | | | | | | | | |]; subst; inversion Hw; subst.
    eapply lb_assvar; [apply stmt_at_P; exact Hn | | exact Ho | intros _; exact Hi |].
    + rewrite eval_update_invariant by assumption. exact H.
    + rewrite update_eq, apply_upd_inv, update_cancel. reflexivity.
  - eapply LB_IfTrue1; [unfold test_at; simpl; rewrite Hn; reflexivity | exact H | exact Hi].
  - eapply LB_IfFalse1; [unfold test_at; simpl; rewrite Hn; reflexivity | exact H | exact Hi].
  - eapply LB_IfTrue2; [exact Hn | exact H].
  - eapply LB_IfFalse2; [exact Hn | exact H].
  - eapply LB_LoopMain; [exact Hn | exact H | exact Hi |].
    apply outside_neq; [exact Hp | apply path_exit].
  - eapply LB_LoopBase; [exact Hn | exact H].
  - eapply LB_Loop1; [exact Hn | exact H].
  - eapply LB_Loop2; [exact Hn | exact H].
  - inversion Hok as [? Hfr | | | | | | | | | | |]; subst; inversion Hfr; subst.
    rewrite pfx_nil, (inst_nil HΓ).
    apply LB_Call; [reflexivity | exact Hi].
  - inversion Hok; subst. rewrite pfx_nil, (inst_nil HΓ).
    apply LB_Return1; [apply stmt_at_P; exact Hn | exact (E_stop Γ main (RProc p))].
  - inversion Hok as [? Hfr | | | | | | | | | | |]; subst; inversion Hfr; subst.
    rewrite pfx_nil, (inst_nil HΓ).
    apply LB_UnCall; [reflexivity | exact Hi].
  - inversion Hok; subst. rewrite pfx_nil, (inst_nil HΓ).
    apply LB_Return2; [apply stmt_at_P; exact Hn | exact (E_stop Γ main (RInv p))].
  - inversion Hwf as [? Hw | | | | | | | | | | | |]; subst; inversion Hw; subst.
    eapply lb_assarr; [apply stmt_at_P; exact Hn | | eassumption | | exact Ho
                      | intros _; exact Hi |].
    + rewrite eval_aupdate_invariant by assumption. eassumption.
    + rewrite eval_aupdate_invariant by assumption. eassumption.
    + rewrite aget_aupdate_eq, apply_upd_inv, aupdate_cancel. reflexivity.
Qed.

(* ---- 5d. Runs ---- *)

Local Hint Constructors cs_ok frag : core.

Lemma cs_ok_step :
  lv_penv -> forall cfg cfg', @jstep nv na asize Γ cfg cfg' -> cs_ok (fst cfg) -> cs_ok (fst cfg').
Proof.
  intros HΓ cfg cfg' H; induction H; intros Hok; simpl in *; inversion Hok; subst;
    repeat match goal with
           | [ Hf : frag (Sseq _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Sif _ _ _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Sloop _ _ _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Scall _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Suncall _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hc : cs_ok (CS_post _) |- _ ] => inversion Hc; subst; clear Hc
           end;
    try (constructor; auto; fail).
  all: try match goal with [ Hf : frag (Slocal _ _ _ _) |- _ ] => inversion Hf end.
  all: try (constructor; [rewrite (top_step H); assumption | auto]; fail).
  all: try (constructor; constructor; fail).
  all: try (constructor; [simpl; apply inst_nil; exact HΓ
                         | constructor; rewrite inst_nil by exact HΓ; apply HΓ]; fail).
  all: try (constructor; [simpl; rewrite inst_nil by exact HΓ; reflexivity
                         | constructor; rewrite inst_nil by exact HΓ; apply frag_inv, HΓ]; fail).
Qed.

Inductive lvb_star (fixed : bool) : lvcfg -> lvcfg -> Prop :=
  | LBS_refl : forall c, lvb_star fixed c c
  | LBS_step : forall c1 c2 c3, lvb Γ main fixed c1 c2 -> lvb_star fixed c2 c3 -> lvb_star fixed c1 c3.

Lemma lvb_star_trans :
  forall fixed c1 c2 c3, lvb_star fixed c1 c2 -> lvb_star fixed c2 c3 -> lvb_star fixed c1 c3.
Proof. intros fixed c1 c2 c3 H; induction H; intros; [assumption | econstructor; eauto]. Qed.

(* A run of the token semantics of main is a run of the machine forwards,
   and the machine runs it backwards to where it started. *)
Theorem lv_run :
  forall fixed, lv_penv -> wf_penv Γ ->
  forall c c', jstar Γ c c' ->
    top (fst c) = main -> cs_ok (fst c) -> wf_cs (fst c) ->
    lvf_star Γ main fixed (Phi (fst c) (snd c)) (Phi (fst c') (snd c'))
    /\ lvb_star fixed (Phi (fst c') (snd c')) (Phi (fst c) (snd c)).
Proof.
  intros fixed HΓ HΓw c c' H; induction H as [c | c1 c2 c3 H12 H23 IH];
    intros Htop Hok Hwf; [split; constructor |].
  destruct c1 as [cs1 s1], c2 as [cs2 s2]; simpl in *.
  assert (Hf : frame_ok RMain [] (RMain, PStart) (RMain, PStop) (top cs1))
    by (rewrite Htop; apply (fo_root RMain)).
  destruct IH as [IHf IHb].
  - rewrite (top_step H12). exact Htop.
  - exact (cs_ok_step HΓ H12 Hok).
  - exact (wf_cs_step_preserved HΓw H12 Hwf).
  - unfold Phi in *.
    destruct (lv_fwd_sim fixed HΓ H12 [] Hf Hok) as [[Es Ep] | Hs];
    destruct (lv_bwd_sim fixed HΓ H12 [] Hf Hok Hwf) as [[Es' Ep'] | Hb]; simpl in *.
    + subst. rewrite Ep. split; assumption.
    + subst. rewrite Ep. split; assumption.
    + subst. rewrite <- Ep' in IHf. split; [| rewrite Ep'; assumption].
      rewrite Ep' in Hs. simpl in Hs. exact IHf.
    + split; [econstructor; eassumption |].
      eapply lvb_star_trans; [exact IHb | econstructor; [exact Hb | constructor]].
Qed.

(* In particular, every big-step execution of main is a run of the machine
   from <s, start, entry(main), []> to <s', exit(main), stop, []>, and back:
   their Lemma 1 (LNCS; arXiv Lemma 3), "only if" direction, from any
   store, together with its backward counterpart. *)
Corollary exec_lv :
  forall fixed, lv_penv -> wf_penv Γ -> frag main -> wf_stmt main ->
  forall s s', exec Γ main s s' ->
    lvf_star Γ main fixed (mkcfg s (RMain, PStart) (RMain, entry_pt main) [])
                          (mkcfg s' (RMain, exit_pt main) (RMain, PStop) [])
    /\ lvb_star fixed (mkcfg s' (RMain, exit_pt main) (RMain, PStop) [])
                      (mkcfg s (RMain, PStart) (RMain, entry_pt main) []).
Proof.
  intros fixed HΓ HΓw Hfr Hwf s s' H.
  apply exec_iff_jstar in H.
  pose proof (lv_run fixed HΓ HΓw H eq_refl (ok_pre Hfr) (wf_cs_pre Hwf)) as R.
  unfold Phi in R; simpl in R. rewrite !pfx_nil in R. exact R.
Qed.

End Sim.

(* ================================================================= *)
(* 7. The converse: every step of the repaired machine is matched     *)
(* ================================================================= *)

Section Complete.
Context {nv na asize : nat}.

Local Notation stmt := (@janus.stmt nv na).
Local Notation store := (@janus.store nv na asize).
Local Notation penv := (@janus.penv nv na).
Local Notation cont_stmt := (@janus.cont_stmt nv na).
Local Notation lvcfg := (@lvcfg nv na asize).

Variables (Γ : penv) (main : stmt).

Local Notation rstmt := (rstmt Γ main).
Local Notation edge := (edge Γ main).
Local Notation phi := (phi (nv := nv) (na := na)).

(* ---- 7a. Frames reached from a root, and the edges out of them ---- *)

(* The frames of phi: a root, and the six descents into sub-statements. *)
Inductive freach : root -> path -> label -> label -> stmt -> Prop :=
  | FR_root : forall r, freach r [] (r, PStart) (r, PStop) (rstmt r)
  | FR_seq_L : forall r P pred succ a b, freach r P pred succ (Sseq a b) ->
      freach r (P ++ [DL]) pred (r, pfx (P ++ [DR]) (entry_pt b)) a
  | FR_seq_R : forall r P pred succ a b, freach r P pred succ (Sseq a b) ->
      freach r (P ++ [DR]) (r, pfx (P ++ [DL]) (exit_pt a)) succ b
  | FR_then : forall r P pred succ e1 a b e2, freach r P pred succ (Sif e1 a b e2) ->
      freach r (P ++ [DThen]) (r, PT1 P) (r, PT2 P) a
  | FR_else : forall r P pred succ e1 a b e2, freach r P pred succ (Sif e1 a b e2) ->
      freach r (P ++ [DElse]) (r, PT1 P) (r, PT2 P) b
  | FR_do : forall r P pred succ e1 a b e2, freach r P pred succ (Sloop e1 a b e2) ->
      freach r (P ++ [DDo]) (r, PT1 P) (r, PT2 P) a
  | FR_loop : forall r P pred succ e1 a b e2, freach r P pred succ (Sloop e1 a b e2) ->
      freach r (P ++ [DLoop]) (r, PT2 P) (r, PT1 P) b.

Lemma freach_ok : forall r P pred succ st, freach r P pred succ st -> frame_ok Γ main r P pred succ st.
Proof.
  intros r P pred succ st H; induction H.
  - apply fo_root.
  - eapply fo_seq_L; eassumption.
  - eapply fo_seq_R; eassumption.
  - eapply fo_then; eassumption.
  - eapply fo_else; eassumption.
  - eapply fo_do; eassumption.
  - eapply fo_loop; eassumption.
Qed.

Lemma pfx_cons_inj :
  forall d d' x x', path_of x <> None -> pfx [d] x = pfx [d'] x' -> d = d' /\ x = x'.
Proof.
  intros d d' [p|p|p| |] [p'|p'|p'| |] Hx H; simpl in *; try discriminate;
    try (exfalso; apply Hx; reflexivity); injection H as -> ->; split; reflexivity.
Qed.

Lemma pfx_cons_root :
  forall d x, path_of x <> None -> pfx [d] x <> PT1 [] /\ pfx [d] x <> PT2 [].
Proof. intros d [p|p|p| |] Hx; simpl in *; split; try discriminate; exfalso; apply Hx; reflexivity. Qed.

(* Inversion of flow at a point inside a sub-statement. *)
Ltac pth :=
  first [ apply path_exit | apply path_entry | assumption
        | match goal with
          | [ F : flow _ ?x _ |- path_of ?x <> None ] => exact (proj1 (flow_paths F))
          end ].

Ltac peq :=
  match goal with
  | [ E : pfx [_] _ = pfx [_] _ |- _ ] =>
      apply pfx_cons_inj in E;
      [ let E1 := fresh in let E2 := fresh in
        destruct E as [E1 E2]; try discriminate E1; subst
      | pth ]
  end.

Ltac ptc :=
  match goal with
  | [ E : PT1 [] = pfx _ ?x |- _ ] => destruct x; simpl in E; discriminate
  | [ E : PT2 [] = pfx _ ?x |- _ ] => destruct x; simpl in E; discriminate
  | [ E : pfx _ ?x = PT1 [] |- _ ] => destruct x; simpl in E; discriminate
  | [ E : pfx _ ?x = PT2 [] |- _ ] => destruct x; simpl in E; discriminate
  end.

Ltac flow_sub H :=
  inversion H; subst; try ptc; try peq;
  first [ left; split; reflexivity
        | right; eexists; split; [reflexivity | assumption] ].

Lemma flow_seq_L :
  forall (a b : stmt) x0 y0, path_of x0 <> None -> flow (Sseq a b) (pfx [DL] x0) y0 ->
    (x0 = exit_pt a /\ y0 = pfx [DR] (entry_pt b)) \/ (exists y1, y0 = pfx [DL] y1 /\ flow a x0 y1).
Proof. intros a b x0 y0 Hx H. flow_sub H. Qed.

Lemma flow_seq_R :
  forall (a b : stmt) x0 y0, path_of x0 <> None -> flow (Sseq a b) (pfx [DR] x0) y0 ->
    False \/ (exists y1, y0 = pfx [DR] y1 /\ flow b x0 y1).
Proof. intros a b x0 y0 Hx H. flow_sub H. Qed.

Lemma flow_then :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sif e1 a b e2) (pfx [DThen] x0) y0 ->
    (x0 = exit_pt a /\ y0 = PT2 []) \/ (exists y1, y0 = pfx [DThen] y1 /\ flow a x0 y1).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub H. Qed.

Lemma flow_else :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sif e1 a b e2) (pfx [DElse] x0) y0 ->
    (x0 = exit_pt b /\ y0 = PT2 []) \/ (exists y1, y0 = pfx [DElse] y1 /\ flow b x0 y1).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub H. Qed.

Lemma flow_do :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sloop e1 a b e2) (pfx [DDo] x0) y0 ->
    (x0 = exit_pt a /\ y0 = PT2 []) \/ (exists y1, y0 = pfx [DDo] y1 /\ flow a x0 y1).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub H. Qed.

Lemma flow_loop :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sloop e1 a b e2) (pfx [DLoop] x0) y0 ->
    (x0 = exit_pt b /\ y0 = PT1 []) \/ (exists y1, y0 = pfx [DLoop] y1 /\ flow b x0 y1).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub H. Qed.

Lemma path_pfx_cons : forall d x, path_of x <> None -> path_of (pfx [d] x) <> None.
Proof. intros d [p|p|p| |] H; simpl; try discriminate; exact H. Qed.

(* Out of a point of the statement at a reached frame, an edge of the
   root either is a flow edge of that statement, or leaves its exit
   towards succ. *)
Lemma edge_under :
  forall r P pred succ st, freach r P pred succ st ->
  forall x0 y, path_of x0 <> None -> edge (r, pfx P x0) y ->
    (exists y0, y = (r, pfx P y0) /\ flow st x0 y0) \/ (x0 = exit_pt st /\ y = succ).
Proof.
  intros r P pred succ st H; induction H; intros x0 y Hx He.
  1: { rewrite pfx_nil in He. inversion He; subst.
       - left. exists y0. rewrite pfx_nil. split; [reflexivity | assumption].
       - exfalso. apply Hx. reflexivity.
       - right. split; reflexivity. }
  (* the six descents: ask the parent frame about pfx [d] x0 *)
  all: rewrite <- pfx_app in He;
       destruct (IHfreach _ _ (path_pfx_cons _ _ Hx) He) as [[y0 [-> Hf]] | [Hex ->]].
  - destruct (flow_seq_L _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pfx_app. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hex. apply pfx_cons_inj in Hex; [destruct Hex as [Hd _]; discriminate Hd | exact Hx].
  - destruct (flow_seq_R _ Hx Hf) as [[] | [y1 [-> Hf1]]].
    left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - simpl in Hex. apply pfx_cons_inj in Hex; [destruct Hex as [_ ->] | exact Hx].
    right. split; reflexivity.
  - destruct (flow_then _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt2_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hex. exact (proj2 (pfx_cons_root DThen _ Hx) Hex).
  - destruct (flow_else _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt2_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hex. exact (proj2 (pfx_cons_root DElse _ Hx) Hex).
  - destruct (flow_do _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt2_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hex. exact (proj2 (pfx_cons_root DDo _ Hx) Hex).
  - destruct (flow_loop _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt1_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hex. exact (proj2 (pfx_cons_root DLoop _ Hx) Hex).
Qed.

(* The successor of an exit is succ, except the internal edge from the
   until-point of a loop to its loop body. *)
Lemma exit_succ_blk :
  forall r P pred succ st, freach r P pred succ st -> exit_pt st = PBlk [] ->
  forall y, edge (r, pfx P (PBlk [])) y -> y = succ.
Proof.
  intros r P pred succ st H Hst y He. rewrite <- Hst in He.
  destruct (edge_under H _ (path_exit st) He) as [[y0 [_ Hf]] | [_ ->]]; [| reflexivity].
  exfalso. rewrite Hst in Hf.
  destruct st; simpl in Hst; try discriminate.
  all: try (inversion Hf; fail).
  all: destruct (exit_pt st2); simpl in Hst; discriminate.
Qed.

Lemma exit_succ_if :
  forall r P pred succ e1 a b e2, freach r P pred succ (Sif e1 a b e2) ->
  forall y, edge (r, pfx P (PT2 [])) y -> y = succ.
Proof.
  intros r P pred succ e1 a b e2 H y He.
  destruct (edge_under H (PT2 []) ltac:(discriminate) He) as [[y0 [_ Hf]] | [_ ->]]; [| reflexivity].
  exfalso. inversion Hf; subst; ptc.
Qed.

Lemma exit_succ_loop :
  forall r P pred succ e1 a b e2, freach r P pred succ (Sloop e1 a b e2) ->
  forall y, edge (r, pfx P (PT2 [])) y -> y = succ \/ y = (r, pfx (P ++ [DLoop]) (entry_pt b)).
Proof.
  intros r P pred succ e1 a b e2 H y He.
  destruct (edge_under H (PT2 []) ltac:(discriminate) He) as [[y0 [-> Hf]] | [_ ->]];
    [| left; reflexivity].
  right. inversion Hf; subst; try ptc. rewrite pfx_app. reflexivity.
Qed.

(* Out of start, the only edge goes to the entry of the root. *)
Lemma start_succ : forall r y, edge (r, PStart) y -> y = (r, entry_pt (rstmt r)).
Proof.
  intros r y He. inversion He; subst; [| reflexivity |].
  - exfalso. match goal with [ F : flow _ PStart _ |- _ ] => apply (proj1 (flow_paths F)); reflexivity end.
  - exfalso. match goal with [ E : exit_pt _ = PStart |- _ ] => eapply path_exit; rewrite E; reflexivity end.
Qed.

End Complete.





(* ================================================================= *)
(* 6. Axiom audit                                                     *)
(* ================================================================= *)

(* tools/audit.sh (SRC=janus/lv.v) checks that this block lists every
   result and that each prints "Closed under the global context". *)
Print Assumptions path_of_pfx.
Print Assumptions path_entry.
Print Assumptions path_exit.
Print Assumptions flow_paths.
Print Assumptions s0_neq_s1.
Print Assumptions e1_prefix.
Print Assumptions e1_exit.
Print Assumptions e1_escape.
Print Assumptions e1_printed_two_results.
Print Assumptions e1_janus_one_result.
Print Assumptions e1_fixed_no_escape.
Print Assumptions e2_reachable.
Print Assumptions e2_printed_loop_lemma_fails.
Print Assumptions e2_fixed_stuck.
Print Assumptions e3_printed_backward_lost.
Print Assumptions e3_fixed_rejects.
Print Assumptions pfx_app.
Print Assumptions pfx_nil.
Print Assumptions node_app.
Print Assumptions node_snoc.
Print Assumptions flow_lift.
Print Assumptions edge_lift.
Print Assumptions outside_ext.
Print Assumptions outside_sib.
Print Assumptions outside_up.
Print Assumptions outside_neq.
Print Assumptions outside_root.
Print Assumptions outside_nopath.
Print Assumptions fo_root.
Print Assumptions fo_seq_L.
Print Assumptions fo_seq_R.
Print Assumptions pt1_at.
Print Assumptions pt2_at.
Print Assumptions fo_then.
Print Assumptions fo_else.
Print Assumptions fo_do.
Print Assumptions fo_loop.
Print Assumptions inst_nil.
Print Assumptions stmt_at_P.
Print Assumptions test2_at.
Print Assumptions frag_inv.
Print Assumptions lv_fwd_sim.
Print Assumptions lb_assvar.
Print Assumptions lb_assarr.
Print Assumptions lv_bwd_sim.
Print Assumptions cs_ok_step.
Print Assumptions lvb_star_trans.
Print Assumptions lv_run.
Print Assumptions exec_lv.
