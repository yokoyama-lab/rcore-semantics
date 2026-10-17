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
