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

  Results.  Section 5: every token step is zero or one step of the
  machine, forwards (lv_fwd_sim) and backwards (lv_bwd_sim), for the
  printed and the repaired rules.  Section 7: conversely, every step of
  the repaired machine from the configuration of a token is matched by
  token steps (lv_complete_step, lv_complete_run), so that their Lemma 1
  holds in both directions and from any store (lv_lemma1); the proof uses
  the repairs of E1 and E2 (make janus-mutants).

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
   Lemma (LNCS Lemma 3, arXiv Lemma 5) fails at this reachable
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

(* ---- (E4) the Loop Lemma, right to left:  if 1 then skip else skip fi 1 ----
   Their Loop Lemma assumes only that the left-hand configuration c is
   reachable.  Backward IfTrue2 does not constrain the next label of its
   source, so a configuration c' with a label that no edge reaches steps
   back to the reachable c, but c does not step forwards to c'.  This holds
   for the repaired rules too; the statement needs c' reachable as well
   (lv_loop_lemma below). *)
Definition main4 : @stmt 1 1 := Sif (Econst 1) Sskip Sskip (Econst 1).
Definition c4 : @lvcfg 1 1 1 :=
  mkcfg s0 (RMain, PBlk [DThen]) (RMain, PT2 []) [Fift (RMain, PT1 []) (RMain, PT2 [])].
Definition c4' : @lvcfg 1 1 1 := mkcfg s0 (RMain, PT2 []) (RMain, PStart) [].

Example e4_loop_lemma_needs_both_reachable :
  forall fixed,
    lvf_star Γe main4 fixed (mkcfg s0 (RMain, PStart) (RMain, PT1 []) []) c4
    /\ lvb Γe main4 fixed c4' c4 /\ ~ lvf Γe main4 fixed c4 c4'.
Proof.
  intro fixed. split; [| split].
  - eapply LFS_step.
    { apply (@LF_IfTrue1 1 1 1 Γe main4 fixed s0 (RMain, PStart) RMain [] (Econst 1)
               Sskip Sskip (Econst 1) []); reflexivity. }
    eapply LFS_step; [apply LF_Skip; [reflexivity | edge_flow] | apply LFS_refl].
  - apply (@LB_IfTrue2 1 1 1 Γe main4 fixed s0 RMain [] (Econst 1) Sskip Sskip (Econst 1)
             (RMain, PStart) []); reflexivity.
  - intro H; inversion H; subst; unfold main4 in *; clean; try discriminate.
    match goal with
    | [ He : edge _ _ (RMain, PT2 []) (RMain, PStart) |- _ ] => inversion He; subst
    end.
    match goal with
    | [ Hf : flow _ _ PStart |- _ ] =>
        apply flow_paths in Hf; destruct Hf as [_ Hf]; apply Hf; reflexivity
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
          | [ F : flow _ _ ?x |- path_of ?x <> None ] => exact (proj2 (flow_paths F))
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

(* ---- 7b. Invariants of the stack and of the token ---- *)

(* The frames above the topmost call/uncall element belong to enclosing
   constructs: their labels lie outside the current statement. *)
Fixpoint stk_ok (r : root) (P : path) (stk : list frame) : Prop :=
  match stk with
  | [] => True
  | Fcall _ :: _ | Funcall _ :: _ => True
  | Fift l1 l2 :: rest | Fiff l1 l2 :: rest | Floop1 l1 l2 :: rest | Floop2 l1 l2 :: rest =>
      outside r P l1 /\ outside r P l2 /\ stk_ok r P rest
  end.

Lemma stk_ok_ext : forall r P Q stk, stk_ok r P stk -> stk_ok r (P ++ Q) stk.
Proof.
  intros r P Q stk; induction stk as [|f stk IH]; [trivial |].
  destruct f; simpl; try tauto;
    intros [H1 [H2 H3]]; repeat split; try apply outside_ext; auto.
Qed.

Lemma stk_ok_push :
  forall r P d stk (F : label -> label -> frame),
    (forall l1 l2, F l1 l2 = Fift l1 l2 \/ F l1 l2 = Fiff l1 l2
                   \/ F l1 l2 = Floop1 l1 l2 \/ F l1 l2 = Floop2 l1 l2) ->
    stk_ok r P stk -> stk_ok r (P ++ [d]) (F (r, PT1 P) (r, PT2 P) :: stk).
Proof.
  intros r P d stk F HF H.
  destruct (outside_up r P d) as [O1 O2].
  destruct (HF (r, PT1 P) (r, PT2 P)) as [E | [E | [E | E]]]; rewrite E; simpl;
    repeat split; try assumption; apply stk_ok_ext; exact H.
Qed.

Lemma not_outside :
  forall r P x q, path_of x = Some (P ++ q) -> ~ outside r P (r, x).
Proof. intros r P x q Hx [H | H]; [apply H; reflexivity | apply (H q); exact Hx]. Qed.

Inductive at_exit : cont_stmt -> Prop :=
  | AE_post : forall st, at_exit (CS_post st)
  | AE_seq_R : forall a c, at_exit c -> at_exit (CS_seq_R a c).

Lemma at_exit_dec : forall c, {at_exit c} + {~ at_exit c}.
Proof.
  induction c; try (right; intro H; inversion H; fail).
  - left; constructor.
  - destruct IHc; [left; constructor; assumption | right; intro H; inversion H; contradiction].
Defined.

Lemma lift_star :
  forall (F : cont_stmt -> cont_stmt),
    (forall c (s : store) c' s', jstep Γ (c, s) (c', s') -> jstep Γ (F c, s) (F c', s')) ->
    forall c (s : store) c' s', jstar Γ (c, s) (c', s') -> jstar Γ (F c, s) (F c', s').
Proof. intros F HF c s c' s' H. exact (jstar_lift F HF H). Qed.

Ltac lift C H :=
  apply (lift_star C) in H; [| intros; constructor; assumption].

(* A token at an exit reaches CS_post of its statement by administrative
   steps, which do not move the configuration. *)
Lemma exit_norm :
  forall c, at_exit c -> forall (s : store),
    jstar Γ (c, s) (CS_post (top c), s)
    /\ forall r P pred succ stk, phi r P pred succ stk c = phi r P pred succ stk (CS_post (top c)).
Proof.
  intros c H; induction H; intro s; [split; [apply JS_refl | reflexivity] |].
  destruct (IHat_exit s) as [Hj Hp]. split.
  - lift (fun x : cont_stmt => CS_seq_R a x) Hj.
    eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Seq_Exit].
  - intros r P pred succ stk. simpl. rewrite Hp. simpl. rewrite pfx_app. reflexivity.
Qed.

Lemma call_ok_nil : lv_penv Γ -> forall q, call_ok (Γ q) [] = true.
Proof.
  intros H q. unfold call_ok. rewrite (proj1 (H q)). simpl. exact (inj_onb_id _).
Qed.

(* ---- 7c. From a step of the machine back to token steps ---- *)

Ltac kill_lv Hn Hstk :=
  unfold stmt_at, test_at in *; simpl in *;
  repeat match goal with
         | [ E : node _ (_ ++ []) = _ |- _ ] => rewrite app_nil_r in E
         | [ E : context [match node _ (_ ++ []) with _ => _ end] |- _ ] => rewrite app_nil_r in E
         end;
  try (rewrite Hn in *; simpl in *);
  repeat match goal with
         | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
         | [ H : _ /\ _ |- _ ] => destruct H
         end;
  try congruence;
  try (exfalso;
       match goal with
       | [ Ho : outside _ _ (_, _) |- _ ] =>
           destruct Ho as [Ho | Ho]; [apply Ho; reflexivity | apply (Ho []); simpl; reflexivity]
       end).

Lemma complete_pre :
  lv_penv Γ -> forall (st : stmt) r P pred succ stk (s : store) d,
    freach r P pred succ st -> stk_ok r P stk -> frag st ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk (CS_pre st))) d ->
    exists c' s', jstar Γ (CS_pre st, s) (c', s') /\ to_cfg s' (phi r P pred succ stk c') = d.
Proof.
  intros HΓ st; induction st; intros r P pred succ stk s d Hr Hstk Hfr Hlv;
    pose proof (fo_node (freach_ok Hr)) as Hn; simpl in Hlv.
  (* skip, assignment, array assignment: one step to the exit *)
  1-2, 9: inversion Hlv; subst; kill_lv Hn Hstk;
    try (exfalso; inversion Hfr; fail);
    (eexists; eexists; split;
     [ apply jstar_one; econstructor; eassumption
     | simpl; match goal with
              | [ He : edge (_, PBlk (_ ++ [])) ?l |- _ ] =>
                  rewrite (exit_succ_blk Hr eq_refl He); reflexivity
              end ]).
  - (* sequence: enter, then the first statement *)
    inversion Hfr; subst. rewrite pfx_app in Hlv.
    destruct (IHst1 _ _ _ _ _ _ _ (FR_seq_L Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hlv)
      as [c' [s' [Hj Hp]]].
    exists (CS_seq_L c' st2), s'. split; [| exact Hp].
    lift (fun x : cont_stmt => CS_seq_L x st2) Hj.
    eapply JS_step; [apply J_Seq_Enter | exact Hj].
  - (* conditional: the test *)
    inversion Hlv; subst; kill_lv Hn Hstk.
    all: eexists; exists s; split;
      [ apply jstar_one; first [ apply J_If_True; assumption | apply J_If_False; assumption ]
      | simpl; rewrite ?app_nil_r; reflexivity ].
  - (* loop: the entry assertion *)
    inversion Hlv; subst; kill_lv Hn Hstk.
    all: eexists; exists s; split;
      [ apply jstar_one; apply J_Loop_Enter; assumption
      | simpl; rewrite ?app_nil_r; reflexivity ].
  - (* call *)
    inversion Hfr; subst. inversion Hlv; subst; kill_lv Hn Hstk.
    all: exists (CS_call q [] (CS_pre (inst (Γ q) []))), s; split;
      [ apply jstar_one; apply J_Call_Enter; apply call_ok_nil; exact HΓ | ].
    all: match goal with
         | [ He : edge (_, PStart) _ |- _ ] => rewrite (start_succ He)
         end.
    all: simpl; rewrite pfx_nil, (inst_nil HΓ), ?app_nil_r; reflexivity.
  - (* uncall *)
    inversion Hfr; subst. inversion Hlv; subst; kill_lv Hn Hstk.
    all: exists (CS_uncall q [] (CS_pre (inv (inst (Γ q) [])))), s; split;
      [ apply jstar_one; apply J_Uncall_Enter; apply call_ok_nil; exact HΓ | ].
    all: match goal with
         | [ He : edge (_, PStart) _ |- _ ] => rewrite (start_succ He)
         end.
    all: simpl; rewrite pfx_nil, (inst_nil HΓ), ?app_nil_r; reflexivity.
  - inversion Hfr.
Qed.

Lemma pblk_at : forall P, pfx P (PBlk []) = PBlk P.
Proof. intro P. simpl. rewrite app_nil_r. reflexivity. Qed.

(* At the until-point the machine either leaves the loop (LoopBase, whose
   repaired side condition excludes the edge into the loop body) or
   iterates (Loop1). *)
Lemma complete_until :
  lv_penv Γ -> forall e1 (a b : stmt) e2 r P pred succ stk (s : store) d,
    freach r P pred succ (Sloop e1 a b e2) -> stk_ok r P stk ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk (CS_loop_until e1 a b e2))) d ->
    exists c' s', jstar Γ (CS_loop_until e1 a b e2, s) (c', s')
                  /\ to_cfg s' (phi r P pred succ stk c') = d.
Proof.
  intros HΓ e1 a b e2 r P pred succ stk s d Hr Hstk Hlv.
  pose proof (fo_node (freach_ok Hr)) as Hn. simpl in Hlv.
  inversion Hlv; subst; kill_lv Hn Hstk.
  - (* LoopBase: leave the loop *)
    eexists; exists s. split; [apply jstar_one; apply J_Loop_Exit; assumption |].
    match goal with
    | [ He : edge (_, PT2 P) ?l, Hne : ?l <> _ |- _ ] =>
        rewrite <- pt2_at in He;
        destruct (exit_succ_loop Hr He) as [-> | E]; [| exfalso; apply Hne; exact E]
    end.
    simpl. rewrite app_nil_r. reflexivity.
  - (* Loop1: iterate *)
    eexists; exists s.
    split; [apply jstar_one; apply J_Loop_Iter1; assumption | reflexivity].
Qed.

Lemma complete_cs :
  lv_penv Γ -> forall cs r P pred succ stk (s : store) d,
    freach r P pred succ (top cs) -> stk_ok r P stk -> cs_ok Γ cs -> ~ at_exit cs ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk cs)) d ->
    exists c' s', jstar Γ (cs, s) (c', s') /\ to_cfg s' (phi r P pred succ stk c') = d.
Proof.
  intros HΓ cs;
    induction cs as [st | st | cs IHcs b | a cs IHcs | e1 cs IHcs b e2 | e1 a cs IHcs e2
                    | e1 a b e2 | e1 cs IHcs b e2 | e1 a b e2 | e1 a cs IHcs e2
                    | q ys cs IHcs | q ys cs IHcs | x v e1 cs IHcs e2];
    intros r P pred succ stk s d Hr Hstk Hok Hne Hlv; simpl in Hr.
  - (* pre *) inversion Hok; subst. eapply complete_pre; eassumption.
  - exfalso. apply Hne. constructor.
  - (* seq_L *)
    inversion Hok; subst. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. simpl in Hlv. rewrite Hp in Hlv. simpl in Hlv.
      destruct (complete_pre HΓ (FR_seq_R Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hlv)
        as [c' [s' [Hj2 Hp2]]].
      exists (CS_seq_R (top cs) c'), s'. split; [| exact Hp2].
      lift (fun x : cont_stmt => CS_seq_L x b) Hj. lift (fun x : cont_stmt => CS_seq_R (top cs) x) Hj2.
      eapply jstar_trans; [exact Hj |]. eapply JS_step; [apply J_Seq_Mid | exact Hj2].
    + simpl in Hlv.
      destruct (IHcs _ _ _ _ _ _ _ (FR_seq_L Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hx Hlv)
        as [c' [s' [Hj Hp]]].
      exists (CS_seq_L c' b), s'. split; [| exact Hp]. lift (fun x : cont_stmt => CS_seq_L x b) Hj. exact Hj.
  - (* seq_R *)
    inversion Hok; subst. simpl in Hlv.
    assert (Hx : ~ at_exit cs) by (intro H; apply Hne; constructor; exact H).
    destruct (IHcs _ _ _ _ _ _ _ (FR_seq_R Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hx Hlv)
      as [c' [s' [Hj Hp]]].
    exists (CS_seq_R a c'), s'. split; [| exact Hp]. lift (fun x : cont_stmt => CS_seq_R a x) Hj. exact Hj.
  - (* if_then *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_if_then e1 x b e2) Hj.
      inversion Hlv; subst; kill_lv Hn Hstk.
      eexists; exists s. split.
      * eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Fi_True; assumption].
      * match goal with
        | [ He : edge (_, PT2 P) _ |- _ ] => rewrite <- pt2_at in He; rewrite (exit_succ_if Hr He)
        end.
        simpl. rewrite app_nil_r. reflexivity.
    + destruct (IHcs _ _ _ _ _ _ _ (FR_then Hr)
                  (stk_ok_push _ _ _ _ Fift ltac:(intros; left; reflexivity) Hstk)
                  ltac:(assumption) Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_if_then e1 c' b e2), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_if_then e1 x b e2) Hj. exact Hj.
  - (* if_else *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_if_else e1 a x e2) Hj.
      inversion Hlv; subst; kill_lv Hn Hstk.
      eexists; exists s. split.
      * eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Fi_False; assumption].
      * match goal with
        | [ He : edge (_, PT2 P) _ |- _ ] => rewrite <- pt2_at in He; rewrite (exit_succ_if Hr He)
        end.
        simpl. rewrite app_nil_r. reflexivity.
    + destruct (IHcs _ _ _ _ _ _ _ (FR_else Hr)
                  (stk_ok_push _ _ _ _ Fiff ltac:(intros; right; left; reflexivity) Hstk)
                  ltac:(assumption) Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_if_else e1 a c' e2), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_if_else e1 a x e2) Hj. exact Hj.
  - (* loop_from: do, then the body *)
    inversion Hok; subst. simpl in Hlv.
    destruct (complete_pre HΓ (FR_do Hr)
                (stk_ok_push _ _ _ _ Floop1 ltac:(intros; right; right; left; reflexivity) Hstk)
                ltac:(assumption) Hlv) as [c' [s' [Hj Hp]]].
    exists (CS_loop_do e1 c' b e2), s'. split; [| exact Hp].
    lift (fun x : cont_stmt => CS_loop_do e1 x b e2) Hj.
    eapply JS_step; [apply J_Loop_Do | exact Hj].
  - (* loop_do *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      destruct (complete_until HΓ Hr Hstk Hlv) as [c' [s' [Hj2 Hp2]]].
      exists c', s'. split; [| exact Hp2].
      lift (fun x : cont_stmt => CS_loop_do e1 x b e2) Hj.
      eapply jstar_trans; [exact Hj |]. eapply JS_step; [apply J_Loop_DoDone | exact Hj2].
    + destruct (IHcs _ _ _ _ _ _ _ (FR_do Hr)
                  (stk_ok_push _ _ _ _ Floop1 ltac:(intros; right; right; left; reflexivity) Hstk)
                  ltac:(assumption) Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_loop_do e1 c' b e2), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_loop_do e1 x b e2) Hj. exact Hj.
  - (* loop_until *) eapply complete_until; eassumption.
  - (* loop_loop *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_loop_loop e1 a x e2) Hj.
      inversion Hlv; subst; kill_lv Hn Hstk.
      * (* LoopMain is excluded by the repaired side condition (E2) *)
        exfalso. match goal with
                 | [ Hm : true = true -> _ <> _ |- _ ] => apply (Hm eq_refl); reflexivity
                 end.
      * eexists; exists s. split;
          [eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Loop_Iter2; assumption]
          | reflexivity].
    + destruct (IHcs _ _ _ _ _ _ _ (FR_loop Hr)
                  (stk_ok_push _ _ _ _ Floop2 ltac:(intros; right; right; right; reflexivity) Hstk)
                  ltac:(assumption) Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_loop_loop e1 a c' e2), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_loop_loop e1 a x e2) Hj. exact Hj.
  - (* call *)
    inversion Hok as [| | | | | | | | | | q0 c0 Htop Hok' |]; subst. simpl in Hlv.
    destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_call q [] x) Hj. rewrite Htop, <- (inst_nil HΓ) in Hj.
      inversion Hlv; subst; kill_lv Hn Hstk.
      eexists; exists s. split.
      * eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Call_Exit; apply call_ok_nil; exact HΓ].
      * match goal with
        | [ He : edge (_, PBlk P) _ |- _ ] =>
            rewrite <- pblk_at in He; rewrite (exit_succ_blk Hr eq_refl He)
        end.
        simpl. rewrite app_nil_r. reflexivity.
    + assert (Hr' : freach (RProc q) [] (RProc q, PStart) (RProc q, PStop) (top cs))
        by (rewrite Htop; apply (FR_root (RProc q))).
      destruct (IHcs _ _ _ _ (Fcall (r, PBlk P) :: stk) _ _ Hr' I Hok' Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_call q [] c'), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_call q [] x) Hj. exact Hj.
  - (* uncall *)
    inversion Hok as [| | | | | | | | | | | q0 c0 Htop Hok']; subst. simpl in Hlv.
    destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_uncall q [] x) Hj. rewrite Htop, <- (inst_nil HΓ) in Hj.
      inversion Hlv; subst; kill_lv Hn Hstk.
      eexists; exists s. split.
      * eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Uncall_Exit; apply call_ok_nil; exact HΓ].
      * match goal with
        | [ He : edge (_, PBlk P) _ |- _ ] =>
            rewrite <- pblk_at in He; rewrite (exit_succ_blk Hr eq_refl He)
        end.
        simpl. rewrite app_nil_r. reflexivity.
    + assert (Hr' : freach (RInv q) [] (RInv q, PStart) (RInv q, PStop) (top cs))
        by (rewrite Htop; apply (FR_root (RInv q))).
      destruct (IHcs _ _ _ _ (Funcall (r, PBlk P) :: stk) _ _ Hr' I Hok' Hx Hlv) as [c' [s' [Hj Hp]]].
      exists (CS_uncall q [] c'), s'. split; [| exact Hp].
      lift (fun x : cont_stmt => CS_uncall q [] x) Hj. exact Hj.
  - inversion Hok.
Qed.

(* ---- 7d. The whole program ---- *)

Lemma jstar_ok :
  lv_penv Γ -> forall (c c' : cont_stmt * store), jstar Γ c c' ->
    top (fst c') = top (fst c) /\ (cs_ok Γ (fst c) -> cs_ok Γ (fst c')).
Proof.
  intros HΓ c c' H; induction H as [c | c1 c2 c3 H12 H23 IH]; [split; auto |].
  destruct c1 as [cs1 s1], c2 as [cs2 s2]; simpl in *.
  destruct IH as [IHt IHo]. split.
  - rewrite IHt. exact (top_step H12).
  - intro Hok. apply IHo. exact (cs_ok_step HΓ H12 Hok).
Qed.

Ltac push_case IH :=
  match goal with
  | [ |- context [phi ?r0 ?P0 ?p0 ?s0 (?f :: ?stk0) ?c] ] =>
      specialize (IH r0 P0 p0 s0 (f :: stk0));
      destruct (phi r0 P0 p0 s0 (f :: stk0) c) as [[a' b'] k'];
      destruct IH as [[_ [_ ->]] | [Hq | [f' [ext ->]]]];
      [ right; right; exists f, []; reflexivity
      | right; left; exact Hq
      | right; right; exists f, (ext ++ [f']); rewrite <- app_assoc; reflexivity ]
  end.

Ltac path_case :=
  right; left; simpl;
  first [ discriminate
        | rewrite path_of_pfx;
          match goal with
          | [ |- context [path_of (entry_pt ?t)] ] =>
              destruct (path_of (entry_pt t)) eqn:E; [discriminate | exfalso; exact (path_entry t E)]
          end ].

(* Where the configuration of a token says "next: stop, stack unchanged",
   the token is at the exit of its statement. *)
Lemma phi_next :
  forall c, cs_ok Γ c -> forall r P pred succ stk,
    let '(a, b, k) := phi r P pred succ stk c in
    (at_exit c /\ b = succ /\ k = stk) \/ path_of (snd b) <> None
    \/ (exists f ext, k = ext ++ f :: stk).
Proof.
  intros c Hok; induction Hok; intros r P pred succ stk; simpl.
  - right; left. rewrite path_of_pfx. destruct (path_of (entry_pt st)) eqn:E;
      [discriminate | exfalso; exact (path_entry st E)].
  - left. repeat split; constructor.
  - specialize (IHHok r (P ++ [DL]) pred (r, pfx (P ++ [DR]) (entry_pt b)) stk).
    destruct (phi r (P ++ [DL]) pred _ stk c) as [[a' b'] k'].
    destruct IHHok as [[_ [-> _]] | [Hq | Hq]]; [right; left | right; left | right; right]; auto.
    simpl. rewrite path_of_pfx. destruct (path_of (entry_pt b)) eqn:E;
      [discriminate | exfalso; exact (path_entry b E)].
  - specialize (IHHok r (P ++ [DR]) (r, pfx (P ++ [DL]) (exit_pt a)) succ stk).
    destruct (phi r (P ++ [DR]) _ succ stk c) as [[a' b'] k'].
    destruct IHHok as [[Hx [-> ->]] | [Hq | Hq]]; [left | right; left | right; right]; auto.
    split; [constructor; exact Hx | split; reflexivity].
  - push_case IHHok.
  - push_case IHHok.
  - path_case.
  - push_case IHHok.
  - path_case.
  - push_case IHHok.
  - push_case IHHok.
  - push_case IHHok.
Qed.

(* Every step of the repaired machine from the configuration of a token
   in main is matched by token steps. *)
Theorem lv_complete_step :
  lv_penv Γ -> forall cs (s : store) d,
    top cs = main -> cs_ok Γ cs -> lvf Γ main true (Phi cs s) d ->
    exists c' s', jstar Γ (cs, s) (c', s') /\ Phi c' s' = d.
Proof.
  intros HΓ cs s d Htop Hok Hlv. unfold Phi in *.
  destruct (at_exit_dec cs) as [Hx | Hx].
  - exfalso. destruct (exit_norm Hx s) as [_ Hp]. rewrite Hp in Hlv. simpl in Hlv.
    inversion Hlv; subst; unfold stmt_at, test_at in *; simpl in *; discriminate.
  - eapply complete_cs; try eassumption.
    + rewrite Htop. apply (FR_root RMain).
    + exact I.
Qed.

Theorem lv_complete_run :
  lv_penv Γ -> forall (c d : lvcfg), lvf_star Γ main true c d ->
  forall cs (s : store), c = Phi cs s -> top cs = main -> cs_ok Γ cs ->
    exists c' s', jstar Γ (cs, s) (c', s') /\ Phi c' s' = d.
Proof.
  intros HΓ c d H; induction H as [c | c1 c2 c3 H12 H23 IH]; intros cs s E Htop Hok.
  - exists cs, s. split; [apply JS_refl | exact (eq_sym E)].
  - rewrite E in H12.
    edestruct (lv_complete_step HΓ) as [c' [s' [Hj Hp]]]; [exact Htop | exact Hok | exact H12 |].
    destruct (jstar_ok HΓ Hj) as [Ht Ho]; simpl in Ht, Ho.
    destruct (IH c' s' (eq_sym Hp) ltac:(rewrite Ht; exact Htop) (Ho Hok)) as [c'' [s'' [Hj2 Hp2]]].
    exists c'', s''. split; [eapply jstar_trans; eassumption | exact Hp2].
Qed.

Lemma lv_run_fwd :
  lv_penv Γ -> forall (c c' : cont_stmt * store), jstar Γ c c' -> top (fst c) = main -> cs_ok Γ (fst c) ->
    lvf_star Γ main true (Phi (fst c) (snd c)) (Phi (fst c') (snd c')).
Proof.
  intros HΓ c c' H; induction H as [c | c1 c2 c3 H12 H23 IH]; intros Htop Hok; [constructor |].
  destruct c1 as [cs1 s1], c2 as [cs2 s2]; simpl in *.
  assert (Hf : frame_ok Γ main RMain [] (RMain, PStart) (RMain, PStop) (top cs1))
    by (rewrite Htop; apply (fo_root Γ main RMain)).
  specialize (IH ltac:(rewrite (top_step H12); exact Htop) (cs_ok_step HΓ H12 Hok)).
  unfold Phi in *.
  destruct (lv_fwd_sim true HΓ H12 [] Hf Hok) as [[Es Ep] | Hs]; simpl in *.
  - subst. rewrite Ep. exact IH.
  - econstructor; eassumption.
Qed.

(* Their Lemma 1 (LNCS; arXiv Lemma 3), both directions, for the repaired
   rules and from any store: main runs from s to s' in the big-step
   semantics iff the machine runs from <s, start, entry(main), []> to
   <s', exit(main), stop, []>.  (With the printed LoopBase the "if"
   direction fails: e1_printed_two_results, e1_janus_one_result.) *)
Theorem lv_lemma1 :
  lv_penv Γ -> frag main -> forall (s s' : store),
    exec Γ main s s'
    <-> lvf_star Γ main true (mkcfg s (RMain, PStart) (RMain, entry_pt main) [])
                             (mkcfg s' (RMain, exit_pt main) (RMain, PStop) []).
Proof.
  intros HΓ Hfr s s'. split.
  - intro H. apply exec_iff_jstar in H.
    pose proof (lv_run_fwd HΓ H eq_refl (ok_pre Γ Hfr)) as R.
    unfold Phi in R; simpl in R. rewrite !pfx_nil in R. exact R.
  - intro H.
    assert (E : mkcfg s (RMain, PStart) (RMain, entry_pt main) [] = Phi (CS_pre main) s)
      by (unfold Phi; simpl; rewrite pfx_nil; reflexivity).
    edestruct (lv_complete_run HΓ H) as [c' [s'' [Hj Hp]]]; [exact E | reflexivity | exact (ok_pre Γ Hfr) |].
    destruct (jstar_ok HΓ Hj) as [Ht Ho]; simpl in Ht, Ho. specialize (Ho (ok_pre Γ Hfr)).
    pose proof (phi_next Ho RMain [] (RMain, PStart) (RMain, PStop) []) as Hn.
    unfold Phi, to_cfg in Hp.
    destruct (phi RMain [] (RMain, PStart) (RMain, PStop) [] c') as [[a b] k].
    injection Hp as -> -> -> ->.
    destruct Hn as [[Hx _] | [Hn | [f [ext Hk]]]].
    + destruct (exit_norm Hx s') as [Hj2 _]. rewrite Ht in Hj2.
      apply exec_iff_jstar. eapply jstar_trans; eassumption.
    + exfalso. apply Hn. reflexivity.
    + exfalso. destruct ext; discriminate Hk.
Qed.

(* ---- 7e. No step of the machine leaves the configuration unchanged ---- *)

Lemma flow_irrefl : forall (st : stmt) x y, flow st x y -> x <> y.
Proof. intros st x y H; induction H; intro E; try ptc; try peq; congruence. Qed.

Lemma edge_irrefl : forall l, edge l l -> False.
Proof.
  intros l H; inversion H; subst;
    try (eapply flow_irrefl; [eassumption | reflexivity]);
    match goal with
    | [ E : entry_pt ?t = _ |- _ ] => apply (path_entry t); rewrite E; reflexivity
    | [ E : _ = entry_pt ?t |- _ ] => apply (path_entry t); rewrite <- E; reflexivity
    | [ E : exit_pt ?t = _ |- _ ] => apply (path_exit t); rewrite E; reflexivity
    | [ E : _ = exit_pt ?t |- _ ] => apply (path_exit t); rewrite <- E; reflexivity
    end.
Qed.

Ltac stuck_cycle :=
  first [ eapply edge_irrefl; eassumption
        | match goal with
          | [ E : ?p = _ :: ?p |- _ ] => apply (f_equal (@length _)) in E; simpl in E; lia
          | [ E : _ :: ?p = ?p |- _ ] => apply (f_equal (@length _)) in E; simpl in E; lia
          end ].

Lemma lvf_irrefl : forall fixed (c : lvcfg), lvf Γ main fixed c c -> False.
Proof. intros fixed c H; inversion H; subst; stuck_cycle. Qed.

Lemma lvb_irrefl : forall fixed (c : lvcfg), lvb Γ main fixed c c -> False.
Proof. intros fixed c H; inversion H; subst; stuck_cycle. Qed.

(* ---- 7f. Completeness with the shape of the token run ---- *)

(* dec cs s F d: from (cs, s) the token takes administrative steps (which
   keep the configuration of the frame F) and then exactly one step, to a
   position whose configuration is d. *)
Definition dec (cs : cont_stmt) (s : store) r P pred succ stk (d : lvcfg) : Prop :=
  exists k1 k2 t2, jstar Γ (cs, s) (k1, s) /\ phi r P pred succ stk k1 = phi r P pred succ stk cs
                   /\ jstep Γ (k1, s) (k2, t2) /\ to_cfg t2 (phi r P pred succ stk k2) = d.

Lemma dec_one :
  forall cs (s : store) k2 t2 r P pred succ stk d,
    jstep Γ (cs, s) (k2, t2) -> to_cfg t2 (phi r P pred succ stk k2) = d ->
    dec cs s r P pred succ stk d.
Proof. intros. exists cs, k2, t2. repeat split; auto. apply JS_refl. Qed.

Lemma dec_pre :
  forall cs cs1 (s : store) r P pred succ stk d,
    jstar Γ (cs, s) (cs1, s) -> phi r P pred succ stk cs1 = phi r P pred succ stk cs ->
    dec cs1 s r P pred succ stk d -> dec cs s r P pred succ stk d.
Proof.
  intros cs cs1 s r P pred succ stk d Hj Hp [k1 [k2 [t2 [Hj1 [Hp1 [Hs Hd]]]]]].
  exists k1, k2, t2. repeat split; try assumption.
  - eapply jstar_trans; eassumption.
  - rewrite Hp1. exact Hp.
Qed.

Lemma dec_lift :
  forall (C : cont_stmt -> cont_stmt) r P pred succ stk r' P' pred' succ' stk',
    (forall c (s : store) c' s', jstep Γ (c, s) (c', s') -> jstep Γ (C c, s) (C c', s')) ->
    (forall c, phi r P pred succ stk (C c) = phi r' P' pred' succ' stk' c) ->
    forall cs (s : store) d, dec cs s r' P' pred' succ' stk' d -> dec (C cs) s r P pred succ stk d.
Proof.
  intros C r P pred succ stk r' P' pred' succ' stk' HC HP cs s d [k1 [k2 [t2 [Hj [Hp [Hs Hd]]]]]].
  exists (C k1), (C k2), t2. repeat split.
  - exact (lift_star C HC Hj).
  - rewrite !HP. exact Hp.
  - apply HC. exact Hs.
  - rewrite HP. exact Hd.
Qed.

Ltac dlift C := eapply (dec_lift C); [intros; constructor; assumption | intros; reflexivity |].

Lemma dec_pre_shape :
  lv_penv Γ -> forall (st : stmt) r P pred succ stk (s : store) d,
    freach r P pred succ st -> stk_ok r P stk -> frag st ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk (CS_pre st))) d ->
    dec (CS_pre st) s r P pred succ stk d.
Proof.
  intros HΓ st; induction st; intros r P pred succ stk s d Hr Hstk Hfr Hlv;
    pose proof (fo_node (freach_ok Hr)) as Hn; simpl in Hlv.
  1-2, 9: inversion Hlv; subst; kill_lv Hn Hstk;
    try (exfalso; inversion Hfr; fail);
    (eapply dec_one;
     [ econstructor; eassumption
     | simpl; match goal with
              | [ He : edge (_, PBlk (_ ++ [])) ?l |- _ ] =>
                  rewrite (exit_succ_blk Hr eq_refl He); reflexivity
              end ]).
  - inversion Hfr; subst. rewrite pfx_app in Hlv.
    apply (dec_pre (cs1 := CS_seq_L (CS_pre st1) st2));
      [apply jstar_one; apply J_Seq_Enter | simpl; rewrite pfx_app; reflexivity |].
    dlift (fun x : cont_stmt => CS_seq_L x st2).
    exact (IHst1 _ _ _ _ _ _ _ (FR_seq_L Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hlv).
  - inversion Hlv; subst; kill_lv Hn Hstk.
    all: eapply dec_one;
      [ first [ apply J_If_True; assumption | apply J_If_False; assumption ]
      | simpl; rewrite ?app_nil_r; reflexivity ].
  - inversion Hlv; subst; kill_lv Hn Hstk.
    all: eapply dec_one; [apply J_Loop_Enter; assumption | simpl; rewrite ?app_nil_r; reflexivity].
  - inversion Hfr; subst. inversion Hlv; subst; kill_lv Hn Hstk.
    all: eapply dec_one; [apply J_Call_Enter; apply call_ok_nil; exact HΓ |].
    all: match goal with
         | [ He : edge (_, PStart) _ |- _ ] => rewrite (start_succ He)
         end.
    all: simpl; rewrite pfx_nil, (inst_nil HΓ), ?app_nil_r; reflexivity.
  - inversion Hfr; subst. inversion Hlv; subst; kill_lv Hn Hstk.
    all: eapply dec_one; [apply J_Uncall_Enter; apply call_ok_nil; exact HΓ |].
    all: match goal with
         | [ He : edge (_, PStart) _ |- _ ] => rewrite (start_succ He)
         end.
    all: simpl; rewrite pfx_nil, (inst_nil HΓ), ?app_nil_r; reflexivity.
  - inversion Hfr.
Qed.

Lemma dec_until :
  lv_penv Γ -> forall e1 (a b : stmt) e2 r P pred succ stk (s : store) d,
    freach r P pred succ (Sloop e1 a b e2) -> stk_ok r P stk ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk (CS_loop_until e1 a b e2))) d ->
    dec (CS_loop_until e1 a b e2) s r P pred succ stk d.
Proof.
  intros HΓ e1 a b e2 r P pred succ stk s d Hr Hstk Hlv.
  pose proof (fo_node (freach_ok Hr)) as Hn. simpl in Hlv.
  inversion Hlv; subst; kill_lv Hn Hstk.
  - eapply dec_one; [apply J_Loop_Exit; assumption |].
    match goal with
    | [ He : edge (_, PT2 P) ?l, Hne : ?l <> _ |- _ ] =>
        rewrite <- pt2_at in He;
        destruct (exit_succ_loop Hr He) as [-> | E]; [| exfalso; apply Hne; exact E]
    end.
    simpl. rewrite app_nil_r. reflexivity.
  - eapply dec_one; [apply J_Loop_Iter1; assumption | reflexivity].
Qed.

Lemma dec_cs :
  lv_penv Γ -> forall cs r P pred succ stk (s : store) d,
    freach r P pred succ (top cs) -> stk_ok r P stk -> cs_ok Γ cs -> ~ at_exit cs ->
    lvf Γ main true (to_cfg s (phi r P pred succ stk cs)) d ->
    dec cs s r P pred succ stk d.
Proof.
  intros HΓ cs;
    induction cs as [st | st | cs IHcs b | a cs IHcs | e1 cs IHcs b e2 | e1 a cs IHcs e2
                    | e1 a b e2 | e1 cs IHcs b e2 | e1 a b e2 | e1 a cs IHcs e2
                    | q ys cs IHcs | q ys cs IHcs | x v e1 cs IHcs e2];
    intros r P pred succ stk s d Hr Hstk Hok Hne Hlv; simpl in Hr.
  - inversion Hok; subst. eapply dec_pre_shape; eassumption.
  - exfalso. apply Hne. constructor.
  - (* seq_L *)
    inversion Hok; subst. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. simpl in Hlv. rewrite Hp in Hlv. simpl in Hlv.
      lift (fun x : cont_stmt => CS_seq_L x b) Hj.
      apply (dec_pre (cs1 := CS_seq_R (top cs) (CS_pre b)));
        [ eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Seq_Mid]
        | simpl; rewrite Hp; reflexivity |].
      dlift (fun x : cont_stmt => CS_seq_R (top cs) x).
      exact (dec_pre_shape HΓ (FR_seq_R Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hlv).
    + simpl in Hlv. dlift (fun x : cont_stmt => CS_seq_L x b).
      exact (IHcs _ _ _ _ _ _ _ (FR_seq_L Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hx Hlv).
  - (* seq_R *)
    inversion Hok; subst. simpl in Hlv.
    assert (Hx : ~ at_exit cs) by (intro H; apply Hne; constructor; exact H).
    dlift (fun x : cont_stmt => CS_seq_R a x).
    exact (IHcs _ _ _ _ _ _ _ (FR_seq_R Hr) (stk_ok_ext _ _ _ _ Hstk) ltac:(assumption) Hx Hlv).
  - (* if_then *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_if_then e1 x b e2) Hj.
      apply (dec_pre (cs1 := CS_if_then e1 (CS_post (top cs)) b e2));
        [exact Hj | simpl; rewrite Hp; reflexivity |].
      inversion Hlv; subst; kill_lv Hn Hstk.
      eapply dec_one; [apply J_Fi_True; assumption |].
      match goal with
      | [ He : edge (_, PT2 P) _ |- _ ] => rewrite <- pt2_at in He; rewrite (exit_succ_if Hr He)
      end.
      simpl. rewrite app_nil_r. reflexivity.
    + dlift (fun x : cont_stmt => CS_if_then e1 x b e2).
      exact (IHcs _ _ _ _ _ _ _ (FR_then Hr)
               (stk_ok_push _ _ _ _ Fift ltac:(intros; left; reflexivity) Hstk)
               ltac:(assumption) Hx Hlv).
  - (* if_else *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_if_else e1 a x e2) Hj.
      apply (dec_pre (cs1 := CS_if_else e1 a (CS_post (top cs)) e2));
        [exact Hj | simpl; rewrite Hp; reflexivity |].
      inversion Hlv; subst; kill_lv Hn Hstk.
      eapply dec_one; [apply J_Fi_False; assumption |].
      match goal with
      | [ He : edge (_, PT2 P) _ |- _ ] => rewrite <- pt2_at in He; rewrite (exit_succ_if Hr He)
      end.
      simpl. rewrite app_nil_r. reflexivity.
    + dlift (fun x : cont_stmt => CS_if_else e1 a x e2).
      exact (IHcs _ _ _ _ _ _ _ (FR_else Hr)
               (stk_ok_push _ _ _ _ Fiff ltac:(intros; right; left; reflexivity) Hstk)
               ltac:(assumption) Hx Hlv).
  - (* loop_from *)
    inversion Hok; subst. simpl in Hlv.
    apply (dec_pre (cs1 := CS_loop_do e1 (CS_pre a) b e2));
      [apply jstar_one; apply J_Loop_Do | reflexivity |].
    dlift (fun x : cont_stmt => CS_loop_do e1 x b e2).
    exact (dec_pre_shape HΓ (FR_do Hr)
             (stk_ok_push _ _ _ _ Floop1 ltac:(intros; right; right; left; reflexivity) Hstk)
             ltac:(assumption) Hlv).
  - (* loop_do *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      lift (fun x : cont_stmt => CS_loop_do e1 x b e2) Hj.
      apply (dec_pre (cs1 := CS_loop_until e1 (top cs) b e2));
        [ eapply jstar_trans; [exact Hj | apply jstar_one; apply J_Loop_DoDone]
        | simpl; rewrite Hp; reflexivity |].
      exact (dec_until HΓ Hr Hstk Hlv).
    + dlift (fun x : cont_stmt => CS_loop_do e1 x b e2).
      exact (IHcs _ _ _ _ _ _ _ (FR_do Hr)
               (stk_ok_push _ _ _ _ Floop1 ltac:(intros; right; right; left; reflexivity) Hstk)
               ltac:(assumption) Hx Hlv).
  - (* loop_until *) eapply dec_until; eassumption.
  - (* loop_loop *)
    inversion Hok; subst. simpl in Hlv. destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_loop_loop e1 a x e2) Hj.
      apply (dec_pre (cs1 := CS_loop_loop e1 a (CS_post (top cs)) e2));
        [exact Hj | simpl; rewrite Hp; reflexivity |].
      inversion Hlv; subst; kill_lv Hn Hstk.
      * exfalso. match goal with
                 | [ Hm : true = true -> _ <> _ |- _ ] => apply (Hm eq_refl); reflexivity
                 end.
      * eapply dec_one; [apply J_Loop_Iter2; assumption | reflexivity].
    + dlift (fun x : cont_stmt => CS_loop_loop e1 a x e2).
      exact (IHcs _ _ _ _ _ _ _ (FR_loop Hr)
               (stk_ok_push _ _ _ _ Floop2 ltac:(intros; right; right; right; reflexivity) Hstk)
               ltac:(assumption) Hx Hlv).
  - (* call *)
    inversion Hok as [| | | | | | | | | | q0 c0 Htop Hok' |]; subst. simpl in Hlv.
    destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_call q [] x) Hj. rewrite Htop, <- (inst_nil HΓ) in Hj.
      apply (dec_pre (cs1 := CS_call q [] (CS_post (inst (Γ q) []))));
        [exact Hj | simpl; rewrite Hp, Htop, (inst_nil HΓ); reflexivity |].
      inversion Hlv; subst; kill_lv Hn Hstk.
      eapply dec_one; [apply J_Call_Exit; apply call_ok_nil; exact HΓ |].
      match goal with
      | [ He : edge (_, PBlk P) _ |- _ ] =>
          rewrite <- pblk_at in He; rewrite (exit_succ_blk Hr eq_refl He)
      end.
      simpl. rewrite app_nil_r. reflexivity.
    + assert (Hr' : freach (RProc q) [] (RProc q, PStart) (RProc q, PStop) (top cs))
        by (rewrite Htop; apply (FR_root (RProc q))).
      dlift (fun x : cont_stmt => CS_call q [] x).
      exact (IHcs _ _ _ _ (Fcall (r, PBlk P) :: stk) _ _ Hr' I Hok' Hx Hlv).
  - (* uncall *)
    inversion Hok as [| | | | | | | | | | | q0 c0 Htop Hok']; subst. simpl in Hlv.
    destruct (at_exit_dec cs) as [Hx | Hx].
    + destruct (exit_norm Hx s) as [Hj Hp]. rewrite Hp in Hlv. simpl in Hlv.
      pose proof (fo_node (freach_ok Hr)) as Hn.
      lift (fun x : cont_stmt => CS_uncall q [] x) Hj. rewrite Htop, <- (inst_nil HΓ) in Hj.
      apply (dec_pre (cs1 := CS_uncall q [] (CS_post (inv (inst (Γ q) [])))));
        [exact Hj | simpl; rewrite Hp, Htop, (inst_nil HΓ); reflexivity |].
      inversion Hlv; subst; kill_lv Hn Hstk.
      eapply dec_one; [apply J_Uncall_Exit; apply call_ok_nil; exact HΓ |].
      match goal with
      | [ He : edge (_, PBlk P) _ |- _ ] =>
          rewrite <- pblk_at in He; rewrite (exit_succ_blk Hr eq_refl He)
      end.
      simpl. rewrite app_nil_r. reflexivity.
    + assert (Hr' : freach (RInv q) [] (RInv q, PStart) (RInv q, PStop) (top cs))
        by (rewrite Htop; apply (FR_root (RInv q))).
      dlift (fun x : cont_stmt => CS_uncall q [] x).
      exact (IHcs _ _ _ _ (Funcall (r, PBlk P) :: stk) _ _ Hr' I Hok' Hx Hlv).
  - inversion Hok.
Qed.

Lemma jstar_wf :
  wf_penv Γ -> forall (c c' : cont_stmt * store), jstar Γ c c' -> wf_cs (fst c) -> wf_cs (fst c').
Proof.
  intros HΓ c c' H; induction H as [c | c1 c2 c3 H12 H23 IH]; intros Hwf; [exact Hwf |].
  destruct c1 as [cs1 s1], c2 as [cs2 s2]. apply IH. exact (wf_cs_step_preserved HΓ H12 Hwf).
Qed.

(* Their Loop Lemma, left to right, for the repaired rules: from the
   configuration of a well-formed token in main, every forward step of the
   machine is undone by a backward step. *)
Theorem lv_loop_fwd :
  lv_penv Γ -> wf_penv Γ -> forall cs (s : store) c',
    top cs = main -> cs_ok Γ cs -> wf_cs cs ->
    lvf Γ main true (Phi cs s) c' -> lvb Γ main true c' (Phi cs s).
Proof.
  intros HΓ HΓw cs s c' Htop Hok Hwf Hlv.
  destruct (at_exit_dec cs) as [Hx | Hx].
  - exfalso. unfold Phi in Hlv. destruct (exit_norm Hx s) as [_ Hp]. rewrite Hp in Hlv. simpl in Hlv.
    inversion Hlv; subst; unfold stmt_at, test_at in *; simpl in *; discriminate.
  - unfold Phi in Hlv.
    assert (Hr : freach RMain [] (RMain, PStart) (RMain, PStop) (top cs))
      by (rewrite Htop; apply (FR_root RMain)).
    destruct (dec_cs HΓ [] s Hr I Hok Hx Hlv) as [k1 [k2 [t2 [Hj [Hp [Hs Hd]]]]]].
    destruct (jstar_ok HΓ Hj) as [Ht Ho]; simpl in Ht, Ho. specialize (Ho Hok).
    pose proof (jstar_wf HΓw Hj Hwf) as Hw; simpl in Hw.
    assert (Hf : frame_ok Γ main RMain [] (RMain, PStart) (RMain, PStop) (top k1))
      by (rewrite Ht, Htop; apply (fo_root Γ main RMain)).
    destruct (lv_bwd_sim true HΓ Hs [] Hf Ho Hw) as [[Es Ep] | Hb]; simpl in *.
    + exfalso. subst t2. rewrite <- Ep, Hp in Hd. unfold Phi in *. rewrite <- Hd in Hlv.
      exact (lvf_irrefl Hlv).
    + unfold Phi. rewrite <- Hd, <- Hp. exact Hb.
Qed.

(* ---- 7g. Edges into a statement ---- *)

Ltac flow_sub_in H :=
  inversion H; subst; try ptc; try peq;
  first [ left; split; reflexivity
        | right; eexists; split; [reflexivity | assumption] ].

Lemma flow_seq_L_in :
  forall (a b : stmt) x0 y0, path_of x0 <> None -> flow (Sseq a b) y0 (pfx [DL] x0) ->
    False \/ (exists y1, y0 = pfx [DL] y1 /\ flow a y1 x0).
Proof. intros a b x0 y0 Hx H. flow_sub_in H. Qed.

Lemma flow_seq_R_in :
  forall (a b : stmt) x0 y0, path_of x0 <> None -> flow (Sseq a b) y0 (pfx [DR] x0) ->
    (x0 = entry_pt b /\ y0 = pfx [DL] (exit_pt a)) \/ (exists y1, y0 = pfx [DR] y1 /\ flow b y1 x0).
Proof. intros a b x0 y0 Hx H. flow_sub_in H. Qed.

Lemma flow_then_in :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sif e1 a b e2) y0 (pfx [DThen] x0) ->
    (x0 = entry_pt a /\ y0 = PT1 []) \/ (exists y1, y0 = pfx [DThen] y1 /\ flow a y1 x0).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub_in H. Qed.

Lemma flow_else_in :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sif e1 a b e2) y0 (pfx [DElse] x0) ->
    (x0 = entry_pt b /\ y0 = PT1 []) \/ (exists y1, y0 = pfx [DElse] y1 /\ flow b y1 x0).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub_in H. Qed.

Lemma flow_do_in :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sloop e1 a b e2) y0 (pfx [DDo] x0) ->
    (x0 = entry_pt a /\ y0 = PT1 []) \/ (exists y1, y0 = pfx [DDo] y1 /\ flow a y1 x0).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub_in H. Qed.

Lemma flow_loop_in :
  forall e1 (a b : stmt) e2 x0 y0, path_of x0 <> None ->
    flow (Sloop e1 a b e2) y0 (pfx [DLoop] x0) ->
    (x0 = entry_pt b /\ y0 = PT2 []) \/ (exists y1, y0 = pfx [DLoop] y1 /\ flow b y1 x0).
Proof. intros e1 a b e2 x0 y0 Hx H. flow_sub_in H. Qed.

(* Into a point of the statement at a reached frame, an edge of the root
   either is a flow edge of that statement, or enters its entry from pred. *)
Lemma edge_into :
  forall r P pred succ st, freach r P pred succ st ->
  forall x0 y, path_of x0 <> None -> edge y (r, pfx P x0) ->
    (exists y0, y = (r, pfx P y0) /\ flow st y0 x0) \/ (x0 = entry_pt st /\ y = pred).
Proof.
  intros r P pred succ st H; induction H; intros x0 y Hx He.
  1: { rewrite pfx_nil in He. inversion He; subst.
       - left. exists x. rewrite pfx_nil. split; [reflexivity | assumption].
       - right. split; reflexivity.
       - exfalso. apply Hx. reflexivity. }
  all: rewrite <- pfx_app in He;
       destruct (IHfreach _ _ (path_pfx_cons _ _ Hx) He) as [[y0 [-> Hf]] | [Hen ->]].
  - destruct (flow_seq_L_in _ Hx Hf) as [[] | [y1 [-> Hf1]]].
    left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - simpl in Hen. apply pfx_cons_inj in Hen; [destruct Hen as [_ ->] | exact Hx].
    right. split; reflexivity.
  - destruct (flow_seq_R_in _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pfx_app. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hen. apply pfx_cons_inj in Hen; [destruct Hen as [Hd _]; discriminate Hd | exact Hx].
  - destruct (flow_then_in _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt1_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hen. exact (proj1 (pfx_cons_root DThen _ Hx) Hen).
  - destruct (flow_else_in _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt1_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hen. exact (proj1 (pfx_cons_root DElse _ Hx) Hen).
  - destruct (flow_do_in _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt1_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hen. exact (proj1 (pfx_cons_root DDo _ Hx) Hen).
  - destruct (flow_loop_in _ Hx Hf) as [[-> ->] | [y1 [-> Hf1]]].
    + right. rewrite pt2_at. split; reflexivity.
    + left. exists y1. rewrite pfx_app. split; [reflexivity | exact Hf1].
  - exfalso. simpl in Hen. exact (proj1 (pfx_cons_root DLoop _ Hx) Hen).
Qed.

Lemma entry_pred_blk :
  forall r P pred succ st, freach r P pred succ st -> entry_pt st = PBlk [] ->
  forall y, edge y (r, pfx P (PBlk [])) -> y = pred.
Proof.
  intros r P pred succ st H Hst y He. rewrite <- Hst in He.
  destruct (edge_into H _ (path_entry st) He) as [[y0 [_ Hf]] | [_ ->]]; [| reflexivity].
  exfalso. rewrite Hst in Hf.
  destruct st; simpl in Hst; try discriminate.
  all: try (inversion Hf; fail).
  all: destruct (entry_pt st1); simpl in Hst; discriminate.
Qed.

Lemma entry_pred_if :
  forall r P pred succ e1 a b e2, freach r P pred succ (Sif e1 a b e2) ->
  forall y, edge y (r, pfx P (PT1 [])) -> y = pred.
Proof.
  intros r P pred succ e1 a b e2 H y He.
  destruct (edge_into H (PT1 []) ltac:(discriminate) He) as [[y0 [_ Hf]] | [_ ->]]; [| reflexivity].
  exfalso. inversion Hf; subst; ptc.
Qed.

Lemma entry_pred_loop :
  forall r P pred succ e1 a b e2, freach r P pred succ (Sloop e1 a b e2) ->
  forall y, edge y (r, pfx P (PT1 [])) -> y = pred \/ y = (r, pfx (P ++ [DLoop]) (exit_pt b)).
Proof.
  intros r P pred succ e1 a b e2 H y He.
  destruct (edge_into H (PT1 []) ltac:(discriminate) He) as [[y0 [-> Hf]] | [_ ->]];
    [| left; reflexivity].
  right. inversion Hf; subst; try ptc. rewrite pfx_app. reflexivity.
Qed.

Lemma stop_pred : forall q y, edge y (q, PStop) -> y = (q, exit_pt (rstmt q)).
Proof.
  intros q y He. inversion He; subst; [| | reflexivity].
  - exfalso. match goal with [ F : flow _ _ PStop |- _ ] => apply (proj2 (flow_paths F)); reflexivity end.
  - exfalso. match goal with [ E : entry_pt _ = PStop |- _ ] => eapply path_entry; rewrite E; reflexivity end.
Qed.

(* ---- 7h. Entries, and invariants for running backwards ---- *)

Inductive at_entry : cont_stmt -> Prop :=
  | AN_pre : forall st, at_entry (CS_pre st)
  | AN_seq_L : forall c b, at_entry c -> at_entry (CS_seq_L c b).

Lemma at_entry_dec : forall c, {at_entry c} + {~ at_entry c}.
Proof.
  induction c; try (right; intro H; inversion H; fail).
  - left; constructor.
  - destruct IHc; [left; constructor; assumption | right; intro H; inversion H; contradiction].
Defined.

(* A token at an entry is reached from CS_pre of its statement by
   administrative steps, which do not move the configuration. *)
Lemma entry_norm :
  forall c, at_entry c -> forall (s : store),
    jstar Γ (CS_pre (top c), s) (c, s)
    /\ forall r P pred succ stk, phi r P pred succ stk c = phi r P pred succ stk (CS_pre (top c)).
Proof.
  intros c H; induction H; intro s; [split; [apply JS_refl | reflexivity] |].
  destruct (IHat_entry s) as [Hj Hp]. split.
  - lift (fun x : cont_stmt => CS_seq_L x b) Hj.
    eapply JS_step; [apply J_Seq_Enter | exact Hj].
  - intros r P pred succ stk. simpl. rewrite Hp. simpl. rewrite pfx_app. reflexivity.
Qed.

Local Hint Constructors cs_ok frag : core.

Lemma cs_ok_back :
  lv_penv Γ -> forall cfg cfg', @jstep nv na asize Γ cfg cfg' -> cs_ok Γ (fst cfg') -> cs_ok Γ (fst cfg).
Proof.
  intros HΓ cfg cfg' H; induction H; intros Hok; simpl in *; inversion Hok; subst;
    repeat match goal with
           | [ Hc : cs_ok _ (CS_pre _) |- _ ] => inversion Hc; subst; clear Hc
           | [ Hc : cs_ok _ (CS_post _) |- _ ] => inversion Hc; subst; clear Hc
           | [ Hf : frag (Scall _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Suncall _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Slocal _ _ _ _) |- _ ] => inversion Hf
           | [ Hf : frag (Sseq _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Sif _ _ _ _) |- _ ] => inversion Hf; subst; clear Hf
           | [ Hf : frag (Sloop _ _ _ _) |- _ ] => inversion Hf; subst; clear Hf
           end;
    try (constructor; auto; fail).
  all: try (constructor; [rewrite <- (top_step H); assumption | auto]; fail).
  all: try (constructor; [simpl; apply inst_nil; exact HΓ
                         | constructor; rewrite inst_nil by exact HΓ; apply HΓ]; fail).
  all: try (constructor; [simpl; rewrite inst_nil by exact HΓ; reflexivity
                         | constructor; rewrite inst_nil by exact HΓ; apply frag_inv, HΓ]; fail).
Qed.

Lemma jstar_ok_back :
  lv_penv Γ -> forall (c c' : cont_stmt * store), jstar Γ c c' -> cs_ok Γ (fst c') -> cs_ok Γ (fst c).
Proof.
  intros HΓ c c' H; induction H as [c | c1 c2 c3 H12 H23 IH]; intros Hok; [exact Hok |].
  exact (cs_ok_back HΓ H12 (IH Hok)).
Qed.

(* At the entry of the loop body s2 the until-test e2 is false: this holds
   of every reachable token, and the backward LoopBase needs it. *)
Fixpoint gok (s : store) (cs : cont_stmt) : Prop :=
  match cs with
  | CS_seq_L c _ | CS_seq_R _ c | CS_if_then _ c _ _ | CS_if_else _ _ c _
  | CS_loop_do _ c _ _ | CS_call _ _ c | CS_uncall _ _ c | CS_local _ _ _ c _ => gok s c
  | CS_loop_loop _ _ c e2 => (at_entry c -> truth s e2 = Some false) /\ gok s c
  | _ => True
  end.

Lemma step_into_entry :
  forall cfg cfg', @jstep nv na asize Γ cfg cfg' -> at_entry (fst cfg') ->
    at_entry (fst cfg) /\ snd cfg = snd cfg'.
Proof.
  intros cfg cfg' H; induction H; intros He; simpl in *; inversion He; subst;
    try (split; [constructor | reflexivity]).
  destruct (IHjstep ltac:(assumption)) as [Ha Hb]. split; [constructor; exact Ha | exact Hb].
Qed.

Lemma gok_step :
  forall cfg cfg', @jstep nv na asize Γ cfg cfg' -> gok (snd cfg) (fst cfg) -> gok (snd cfg') (fst cfg').
Proof.
  intros cfg cfg' H; induction H; intros Hg; simpl in *; try tauto.
  destruct Hg as [Hg1 Hg2]. split; [| apply IHjstep; exact Hg2].
  intro He. destruct (step_into_entry H He) as [He0 Es]; simpl in *. subst. apply Hg1. exact He0.
Qed.

Lemma jstar_gok :
  forall (c c' : cont_stmt * store), jstar Γ c c' -> gok (snd c) (fst c) -> gok (snd c') (fst c').
Proof.
  intros c c' H; induction H as [c | c1 c2 c3 H12 H23 IH]; intros Hg; [exact Hg |].
  apply IH. exact (gok_step H12 Hg).
Qed.

End Complete.














(* ================================================================= *)
(* 8. Axiom audit                                                     *)
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
Print Assumptions freach_ok.
Print Assumptions pfx_cons_inj.
Print Assumptions pfx_cons_root.
Print Assumptions flow_seq_L.
Print Assumptions flow_seq_R.
Print Assumptions flow_then.
Print Assumptions flow_else.
Print Assumptions flow_do.
Print Assumptions flow_loop.
Print Assumptions path_pfx_cons.
Print Assumptions edge_under.
Print Assumptions exit_succ_blk.
Print Assumptions exit_succ_if.
Print Assumptions exit_succ_loop.
Print Assumptions start_succ.
Print Assumptions stk_ok_ext.
Print Assumptions stk_ok_push.
Print Assumptions not_outside.
Print Assumptions at_exit_dec.
Print Assumptions lift_star.
Print Assumptions exit_norm.
Print Assumptions call_ok_nil.
Print Assumptions complete_pre.
Print Assumptions pblk_at.
Print Assumptions complete_until.
Print Assumptions complete_cs.
Print Assumptions jstar_ok.
Print Assumptions phi_next.
Print Assumptions lv_complete_step.
Print Assumptions lv_complete_run.
Print Assumptions lv_run_fwd.
Print Assumptions lv_lemma1.
