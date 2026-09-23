(* witness_driver.ml -- run the gap witnesses of proofs.v Sect. 41A/41B
   through the EXTRACTED interpreter (rcore_interp.ml, produced by
   `make extract`), so that the third column of docs/gap-witness-table.md
   is executed and not only proved.

   Build and run with: make witness-test

   Each witness is run three ways: the well-formedness decision
   procedure [wf_cmd_dec], the big-step evaluator [eval_cmd_fuel]
   (= exec_ds by [eval_cmd_correct]) and the small-step stepper
   [step_fun]/[steps_n] iterated to a fixed point (= exec_ss by
   [step_fun_correct]).  The expectations checked at the end are the
   ones proved in proofs.v: gap_witness_ds (l.3765), gap_witness2_ds
   (l.3791), odd_store_reachable (l.3860), loop_gap_ss (l.3867),
   step_fun_on_gap_witness (l.4801), wf_cc_dec_rejects (l.4380) and
   ss_asn_stuck_iff (odot undefined => stuck). *)

open Rcore_interp

(* --- variables: Fin.t 10 extracts to [F1 of int | FS of int * t], the
   int being the remaining bound; X0 = F1 9, X1 = FS (9, F1 8), ... --- *)
let rec fin k n = if k = 0 then F1 (n - 1) else FS (n - 1, fin (k - 1) (n - 1))
let xv k : var = fin k 10
let x0 = xv 0 and x1 = xv 1 and x2 = xv 2 and x3 = xv 3 and x4 = xv 4
and x5 = xv 5 and x6 = xv 6 and x9 = xv 9

(* --- stores: Vector.t val 10 --- *)
let rec const_nil n = if n = 0 then Nil else Cons (Vnil, n - 1, const_nil (n - 1))
let nil_store : store = const_nil 10
let vt = Vpair (Vnil, Vnil)                       (* the paper's t *)
let vodd = Vpair (vt, Vnil)                       (* ((nil.nil).nil) *)
let neq_store = update nil_store x2 vt            (* proofs.v l.3786 *)
let odd_store = update (update nil_store x1 vt) x0 vodd   (* l.3851 *)
let t_store  = update nil_store x0 vt

let rec string_of_val = function
  | Vnil -> "nil"
  | Vpair (a, b) -> "(" ^ string_of_val a ^ "." ^ string_of_val b ^ ")"

(* print only the non-nil variables; "{}" is the all-nil store *)
let show_store s =
  let b = Buffer.create 64 in
  for k = 0 to 9 do
    match lookup s (xv k) with
    | Vnil -> ()
    | v -> Buffer.add_string b
             (Printf.sprintf "%sX%d=%s" (if Buffer.length b = 0 then "" else " ") k (string_of_val v))
  done;
  "{" ^ Buffer.contents b ^ "}"

let store_eq a b =
  let ok = ref true in
  for k = 0 to 9 do if lookup a (xv k) <> lookup b (xv k) then ok := false done;
  !ok

(* --- iterate the stepper; None = stuck before reaching a terminal config --- *)
let rec run_ss cc s n =
  if n = 0 then `Fuel
  else match step_fun cc s with
       | None -> (match cc with CC_at_post _ -> `Done s | _ -> `Stuck (s, n))
       | Some (cc', s') -> run_ss cc' s' (n - 1)

let failures = ref 0
let check name b =
  Printf.printf "    %-52s %s\n" name (if b then "ok" else "FAILED");
  if not b then incr failures

(* Run one witness and check it against the outcome proofs.v establishes.
   [expect] is [Some s'] when exec_ds is defined with result s', [None]
   when it is undefined (and exec_ss must then be stuck). *)
let witness name c s0 ~wf ~expect =
  Printf.printf "== %s\n    initial store %s\n" name (show_store s0);
  let w = wf_cmd_dec c in
  Printf.printf "    wf_cmd_dec  : %b\n" w;
  let big = eval_cmd_fuel 10000 c s0 in
  Printf.printf "    eval_cmd_fuel (exec_ds): %s\n"
    (match big with Some s -> show_store s | None -> "undefined");
  let small = run_ss (CC_at_pre c) s0 10000 in
  Printf.printf "    step_fun*     (exec_ss): %s\n"
    (match small with
     | `Done s -> "terminal, " ^ show_store s
     | `Stuck (s, _) -> "STUCK (step_fun = None) in " ^ show_store s
     | `Fuel -> "out of fuel");
  check "wf_cmd_dec as expected" (w = wf);
  (match expect with
   | Some s' ->
       check "exec_ds defined with the expected store"
         (match big with Some s -> store_eq s s' | None -> false);
       check "exec_ss reaches the terminal configuration with it"
         (match small with `Done s -> store_eq s s' | _ -> false)
   | None ->
       check "exec_ds undefined" (big = None);
       check "exec_ss stuck" (match small with `Stuck _ -> true | _ -> false));
  big

let () =
  (* Witness 1: gap_witness, proofs.v l.3762-3785 *)
  let gw1 = Cass (x0, Enil) in
  ignore (witness "gap_witness: X0 ^= nil at nil_store" gw1 nil_store
            ~wf:true ~expect:(Some nil_store));
  check "step_fun_on_gap_witness (l.4801) reproduced"
    (step_fun (CC_at_pre gw1) nil_store = Some (CC_at_post gw1, nil_store));

  (* Witness 2: gap_witness2, l.3786-3800 *)
  let gw2 = Cass (x0, Eeq (x1, x2)) in
  ignore (witness "gap_witness2: X0 ^= =? X1 X2 at neq_store" gw2 neq_store
            ~wf:true ~expect:(Some neq_store));

  (* Witness 3: the loop of rc2026_loop_guards_are_stricter at odd_store,
     l.3851-3885; first check odd_store_reachable (l.3860). *)
  let build = Cseq (Cass (x1, Eeq (x2, x3)), Cass (x0, Econs (x1, x4))) in
  ignore (witness "odd_store_reachable: X1 ^= =? X2 X3; X0 ^= cons X1 X4" build nil_store
            ~wf:true ~expect:(Some odd_store));
  let lp = Cloop (x0, Cass (x5, Enil), x1) in
  ignore (witness "odd loop: from X0 loop X5 ^= nil until X1 at odd_store" lp odd_store
            ~wf:true ~expect:(Some odd_store));
  ignore (witness "odd loop inverted (inv): from X1 loop X5 ^= nil until X0" (inv lp) odd_store
            ~wf:true ~expect:(Some odd_store));
  (* control: the same loop with X0 = t exactly *)
  ignore (witness "control loop_t: same loop at {X0=t, X1=t}" lp (update t_store x1 vt)
            ~wf:true ~expect:(Some (update t_store x1 vt)));

  (* Witness 4 (ours): the self-assignment, not well-formed
     (nf_expr_not_self l.409, wf_cc_dec_rejects l.4380); eval_expr reads
     the full store (l.202), so X0 ^= X0 clears X0 = t. *)
  let sa = Cass (x0, Evar x0) in
  ignore (witness "selfassign (not wf): X0 ^= X0 at {X0=t}" sa t_store
            ~wf:false ~expect:(Some nil_store));
  ignore (witness "selfassign_inv: X0 ^= X0 at nil_store does not restore t" sa nil_store
            ~wf:false ~expect:(Some nil_store));

  (* Witness 5 (ours): mismatched clear, d = t, e = nil: odot undefined
     (l.214), so exec_ds is undefined and step_fun is None. *)
  ignore (witness "mismatchclear: X0 ^= nil at {X0=t}" gw1 t_store
            ~wf:true ~expect:None);

  (* Control: examples/reverse.rcore of both old interpreters, on a list
     of nil-trees since the extracted value domain has no atoms. *)
  let seq = List.fold_right (fun c acc -> Cseq (c, acc)) in
  let body = seq [
      Cass (x6, Eeq (x1, x0)); Cass (x5, Eeq (x2, x0));
      Cass (x3, Ehd x1); Cass (x4, Etl x1); Cass (x1, Econs (x3, x4));
      Cass (x1, Evar x4); Cass (x4, Evar x1);
      Cass (x4, Econs (x3, x2)); Cass (x3, Ehd x4); Cass (x2, Etl x4);
      Cass (x2, Evar x4); Cass (x4, Evar x2);
      Cass (x5, Eeq (x2, x0)) ] (Cass (x6, Eeq (x1, x0))) in
  let reverse = seq [
      Cass (x5, Econs (x0, x0)); Cass (x6, Eeq (x1, x0));
      Cloop (x5, body, x6); Cass (x5, Eeq (x2, x0)) ] (Cass (x6, Econs (x0, x0))) in
  let input = Vpair (Vnil, Vpair (vt, Vnil)) in           (* [nil, t] *)
  let expected = update nil_store x2 (Vpair (vt, Vpair (Vnil, Vnil))) in (* [t, nil] *)
  ignore (witness "control reverse.rcore on (nil.((nil.nil).nil))" reverse (update nil_store x1 input)
            ~wf:true ~expect:(Some expected));
  ignore x9;
  if !failures = 0 then print_endline "\nall witness checks passed"
  else (Printf.printf "\n%d WITNESS CHECK(S) FAILED\n" !failures; exit 1)
