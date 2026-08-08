(* test_interp.ml -- run the extracted interpreter.

   Extraction is only worth claiming if the output actually runs, so this
   driver exercises it end to end: the big-step evaluator, the small-step
   stepper, their agreement, the inverter, and the two well-formedness
   decision procedures.  It is the executable counterpart of
   [eval_cmd_correct], [step_fun_correct] and [inv_step_reverses].

   Build and run with: make extract-test *)

open Rcore_interp

(* --- variables (Fin.t 10; the int is the remaining bound) --- *)
let x0 : var = F1 9
let x1 : var = FS (9, F1 8)

(* --- the all-nil store, i.e. [Vector.const Vnil 10] --- *)
let rec const_nil n = if n = 0 then Nil else Cons (Vnil, n - 1, const_nil (n - 1))
let nil_store : store = const_nil 10

let vt = Vpair (Vnil, Vnil)          (* the paper's [t]; [f] is [Vnil] *)

let rec string_of_val = function
  | Vnil -> "nil"
  | Vpair (a, b) -> "(" ^ string_of_val a ^ "." ^ string_of_val b ^ ")"

let show_store s = String.concat " " [ "X0="; string_of_val (lookup s x0);
                                       "X1="; string_of_val (lookup s x1) ]

let failures = ref 0
let check name b =
  Printf.printf "%-46s %s\n" name (if b then "ok" else "FAILED");
  if not b then incr failures

(* --- run the small-step stepper to a fixed point --- *)
let rec run_ss cc s n =
  if n = 0 then None
  else match step_fun cc s with
       | None -> Some (cc, s)
       | Some (cc', s') -> run_ss cc' s' (n - 1)

let () =
  (* [X0 ^= X1] in a store where X1 = t.  Well-formed: X0 does not occur
     in the right-hand side. *)
  let prog = Cass (x0, Evar x1) in
  let s0 = update nil_store x1 vt in
  Printf.printf "program : X0 ^= X1\ninitial : %s\n" (show_store s0);

  check "wf_cmd_dec accepts it" (wf_cmd_dec prog);
  check "wf_cc_dec accepts its entry position" (wf_cc_dec (CC_at_pre prog));
  check "wf_cmd_dec rejects the self-assignment"
    (not (wf_cmd_dec (Cass (x0, Evar x0))));

  (* big step *)
  let big = eval_cmd_fuel 100 prog s0 in
  (match big with
   | Some s -> Printf.printf "big-step: %s\n" (show_store s)
   | None   -> print_endline "big-step: undefined");
  check "big step is defined" (big <> None);

  (* small step, and agreement with the big step *)
  let small = run_ss (CC_at_pre prog) s0 100 in
  (match small with
   | Some (_, s) -> Printf.printf "small   : %s\n" (show_store s)
   | None -> print_endline "small   : did not settle");
  check "small step agrees with big step"
    (match big, small with
     | Some sb, Some (cc, ss) ->
         cc = CC_at_post prog && lookup sb x0 = lookup ss x0
         && lookup sb x1 = lookup ss x1
     | _ -> false);

  check "it takes exactly one small step"
    (match steps_n 1 (CC_at_pre prog) s0 with
     | Some (CC_at_post _, _) -> true | _ -> false);

  (* the inverter undoes it: C ; inv C is the identity here *)
  check "inv is the identity on assignments" (inv prog = prog);
  let round =
    match big with
    | Some s -> eval_cmd_fuel 100 (inv prog) s
    | None -> None in
  (match round with
   | Some s -> Printf.printf "after inv: %s\n" (show_store s)
   | None -> print_endline "after inv: undefined");
  check "C then inv C restores the initial store"
    (match round with
     | Some s -> lookup s x0 = lookup s0 x0 && lookup s x1 = lookup s0 x1
     | None -> false);

  (* cc_inv mirrors the token position *)
  check "cc_inv maps entry to exit of the inverse"
    (cc_inv (CC_at_pre prog) = CC_at_post (inv prog));

  (* the gap witness: amended rules step where the printed ones are stuck *)
  let gap = Cass (x0, Enil) in
  check "the gap witness steps under the amended rule"
    (match step_fun (CC_at_pre gap) nil_store with
     | Some (CC_at_post _, _) -> true | _ -> false);

  if !failures = 0 then print_endline "\nall checks passed"
  else (Printf.printf "\n%d CHECK(S) FAILED\n" !failures; exit 1)
