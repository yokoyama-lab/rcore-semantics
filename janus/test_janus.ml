(* janus/test_janus.ml -- run the extracted Janus interpreter (janus/janus_interp.ml)
   forwards with [run] and backwards with [brun] on the worked examples of
   janus.v.  Each forward run must reach the expected exit configuration
   (where janus.v states one), and each backward run from the exit must
   return to the entry configuration. *)
open Janus_interp

let failures = ref 0

let check name ok =
  Printf.printf "%-40s %s\n" name (if ok then "ok" else "FAILED");
  if not ok then incr failures

(* sizes: variables, arrays, array length *)
let fwd (nv, na, asz) g n cfg = run nv na asz g n cfg
let bwd (nv, na, asz) g n cfg = brun nv na asz g n cfg

let roundtrip name sz g n prog s0 expected =
  let (c1, s1) = fwd sz g n (CS_pre prog, s0) in
  check (name ^ ": forward reaches the exit") (c1 = CS_post prog);
  (match expected with
   | Some s -> check (name ^ ": forward store as in janus.v") (s1 = s)
   | None -> ());
  let (c2, s2) = bwd sz g n (c1, s1) in
  check (name ^ ": backward returns to the entry") (c2 = CS_pre prog && s2 = s0)

let () =
  let big = (10, 4, 8) and small = (3, 1, 2) in
  roundtrip "divmod (/ and %)" big _UU0393_0 20 ex_divmod ex_divmod_pre (Some ex_divmod_post);
  roundtrip "local/delocal" big _UU0393_0 20 ex_local ex_local_pre (Some ex_local_post);
  roundtrip "arrays" big _UU0393_0 40 ex_arr zero_store None;
  roundtrip "call by reference" big _UU0393_1 40 ex_call zero_store None;
  roundtrip "store of size 3/1/2" small _UU0393_s 40 ex_small small_zero (Some ex_small_post);
  if !failures = 0 then print_endline "all extracted runs agree with janus.v"
  else (Printf.printf "%d check(s) FAILED\n" !failures; exit 1)
