#!/usr/bin/env python3
"""Mutation check for janus/janus.v: break one definition at a time and
confirm that the proofs notice.

Each mutant is built from a fresh copy of janus/janus.v in a temporary
directory (the repository file is never modified).  For every mutant the
script reports the first failing result (the enclosing Theorem/Lemma/
Example/... of the first error) and compares it with the expected one.
An unmutated control copy must compile.

Usage (from the repository root):  python3 tools/janus-mutants.py
Exit status 0 iff the control compiles and every mutant fails in the
expected result.  Needs `rocq` on PATH (ROCQ overrides).
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

SRC = "janus/janus.v"
LV = "janus/lv.v"
EMBED = "janus/embed.v"
ROCQ = os.environ.get("ROCQ", "rocq")

# (description, [(old, new), ...], expected first failing result)
# Replacements must match exactly once.  Mutants 4 and 5 also patch the
# decision procedure wf_stmt_dec, whose script would otherwise be the first
# thing to break (it is a proof about the definition being mutated, not one
# of the properties under test).
MUTANTS = [
    ("J_Loop_Iter2: guard e1 false flipped to e1 true",
     [("  | J_Loop_Iter2 : forall e1 s1 s2 e2 s,\n      truth s e1 = Some false ->",
       "  | J_Loop_Iter2 : forall e1 s1 s2 e2 s,\n      truth s e1 = Some true ->")],
     "jstep_bwd_deterministic"),
    ("J_Call_Enter: premise call_ok removed",
     [("  | J_Call_Enter : forall p ys s,\n      call_ok (Γ p) ys = true ->\n",
       "  | J_Call_Enter : forall p ys s,\n")],
     "wf_cs_step_preserved_cfg"),
    ("call_ok: no-capture clause (nocap) dropped",
     [("  && inj_onb (ren (formals pr) ys) (fv (body pr))\n"
       "  && nocap (ren (formals pr) ys) (body pr).",
       "  && inj_onb (ren (formals pr) ys) (fv (body pr)).")],
     "wf_inst"),
    ("J_Local_Exit: outer value not restored",
     [("(CS_post (Slocal x e1 st e2), update s x v)\n  | J_Ctx_Local",
       "(CS_post (Slocal x e1 st e2), s)\n  | J_Ctx_Local")],
     "jstep_bwd_deterministic"),
    ("wf_Slocal / wf_cs_local: condition x not in e2 dropped",
     [("      nf_expr x e1 -> nf_expr x e2 -> wf_stmt st -> wf_stmt (Slocal x e1 st e2)",
       "      nf_expr x e1 -> wf_stmt st -> wf_stmt (Slocal x e1 st e2)"),
      ("      nf_expr x e1 -> nf_expr x e2 -> wf_cs cs -> wf_cs (CS_local x v e1 cs e2).",
       "      nf_expr x e1 -> wf_cs cs -> wf_cs (CS_local x v e1 cs e2)."),
      ("    destruct (nf_expr_dec x e2) as [H2 | H2];\n"
       "    [| right; intro Hw; inversion Hw; subst; contradiction].\n"
       "    destruct (wf_stmt_dec a) as [Ha | Ha].",
       "    destruct (wf_stmt_dec a) as [Ha | Ha].")],
     "wf_stmt_inv"),
    ("wf_Saass: condition a not in e1 dropped",
     [("      anf_expr a e1 -> anf_expr a e2 -> wf_stmt (Saass a e1 op e2).",
       "      anf_expr a e2 -> wf_stmt (Saass a e1 op e2)."),
      ("  - destruct (anf_expr_dec r e1) as [H1 | H1];\n"
       "    [| right; intro Hw; inversion Hw; subst; contradiction].\n"
       "    destruct (anf_expr_dec r e2) as [H2 | H2];",
       "  - destruct (anf_expr_dec r e2) as [H2 | H2];")],
     "jstep_bwd_deterministic"),
    ("inv: array update keeps op instead of inv_upd op",
     [("  | Saass a e1 op e2  => Saass a e1 (inv_upd op) e2",
       "  | Saass a e1 op e2  => Saass a e1 op e2")],
     "inv_step_reverses_cfg"),
    ("E_IfT: fi assertion polarity flipped",
     [("      truth s e1 = Some true -> exec Γ a s s' -> truth s' e2 = Some true ->\n      exec Γ (Sif e1 a b e2) s s'",
       "      truth s e1 = Some true -> exec Γ a s s' -> truth s' e2 = Some false ->\n      exec Γ (Sif e1 a b e2) s s'")],
     "exec_jstar_mut"),
    ("E_Local: outer value not restored",
     [("      exec Γ (Slocal x e1 st e2) s (update s1 x (s x))",
       "      exec Γ (Slocal x e1 st e2) s s1")],
     "exec_jstar_mut"),
    # Partial evaluation (section 2): each mutant restores a behaviour of
    # the total evaluation or of another Janus dialect.
    ("Bdiv: a zero divisor yields 0 instead of no value",
     [("  | Bdiv   => if Z.eqb b 0 then None else Some (Z.div a b)",
       "  | Bdiv   => Some (Z.div a b)")],
     "j_div_by_zero_stuck"),
    ("Bdiv: rounds towards zero (Z.quot) instead of minus infinity",
     [("  | Bdiv   => if Z.eqb b 0 then None else Some (Z.div a b)",
       "  | Bdiv   => if Z.eqb b 0 then None else Some (Z.quot a b)")],
     "j_div_run"),
    ("aread: an out-of-bounds read yields 0 instead of no value",
     [("  match idx z with Some i => Some (aget s a i) | None => None end.",
       "  match idx z with Some i => Some (aget s a i) | None => Some 0 end.")],
     "j_oob_read_stuck"),
    ("eval: && short-circuits on a false left operand",
     [("  | Ebin op e1 e2 => match eval s e1, eval s e2 with\n",
       "  | Ebin Bland e1 e2 => match eval s e1 with\n"
       "                        | Some 0 => Some 0\n"
       "                        | Some v1 => match eval s e2 with\n"
       "                                     | Some v2 => apply_bin Bland v1 v2\n"
       "                                     | None => None end\n"
       "                        | None => None end\n"
       "  | Ebin op e1 e2 => match eval s e1, eval s e2 with\n")],
     "j_strict_and_stuck"),
    # janus/lv.v: undo each repair of the Lanese-Vidal rules (target LV).
    ("lv: repaired LoopBase tests entry(s1) again (erratum E1)",
     [("      l2' <> (if fixed then (r, pfx (p ++ [DLoop]) (entry_pt s2))         (* E1 *)",
       "      l2' <> (if fixed then (r, pfx (p ++ [DDo]) (entry_pt s1))         (* E1 *)")],
     "e1_fixed_no_escape", LV),
    ("lv: repaired LoopMain forbids an unreachable label instead of exit(s2) (erratum E2)",
     [("      (fixed = true -> l <> (r, pfx (p ++ [DLoop]) (exit_pt s2))) ->         (* E2 *)",
       "      (fixed = true -> l <> (r, PStop)) ->         (* E2 *)")],
     "e2_fixed_stuck", LV),
    ("lv: repaired backward Skip tests l' -> l'' instead of l -> l' (erratum E3)",
     [("      stmt_at l' = Some Sskip -> edge l' l'' ->\n      (fixed = true -> edge l l') ->",
       "      stmt_at l' = Some Sskip -> edge l' l'' ->\n      (fixed = true -> edge l' l'') ->")],
     "e3_fixed_rejects", LV),
    # janus/lv.v, our extension: a delocal that does not restore the saved
    # outer value no longer matches J_Local_Exit.
    ("lv: Delocal does not restore the saved outer value (extension)",
     [("              (mkcfg (update s x v) (r, PT2 p) l2' π).",
       "              (mkcfg s (r, PT2 p) l2' π).")],
     "lv_fwd_sim", LV),
    # janus/embed.v: break the embedding on either side (target EMBED).
    ("embed: G_Loop_Iter2 goes to the until-point (Theorem A must notice)",
     [("      gstep (GC_loop_loop g1 s1 (GC_post s2) g2, s) (GC_loop_from g1 s1 s2 g2, s)\n",
       "      gstep (GC_loop_loop g1 s1 (GC_post s2) g2, s) (GC_loop_until g1 s1 s2 g2, s)\n")],
     "gstep_jstep_cfg", EMBED),
    ("embed: R-CORE mid-loop translated to the from-point (Theorem B must notice)",
     [("  | proofs.CC_mid_loop x c y => GC_loop_until x GSkip (T c) y\n",
       "  | proofs.CC_mid_loop x c y => GC_loop_from x GSkip (T c) y\n")],
     "rcore_sim", EMBED),
]

HEADER = re.compile(
    r"^(Theorem|Lemma|Corollary|Example|Fixpoint|Definition|Inductive)\s+([A-Za-z0-9_']+)")
ERRLINE = re.compile(r'File "[^"]*", line (\d+), characters')


def enclosing(lines, lineno):
    for i in range(lineno - 1, -1, -1):
        m = HEADER.match(lines[i])
        if m:
            return m.group(2)
    return "?"


def build(text, target=SRC):
    d = tempfile.mkdtemp(prefix="janus-mut-")
    try:
        os.makedirs(os.path.join(d, "janus"))
        if target != SRC:
            # lv.v and embed.v import janus.v (embed.v also proofs.v):
            # build the unmutated dependencies first
            for dep in [SRC] + (["proofs.v"] if target == EMBED else []):
                shutil.copy(dep, os.path.join(d, dep))
                subprocess.run([ROCQ, "c", "-Q", ".", "RCore", dep], cwd=d, check=True,
                               capture_output=True, text=True, timeout=1800)
        with open(os.path.join(d, target), "w") as f:
            f.write(text)
        r = subprocess.run([ROCQ, "c", "-Q", ".", "RCore", target], cwd=d,
                           capture_output=True, text=True, timeout=1800)
        out = r.stdout + r.stderr
        if r.returncode == 0:
            return True, None
        # the first "File ..., line N" that is followed by an Error
        blocks = out.split("\nFile ")
        for b in blocks:
            if "Error" in b:
                m = ERRLINE.search("File " + b if not b.startswith("File ") else b)
                if m:
                    return False, int(m.group(1))
        return False, None
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main():
    text = open(SRC).read()
    ok = True
    good, _ = build(text)
    print(f"control (unmutated)           : {'compiles' if good else 'FAILS'}")
    ok &= good
    good_lv, _ = build(open(LV).read(), LV)
    print(f"control lv.v (unmutated)      : {'compiles' if good_lv else 'FAILS'}")
    ok &= good_lv
    good_embed, _ = build(open(EMBED).read(), EMBED)
    print(f"control embed.v (unmutated)   : {'compiles' if good_embed else 'FAILS'}")
    ok &= good_embed
    for i, m in enumerate(MUTANTS, 1):
        desc, reps, expected = m[:3]
        target = m[3] if len(m) > 3 else SRC
        mut = text if target == SRC else open(target).read()
        for old, new in reps:
            n = mut.count(old)
            if n != 1:
                print(f"mutant {i}: replacement matched {n} times, source changed? ({desc})")
                ok = False
                break
            mut = mut.replace(old, new)
        else:
            compiled, line = build(mut, target)
            mlines = mut.split("\n")
            got = "(compiles!)" if compiled else (enclosing(mlines, line) if line else "?")
            hit = (not compiled) and got == expected
            ok &= hit
            print(f"mutant {i}: {desc}\n    first failure: {got}"
                  f"  expected: {expected}  {'ok' if hit else 'MISMATCH'}")
    print("all mutants killed as expected" if ok else "MUTATION CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
