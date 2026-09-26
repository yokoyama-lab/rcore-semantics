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
ROCQ = os.environ.get("ROCQ", "rocq")

# (description, [(old, new), ...], expected first failing result)
# Replacements must match exactly once.  Mutants 4 and 5 also patch the
# decision procedure wf_stmt_dec, whose script would otherwise be the first
# thing to break (it is a proof about the definition being mutated, not one
# of the properties under test).
MUTANTS = [
    ("J_Loop_Iter2: guard e1 = 0 flipped to e1 <> 0",
     [("  | J_Loop_Iter2 : forall e1 s1 s2 e2 s,\n      eval s e1 = 0 ->",
       "  | J_Loop_Iter2 : forall e1 s1 s2 e2 s,\n      eval s e1 <> 0 ->")],
     "jstep_bwd_deterministic"),
    ("J_Call_Enter: premise call_ok removed",
     [("  | J_Call_Enter : forall p ys s,\n      call_ok (Γ p) ys = true ->\n",
       "  | J_Call_Enter : forall p ys s,\n")],
     "wf_cs_step_preserved_cfg"),
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
     [("      eval s e1 <> 0 -> exec Γ a s s' -> eval s' e2 <> 0 ->\n      exec Γ (Sif e1 a b e2) s s'",
       "      eval s e1 <> 0 -> exec Γ a s s' -> eval s' e2 = 0 ->\n      exec Γ (Sif e1 a b e2) s s'")],
     "exec_jstar_mut"),
    ("E_Local: outer value not restored",
     [("      exec Γ (Slocal x e1 st e2) s (update s1 x (s x))",
       "      exec Γ (Slocal x e1 st e2) s s1")],
     "exec_jstar_mut"),
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


def build(text):
    d = tempfile.mkdtemp(prefix="janus-mut-")
    try:
        os.makedirs(os.path.join(d, "janus"))
        with open(os.path.join(d, SRC), "w") as f:
            f.write(text)
        r = subprocess.run([ROCQ, "c", "-Q", ".", "RCore", SRC], cwd=d,
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
    for i, (desc, reps, expected) in enumerate(MUTANTS, 1):
        mut = text
        for old, new in reps:
            n = mut.count(old)
            if n != 1:
                print(f"mutant {i}: replacement matched {n} times, source changed? ({desc})")
                ok = False
                break
            mut = mut.replace(old, new)
        else:
            compiled, line = build(mut)
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
