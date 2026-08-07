# rcore-semantics

A Rocq (formerly Coq) mechanization of the meta-level reversible
small-step semantics of the minimalist reversible language **R-CORE**.
Everything is in one self-contained file, `proofs.v`, which needs only
the Rocq standard library and introduces no axioms.

This repository is the public release of the artifact. Development
happens elsewhere; what is kept here is the file the papers refer to,
the build, and the audit that makes the axiom-free claim checkable.

## The papers

The semantics is the one introduced in

> Toya Makino and Tetsuo Yokoyama,
> *Small-Step Semantics with Meta-Level Reversibility for a Reversible
> Core Language*, Reversible Computation (RC 2026), eds. C. Aubert and
> L. Roversi, LNCS, vol. 16626, pp. 201-218, Springer, 2026.
> [doi:10.1007/978-3-032-30839-9_12](https://doi.org/10.1007/978-3-032-30839-9_12)

and R-CORE itself in

> Robert Gluck and Tetsuo Yokoyama, *A Minimalist's Reversible While
> Language*, IEICE Trans. Inf. & Syst., vol. E100-D, no. 5,
> pp. 1026-1034, 2017.
> [doi:10.1587/transinf.2016EDP7274](https://doi.org/10.1587/transinf.2016EDP7274)

A companion letter reporting the verification is in preparation. It
records, among other things, that the equivalence theorem of RC 2026
does not hold for the assignment rules as printed, and proves it for
the amended rule.

## What is proved

- determinism in both directions, backward determinism needing
  well-formedness only of the target that the two steps reach;
- the equivalence of the three semantics of RC 2026 (denotational,
  token-based small-step, and the finer-grained one over flowchart
  atoms) on terminating runs;
- the same for the finer-grained semantics over a fixed well-formed
  flowchart, with a counterexample when a configuration records only
  the flowchart that is left;
- the printed rules of RC 2026, transcribed, and the witnesses on
  which they behave differently from the amended ones;
- a verified interpreter, a syntactic inverter unique up to contextual
  equivalence, and full abstraction of the denotational semantics.

## Building

```sh
make          # compile proofs.v
make check    # re-check the compiled object
make audit    # enforce the axiom-free claim (see below)
```

Rocq 9.1.1 was used. No package other than the standard library is
needed.

## The audit

`Print Assumptions` does not fail a build when a result depends on an
axiom, and nothing notices when a new result is added and no one audits
it. `make audit` closes both gaps:

1. `proofs.v` contains no `Admitted`, `Axiom`, `Parameter` or
   `Conjecture`;
2. every top-level `Theorem`, `Lemma`, `Corollary` and `Example` is
   passed to `Print Assumptions`;
3. every verdict the build prints is `Closed under the global context`.

So "the development is axiom-free" is checked rather than promised.

## License

MIT. See `LICENSE`.
