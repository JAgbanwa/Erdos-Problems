# Release notes — preprint v1.0

First official public preprint release of Paper III.

## Included
- publication PDF, LaTeX source, and Markdown source (EN + ES);
- figures;
- public validation-status record and internal adversarial audits;
- reproducibility material;
- Lean 4 / Mathlib v4.28.0 formalization of the proved core.

## Mathematical scope
Proves the linear-error clique-partition bound for split graphs,
\[ |E(G)| - 2\nu_3(G) \le \tfrac{n^2}{6} + Cn, \qquad \mathrm{cp}(G) \le \tfrac{n^2}{6}+Cn, \]
with an absolute constant \(C\), sharpening the asymptotic \((1/6+o(1))n^2\) bound to the correct
linear-error scale.

## Formalization status (honest)
The Lean development compiles zero-`sorry` for the proved core. It is **not axiom-clean by design**:
its trusted project layer consists of exactly two named external asymptotic inputs, `AX1`
(Haxell–Rödl / Yuster) and `AX2` (Dross + Barber–Kühn–Lo–Osthus). The reported axiom footprint of
Theorem 1.1 is `propext, Classical.choice, Quot.sound, AX1, AX2`.

## Open gates
External peer review, an independent reproduction of the build, the public release commit, and the
prior-art / novelty assessment remain pending.
