# Environment (reference; the auditor should prefer independent tooling)

The internal audit in `OUR_INTERNAL_AUDIT/` was produced with:

- OS: Windows 11 (x64).
- Python 3.14.
- SymPy 1.14 (symbolic identities).
- SciPy 1.17 — HiGHS LP backend (fractional triangle-packing LP).
- PuLP + CBC (exact 0/1 ILP for integral triangle-packing number ν₃).
- `fractions.Fraction` for exact rational arithmetic.
- reportlab 5.0 (PDF certificates).

For **independence**, the external auditor is encouraged to use *different* tools where
possible, e.g.:
- a different CAS (Mathematica, Maxima, or hand-verified exact arithmetic) for the
  algebraic identities;
- an exact rational LP/simplex (e.g. `cvxpy` with an exact backend, `sage`, or a
  rational-arithmetic simplex) rather than a floating-point solver, for ν₃*;
- a different ILP solver (Gurobi/GLPK/SCIP) for ν₃, as a cross-check against CBC.

The Lean toolchain is intentionally **not** part of this engagement.

## Provenance of what you received
`SHA256_MANIFEST.txt` (package root) lists the SHA-256 of every file in this package.
Record, in your deliverable's `received_inputs.sha256`, the hashes of the files you
actually audited, so the record is unambiguous about *which version* was audited.
