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

## Lean toolchain (Block F — NOW part of this engagement)
The formalization is a **Lean 4 / Mathlib** project. Audit it with the **pinned**
toolchain, not a newer one:
- `lean-toolchain`: `leanprover/lean4:v4.28.0` (see `CLAIMS/LEAN_FORMALIZATION/lean-toolchain`).
- Mathlib: the revision declared in `CLAIMS/LEAN_FORMALIZATION/lakefile.toml`
  (`lake-manifest.json` at the release commit pins the exact commit). Fetch prebuilt
  oleans with `lake exe cache get` **before** the first `lake build`, or Mathlib compiles
  from scratch (hours).
- Tools: `lake`, `lean`, `elan` (via elan). Axiom/statement gate: `lake env lean gate.lean`.
- A `lake build` is long — per `EXECUTION_PROTOCOL.md`, run it in the background, write
  its raw log to a file, and `grep` the file for progress/errors (do **not** pipe through
  `tail`, which buffers until the pipe closes).
- Independence note: the formalization audit is about *what the kernel certifies*, so the
  independent check is the **axiom report** (`#print axioms`) and the **statement ↔ ledger**
  comparison, not a re-proof. Do not accept "Lean checked it" without F2/F3.

## Provenance of what you received
`SHA256_MANIFEST.txt` (package root) lists the SHA-256 of every file in this package.
Record, in your deliverable's `received_inputs.sha256`, the hashes of the files you
actually audited, so the record is unambiguous about *which version* was audited.
