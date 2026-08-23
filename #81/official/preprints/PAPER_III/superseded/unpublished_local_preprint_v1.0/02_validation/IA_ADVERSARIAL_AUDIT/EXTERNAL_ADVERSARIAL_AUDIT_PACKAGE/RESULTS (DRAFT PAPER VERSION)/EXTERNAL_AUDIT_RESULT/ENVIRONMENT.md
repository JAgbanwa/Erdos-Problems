# Environment (external adversarial audit)

- OS: Windows 11 Home 10.0.26200 (x64)
- Python 3.14.4
- numpy 2.4.4 (integer edge-use counters in C4; exact — no floating point in any verdict)
- scipy 1.17.1 (ONLY `linear_sum_assignment` on integer matrices in C4 part (i) —
  an assignment is a certificate, its optimality is not relied on; scipy's LP was NOT used)
- PuLP 3.3.2 + CBC (ONLY as the cross-validated *target* in C3/E — never as the
  source of a verdict; every verdict-bearing ν₃ value comes from this audit's own
  branch-and-bound or from explicit verified packings)
- `fractions.Fraction` (exact rational arithmetic; all closed-form comparisons)
- Self-written, dependency-free components (independence from the internal audit's
  SymPy/HiGHS/CBC stack):
  - exact multivariate polynomial algebra (`blockD/rederive_algebra.py`)
  - exact rational Gaussian elimination + LP vertex enumeration (C1 method 1)
  - exact rational tableau simplex, Bland's rule (C1 method 2)
  - exact branch-and-bound for ν₃ (C3)
  - 1-factorizations of K_t by the circle method (C3/C4), verified per instance
- Web sources for Block B: arXiv:math/0305350 (Yuster), arXiv:1503.08191 (Dross),
  Springer/Wiley/ACM indices for citation metadata (retrieved 2026-07-21).
- Randomness: every script fixes its RNG seed (81, 424242, 8181, 2304, 7, 20260721);
  all results are deterministic and reproducible bit-for-bit.
- Every script writes its full log under its block's `results/` and returns a
  nonzero exit code on any failure.

## Independence statement

Shared tooling with the internal audit is limited to Python itself, plus PuLP/CBC
used strictly as a cross-check target (Block E) with solver status verified. All
verdict-bearing computations use different methods from the internal audit:
exact rational certificates instead of float LP (C1 vs their block02); self-written
polynomial algebra instead of SymPy (D vs their block01); pure-integer arithmetic
grids instead of Fraction loops (C2 vs their block03, 3× the range); own B&B +
packing certificates instead of CBC-only (C3 vs their block04).
