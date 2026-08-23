# Block 02 — Common-profile LP: ν₃*(H(p,q,d)) = F(p,q,d) (Theorem 3.1 / E-3.1)

## What is audited
The closed-form fractional triangle-packing value of the common-profile split graph
`H(p,q,d)` (clique `K` of order `p`; `q` independent vertices, each adjacent to the same
`d`-subset `N ⊆ K`) equals the three-term minimum

```
F(p,q,d) = min{ (C(p,2)+q·d)/3 ,  C(d,2)+C(p−d,2) ,  C(d,2)+(d(p−d)+C(p−d,2))/3 }.
```

## Method (two independent verifications per instance)
For each `(p,q,d)` the script **builds the actual graph** and enumerates all triangles
(KKK and KKI) and all edges.

- **(LP)** Solves the direct fractional triangle-packing LP
  `maximize Σ_t x_t s.t. Σ_{t∋e} x_t ≤ 1, x_t ≥ 0` with SciPy HiGHS; its optimum is
  `ν₃*(H)`, compared against the closed form `F(p,q,d)`.
- **(EXACT)** Builds, for the branch attaining `F`, the explicit symmetric fractional
  **cover** (exact rational weights on the four edge classes `E(N), E(N,I), E(N,R), E(R)`:
  uniform `1/3`; separated `a=e=1`; hot `a=1,c=e=1/3`) and verifies **with exact rationals**
  that (a) every triangle is covered with total weight `≥ 1` and (b) the cover value equals
  that branch value `= F`. A feasible cover of value `F` proves `ν₃*(H) = τ₃*(H) ≤ F`
  **exactly**, so the float tolerance in (LP) cannot hide a gap — the upper bound is
  certified by exact arithmetic.

Both are **independent, direct-graph** checks (neither uses the reduced 4-variable
symmetrized LP of the proof).

> **Note (adversarial-audit fix).** An external adversarial audit (Block E) observed that
> an earlier version *described* the (EXACT) check but only ran (LP). The (EXACT)
> rational cover certificate above is the implemented fix; the float tolerance concern is
> thereby resolved by an exact upper-bound certificate.

## Files
- `verify_common_profile_LP.py` — the audit script.
- `results/common_profile_LP_results.txt` — full log.
- `certificate_block02.pdf` — audit certificate (English).

## How to reproduce
```
python verify_common_profile_LP.py
```

## Result
**351/351 instances match** (grid `3 ≤ p ≤ 8`, `0 ≤ q ≤ 8`, `0 ≤ d ≤ p`), maximum
observed `|LP − F| = 3.9×10⁻¹⁴` (solver floating-point noise; closed form is exact).
