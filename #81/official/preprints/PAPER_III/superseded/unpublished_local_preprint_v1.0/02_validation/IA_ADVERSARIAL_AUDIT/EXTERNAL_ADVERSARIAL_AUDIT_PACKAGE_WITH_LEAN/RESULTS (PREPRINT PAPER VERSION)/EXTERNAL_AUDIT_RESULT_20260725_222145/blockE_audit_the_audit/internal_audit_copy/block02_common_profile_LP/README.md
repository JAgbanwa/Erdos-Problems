# Block 02 — Common-profile LP: ν₃*(H(p,q,d)) = F(p,q,d) (Theorem 3.1 / E-3.1)

## What is audited
The closed-form fractional triangle-packing value of the common-profile split graph
`H(p,q,d)` (clique `K` of order `p`; `q` independent vertices, each adjacent to the same
`d`-subset `N ⊆ K`) equals the three-term minimum

```
F(p,q,d) = min{ (C(p,2)+q·d)/3 ,  C(d,2)+C(p−d,2) ,  C(d,2)+(d(p−d)+C(p−d,2))/3 }.
```

## Method
For each `(p,q,d)` the script **builds the actual graph**, enumerates all triangles
(KKK and KKI) and all edges, and solves the direct fractional triangle-packing LP

```
maximize  Σ_t x_t   s.t.   Σ_{t ∋ e} x_t ≤ 1  ∀ edge e,   x_t ≥ 0
```

with SciPy's HiGHS solver. Its optimum is `ν₃*(H)`. This LP value is compared against the
closed form `F(p,q,d)`. This is an **independent, direct-graph** cross-check of the
formula (it does not use the reduced 4-variable symmetrized LP of the proof).

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
