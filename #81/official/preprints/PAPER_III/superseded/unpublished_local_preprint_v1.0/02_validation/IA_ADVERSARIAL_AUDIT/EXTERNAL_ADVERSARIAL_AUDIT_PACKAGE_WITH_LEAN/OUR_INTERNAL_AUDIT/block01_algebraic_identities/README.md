# Block 01 — Algebraic identities (symbolic, exact)

## What is audited
Every closed-form algebraic identity the paper's audit relies on (LEDGER "Audit status"),
proved **symbolically and exactly** with SymPy (not numerically):

| ID | Paper location | Claim |
|----|----------------|-------|
| I1 | Theorem 4.2 | `T(G) = ½·Σdᵢ + C_α·p² − p/4` (key identity, `= 0`) |
| I2 | (9.12) | `−1/6 + 2/9 − 7/96 = −5/288` |
| I3 | (9.19) | `s²/6 − s·ρ + 2ρ² = 2(ρ − s/4)² + s²/24` |
| I4 | (9.19) | lower bound `≥ s²/24` (sum-of-squares certificate) |
| I5 | (9.20) | `−1/24 + 5/192 = −1/64` |
| I6 | (9.10) | `δ = (p−s)/p ≥ 7/8` for `s ≤ p/8` (p odd) |
| I7 | (9.10) | `δ = (p+1−s)/(p−1) ≥ 7/8` for `s ≤ p/8` (p even) |
| I8 | §9/§10 | corridor threshold `36p = p²/64 ⟺ p = 2304` (squared form of `6√p = p/8`) |
| I9 | (4.3) | `μ` continuity at breakpoint `α = 2/3` |
| I10 | (4.5) | `C_α·p²` and `μ·p²` closed forms |

## Method
Each identity is verified as `simplify(LHS − RHS) == 0` over the polynomial ring
`ℚ[p,q,d,s,ρ,α]`, or as an exact rational (in)equality, or (I4) via an explicit
sum-of-squares decomposition. No floating point is used.

## Files
- `verify_identities.py` — the audit script.
- `results/identities_results.txt` — full pass/fail log written by the script.
- `certificate_block01.pdf` — signed-off audit certificate (English).

## How to reproduce
```
python verify_identities.py        # exit code 0 iff all checks pass
```

## Result
**12/12 identity checks PASS.**
