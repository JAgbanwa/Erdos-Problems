# Block 03 — Unified fractional margin (Theorem 4.2 / E-4.2)

## What is audited
The per-branch completion-of-squares inequality (4.5) that powers Theorem 4.2:

```
F(p,q,d)  ≥  q·d/2 + (C_α + μ(α))·p² − p/2,     α = q/p,
```

for every `(p,q,d)` on the grid `3 ≤ p ≤ 48`, `1 ≤ q ≤ 2p`, `0 ≤ d ≤ p`, together with
the **third-branch dominance** bookkeeping (the hot-neighbourhood branch `t₃` never
breaks the margin).

## Method
Exact rational arithmetic (`fractions.Fraction`), no floating point. For each grid point
we evaluate `F` and the right-hand side exactly and check the inequality; we also record
which of the three branches `t₁,t₂,t₃` attains the minimum (with ties), reproducing the
paper's "45,904 exact rational" and "dominance" audits at a larger grid.

## Files
- `verify_margin.py` — the audit script.
- `results/margin_results.txt` — full log (histogram + verdict).
- `results/margin_failures.txt` — only created if a check fails (none).
- `certificate_block03.pdf` — audit certificate (English).

## How to reproduce
```
python verify_margin.py
```

## Result
**78,384/78,384 exact-rational margin checks PASS.** Third branch is a co-minimiser in
36,317 cases (unique minimiser in 31,303) and never violates the margin.
