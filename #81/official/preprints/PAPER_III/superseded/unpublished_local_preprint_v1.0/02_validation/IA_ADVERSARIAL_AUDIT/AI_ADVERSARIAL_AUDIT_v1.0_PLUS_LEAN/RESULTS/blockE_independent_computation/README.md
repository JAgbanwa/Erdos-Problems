# Block E — Independent Computation

**Verdict: PASS**

- **Paper:** "Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing" (Paper III, v1.1.5)
- **Date:** 2026-07-28
- **Auditor:** Claude Opus 4.8 (Anthropic), invoked via Claude Code

## Scope

Independently reproduce, from scratch, the load-bearing quantitative claims of Paper III using exact
rational arithmetic (`fractions.Fraction`), brute-force linear programming (`scipy.optimize.linprog`),
and integer programming (`pulp`). The script (`scripts/verify_paper3.py`) shares no code with the
manuscript's own audit scripts. Output: `results/verify_paper3_output.txt`.

## Results

| Test | Range | Checks | Result |
|---|---|---|---|
| E-3.1 `F(p,q,d)` vs brute-force LP (`τ₃*` cover and `ν₃*` packing) | `3 ≤ p ≤ 8`, `1 ≤ q ≤ 2p`, `0 ≤ d ≤ p` | 464 instances | PASS — `F = τ₃* = ν₃*` (confirms strong duality on the domain) |
| `μ(α)` definition + continuity at `2/3` + nonnegativity | `α ∈ [0,2]` step `1/100` | ~205 | PASS |
| `rp(t) = χ'(K_t)` (edge-chromatic number) | `t = 0..39` | 40 | PASS |
| Extremizer `K_p ∨ K̄_{2p}` identity `|E| − 2·C(p,2) = n²/6 + n/6` | `p = 1..59` | 59 | PASS |
| Extremizer integral `ν₃ = C(p,2)` (ILP) | `p = 2..5` | 4 | PASS |
| Corridor threshold `36p = p²/64 ⇔ p = 2304` | boundary | 3 | PASS |
| Regime-split coverage (high ∪ sparse ∪ middle = all) + `α ≥ 1/10` in middle | `1 ≤ p,q ≤ 199` | ~59,700 | PASS |
| **Total** | | **60,541** | **0 failures** |

## Key confirmations

- **E-3.1 common-profile formula.** The closed form `F(p,q,d) = min{ (C(p,2)+qd)/3, C(d,2)+C(r,2),
  C(d,2)+(dr+C(r,2))/3 }` (`r = p−d`) matches the brute-force fractional cover optimum `τ₃*` exactly on
  the theorem's stated domain `3 ≤ p`, and `τ₃* = ν₃*` on every instance (independent confirmation of
  finite LP strong duality for these graphs).
- **Boundary honesty.** At `p = 2, d = 0` the closed form gives `F = 1/3` while the graph has no
  triangle (`τ₃* = 0`); this lies **outside** the theorem hypothesis `3 ≤ p` (E-3.1 / `Corollary_10_4`
  carries `hp : 3 ≤ p`) and is therefore expected — the hypotheses are load-bearing and correctly
  stated. Recorded explicitly in the script and as finding F-D03. Not a defect.
- **Sharpness.** The extremizer family reaches `n²/6 + n/6`, confirming the sharp `1/6` leading
  constant and that it respects the `n²/6 + C·n` bound.
- **Regime split is exhaustive** with the bulk lower bound `α ≥ 1/10` holding throughout the middle
  regime — the structural precondition of the proof assembly.

## Reproduction

```bash
cd blockE_independent_computation/scripts
python verify_paper3.py
```

Exit code 0; final line `ALL CHECKS PASSED`.

**Block E verdict: PASS.**
