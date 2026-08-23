# Block D — Counterexample and Boundary Search

**Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing** (v1.1.5)

- **Auditor:** Claude Opus 4.8 (Anthropic), via Claude Code
- **Date:** 2026-07-28
- **Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- **Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Verdict: **PASS**

Directed searches for counterexamples and for pathological boundary behavior found **no counterexample**. Every boundary probed behaves consistently with the manuscript's claims *as stated* (i.e., within their declared hypotheses).

## Searches performed

### 1. Extremizer family `K_p ∨ K̄_{2p}` — sharpness without violation

For the join of a `p`-clique with an independent set of size `2p` (so `n = 3p`):

```
Φ(K_p ∨ K̄_{2p}) = n²/6 + n/6
```

This **matches the manuscript's claimed extremizer value**, confirming the leading constant `1/6` is **sharp** — no linear improvement to `n²/6` is possible. Crucially, `n²/6 + n/6 ≤ n²/6 + Cn` for any `C ≥ 1/6`, so the extremizer **does not violate** Theorem 1.1; it saturates the quadratic term and sits comfortably under the linear envelope. Verified for `p = 1..59` (Block E). The integral packing `ν₃ = C(p,2)` was confirmed by ILP for small `p`.

### 2. High-ratio boundary `q = 2p − 1` (i.e. `s = 1`)

At the high-ratio/corridor boundary, `Phi_le_high_ratio` yields `Φ ≤ n²/6 + n/2`. No counterexample: the bound holds with room to spare relative to the extremizer. The boundary is inclusive and correctly handled by the `2p ≤ q+1` regime test.

### 3. Boundary `p = 2, d = 0` — an honest finding

An initial *broad* fractional-formula test flagged an apparent discrepancy at `p = 2, d = 0`: the closed form `F` evaluates to `1/3`, whereas the actual `τ₃* = 0` (a graph with `p = 2` has no triangles, so the fractional cover is trivially 0).

**Resolution — not a defect.** Theorem 3.1 carries the hypothesis `3 ≤ p`. The point `p = 2` lies **outside the stated domain** and is correctly excluded. The discrepancy is an artifact of the auditor's test exceeding the theorem's declared hypotheses, not a flaw in the paper. This is a *positive* finding: it demonstrates the `3 ≤ p` hypothesis is **load-bearing and correctly stated** — remove it and the formula genuinely breaks, exactly where the manuscript says it must not be applied.

### 4. Corridor threshold `p = 2304`

The mid-corridor switch `s² ≤ 36p` vs `s² > 36p` interacts with the `Prop_10_1_mid` requirement via `36p = p²/64`. Solving: `36 = p/64 ⟺ p = 2304` — verified **exact**, with the inequality strict on both sides (`p < 2304 ⟹ 36p > p²/64`; `p > 2304 ⟹ 36p < p²/64`). No off-by-one or boundary leakage.

### 5. Regime coverage sweep

An exhaustive sweep over `1 ≤ p, q ≤ 199` confirmed that **no** `(p, q)` with `p, q ≥ 1` escapes all four regimes (high-ratio, sparse, bulk, corridor). Zero uncovered lattice points.

## Summary

| Search | Target | Result |
|---|---|---|
| Extremizer `K_p ∨ K̄_{2p}` | Violation of `n²/6+Cn` | None; sharpness confirmed (`p=1..59`) |
| High-ratio boundary `s=1` | Counterexample | None (`Φ ≤ n²/6 + n/2`) |
| `p=2, d=0` formula probe | Paper flaw | Out-of-domain; hypothesis load-bearing |
| Corridor threshold | Off-by-one at `p=2304` | Exact, strict both sides |
| Coverage sweep `p,q ≤ 199` | Regime gap | 0 uncovered points |

**No counterexample found. All boundary behavior is consistent with the correctly-hypothesized claims.**

**Block D verdict: PASS.**
