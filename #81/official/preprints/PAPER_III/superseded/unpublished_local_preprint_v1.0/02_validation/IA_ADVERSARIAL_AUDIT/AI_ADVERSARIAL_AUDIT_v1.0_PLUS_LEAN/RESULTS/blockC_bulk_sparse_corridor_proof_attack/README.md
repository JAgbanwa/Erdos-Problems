# Block C — Bulk / Sparse / Corridor Proof Attack

**Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing** (v1.1.5)

- **Auditor:** Claude Opus 4.8 (Anthropic), via Claude Code
- **Date:** 2026-07-28
- **Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- **Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Verdict: **PASS**

Eight independent adversarial attack vectors were mounted against the proof architecture. **Every attack fails** — i.e., the proof withstands each one. No vulnerability was found.

## Proof architecture under attack

The proof is a **minimal-counterexample strong induction on `n`** (in `Main.lean`), splitting into a low-degree deletion step and a high-degree "eventual bound" step. The eventual bound partitions by the ratio `α = q/p` (with `p` = clique size, `q` = independent-set size) into four regimes: **high-ratio**, **sparse**, **bulk**, and **corridor**. Two external axioms AX1 (bulk) and AX2 (sparse) are the only non-effective inputs.

---

### Attack 1 — Break the telescoping in the minimal-counterexample induction

**Attack.** In `global_bound_from_eventual_high_degree`, a low-degree independent vertex `v` with `d(v) ≤ (2n−1)/6 + 1` is deleted. Try to show the quadratic accounting loses slack, so the induction hypothesis `Φ(G−v) ≤ (n−1)²/6 + C(n−1)` cannot be pushed back up to `Φ(G) ≤ n²/6 + Cn`.

**Why it fails.** The threshold `(2n−1)/6` is *exactly* tuned. Deleting `v` drops edge count by `d(v)` and cannot increase `ν₃`, so `Φ` drops by at most `d(v)`. Then:

```
(n−1)²/6 + (2n−1)/6 = (n² − 2n + 1 + 2n − 1)/6 = n²/6      (EXACT)
```

The quadratic terms telescope with **zero residual**, and the linear term obeys `C(n−1) + 1 ≤ Cn` for `C ≥ 1`. No slack is lost. **Attack fails.**

### Attack 2 — Make `ν₃` increase under vertex deletion

**Attack.** `Phi_le_erase_independent` claims `Φ(G−i) ≤ Φ(G) − d(i)` (actually the drop is `≤ d(i)`), relying on `ν₃` being monotone-nonincreasing under deletion. Try to construct a case where deleting a vertex *increases* the maximum triangle packing.

**Why it fails.** `G−i` is an **induced subgraph** of `G`. Any triangle packing of `G−i` is also a triangle packing of `G` (triangles and disjointness lift verbatim), hence `ν₃(G−i) ≤ ν₃(G)`. Edge count drops by exactly `d(i)`, `ν₃` can only decrease, so `Φ` drops by at most `d(i)`. This is **proven in Lean** (`Phi_le_erase_independent`). **Attack fails.**

### Attack 3 — Find a `(p,q)` pair hitting no regime

**Attack.** The eventual bound is a case split over `α = q/p`. Try to exhibit integers `p, q ≥ 1` that fall into *none* of the four regimes (a coverage hole).

**Why it fails.** The regimes are **exhaustive by construction**: high-ratio (`2p ≤ q+1`) ∪ sparse (`2q ≤ p`) ∪ middle (the complement) = everything, and within the middle `α > 1/2 ≥ 1/10`, so it decomposes into bulk (`α ∈ [1/10, 19/10]`) ∪ corridor (`α ∈ (19/10, 2)`). Block E verified computationally that **0 gaps** exist for `1 ≤ p, q ≤ 199`. **Attack fails.**

### Attack 4 — Break the bulk-regime constant

**Attack.** Bulk claims `α ∈ [1/10, 19/10] ⟹ Φ ≤ n²/6` via `E_4_3` + AX1. Try to show the margin `μ(α)·p²` is too small to absorb AX1's `o(n²)` fractional-integral gap.

**Why it fails.** AX1 (cover-side) gives `τ₃* − ν₃ ≤ ε·n²` for `n ≥ n₀(ε)`. The structural margin `μ(α)·p²` is bounded below by a positive constant times `p²` throughout `α ∈ [1/10, 19/10]`; choosing `ε` small enough (which only pushes `n₀` up, still a finite absolute threshold folded into `N`) makes `ε·n² < μ(α)·p²`. `E_4_3` delivers `Φ ≤ n²/6` on the nose. **Attack fails.**

### Attack 5 — Break the corridor sub-split `s² ≤ 36p` vs `s² > 36p`

**Attack.** The corridor (`s = 2p − q`, with `19p < 10q` and `q+1 < 2p`, so `s < p/10`) splits into `Prop_10_1_low` (`s² ≤ 36p`) and `Prop_10_1_mid` (`s² > 36p`, requiring `p ≥ 2304` and `8s ≤ p`). Try to find a corridor point where `Prop_10_1_mid`'s hypotheses `p ≥ 2304` or `8s ≤ p` fail.

**Why it fails.** In the eventual regime `n ≥ N = max(nBulk, nSparse, 7000)`, so `p ≥ 2304` holds. Corridor forces `s < p/10`, hence `8s < 0.8p < p`, so `8s ≤ p` holds automatically. The threshold `36p = p²/64 ⟺ p = 2304` is exact (verified in Block E), and the two sub-cases are exhaustive and each closed **without any axiom**. **Attack fails.**

### Attack 6 — AX2 not applicable in the sparse regime

**Attack.** Sparse uses `E_8` + AX2, which requires a **triangle-divisible** residual graph `H` with `δ(H) ≥ (0.9+ε)·|V(H)|`. Try to show the residual is not triangle-divisible, or that the minimum-degree bound fails.

**Why it fails.** The `E_8` construction produces a residual `H` that is triangle-divisible by design: `|E(H)| ≡ 0 (mod 3)` and all degrees even (the divisibility construction is exhaustively checked in the internal audit to order 18, cross-reproduced in Block F). The minimum degree satisfies `δ(H) ≥ (0.9 + ε₀)·p` with `ε₀ = 1/100`, i.e. `0.91p`, comfortably above the `(0.9+ε)n` threshold AX2 needs. **Attack fails.**

### Attack 7 — The non-effective constant `C` makes the theorem vacuous/circular

**Attack.** `Theorem_1_1` only asserts `∃ C`. Argue this is vacuous (any bound holds for large enough `C`) or circular (C secretly depends on the graph).

**Why it fails.** `C = max(2, N)` where `N ≥ 7000` is a **fixed absolute constant** independent of `G` — the same `C` works for *all* split graphs simultaneously (the `∃ C` is outside the `∀ G`, exactly as in `Theorem_1_1`'s type). It is finite and non-vacuous. Its non-effectivity (you cannot write down its numeric value) is **inherited from AX1/AX2's non-effective thresholds** and is **honestly disclosed in §11.3**. Non-effective ≠ vacuous ≠ circular. This is a disclosed limitation, **not a defect**. **Attack fails.**

### Attack 8 — Corollary 1.2 does not follow from Theorem 1.1

**Attack.** Try to break the step `cp(G) ≤ n²/6 + Cn`.

**Why it fails.** `cp(G) ≤ Φ(G)` is Eq. (1.1), formalized as `cp_le_Phi` (`CliquePartition.lean`), composed with `Theorem_1_1`. The composition is a single transitivity step, machine-checked. **Attack fails.**

---

## Summary

| # | Attack vector | Result |
|---|---|---|
| 1 | Telescoping / threshold tuning | Fails (exact `n²/6`) |
| 2 | `ν₃` monotonicity under deletion | Fails (induced subgraph) |
| 3 | Regime coverage hole | Fails (0 gaps) |
| 4 | Bulk margin vs AX1 loss | Fails (`μp²` absorbs `εn²`) |
| 5 | Corridor sub-split exhaustiveness | Fails (`p≥2304`, `8s≤p`) |
| 6 | AX2 applicability (sparse) | Fails (divisible, `δ≥0.91p`) |
| 7 | Non-effective `C` vacuous/circular | Fails (fixed absolute `C`, disclosed) |
| 8 | Corollary 1.2 derivation | Fails (`cp≤Φ` + Thm 1.1) |

**8 attack vectors mounted, 0 vulnerabilities found.**

**Block C verdict: PASS.**
