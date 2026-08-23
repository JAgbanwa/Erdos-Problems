# Block A — Claim Faithfulness Audit

**Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing** (v1.1.5)

- **Auditor:** Claude Opus 4.8 (Anthropic), via Claude Code
- **Date:** 2026-07-28
- **Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- **Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Verdict: **PASS**

Every load-bearing claim in the manuscript maps to a corresponding Lean declaration, and each mapping is an **EXACT** match (same quantifier structure, same hypotheses, same conclusion). No mismatch, no weakening, no silent hypothesis strengthening was found.

## Scope of this block

This block checks *faithfulness*: does the Lean formalization state what the manuscript claims — no more, no less? It does **not** re-audit the proofs (Block C) or the computations (Blocks E/F). It is a one-to-one claim-to-declaration correspondence check.

## Anchor: the two headline statements

The manuscript's main result and its corollary are formalized with exactly the intended shape (`∃ C`, universally quantified over all split graphs, linear error term):

```lean
Theorem_1_1 : ∃ C : ℝ, ∀ G : SplitGraph,
  ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ)^2 / 6 + C * (G.n : ℝ)

Corollary_1_2 : ∃ C : ℝ, ∀ G : SplitGraph,
  (G.cp : ℝ) ≤ (G.n : ℝ)^2 / 6 + C * (G.n : ℝ)
```

Here `Phi(G) = |E(G)| − 2·ν₃(G)` and `cp(G)` is the clique-partition number. The leading constant `1/6` is present verbatim, and the error is genuinely linear (`C·n`).

## Claim-to-Lean correspondence table

| Manuscript claim | Lean declaration | File | Match |
|---|---|---|---|
| Theorem 1.1 — `Φ(G) ≤ n²/6 + C·n` for every split graph | `Theorem_1_1` | `Main.lean` | **EXACT** |
| Corollary 1.2 — `cp(G) ≤ n²/6 + C·n` | `Corollary_1_2` | `Main.lean` | **EXACT** |
| Theorem 2.1 — Haxell–Rödl / Yuster fractional-integral gap (AX1) | `axiom AX1` | `AX.lean` | **EXACT** (external) |
| Theorem 2.3 — Dross / Barber–Kühn–Lo–Osthus decomposition (AX2) | `axiom AX2` | `AX.lean` | **EXACT** (external) |
| Theorem 3.1 — common-profile closed form `τ₃*(commonProfile p q d) = F p q d`, under `3≤p`, `1≤q`, `d≤p` | `E_3_1` / `Corollary_10_4` (`hp : 3 ≤ p`, `hq : 1 ≤ q`, `hd : d ≤ p`) | `E_3_1.lean` | **EXACT** |
| Lemma 4.1 / 4.2 — fractional cloning + unified margin | `E_4_1`, `E_4_2` | `E_4_agg.lean`, `E_4_2.lean` | **EXACT** |
| E-4.3 — bulk assembly, `α ∈ [ε, 2−ε] ⟹ Φ ≤ n²/6` | `E_4_3` | `E_4_3.lean` | **EXACT** |
| Lemma 5.1 — one-factor averaging; Cor 5.3 — `s = O(√p)` | `E_5_1`, `cor_5_3` | `E_5.lean` | **EXACT** |
| Lemma 5.2 — double-factor bound | `E_5_2` | `E_5.lean` | **EXACT** |
| Lemma 6.1 — polarization | `E_6_1` | `E_6_1.lean` | **EXACT** |
| Lemma 7.1 — reserved-gain | `E_7_1` | `E_7_1.lean` | **EXACT** |
| Prop 10.1 / 10.5 — corridor bounds (low and mid splits) | `Prop_10_1_low`, `Prop_10_1_mid` | `Prop_10_1.lean` | **EXACT** |
| Sparse assembly (§8) | `E_8`, `E_8_Core` | `E_8.lean` | **EXACT** |
| Eq. (1.1) — `cp(G) ≤ Φ(G)` | `cp_le_Phi` | `CliquePartition.lean` | **EXACT** |
| Extremizer `K_p ∨ K̄_{2p}` and its identity | `completeSplit`, `Corollary_10_4b` | `Prop_10_1.lean` / `E_3_1.lean` | **EXACT** |
| Weak duality `ν₃* ≤ τ₃*` | `nu3Star_le_tau3Star` | `Duality.lean` | **EXACT** |
| Unconditional packing corollary 1 — factorization assignment | `factorization_assignment_packing` | `E_5.lean` | **EXACT** |
| Unconditional packing corollary 2 — double factorization | `double_factorization_packing` | `E_5.lean` | **EXACT** |
| Unconditional packing corollary 3 — reserved-gain subset bound | `reserved_gain_packing_bound_subset` | `E_7_1.lean` | **EXACT** |

## Numbering / naming compatibility note

The Lean namespace uses `PaperIII.Theorem_1_1`, `PaperIII.Corollary_1_2`, etc. These correspond directly to the manuscript's Theorem 1.1 and Corollary 1.2. Several supporting declarations retain **historical names** from earlier draft revisions (e.g. `E_x_y` maps to the manuscript's Lemma/Prop x.y, `commonProfile`/`completeSplit` are the formal encodings of the profile and the extremizer). The mapping is stable and unambiguous; no manuscript statement is orphaned and no Lean statement over-claims relative to the manuscript.

## Summary

- **18+ manuscript claims mapped**, spanning the main theorem, corollary, both external axioms, all supporting lemmas/propositions, the extremizer identity, weak duality, and the three unconditional packing corollaries.
- **All EXACT.** No mismatch, no domain drift, no hidden strengthening of hypotheses in the manuscript's favor.
- The `∃ C` existential shape and the `1/6` leading constant are faithfully represented.

**Block A verdict: PASS.**
