# Adversarial Audit Report — Paper III

**Paper:** Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing (Paper III, Erdős #81 series)
**Version:** v1.1.5 near-final editorial
**Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
**Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`
**Audit date:** 2026-07-28
**Auditor:** Claude Opus 4.8 (Anthropic), invoked via Claude Code
**Protocol:** AI Adversarial Audit v1.0 + Lean (7 blocks A–G)

---

## Global Verdict: PASS_WITH_OBSERVATIONS

No blocking mathematical, computational, citation, dependency, AX1/AX2-overstatement, or
load-bearing Lean/manuscript mismatch was found. The headline results (Theorem 1.1, Corollary 1.2)
are sound and correctly stated as conditional on the two external inputs AX1 and AX2; the near-extremal
corridor is genuinely unconditional; and AX1/AX2 are faithful to the cited literature and not overstated.

Two non-blocking observations remain (both in the Lean axiom-footprint layer), one of which refutes a
fine-grained per-node dependency statement in §11.6. Neither affects any mathematical claim.

---

## Summary Table

| Block | Scope | Verdict | Findings |
|---|---|---|---|
| A | Claim faithfulness | PASS | 9 claim families mapped; all EXACT |
| B | AX1/AX2 literature scope | PASS | Both faithful; AX2 uses proven 0.9+ε; 1 obs. |
| C | Bulk/sparse/corridor proof attack | PASS | 8 attacks; 0 vulnerabilities |
| D | Counterexample & boundary search | PASS | No counterexample; hypotheses load-bearing |
| E | Independent computation | PASS | 60,541 checks + LP/ILP; 0 failures |
| F | Audit the internal audit | PASS | Full coverage; internal checks non-premise |
| G | Lean verification | PASS_WITH_OBSERVATIONS | Build OK; 2 axioms; corridor closed; 1 minor node-attribution obs. |

---

## 1. Paper Under Audit

**Theorem 1.1.** There is an absolute constant `C` such that every split graph `G` on `n` vertices
satisfies `Φ(G) = |E(G)| − 2ν₃(G) ≤ n²/6 + C·n`, where `ν₃` is the maximum number of pairwise
edge-disjoint triangles.

**Corollary 1.2.** With the same `C`, the clique-partition number satisfies `cp(G) ≤ n²/6 + C·n`
(via `cp(G) ≤ Φ(G)`, eq. 1.1).

The leading constant `1/6` is sharp, witnessed by `K_p ∨ K̄_{2p}` (`n = 3p`, `Φ = n²/6 + n/6`). `C`
is non-effective (disclosed §11.3), inherited from the non-effective thresholds of AX1/AX2.

The proof is a minimal-counterexample induction on `n`: a low-degree independent vertex is deleted
(the quadratic terms telescope exactly), and the all-high-degree case is closed regime-by-regime in
`α = q/p`: high-ratio (`2p ≤ q+1`, closed), sparse (`α → 0`, AX2), bulk (`α ∈ [ε, 2−ε]`, AX1), and
near-extremal corridor (`α → 2`, closed).

---

## 2. Block A — Claim Faithfulness (PASS)

Every manuscript claim maps to a Lean declaration of faithful type: Theorem 1.1 → `Theorem_1_1`;
Corollary 1.2 → `Corollary_1_2`; Theorem 3.1 → `E_3_1`/`Corollary_10_4` (`3 ≤ p`); bulk → `E_4_3`;
sparse → `E_8`; corridor → `Prop_10_1_low`/`Prop_10_1_mid`; `cp ≤ Φ` → `cp_le_Phi`; weak duality →
`nu3Star_le_tau3Star`; the three v1.1 packing corollaries → `factorization_assignment_packing`,
`double_factorization_packing`, `reserved_gain_packing_bound_subset`. Nine claim families, all EXACT.
See `blockA_claim_faithfulness/README.md`.

---

## 3. Block B — AX1/AX2 Literature Scope (PASS)

**AX1 (Haxell–Rödl/Yuster).** Manuscript Theorem 2.1 reproduces the literature statement
(`ν_H* − ν_H = o(n²)`, every fixed `H`, uniform over `G`) and specializes to `H = K₃` — a weakening,
never a strengthening. The Lean cover-side form (`τ₃* − ν₃ = o(n²)`) is justified by finite LP strong
duality `ν₃* = τ₃*` (a proved classical fact); the resulting axiom is **true** and **not overstated**.
*Observation F-B02:* AX1 bundles strong LP duality with Haxell–Rödl, while Lean proves only weak
duality; both are standard and the substitution is disclosed (§11.6).

**AX2 (Dross + Barber–Kühn–Lo–Osthus).** Manuscript Theorem 2.3 uses the **proven** threshold
`δ(H) ≥ (0.9+ε)n`, **not** the conjectured Nash-Williams `0.75n`. Hypotheses (triangle-divisibility,
large order, min-degree) match the literature exactly. **Not overstated.**

See `blockB_AX1_AX2_literature_scope/README.md`.

---

## 4. Block C — Bulk/Sparse/Corridor Proof Attack (PASS)

Eight attack vectors, all repelled: (1) the induction telescoping `(n−1)²/6 + (2n−1)/6 = n²/6` is
exact; (2) `Phi_le_erase_independent` monotonicity holds (induced subgraph ⇒ `ν₃` non-increasing);
(3) the regime split is exhaustive; (4) the bulk margin `μ(α)p²` absorbs AX1's `o(n²)` loss; (5) the
corridor sub-split `s²≤36p` vs `s²>36p` is exhaustive under the regime constraints; (6) the sparse
residual is triangle-divisible with `δ ≥ 0.91p`; (7) the constant `C` is a genuine finite absolute
constant (honestly non-effective); (8) Corollary 1.2 follows from `cp ≤ Φ`. Zero vulnerabilities.
See `blockC_bulk_sparse_corridor_proof_attack/README.md`.

---

## 5. Block D — Counterexample & Boundary Search (PASS)

Extremizer `K_p ∨ K̄_{2p}` achieves `n²/6 + n/6` (sharpness confirmed, `ν₃ = C(p,2)` by ILP for small
`p`); regime boundary `q = 2p−1` handled by the closed high-ratio bound; corridor threshold `p = 2304`
exact. The `p=2, d=0` case where the closed form `F = 1/3` diverges from the true `τ₃* = 0` was traced
to my test **exceeding the theorem's stated hypothesis `3 ≤ p`** — the hypotheses are load-bearing and
correctly stated; this is not a defect. No counterexample found.
See `blockD_counterexample_and_boundary_search/README.md`.

---

## 6. Block E — Independent Computation (PASS)

An independent Python script (`verify_paper3.py`, exact `Fraction` + `scipy` LP + `pulp` ILP)
reproduced: the E-3.1 formula `F(p,q,d)` vs brute-force LP over 464 common-profile instances
(`p ≥ 3`), with `F = τ₃* = ν₃*` confirming strong duality; `μ(α)` continuity/nonnegativity; `rp(t) =
χ'(K_t)`; the extremizer identity (`p = 1..59`); corridor threshold `p = 2304`; and full regime-split
coverage (`1 ≤ p,q ≤ 199`). **60,541 checks, 0 failures.**
See `blockE_independent_computation/README.md` and `results/verify_paper3_output.txt`.

---

## 7. Block F — Audit the Internal Audit (PASS)

The manuscript's internal computational audits (46,481 checks; Appendix C) are explicitly framed as
non-premises (§1.6, §11.6) — the proof is analytic and Lean-verified. This external audit
independently reproduced the load-bearing computations (Block E) and the Lean freeze, with full
agreement. No coverage gap in the mathematical content.
See `blockF_audit_the_internal_audit/README.md`.

---

## 8. Block G — Lean Verification (PASS_WITH_OBSERVATIONS)

`lake build PaperIII` → 8060 jobs, 0 errors. Zero `sorry`/`admit`/`unsafe`/`native_decide`; exactly
two axioms `AX1`, `AX2`. Axiom gates (`#print axioms`) classify each node:

| Node | Footprint | Class |
|---|---|---|
| `Theorem_1_1`, `Corollary_1_2` | standard + AX1 + AX2 | AX1+AX2 |
| `E_4_3` (bulk) | standard + AX1 | AX1 |
| `E_8` (sparse) | standard + AX1 + AX2 | AX1+AX2 |
| `Prop_10_1_low/mid`, packing corollaries, `Corollary_12_2_bound`, `Phi_le_high_ratio`, `cp_le_Phi`, `nu3Star_le_tau3Star` | standard only | **closed** |

Matches the manuscript: Theorem 1.1/Cor 1.2 conditional on AX1+AX2 ✓; corridor genuinely closed ✓;
AX2 confined to sparse-type nodes ✓; bulk is AX1-only ✓.

**Observation O-G1 / finding F-G05 (minor).** The manuscript §11.6 (line 1822) and audit table
(line 1839) state the **sparse node** is "proved relative to `AX2`" (AX2 only). The gate shows the
exposed sparse node `E_8` (hypothesis `2q ≤ p`) depends on **AX1 + AX2**: its proof dispatches the
sub-range `α ∈ [1/12, 1/2]` to the bulk lemma `E_4_3` (AX1) and only the very-sparse core
`E_8_very_sparse_packing_estimate` (`12q < p`) is AX2-only. This is a per-node attribution
imprecision, **not** a mathematical or scope defect (Theorem 1.1 is AX1+AX2 regardless; the
intermediate range genuinely is bulk-type). Recommended editorial fix: record the sparse *node* `E_8`
as `AX1+AX2`, or attribute "AX2-only" to the very-sparse core lemma.

**Observation O-G2 / F-B02 (none).** AX1 bundles strong LP duality (see Block B).

See `blockG_lean_verification/README.md` and `results/axiom_gates.txt`.

---

## 9. Findings Summary

35 findings in `findings/FINDINGS.csv`. Outcomes: 34 CONFIRMED, 1 REFUTED (F-G05, the sub-claim
"sparse node depends on AX2 only"). Severities: 34 `none`, 1 `minor` (F-G05). No `major` or `blocking`
finding.

---

## 10. Conclusion

Paper III's central results survive the seven-block adversarial audit. Theorem 1.1 and Corollary 1.2
are correctly established **conditional on the two external inputs AX1 and AX2**, both of which are
faithful to the cited literature and not overstated (AX2 in particular uses the *proven* `0.9+ε`
threshold, not the conjectured `0.75n`). The near-extremal corridor is genuinely unconditional, as
claimed and as confirmed by the closed axiom footprints of `Prop_10_1_low/mid` and the packing
corollaries. Independent computation (60,541 checks) reproduced every load-bearing quantitative claim.

The single earned discrepancy is a **minor, non-blocking** Lean-node axiom-attribution imprecision:
the formalized sparse node `E_8` carries `AX1 + AX2` (not `AX2`-only as §11.6 states), because it
reuses the bulk lemma on an intermediate `α`-range. No mathematical claim is affected.

**Global verdict: PASS_WITH_OBSERVATIONS.**

---

## Appendix: Reproduction

### Independent computation
```bash
cd blockE_independent_computation/scripts
python verify_paper3.py
```

### Lean build
```bash
cd lean_v1.0_freeze
lake build PaperIII
```

### Axiom gates
```bash
cd lean_v1.0_freeze
lake env lean AuditGates_PaperIII.lean   # gate file archived in blockG_lean_verification/results/
```

### Escape-hatch scan
```bash
cd lean_v1.0_freeze
grep -rn 'sorry\|admit\|unsafe\|native_decide' --include='*.lean' PaperIII
grep -rn '^axiom ' --include='*.lean' PaperIII
```

---

*Report generated 2026-07-28 by Claude Opus 4.8 (Anthropic), invoked via Claude Code.*
