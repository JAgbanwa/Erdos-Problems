# Block A — Paper ↔ Ledger faithfulness audit (auditor's reading record)

Auditor: external adversarial audit (Claude, Anthropic model claude-fable-5), 2026-07-21.
Sources read in full: `CLAIMS/LEDGER.md` (226 lines), `CLAIMS/PAPER_v0.9.5/en/PAPER_III_split_lineal_v0.9.5_review_en.md` (2130 lines).
Mechanical presence evidence: `results/blockA_census_results.txt` (35/35 anchors).

## A1 — Statement-by-statement comparison

| Ledger node | Paper location | Hypotheses match | Constants/quantifiers match | Verdict |
|---|---|---|---|---|
| E-3.1 | Theorem 3.1, (3.4)–(3.5) | p ≥ 3 both | F = min of the same three branches, verbatim | **MATCH** |
| E-4.1 | Lemma 4.1, (4.1) | q ≥ 1 both | identical | **MATCH** |
| E-4.2 | Theorem 4.2, (4.3)–(4.5) | 0 < q ≤ 2p both ("Assume 0<q≤2p", §4.2) | μ(α) piecewise (α²/12 on [0,2/3], (2−α)²/48 on [2/3,2]); C_α=(2−2α−α²)/12; −p/4; core step (4.5) with −p/2 — all identical | **MATCH** |
| E-4.3 | §4.3, (4.6) | ε ≤ α ≤ 2−ε | uses AX1 exactly as ledger says | **MATCH** |
| E-5.1 | Lemma 5.1, (5.1) | q ≥ r_p both | identical; Corollary (5.3) closed form (s²−6s+3)/12 identical | **MATCH** |
| E-5.2 | Lemma 5.2, (5.4)–(5.5) | q ≥ r_p both | b_e, V, h=min{r_p,q−r_p}, δ=h/r_p identical | **MATCH** |
| E-6.1 | Lemma 6.1, (6.2) | 2p−3m−1 ≥ 0 both | coefficient (2p−3m−1)/4 identical | **MATCH** |
| E-7.1 | Lemma 7.1, (7.1)–(7.6) | (7.1): b≥2, q≥r_b, b≥χ'(K_ρ); (7.2): b−t_i≥max{ρ,u} ∀i — identical | θ_R, κ_R, and the bound (7.6) term-for-term identical | **MATCH** |
| E-8 | §8, (8.1)–(8.11) | q=o(p), d(v)>(2n−1)/6+k both | conclusion Φ ≤ n²/6+O(n) | **MATCH** |
| E-B | Appendix B / §8.3, (8.5)–(8.6) | \|O\| even | Odd(J)=O, \|E(J)\|≤p−1, Δ(J)≤2 identical | **MATCH** |
| E-D.1 | Lemma D.1 | kernel-perfect, \|L(v)\|≥d⁺+1 | identical | **MATCH** |
| E-D.2 | Lemma D.2 | — | Gale–Shapley, deferred acceptance | **MATCH** |
| E-D.3 | Theorem D.3 | simple bipartite, \|L(e)\|≥Δ | max-degree Galvin case | **MATCH** |
| E-9 | §9 | minimal counterexamples, penalty kn | same branch structure: q≥2p−1 / bulk / α→0 / α→2 short / mesoscopic dichotomy | **MATCH** |
| Prop-10.1 | Proposition 10.1, (10.2)–(10.3) | (i) p≥36, 0≤s≤6√p; (ii) p≥2304, 6√p≤s≤p/8, d(v)>(2n−1)/6+1 — identical | bounds n²/6+2n and n²/6 identical | **MATCH** |
| AX1 | Theorem 2.1 | — | Ledger states the K₃ instance with an explicit ∀ε∃n₀ form; the paper states the general fixed-H theorem and says "We apply this with H=K₃". The ledger axiom is a *weakening* of the paper's Theorem 2.1, and both are within the literature (Block B). | **MATCH (ledger ⊆ paper)** |
| AX2 | Theorem 2.3 | triangle-divisible + δ≥(0.9+ε)\|V\| + \|V\| large — identical; ledger spells out divisibility (\|E\|≡0 mod 3, all degrees even), which is the standard definition and matches the literature | | **MATCH** |
| Cor 1.2 | Corollary 1.2, (1.3) | — | from cp(G) ≤ \|E\|−2ν₃(G) (1.1), identical to ledger | **MATCH** |

**A1 verdict: no statement-level discrepancy found.** Every ledger node appears in the
manuscript with verbatim-equivalent hypotheses, constants, and quantifiers.

## A2 — Dependency DAG reconstructed from the paper's proofs

Reconstructed by reading each proof (NOT copied from the ledger's DAG):

```
LP duality (classical)             -> Thm 3.1
Thm 3.1                            -> Lem 4.1
Lem 4.1 + Appendix A algebra       -> Thm 4.2
Thm 4.2 + AX1 (Thm 2.1)            -> §4.3 (bulk)
χ'(K_t) 1-factorization (classical)-> Lem 5.1 -> (5.2),(5.3)
Lem 5.1 machinery + 2nd moment     -> Lem 5.2
pure counting                      -> Lem 6.1
χ' + Thm 2.2 (= App D: D.1+D.2+König inline -> D.3) + counting -> Lem 7.1
(9.2 degree bound, from minimality) + Dirac + Turán + App B + AX2 -> §8
(5.3) + §4.3 + §8 + Lem 5.2 + Lem 6.1 + Lem 7.1 + §9.3 algebra -> Thm 1.1 (§9)
(5.3) + §9.3 chains (Lem 5.1,5.2,6.1,7.1) [no AX1/AX2]          -> Prop 10.1
Thm 1.1 + (1.1)                    -> Cor 1.2
```

- **Acyclic: YES.** The only candidate cycle is §8's use of the degree bound (8.1),
  which is produced by the minimality setup of §9; the paper states §8's result
  *conditionally on* (8.1) and §9 supplies (8.1) before invoking §8 — a conditional
  lemma consumed later, not a circularity. Prop 10.1(ii) takes the degree bound as an
  explicit hypothesis, so it does not depend on §9's minimality either.
- **§9 assembly uses only cited ingredients: YES** (verified against each branch;
  the §9.3 numeric chains (9.5)–(9.20) were independently re-derived and
  machine-verified in Block D, items D11–D18, including the assembly identity of
  Lemma 7.1 (D23), which the paper does not display).
- The reconstruction agrees with the ledger's DAG (LEDGER.md §"Dependency DAG").

## A3 — "Only two external inputs" census

Mechanical census in `results/blockA_census_results.txt`. Conclusions:

1. **AX1 (Thm 2.1)** is invoked exactly twice as a proof step: §4.3 and §9.1 (bulk). ✔ as claimed.
2. **AX2 (Thm 2.3)** is invoked exactly once: §8.3. ✔ as claimed. Prop 10.1 uses neither. ✔
3. **Thm 2.2 (list edge coloring)** is invoked in §7.2 and proved from scratch in
   Appendix D (kernel lemma D.1, Gale–Shapley D.2, König proved inline in Step 1 of
   D.3 by alternating-path recoloring with the bipartite odd-path parity argument,
   Galvin max-degree case D.3). The Borodin–Kostochka–Woodall refinement is
   explicitly NOT used (hypothesis (7.2) bounds every list by Δ of the gain graph;
   the check `|L| = b−t_i ≥ max{ρ,u} ≥ Δ` is stated and correct since
   deg(v_i)=g_i≤ρ and deg(r)≤u). **The claim that no coloring citation is
   load-bearing is CONFIRMED** (proofs of D.1–D.3 read line-by-line; logically sound).
4. **FINDING A-1 (minor overstatement).** Sections 8 and 2.3 additionally rely on
   *classical* external theorems not covered by AX1/AX2 and not proved in the paper:
   Dirac's theorem (Hamilton cycle at δ>n/2; used twice in §8), Turán's theorem
   (K₅ at δ>3p/4; §8.3/App B), and the 1-factorization of complete graphs
   (χ'(K_t), eq. (2.2), stated without proof; load-bearing for Lemmas 5.1/5.2/7.1
   and hence for Prop 10.1). The paper's §2.4 phrasing "two external *asymptotic*
   inputs" is defensible, and LEDGER.md openly lists Dirac/Turán as E-8
   dependencies; but the stronger phrasings "Sections 5–7 and Proposition 10.1
   depend on no external theorem" (§2.4) and "Proposition 10.1 depends on no
   external theorem whatsoever" (§11.3) overstate: they hold only modulo the
   classical 1-factorization fact (2.2). Severity: MINOR (classical, constructive —
   this audit's scripts construct the factorizations explicitly by the circle
   method, witnessing existence for every order used).

## Other observations (presentational)

- **OBS A-2.** Figure paths in the markdown reference `paperIII_figures_bilingual_v0.9.7/…`,
  but the package ships figures under `CLAIMS/PAPER_v0.9.5/figures/`. Broken relative
  links in the review md (the PDF renders fine). Severity: none (presentation).
- **OBS A-3.** §1.6/§11.6 count "46,390 + 91 = 46,481 checks" and Appendix C names
  scripts (`verify_common_profile_lp.py`, `verify_fractional_margin.py`, …) that are
  NOT part of this review package; the shipped `OUR_INTERNAL_AUDIT/` is a different
  audit with different counts (12 / 351 / 78,384 / 372). Not contradictory, but the
  package alone cannot reproduce the §11.6 numbers. Severity: minor (reproducibility
  of a supplementary claim; no logical weight — the paper itself states no
  computation is a premise).
- **OBS A-4.** Paper's Theorem 2.1 is stated for every fixed H (Haxell–Rödl proved
  single fixed H; Yuster proved families); the proof only needs H=K₃, which is what
  the ledger axiomatizes. Statement is within the cited literature (see Block B).
