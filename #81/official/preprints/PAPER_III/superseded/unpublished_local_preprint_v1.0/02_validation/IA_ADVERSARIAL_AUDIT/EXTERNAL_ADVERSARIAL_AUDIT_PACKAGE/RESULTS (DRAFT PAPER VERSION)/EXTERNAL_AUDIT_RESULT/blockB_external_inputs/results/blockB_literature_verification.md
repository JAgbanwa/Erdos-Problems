# Block B — External inputs AX1/AX2 vs. the literature (verification record)

Auditor: external adversarial audit, 2026-07-21. Method: retrieval of the cited works'
abstracts/statements from public sources (arXiv, publisher indices) on 2026-07-21,
independent of the manuscript's own citation text. Where only secondary confirmation
was available, this is stated.

## B1 — AX1 (Theorem 2.1; Haxell–Rödl [7], Yuster [9])

**Paper's statement (Thm 2.1):** for every fixed graph H, ν*_H(G) − ν_H(G) = o(|V(G)|²)
uniformly over graphs G; applied with H = K₃.
**Ledger's axiom AX1:** the K₃ instance only, in explicit ∀ε>0 ∃n₀ ∀G form.

**Literature verification.**
- Yuster, *Integer and fractional packing of families of graphs*, arXiv:math/0305350
  (= Random Structures & Algorithms 26 (2005) 110–118). The arXiv abstract states
  verbatim: "Our main result is that ν*_F(G) − ν_F(G) = o(|V(G)|²)" for an arbitrary
  *family* F of graphs, uniformly over all graphs G, and adds: "For the special case
  F={H₀} we obtain a significantly simpler proof of a recent difficult result of
  Haxell and Rödl that ν*_{H₀}(G) − ν_{H₀}(G) = o(|V(G)|²)."   [SOURCE_VERIFIED]
- Haxell–Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21
  (2001) 13–38: existence and venue confirmed via Springer index; its single-fixed-graph
  statement is confirmed through Yuster's attribution above and multiple citing works.
  The full journal text is paywalled; the literal in-paper theorem numbering was NOT
  inspected.   [SOURCE_VERIFIED via primary abstract of Yuster + secondary]

**Comparison.** AX1 (K₃ instance, uniform over G) is *weaker than or equal to* both
published results. The ∀ε∃n₀ formalization is the standard unfolding of o(·) with the
uniformity the sources assert. **AX1 is NOT stronger than the literature. PASS.**

Citation metadata check: authors, venues, volumes, years in references [7], [9] match
the public records. PASS.

## B2 — AX2 (Theorem 2.3; Dross [5] + Barber–Kühn–Lo–Osthus [1])

**Paper's statement (Thm 2.3):** for every ε>0, every sufficiently large
triangle-divisible graph H with δ(H) ≥ (0.9+ε)|V(H)| admits a triangle decomposition.
**Ledger's AX2:** identical, with triangle-divisibility spelled out as
|E(H)| ≡ 0 (mod 3) and all degrees even.

**Literature verification.**
- Dross, *Fractional triangle decompositions in graphs with large minimum degree*,
  arXiv:1503.08191 (= SIAM J. Discrete Math. 30(1) (2016) 36–42). The abstract states
  the fractional result at minimum degree 0.9n and states verbatim the combination:
  "for all ε > 0, every large enough triangle divisible graph on n vertices with
  minimum degree at least (0.9 + ε)n admits a triangle decomposition", citing Barber,
  Kühn, Lo, Osthus for the fractional-to-exact conversion.   [SOURCE_VERIFIED]
- Barber–Kühn–Lo–Osthus, *Edge-decompositions of graphs with high minimum degree*,
  Advances in Mathematics 288 (2016) 337–385: venue/volume/year match public records.
  The K₃ case of their theorem converts any fractional threshold above 3/4 into an
  exact decomposition threshold for K₃-divisible graphs; 0.9 > 3/4, so the
  combination is exactly the paper's Theorem 2.3.   [SOURCE_VERIFIED at abstract level]
- Divisibility definition: "triangle-divisible" = every degree even and |E| ≡ 0 mod 3
  is the standard K₃-divisibility (both conditions are necessary for a triangle
  decomposition); the ledger states BOTH conditions, so AX2 requires no less than the
  literature does. PASS.

**Comparison.** AX2 is exactly the published combined statement — the very sentence
appears in Dross's abstract. **AX2 is NOT stronger than the literature. PASS.**

## B3 — Usage localization

Mechanical census (line numbers): see `blockA_faithfulness/results/blockA_census_results.txt`.
- Thm 2.1 (AX1) used as a proof step only in §4.3 and §9.1 (bulk). CONFIRMED.
- Thm 2.3 (AX2) used as a proof step only in §8.3 (sparse). CONFIRMED.
- Proposition 10.1 and the corridor Lemmas 5.1–7.1 use neither AX1 nor AX2. CONFIRMED
  (dependency reconstruction in Block A2; corroborated computationally in Blocks C/D,
  which certify the corridor bounds with no asymptotic input).

## Residual risks / coverage boundary

- The literal in-journal texts of Haxell–Rödl (Combinatorica) and BKLO (Adv. Math.)
  are paywalled; verification of those two rests on their public abstracts, on
  Dross's and Yuster's arXiv statements of the combined/attributed results (primary,
  verbatim), and on consistent secondary citations. Residual risk: LOW — the exact
  sentences the paper needs appear verbatim in the two arXiv abstracts.
- Effectivity: both inputs are ineffective (o(·) rate; "sufficiently large" n₀).
  The paper says so explicitly (§11.3) and never extracts a rate from them. CONFIRMED.

## Verdicts

| Item | Verdict |
|---|---|
| B1 AX1 faithfulness & not-stronger | **PASS** |
| B2 AX2 faithfulness & not-stronger | **PASS** |
| B3 usage localization | **PASS** |
| Citation metadata [1],[5],[7],[9] | **PASS** |
