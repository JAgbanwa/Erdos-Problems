# E2 — independent mathematics (human-style rederivation by the AI auditor)

**Obligation.** Reconstruct the proof-critical arguments independently; identify every step known only through
Lean or an imported paper and whether the prose suffices for human review.

**Input.** EN md `71417794…` (full read, 11:01–11:05 −03:00). No internal-audit verdict or derivation was read
before this record (reading order §1.2). Method: line-by-line rederivation from the stated hypotheses; exact
numerics delegated to E5 (`e5_exact.py`, 74 checks, 0 failures) and bounded searches to E5 (`e5_search.py`).

Labels: `CALCULATION_VERIFIED` (auditor rederived), `COMPUTATION_VERIFIED` (E5 exact), `LEAN_ONLY` (prose is a
sketch; the auditor could not rederive it from the text alone; correctness rests on the formal proof),
`IMPORTED` (proof in a prior paper; not re-audited here).

| # | Component (EN location) | Status | Auditor notes |
|---|---|---|---|
| 1 | Gain/loss identity, Lemma 2.1, (1.3), (1.3a) | CALCULATION_VERIFIED | |Q| = e − g(P); for any partition g(Q)+|Q| = e with ordinary gain C(|K|,2)−1. |
| 2 | LP duality, (2.2)–(2.4); weight 5/6 bound | CALCULATION_VERIFIED | g(K) ≤ (5/6)|E(K)| for K₃ (2 ≤ 5/2) and K₄ (5 = 5). Strong duality: IMPORTED (Paper I, Fourier–Motzkin in Lean). |
| 3 | (2.5) and ⌊(2n+1)²/24⌋ = M(n) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | n(n+1) ≡ 0,2 (mod 6). |
| 4 | Theorem 3.1 (RC01) as a whole | **LEAN_ONLY / IMPORTED** | Lemma 3.2 (bounded-rank nibble) IMPORTED from Paper III. |
| 4a | Lemma 3.3 (two quotas via auxiliary vertices) | CALCULATION_VERIFIED | Both quota inequalities rederived; uses r(u+a) ≤ |U| (r-uniform) and 2b ≤ β, ε. Codegree of original–auxiliary pairs ≤ 1/p ≤ γ₀. |
| 4b | Lemma 3.4 (pairing of disjoint triangles, marks for K₄) | CALCULATION_VERIFIED | Pair mass ≥ (t₃−3)/2; edge loads do not increase; cross-member codegree ≤ 1/t₃ (the text's 3/t₃ is conservative); gain 4m + b₄ ≥ (1−β)(2t₃−6+5t₄) − 5ε|U| − 5C. Unique decomposition of a 6-edge union of two edge-disjoint triangles checked by hand. |
| 4c | C.1–C.2 cleaning accounts (3.7), (3.10) charging 3 per discarded edge, K₄→faces at x/2 | CALCULATION_VERIFIED (local charging rules) | The counting of discarded edges (3δ + 1/k₀ + d)n² itself depends on the regularity partition and exceptional-class conventions that are **not** written out: LEAN_ONLY. |
| 4d | Joint codegree (3.12)–(3.13), ψ_H ≤ t² normalization | CALCULATION_VERIFIED (per-profile bound 1/(a₃t), 1/(a₄t)) | Fibre lower bounds b_H ≥ a₃t³, a₄t⁴ (counting lemma for regular pairs) and (3.8) retention: LEAN_ONLY. |
| 4e | C.3 schedule: a, δ, z, k₀, h, L_T, M_T | COMPUTATION_VERIFIED | h = ⌊4/(δ/8)⁵⌋ with δ = a²¹/2208, matching Mathlib's `SzemerediRegularity` iteration count convention (E3). Table C.1 rows γ_T ≥ 2^−59485 etc. and the domination "after two iterations": LEAN_ONLY (only asserted). |
| 5 | Corollary 3.5 | CALCULATION_VERIFIED | Needs M(n) ≥ n²/6 for n ≥ 6 (E5; fails for n < 6 as negative control). |
| 6 | Lemma 4.1: mixed transport (4.4), twin potential, existence of a non-twin simplicial pair outside the complete-split family, chordality preservation | CALCULATION_VERIFIED | Transport: loads ≤ 2 after mapping both copies, average restores capacity; e(G_uv)+e(G_vu) = 2e(G). Existence: rederived with the rooted Dirac argument (component with an edge contains a simplicial vertex of G). Lex potential (F₄, twin pairs) strictly increases; +2(s−t+1) > 0. Random tests in E5. |
| 7 | Lemma 4.2 and descent (4.5)–(4.6a); no circularity | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | Theorem 5.0's proof (Lemma 5.1 onward) uses only d(G) < ε₀ and the value hypothesis, not Prop 4.3. F₄ monotone along path preserves the value hypothesis. Crossing point of (4.6a) ≈ 3.6725·10¹² (E5), consistent with "fails for n ≤ 3.6·10¹²". |
| 8 | Prop 4.3 (4.7)–(4.8) | CALCULATION_VERIFIED | From descent d(G) < ε₀ − 1/n and Lemma 5.1's comparator estimate. |
| 9 | Lemma 5.1: (5.1a) three regimes, completing the square, PEO edge bound (a−1)r − C(a,2), missing pairs C(u+1,2), window constants | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | Robustness |ΔF₄| ≤ 4 per edit (the text's 6 is conservative). Fractional realizability of the symmetric K₃/K₄ mixtures in (5.1a) by symmetry: AUDITOR_INFERENCE (plausible, Lean-checked per A.2). |
| 10 | Prop 5.2: R is a clique; (5.3); size bounds p/a, q/a, 48(2p−q)₊ ≤ a, 3D ≤ a | CALCULATION_VERIFIED | Common-neighbourhood-is-a-clique argument rederived. |
| 10a | (5.4) mass bounds 400m < a², 2000(A+2m) ≤ 11a², and palette/width (5.7) 40c ≤ 73p, 40(w−1) ≤ 3p, and the degree/width inequalities before (5.4) | **LEAN_ONLY** (orders of magnitude checked) | The text says "Substituting … gives (5.4) and (5.7)" without the computation; the degree bound 64d_max ≤ 113a + 64|X| is asserted. A human reader cannot verify (5.7) from the prose. |
| 11 | Table 2 piece identity (5.4a) and compatibility | CALCULATION_VERIFIED | |
| 12 | First phase (5.5)–(5.7) → 1600m ≤ 2920f + 219A | CALCULATION_VERIFIED given (5.7) | Equitable recolouring (Kempe), PEO ending in R orientation, cyclic shifts averaging. |
| 13 | Second phase (5.8)–(5.14) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | Moments, failure probabilities, linearization; all rational comparisons exact (E5). |
| 14 | Lemma 5.3 coefficients, (5.16), B_n(p) ≤ M(n) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | Substitution of the lower bound on f is valid because its coefficient is negative (independent of the sign of the bound). |
| 15 | Cor 5.4 (5.17)–(5.18) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | |
| 16 | Assembly of Theorem B; thresholds fixed in advance | CALCULATION_VERIFIED | |
| 17 | §6.1 unrestricted lower bound, (6.2); §6.2 (6.3)–(6.4); §6.4 (6.6) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | ILP confirmation for 2 ≤ k ≤ 5, k ≤ h ≤ 7 (E5). |
| 18 | Theorem A all orders, b = N², tower propagation; optimality of 1/6 (quadratic and linear) | CALCULATION_VERIFIED | Tower internals LEAN_ONLY (item 4e). |
| 19 | **Theorem 6.1**: γ = η₀/4, far branch excluded, (6.7) from (5.15a), 16δ | CALCULATION_VERIFIED | Far branch: |Q| < M − η₀n²/2 < M − δ. 16 is exactly the best constant derivable from the retained account (6.7) (LP in E5: max m + A = 16δ). |
| 20 | **Corollary 6.1a**: (6.7a), (6.7b), 48δ, quantifier order | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | Identity (6.7b) rederived (edges internal/exterior/cross counted exactly) and tested on exact optimal partitions (E5). 48 is tight for the account (6.7) (LP max r + A + 3m = 48δ; 47 fails — negative control). With the stronger (5.15a) coefficients one could obtain ≈ 46.8δ; not a defect. τ ≥ 0 not needed (Lean has τ ∈ ℚ). Root chosen before Q. |
| 21 | Cor 6.2 classification; Prop 6.3; (6.12) | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | |
| 22 | Prop D.1 table / D.2 | CALCULATION_VERIFIED (arithmetic) ; constructions IMPORTED/LEAN_ONLY (Bose/Skolem frames) | ILP: c₄(K_n) ≤ M(n) for n ≤ 10; c₃(K₁₀) ≥ 19 (E5). |
| 23 | Theorem C: E.2 induction removing K_s; E.3 witness and unrestricted lower bound | CALCULATION_VERIFIED + COMPUTATION_VERIFIED | (E.3) increments hold for all n ≥ 1; witness rsd ≤ s by hand and by brute force for small n (E5); (E.5) identity. |
| 23a | E.1 normalization bounds (r ≤ 4ρ/10²⁷ etc.), (E.2b), (E.2d), three-case budget | **LEAN_ONLY** | The prose gives the architecture (IndepAllPeel/Obstr/Budget) but not the derivations; not human-verifiable from the text. (E.2a) and (E.2c)→(E.2e)→Q_s(n) CALCULATION_VERIFIED. |
| 24 | §8.2 (8.1a), §8.3 Prop 8.1 | CALCULATION_VERIFIED (8.3)–(8.5) and the Behrend/Ruzsa–Szemerédi arithmetic | Mathlib's `roth_lower_bound` statement not re-read here. |

**Negative controls.** See E5 (5 exact + 4 search controls). In E2 itself: the auditor checked that replacing
M(n) by the rational envelope (2n+1)²/24 breaks the integrality step (5.16)→B ≤ M (E5 negative control), and
that the far-branch exclusion in Thm 6.1 fails if γ > η₀/2 (then δ could exceed η₀n²/2): with γ = η₀/4 there
is slack, as written.

**No mathematical defect found** in the rederived parts. **Limitation (material for the verdict):** items 4, 4c,
4d, 4e, 10a, 22 (constructions) and 23a are not human-reviewable from the manuscript prose alone; their
correctness rests on the Lean development, whose dynamic check (E4) has **not** been run in this audit (stopped
by the E7 blocker). **E2 = INCONCLUSIVE** (no defect found; coverage incomplete for LEAN_ONLY steps).
