# Consolidated claim map — Paper IV v1.22-r3

Columns: claim, Lean declaration, semantic verdict, origin of the verdict.

- **Historical rows (H)** come from run_v1.2_r1 `20_EVIDENCE/E1/E1_RECORD.md` (21 rows). They are inherited by identity: the statement text is unchanged across the v1.2→r3 diff chain, and the Lean cut is 615/615.
- **New rows (N, run_v1.22_r3)** are new. They were produced by a static comparison of the literal frozen headers (`20_EVIDENCE/E1/E1E3_HEADERS_CHECK.json`) and the definitions they use with the EN manuscript text, which is identical to r2 outside the five status paragraphs.
- The new rows **were not part of the original E1**. The Lean types used are not newly elaborated: the headers are source text, and their compilation is the run_v1.2_r1 build (module records PASS, exit 0, logs hash-bound).

## H — historical rows (run_v1.2_r1 E1, inherited by identity)

| ID | Claim | Lean declaration | Verdict |
|---|---|---|---|
| A | Thm A, all-order additive | `Erdos81AllOrders.erdos81_all_orders_additive`; `ExplicitThreshold.erdos81_all_orders_bounded_additive` | MATCH |
| B1 | Thm B (1.1) | `Erdos81Unconditional.erdos81_cliquePartition` | MATCH |
| B2 | Thm B (1.2) | `PaperTheorems.erdos81_max_eq` | MATCH |
| C | Thm C | `DefectExplicitPublication.rooted_defect_eventual/_maximum` | MATCH |
| C′a–d | Thm C′ (6.12), (6.13); Cor 6.3 (6.17); (6.18) | `fixed_defect_joint_stability_real`; `fixed_defect_exact_extremal_edit_real`; `E32.cp_classification_of_theoremCPrimeC` + `FixedExplicit.fixed_defect_stability_explicit` | MATCH (X-27 for (6.18)) |
| 6.3a | Prop 6.3a | `OptimalTemplateObstruction.*` | MATCH; X-17 (Lean existential) |
| 6.1 | Thm 6.1 | `IntegralStability…`, `chordal_joint_stability_real` | MATCH |
| 6.1a | Cor 6.1a | `chordal_joint_stability_real` | MATCH; X-18 (Lean real τ) |
| 6.2 | Cor 6.2 | `ExtremalClassification.chordal_extremal_classification` | MATCH |
| 6.4 | Prop 6.4 | `certified_*_fractional_bound_all_orders`, `uniform_*_partition_bound` | MATCH |
| 6.5 | Thm 6.5 | `sequence_arbitrary_orders_*` | MATCH |
| 6.6 | Cor 6.6 | `E35.theoremC_tower*` | MATCH |
| C.4 | (C.4) | `E35.NfarE_le_tower_poly` | MATCH |
| 3.1 | Thm 3.1 | `RC01Final.rc01_uniformRoundingTarget` | MATCH |
| D.2 | Prop D.2 | `DefectSharpPublication.order_three_insufficient` | MATCH |
| F.3a/b | Lemma F.3a, Cor F.3b | `exists_clique_additive_defect`, `recover_clique_from_edit` | MATCH |
| G.1 | (G.1) annex | `BoundedCliqueGap.chordal_gap_linear_cliqueFree` | MATCH |
| G.2 | Prop G.1 | `FarExploration.CleanupRigidVerdict.threshold_gt_exp` | *historically "not re-extracted"*; now covered by row N10 |

## N — new rows (run_v1.22_r3, static header comparison)

Common facts, verified for all 13 headers:
- The source sha256 equals both the manifest and the JSON.
- The `theorem` line and the header text match an independent re-extraction.
- The namespace is the one stated.
- The run_v1.2_r1 module log hash matches, and the module record is PASS with exit 0.
- In `RootPartitionStability`, `SplitMixedGap` and `SplitCompleteSharpValue` the in-scope variables are only `{V} [Fintype V] [DecidableEq V]`, plus `{G} [DecidableRel G.Adj]`. There are no hidden hypotheses.

Definitions read:
- `splitBaseline n p = p(n−p) − p(p−1)/2`, which is B_n(p).
- `outsideEdges` = edges with both ends outside R, i.e. m = e(G−R).
- `missingIncidences` = Σ_{x∈R} the exterior non-neighbours of x, i.e. A.
- `graphFamDistNorm F … n²` = min edit distance to the family divided by n², i.e. d(G).
- `allSplitSupports` = all S_C = K_C∨I_{V∖C} with C ⊆ V.
- `CertifiedFractionalOptimum G w` = a primal and a dual of equal value w; therefore w = W*(G) and e − w = F₄(G).
- `NearH1Calibration.eps = 10⁻¹²`, `eta = 10⁻¹⁶`.
- The chordality predicates `PaperIV.IsChordal`, `FarRounding.IsChordal` and `SimpleGraph.IsChordal` are equivalent by `Iff.rfl` (`ChordalBridge`).

| ID | Claim (EN) | Declaration | Hypotheses and conclusion compared | Verdict |
|---|---|---|---|---|
| N1 | Thm 5.0, strengthened window (§5, (5.0)) | `PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp` | Text: chordal, n ≥ 4·10¹², d(G) < ε₀, F₄ ≥ n²/6 − η₀n² ⇒ a clique R with \|3p−n\| ≤ n/50 and Q of order ≤ 4 with \|Q\| ≤ B_n(p) − m/20 − A/2. Lean: identical hypotheses (`hdist` with scale n², `hnear` as e − w), identical conclusion. It is a local theorem; no global localization is included. | **MATCH** |
| N2 | Thm 5.0, earlier interface ("the earlier window n/4 ≤ p ≤ n/2 remains valid") | `…exists_near_partition_paid_by_root` | Same hypotheses and conclusion with the window n/4 ≤ \|R\| ≤ n/2. The text derives \|3p−n\| ≤ n/50 from the ratios and attributes the stronger window to N1, not to this declaration. | **MATCH** |
| N3 | Cor 5.4 (5.17), root geometry | `PaperIV.NearCriticalDichotomy.chordal_far_or_criticalRoot` | ∃N ∀n ≥ N ∀ chordal G ∀ certified w: F₄ < n²/6 − η₀n² (strict, as in the text) ∨ ∃ R, C with R a clique of G, \|3\|R\|−n\| ≤ n/50, C nonempty, d_E(G,S_C) ≤ ε₀n², \|3\|C\|−n\| ≤ n/10⁴, and \|\|R\|−\|C\|\| ≤ n/100. **C is not asserted to be a clique of G** (the text calls it a "comparator core"; correct). The last conjunct is a difference of cardinalities, **not a symmetric difference**; the text does not assert it, so Lean is slightly stronger. | **MATCH** (Lean stronger) |
| N4 | Cor 5.4 (5.18), density | `…chordal_far_or_edge_density` | Same regime and the same first disjunct ∨ \|e(G) − 5n²/18\| ≤ n²/10⁴. The text states (5.17) and (5.18) "in the second branch". Since both theorems share the literal first disjunct, taking max(N, N′) yields both second-branch conclusions together. The text disclaims an exact density identity ("5/9 describes the asymptotic density"). | **MATCH** (with max of thresholds, which the text implies) |
| N5 | Dichotomy (1.5) | `PaperIV.HybridDichotomy.chordal_far_or_nearStructure` | far ∨ `Nonempty (NearStructureWitness G)`. The structure fields are: `core` (nonempty) with the edit bound to S_core (the complete-split comparator); `regularized : RegularizedRoot G`, whose `isClique` field makes the root a clique of G; `packing` with `IsK34Packing G` (a packing of the original graph); and `accounts` with the physical ledger and the improved 117/1825, 12687/20000 bound. The text says "the alternatives are exhaustive; … not asserted to be incompatible", and the disjunction is inclusive. | **MATCH** |
| N6 | Optimal quadratic coefficient (6.5a), necessity | `PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_optimal` | For rational c, C and a chordal bound by unrestricted clique partitions (`CliquePartition`, no order bound; this matches "even when cliques of arbitrary order are allowed"), 1/6 ≤ c. The real extension in the text is valid: given real c < 1/6 and C, choose rational c′ ∈ (c, 1/6) and C′ ≥ C. Then cn² + Cn ≤ c′n² + C′n for n ≥ 0, which contradicts the rational theorem. The header does not quantify over reals, and the text says so. | **MATCH** (real case by rational enlargement, a valid one-line argument) |
| N7 | Optimal quadratic coefficient, least element | `…erdos81_quadratic_constant_isLeast` | `IsLeast {c ∈ ℚ \| ∃C N, bound}` (1/6). Membership requires Theorem A (M(n)+b ≤ n²/6 + (1/6+b)n for n ≥ 1); the text says "combines it with Theorem A". The set is over rationals. | **MATCH** (rational set) |
| N8 | Optimal linear coefficient (6.5) | `PaperIV.LinearCoefficient.linear_coefficient_optimal` | For rational c < 1/6 and rational B: ∃N ∀n ≥ N ∃ chordal G with every clique partition Q satisfying \|Q\| > n²/6 + cn + B. The real extension in the text (rational c′ ∈ (c, 1/6), B′ ≥ B₀) is valid. The header is **existential in G**; the text names the complete-split witness and writes cp(G) = M(n), which comes from (6.2)/Thm B, not from this header. This is the same nature as X-17. The additive constant is not minimized (the text says so). | **MATCH**; observation of X-17 type (existential witness) |
| N9 | Identity (6.7b) | `PaperIV.RootPartitionStability.sum_rootPieceDefect_eq` | Finite V, R a clique, any clique partition Q (no order bound): Σ rootPieceDefect R K = \|Q\| − B_\|V\|(\|R\|) + A + 3m. `rootPieceDefect R K = numericDefect(\|K∩R\|, \|K∖R\|) = 1 + C(a,2) + 3C(b,2) − ab`, which is d_R(K) of (6.7a). It uses the actual root and unrestricted pieces, not the capped mixed gain. | **MATCH** |
| N10 | Prop D.3 (D.6) | `PaperIV.SplitMixedGap.mixed_gap_zero` **and** `PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities` | Core ∩ Hosts = ∅, 2 ≤ k ≤ h. The first gives: every fractional packing has value ≤ 2C(k,2), and some clique partition has Σ gainOf = 2C(k,2). The first header alone **does not bound the piece order**, so its partition might contain pieces of order ≥ 5 and need not be a mixed packing. The second gives a partition Q′ of order ≤ 4 with \|Q′\| = kh − C(k,2) (also minimal). The edge-count identity (1.3a), g(Q′) + \|Q′\| = e(S) = C(k,2) + kh, gives g(Q′) = 2C(k,2) with K₂/K₃/K₄ pieces, i.e. an integral mixed packing of gain 2C(k,2). Hence W(S) = W*(S) = 2C(k,2). The text cites both declarations ("together with the bounded construction"). Equality of optimal values is not claimed as integrality of the polytope (the text says "it does not assert that every vertex … is integral"). | **MATCH** (needs both declarations plus (1.3a), all present) |
| N11 | Prop G.1 (G.2) | `FarExploration.CleanupRigidVerdict.threshold_gt_exp` | `CleanupAtWith γ C (ε/30) (ε/4) N₀`, unfolded: ∀n ≥ N₀ ∀G ∀ fractional x with triangle mass ≥ (ε/30)n² − 1, ∃y with weighted codegree ≤ γ, triangle mass ≥ C, and gain loss ≤ (ε/4)n². This is literally the contract in the text. With rational ε > 0, real γ ≤ 1/2, real t ≥ 4 and 7ε ≤ e^{−t} ⇒ e^{t²/16} < N₀. The text notes "the precision parameter is rational in the Lean declaration". It is a lower bound for this contract only, as the text states. | **MATCH** (closes historical G.2 "not re-extracted") |
| N12 | Prop G.1, "in particular N₀ > e^72" | `…threshold_gt_exp_seventy_two` | ε ≤ 1/(7e^{34}) ⇒ e^{72} < N₀ (t = 34, t²/16 = 72.25 > 72). | **MATCH** |

The 13 headers map to the 12 N-rows; N10 uses two declarations.

**Supplementary E1/E3 verdict:** 12/12 new rows MATCH. One new observation, of X-17 type, is recorded under N8 (existential witness in the linear-coefficient header; cp(G) = M(n) comes from other declarations). No translation in `SEMANTIC_COVERAGE_SUPPLEMENT.md` was found to be unjustified. Its four warnings — C is not a clique of G; a size difference is not a symmetric difference; D.3 also needs the bounded constructor; real coefficients go through rational enlargement — are all correct.
