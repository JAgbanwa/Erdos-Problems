# E1 — Claim semantics (first pass, independent)

Inputs: EN md `a501d53b…` (line numbers below), literal Lean headers extracted by
`20_EVIDENCE/E3/extract_headers.py` (`headers_*.txt`). No author verdict/report was used.
Labels: FACT_WITHIN_SCOPE = statement reading; the Lean column is the literal type (static; kernel
confirmation is E4).

## Claim map (headline and quantitative)

| ID | Claim (EN line) | Scope type | Literal hypotheses/quantifiers | Lean declaration (static) | Semantic verdict |
|---|---|---|---|---|---|
| A | Thm A l.53-61: ∃b ∀n≥0 ∀ chordal G: cp≤c4≤M(n)+b | all-order additive | b before n,G; chordal = cycle-chord def; M(n)=⌊n(n+1)/6⌋ (ℕ div) | `Erdos81AllOrders.erdos81_all_orders_additive`; explicit b≤T(h+8): `ExplicitThreshold.erdos81_all_orders_bounded_additive` | MATCH |
| B1 | Thm B (1.1) l.63-68 | eventual exact upper | ∃N ∀n≥N ∀ chordal G ∃Q order≤4, \|Q\|≤M(n) | `Erdos81Unconditional.erdos81_cliquePartition` | MATCH |
| B2 | Thm B (1.2) max over chordal = M(n) | eventual exact max, unrestricted | witness Q order≤4, size M(n), minimal among all partitions | `PaperTheorems.erdos81_max_eq` | MATCH |
| C | Thm C l.82-97: ∀s ∃N_s ∀n≥N_s, rsd≤s ⇒ c4≤Q_s(n); ∃ attaining G with cp=Q_s | fixed-defect, eventual; lower witness unrestricted | rsd def: ∀U ∀ clique R⊊U (∅ allowed) ∃v∈U∖R, ∃ clique C⊆N_U(v), \|N_U(v)\|≤\|C\|+s | `DefectExplicitPublication.rooted_defect_eventual/_maximum`; def `RootedSimplicialDefect.RootedDefectAt`; `defectTarget s n = targetSize(n+s) − C(s+1,2)` (ℕ truncation irrelevant for n≥N) | MATCH (definition equivalent to [15] rsd; see E7) |
| C′a | Thm C′ (6.12) l.910-936 | fixed s; explicit γ_s, N_s^stab, A_s=max(40000(s+1)^3,2/ε_s)=2·10^41(s+1)^8 | real δ, 0≤δ≤γ_s n²; hyp c4(G)≥Q_s(n)−δ (∀ order-4 Q); root C clique of G, \|D\|=s, 2≤\|C\|≤\|H\|, partition of V | `SublinearResearch.fixed_defect_joint_stability_real` (`E32.IsDefectRoot`, `rootEdit`, `rootBaseline=(\|C\|+\|D\|)\|H\|−C(\|C\|,2)`) | MATCH |
| C′b | (6.13) N_bad, E_bad for every unrestricted Q, real τ; root before Q,τ | same-root, unrestricted partitions | ∀Q ∀τ∈ℝ, \|Q\|≤Q_s+τ | same; canonical = `E32.IsCanonicalPiece` (C∪D–H edges; C,C,H triangles); E_bad = Σ C(\|K\|,2) over noncanonical | MATCH (Lean allows any real τ, not only τ≥0: stronger) |
| C′c | Cor 6.3 (6.17) optimal-size template, square-root term | fixed s | same hyp.; T admissible extremal (core size nearest to (2(n+s)+1)/6) | `fixed_defect_exact_extremal_edit_real` | MATCH; resized core not claimed clique ✓ |
| C′d | (6.18) cp=Q_s ⇔ c4=Q_s ⇔ G≅E_s(n,k), k nearest | eventual classification | — | `E32.cp_classification_of_theoremCPrimeC` + `FixedExplicit.fixed_defect_stability_explicit` (premise supplied) | MATCH (the implication alone is conditional; the claim map says so) |
| 6.3a | Prop 6.3a (6.20)-(6.21) | explicit family, each fixed s | n+s=3q, 2s+2≤q, 1≤d, 2d≤q; every labelled optimal template | `OptimalTemplateObstruction.shifted_template_witness/_sqrt_witness/no_linear_optimal_template_bound/optimal_family_nonempty` | MATCH, but Lean statement is existential (∃G) while the text names the explicit graph G_{s,q,d}; explicit form lives in the proof (OBSERVATION E1-O1) |
| 6.1 | Thm 6.1 (6.7) chordal: M−B+m/16+A/2≤δ, d_E=m+A≤16δ; γ=η0/4 | chordal, eventual | rational δ in `chordal_linear_stability_sixteen`; real δ in `chordal_joint_stability_real` | IntegralStability / PublicationStability | MATCH (Lean also gives 2≤\|R\|≤n−\|R\| and the 117/1825, 12687/20000 form) |
| 6.1a | Cor 6.1a τ+48δ, 10τ+480δ, same root, unrestricted Q | chordal | text says τ≥0; Lean any real τ | `chordal_joint_stability_real` | MATCH (Lean stronger in τ) |
| 6.2 | Cor 6.2 / (6.9) eventual classification cp & c4 | chordal eventual | — | `ExtremalClassification.chordal_extremal_classification` | MATCH |
| 6.4 | Prop 6.4 (6.22) all orders incl. 0, s≤n; (6.23) band 4s≤n | finite fractional bound; uniform integral version | certified optimum w (not a feasible dual) | `certified_shifted/refined_fractional_bound_all_orders`; `uniform_shifted/refined_partition_bound` (∃N ∀n s, N≤n, s≤n — threshold independent of s) | MATCH |
| 6.5 | Thm 6.5 sequences: orders→∞ (no monotonicity), s_j=o(n_j); (6.24) upper excess o(n²); (6.25)-(6.26) with eventual near-extremality, rational δ_j, τ | sublinear, arbitrary order sequences | Tendsto order atTop atTop; ∀ᶠ hypothesis | `sequence_arbitrary_orders_partition_bound/_stability` | MATCH ((6.25) d_E expressed as missing+outside, equal to d_E(G,S_R) for a clique R) |
| 6.6 | Cor 6.6 tower T(P(s)), uniform ≤S, s_max(n) | exact bound, uniform band | P(s)=c_T(s+1)^1680, c_T=h+c_far+841780, c_far=c_poly(128·10^82)^105 | `E35.theoremC_tower/_uniform/_uniform_sMax`; `sMaxT = Nat.findGreatest` | MATCH (inverse caveat stated) |
| C.4 | N_far(η)≤T(⌈c_poly/η^105⌉), 0<η≤1 rational | uniform in margin | — | `E35.NfarE_le_tower_poly` (cPoly = 4·17664^5·9000^105+3006) | MATCH |
| 3.1 | Thm 3.1 ∀ξ>0 ∃N ∀G ∀ rational x: w(x)−g(P)≤ξn² (all graphs) | uniform transfer | — | `RC01Final.rc01_uniformRoundingTarget` (`MixedRounding.UniformRoundingTarget`) | MATCH |
| D.2 | Prop D.2 n≡4 mod 6, K_n order≤3 ⇒ >M(n) | fixed family | — | `DefectSharpPublication.order_three_insufficient` | MATCH; scope limited to s=0/K_n (stated) |
| F.3a/b | Lemma F.3a (\|D\|−\|C\|−s)_+²≤ordNE; Cor F.3b | finite, all D | ℕ truncated subtraction = positive part; ordered nonedges | `exists_clique_additive_defect`, `recover_clique_from_edit` (u rational ≥0) | MATCH |
| G.1 | Σx_T ≤ ν3+(10+d/2)n, chordal K_{d+2}-free (annex) | fixed d, triangle (not mixed) gap | — | `BoundedCliqueGap.chordal_gap_linear_cliqueFree` (annex, separate) | MATCH |
| G.2 | Prop G.1 N0>exp(t²/16) for the CleanupAtWith contract | contract-specific | ε rational | `FarExploration.CleanupRigidVerdict.threshold_gt_exp` (not re-extracted) | Not re-extracted (static text only) |

## Required distinctions (mandate §4 E1) — checked
- All-order additive (Thm A) vs eventual exact (Thm B, C) vs fixed-defect (C, C′, 6.3, 6.3a) vs uniform-in-defect (6.4, 6.6, (C.4)) vs sublinear sequences (6.5): kept separate in text and Lean. No growing s is substituted into a fixed-s theorem (6.5 goes through `SublinearEdit`/[22] and `RootScore`).
- Unrestricted partitions: lower bounds (6.1),(6.2),(E.5),(6.20) and partition-control (6.13),(6.26),Cor 6.1a quantify over all `CliquePartition` (no order bound); upper bounds are order ≤4.
- Actual vs resized root: C′ root C is a clique of G; Cor 6.3 resized core is explicitly not claimed a clique (text l.1012; Lean gives only an admissible extremal T).
- Thresholds: (F.1) N_s^stab is separate from F_s; Cor 6.6 bounds F_s only (stated l.1126).

## E1 observations
- E1-O1 (OBSERVATION): Prop 6.3a / abstract "An explicit family" — Lean statements are existential; the explicit family is in the proof term, not the type.
- E1-O2 (OBSERVATION): Cor 6.1a text "τ ≥ 0" and (6.13) "τ≥0"; Lean proves the bounds for all real τ (harmless strengthening).
- E1-O3 (MINOR, wording, l.1259): "under the stronger near-extremality hypothesis on c4" — c4(G)≥Q−δ is the *weaker* hypothesis (implied by cp(G)≥Q−δ since cp≤c4); the same sentence then correctly says it applies to cp. Also reported by E7 (E7-M2).

**E1 first-pass status: PASS** (no semantic defect in headline statements; dynamic confirmation of elaborated types is part of E3/E4).
