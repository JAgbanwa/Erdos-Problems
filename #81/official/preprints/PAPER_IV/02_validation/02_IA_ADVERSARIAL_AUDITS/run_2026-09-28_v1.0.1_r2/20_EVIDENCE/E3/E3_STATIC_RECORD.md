# E3 — formal conformance, STATIC part (dynamic checks reserved for E4)

**Obligation.** Compare displayed theorems/quantitative corollaries with Lean types; check edge-partition
semantics, chordality, gain conventions, coercions, strict inequalities, root predicates, threshold dependence,
discharge of premises.

**Inputs.** `LEAN_SOURCE_SNAPSHOT_v1.0.zip` sha256 0a13c01c…f8a7dd (extracted to C:/piv_r2/src, 504 .lean files
matching SOURCES.json f1769273…, see E0/E0_sources_vs_zip.json); annex ZIP 2847a422…837d (internal
SOURCE_MANIFEST.sha256: 39/39 OK after CRLF normalisation); EN manuscript md 71417794….

**Independent method.** Auditor-written extractor `extract_headers.py` (literal text of each header up to `:=`),
manual reading of every definition occurring in the headline types (outputs: `headers_part1.txt`,
`headers_part2.txt`, `defs_part1.txt`, `defs_part2.txt`), textual sweep for escape hatches
(`textual_sweep_counts.txt`, `textual_sweep_hits.txt`), existence check of every backticked identifier in EN/ES
(`name_check.py` → `name_check.json`). The author's audit scripts were **not** used for these results.

## Findings (static)

| Item | Result |
|---|---|
| Partition semantics | `CliquePartition`: pieces are cliques, card ≥ 2, distinct pieces have disjoint `pairs`, `biUnion pairs = edgeFinset` (exact edge partition). `OrderAtMost r`: all pieces card ≤ r. `size` = number of pieces. MATCH with §1/§2. |
| Chordality | `SimpleGraph.IsChordal`: every cycle of length ≥ 4 has two support vertices adjacent by a non-cycle edge (a chord). `PaperIV.FarRounding.IsChordal` is an `abbrev` of it. MATCH. |
| Target | `targetSize n = n*(n+1)/6` (ℕ division = floor). MATCH M(n). |
| Thm A / B / max | headers quantify `∃ b, ∀ n (incl. 0) ∀ G` resp. `∃ N ∀ n ≥ N`; lower witness optimal against all `CliquePartition` (no order restriction). MATCH. |
| Thm 3.1 | `UniformRoundingTarget ε`: `∃ N, ∀ n ≥ N, ∀ G, ∀ x : FracPacking G (ℚ), ∃ P : Packing G, x.value − P.gain ≤ ε n²`; items = cliques of card 3/4, gain C(k,2)−1. No chordality. MATCH, incl. quantifier order. |
| Thm 5.0 | hypotheses n ≥ 4·10¹², chordal, certified optimum, normalized distance < ε₀ to **all** labelled complete-split supports (cores = all subsets), near value; conclusion clique R, `|3|R|−n| ≤ n/50`, order ≤ 4, `|Q| ≤ B_n(|R|) − m/20 − A/2`. MATCH. |
| Thm 6.1 | `γ = eta/4 = 1/(4·10¹⁶)` with `gamma_pos`; δ ∈ ℚ, `0 ≤ δ ≤ γ n²`; hypothesis quantifies over order-≤4 partitions; conclusion: clique R, 2 ≤ |R| ≤ n−|R|, `B ≤ M`, `(117/1825) m + (12687/20000) A ≤ δ`, `(M − B) + m/16 + A/2 ≤ δ`, `editDist(G, S_R) ≤ 16 δ`. MATCH. Manuscript's "there exist γ>0" is realised by an explicit constant. δ rational vs. real: harmless (integrality allows replacing real δ by ⌊δ⌋) — OBSERVATION only. |
| Cor 6.1a | `∃ R clique, 2 ≤ |R| ≤ n−|R| ∧ ∀ (Q : CliquePartition G) (τ : ℚ), Q.size ≤ M + τ → #noncanonical ≤ τ + 48 δ`. Root precedes every partition; **no** order restriction on Q; τ unrestricted (stronger than the manuscript's τ ≥ 0). `IsCanonicalAt`: exactly 1 outside vertex and 1 or 2 root vertices. MATCH (Lean stronger). |
| Cor 6.2 | `CliqueCoverEq G M ↔ CliqueCover4Eq G M` and `CliqueCover4Eq G M ↔ ∃ R, G = splitGraph R (univ\R) ∧ OptimalCore n |R|`; `OptimalCore n k ↔ k=⌊(n+1)/3⌋ ∨ (n≡1 mod 3 ∧ k=⌊(n+1)/3⌋+1)` = (6.4). MATCH. |
| Thm C | `RootedDefectAt G s`: ∀ U R, R ⊆ U, R clique, U\R ≠ ∅ → ∃ v ∈ U\R, ∃ clique C ⊆ N_U(v), |N_U(v)| ≤ |C| + s. Empty root allowed. Target `defectTarget s n = targetSize(n+s) − C(s+1,2)` (truncated ℕ subtraction, irrelevant for n ≥ s+1 by `targetSize_le_defectTarget`). Maximum witness optimal vs. unrestricted partitions. MATCH. |
| Prop 6.3 | Lean gives the fractional upper bound `x.value ≤ 2C(k,2)` for all fractional packings and a clique partition of total (unrestricted) gain `2C(k,2)`; the equality W = W* as a statement about mixed packings is obtained by combination with `SplitCompleteSharpValue`, not literally one declaration. OBSERVATION. |
| Explicit tower | `E18.Numeric.hIter` literal = manuscript h; `E19.tower2 0 = 1`, `tower2 (m+1) = 2^tower2 m` = T; `sharpThreshold = tower2 (hIter+7)`; `b ≤ tower2 (hIter+8)`. MATCH. |
| Annex (8.1a) | `chordal_gap_linear_cliqueFree`: chordal, `CliqueFree (d+2)`, any fractional **triangle** packing: value ≤ ν₃ + (10 + d/2)|V|. Triangular only; not in `import PaperIV`. MATCH. |
| Escape hatches (text) | 0 code occurrences of `sorry`/`admit`/`axiom` declarations/`native_decide`/`implemented_by`/`unsafe`/`opaque`/`extern`/`ofReduceBool`/`skipKernelTC` — all hits are in comments/docstrings. Metaprograms (`elab`, `#eval … CoreM`) exist only in audit modules (E17/*Audit, ConeAudit, PublicationIncrementAudit, ExplicitThresholdAudit, ConstructorBudgetAudit, E19/AxiomCheck, A4S1/IndepAllAudit); none uses `addDecl`. Dynamic `#print axioms` reserved for E4. |
| Identifier existence | All backticked Lean identifiers in EN/ES resolve to modules/declarations in the freeze, except annex names (present in annex) and non-Lean tokens (hashes, file names, namespaces, Mathlib's `Behrend.roth_lower_bound`, [5]'s `Erdos81`/`ExternalInputs.Inputs`). |

**Negative control.** The extractor was run on a deliberately non-existent name (`OrderAtMost` as a top-level decl:
0 hits, correctly, since it is `CliquePartition.OrderAtMost`) — demonstrates the extractor reports absence rather
than fabricating a match.

**Static result.** No manuscript/Lean mismatch found for the headline statements. E3 overall remains
**pending E4** (types/axioms must be confirmed by the kernel in the isolated build; `#check` of the 195 exports
and cone inspection are dynamic).

**Limitations.** Static text matching cannot detect notation/instance tricks that change meaning at elaboration;
this is why E4 re-prints the elaborated types.

## Final status (2026-09-28)

E4 was not run (STOP at the pre-build checkpoint). The static comparison found **no mismatch**, but the dynamic
confirmation of elaborated types, axioms, cones and the 195 exports is missing. **E3 = INCONCLUSIVE.**
