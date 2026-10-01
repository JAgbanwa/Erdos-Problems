# Gate E3 report — run_v1.2_r1 (Paper IV v1.2)

Verdict: **PASS with finding X-27**. Evidence directory: `20_EVIDENCE/E3/`.

---

## E3 — Formal conformance, static part (first pass, before any build)

Method: literal header extraction from the frozen source directory (identical to ZIP and manifest, E0)
with the auditor's `extract_headers.py`; outputs `headers_defs.txt`, `headers_defs2.txt`, `headers_ext.txt`,
`headers_chordal.txt`. Definitions opened manually: `RootedSimplicialDefect`, `E32/Basic.lean`,
`ExplicitFixedStability.lean`, `PublicationStability.lean`, `DefectExplicitPublication.lean`,
`DefectSharpPublication.lean`, `E32/Consequences.lean`, `E32/Comparison.lean`, `E32/DeletionInduction.lean`,
`E34/L11Main.lean`, `E34/L11Params.lean`, `E34/Params.lean`, `E34/Pinned.lean`, `RootPartitionStability`,
`PieceEdgeStability`, `FixedDefectPieceEdges`, `OptimalTemplateObstruction`, `E35/Theorem.lean`, `E35/Main.lean`,
`E18/Numeric.lean`, `MixedRounding/Defs.lean`, annex `BoundedCliqueGap/{Gap,Defs,AxiomCheck}.lean`.
The elaborated types are NOT yet kernel-confirmed (E4 will `#check`/`#print axioms` them in the auditor build).

## Definitions vs manuscript
| Notion | Lean | Manuscript | Verdict |
|---|---|---|---|
| clique partition | `FarRounding.CliquePartition`: cliques, card≥2, pairwise edge-disjoint `pairs`, `biUnion pairs = edgeFinset` | exact edge partition (A.1) | MATCH |
| M(n) | `targetSize n = n*(n+1)/6` (ℕ) | ⌊n(n+1)/6⌋ | MATCH |
| Q_s(n) | `defectTarget s n = targetSize (n+s) − C(s+1,2)` (ℕ truncated) | M(n+s)−C(s+1,2) | MATCH for n large (truncation only when M(n+s)<C(s+1,2)) |
| rsd ≤ s | `RootedDefectAt`: ∀U R, R⊆U, R clique, U∖R≠∅ → ∃v∈U∖R ∃C⊆N_U(v) clique, \|N_U(v)\|≤\|C\|+s | §1 l.84 | MATCH; `E32.rsd` = Nat.find, `rsd_le_iff` |
| template T(C,D,H) | `defSplitGraph C D H`: C–C, (C∪D)–H adjacent, nothing else | (K_C⊔I_D)∨I_H | MATCH |
| root | `E32.IsDefectRoot`: disjoint cover, C clique of G, \|D\|=s, 2≤\|C\|≤\|H\| | l.101, l.899 | MATCH |
| baseline | `rootBaseline = (\|C\|+\|D\|)\|H\| − C(\|C\|,2)` | (6.10) k(n−k)−C(k−s,2) | MATCH |
| canonical piece (defect) | `IsCanonicalPiece`: {x,h}, x∈C∪D, h∈H or {c,c',h} | l.908 | MATCH |
| canonical piece (chordal) | `IsCanonicalAt R K`: \|K∖R\|=1 ∧ \|K∩R\|∈{1,2} | l.868 | MATCH |
| E_bad | Σ over noncanonical pieces of C(\|K\|,2) | l.908 | MATCH |
| optimal template | `IsAdmissibleExtremal`: G = defSplitGraph C D H, \|D\|=s, NearestCore(n+s,\|C\|+s) = \|6k−(2m+1)\|≤3 | "nearest integer to (2(n+s)+1)/6" | MATCH |
| γ_s, A_s, N_s^stab | `stabilityGamma = min(min 1 (etaNF/4), epsS/4)/2`; `stabilityConstant = max(40000(s+1)^3, 2/epsS)`; `stabilityThreshold = 2·deletionBase + sharpThreshold + s + 4`, `deletionBase = minDegThreshold + F_s + s + 3 + ⌈1/ε_s⌉ + ⌈A_s⌉ + 1`, `minDegThreshold = ⌈10^50(s+1)^8⌉ + NLoc(NeditE,s,ε_s) + NfarE(etaNF s) + s + 5`; `epsS = 1/(10^41(s+1)^8)` | (6.11), (F.1) | MATCH (term by term) |
| F.11 parameters | `y11 = ⌈256K²/ε²⌉`, `δ11 = 1/(4y²)`, `B11 = ⌊8K/δ11⌋`, `m11V = ⌈2^58(K+1)^15/ε^12⌉` | (F.11) | MATCH |
| pinned sample | `PinnedOn`: ∃ tree T, map ι preserving on-path relation (not required injective), subtrees T_u ∋ ι(x_u), adjacency ⇔ intersection | F.5 | MATCH |
| tower | `E19.tower2`, `E35.Ptower s = cT(s+1)^1680`, `cT = hIter + cFar + 841780`, `cFar = cPoly(128·10^82)^105`, `cPoly = 4·17664^5·9000^105+3006`, `hIter = 4·8^5·2208^5·4500^105·(2·10^16)^105` | §6.3, (6.28) | MATCH |
| s_max | `sMaxT n = Nat.findGreatest (tower2(Ptower S) ≤ n) n` | (6.29) | MATCH incl. the stated caveat |

## Headline theorems
All entries of E1's claim map were compared with the literal headers: quantifier order, exact coverage,
order bounds, unrestricted lower bounds, real/rational deficits and the "root before Q and τ" order all
match. See E1_RECORD.md for the table.

## F.5 case structure (static)
`E34.lemma11_V` = by_cases on (A) every admissible ψ has conf ≥ δ11 n² → `l11_caseA` (thm2 + pinned⇒proper);
else fix ψ with conf < δ11 n²; by_cases (B1) some section c has all rank assignments with mismatch > ε/(2K) n²
→ `l11_caseB1` (claim5_count, block_ineq, δ11·y²=1/4, prefix counting with `card_prefix_le`); else (B2)
`l11_caseB2` produces a chordal glued F with d_E(G,F) < εn², contradicting farness. The three cases are
exhaustive by construction (two nested `by_cases`), the common conclusion is "at most half of the n^m ordered
samples are pinned". Matches Appendix F.5 text l.2320-2341.

## Export and target scope (static)
- `ReleaseExportCheck.lean`: only import `PaperIV`; exactly **224** `#check` lines (recount).
- 19 targets = FREEZE_SCOPE list; union of their import closures = all 607 modules (after correction C-01).
- `ResearchAudit` custom cone check over **75** literal targets (recount = manuscript's 75): forbids roots
  Erdos81/GalvinRoute/RouteB and any axiom outside {propext, Classical.choice, Quot.sound}.
- `OptimalTemplateObstructionAudit`: 6 targets, union cone, same checks.
- `FDCheck.ASCheck`: 6 selected declarations (public Theorem C eventual/maximum, E35.theoremC_tower,
  fixed_defect_stability_explicit, fixed_defect_joint_stability_real, sequence_arbitrary_orders_stability);
  forbids 6 named removal keys (`AlonShapira.lemma_4_2`, two `near_chordal_of_*` lemmas,
  `EditRoute.editApproxAt_all`, `EditRoute.fixedL4Localization_unconditional`, `AFKS.strong_regularity`).
  Scope = named lemmas only, as the manuscript states (§7 l.1138).
- Cone traversal code: type + value constants, recursive; axioms detected via `axiomInfo`. Limitation: does
  not detect relocated/renamed copies (stated in §7), and a constant missing from the environment is silently
  skipped (cannot happen for elaborated terms).

## Observations
- E3-O1: E34 uses `AlonShapira.IsChordal` / `AlonShapira.editDist` (definitions in the RequestProject tree) — the
  manuscript discloses that shared definitions remain (§7). Their agreement with the paper's chordality is used
  through bridge lemmas; dynamic confirmation that the public types use `PaperIV.FarRounding.IsChordal`/
  `RootedDefectAt` only (they do, statically) is sufficient for the public statements.
- E3-O2: Several audit targets (ResearchAudit, OptimalTemplateObstructionAudit, E17.ImprovedFarRoundingAudit)
  contain no `#print axioms`; they rely on custom elaborators. E4 will not rely on them: the auditor writes an
  independent `#print axioms`/cone file.

**E3 static status: PASS (no conformance defect found); dynamic part pending (E4).**

## Dynamic part (after E4, 2026-09-30 22:00 UTC)
- Elaborated types printed by `AuditorChecks.lean` agree with the static headers; all 50 listed public
  declarations exist in the environment built from the cut; 224 exports compile through `import PaperIV` alone.
- The 19 targets are exactly FREEZE_SCOPE; their closure is 607 modules (runner PLAN.json).
- Cone checks: standard axioms only; no `Erdos81` root; ASCheck exclusions confirmed on the six named cones.
- **X-27 (MODERATE):** `E32.cp_classification_of_theoremCPrimeC` (cited in Table 9 for the unrestricted
  equality classification) and `E32.ref15Theorem11_of_theoremCPrimeC` depend, via `E32.theoremC_at` →
  `DefectSharpPublication.rooted_defect_eventual`, on the historical Alon–Shapira removal chain
  (`AlonShapira.lemma_4_2`, `AFKS.strong_regularity`, `EditRoute.fixedL4Localization_unconditional`, …).
  The manuscript presents that chain as historical and not selected (§7 l.1138, E.2 l.1951, ref. [23]) without
  saying that the cp-part of (6.18) and the formal comparison with [15, Theorem 1.1] still use it.

**E3 verdict: PASS with one MODERATE provenance finding (X-27).** No statement–type mismatch.
