# E4 — Formal reproduction (isolated project, shared pinned dependencies)

## Setup
- **Runner:** `auditor_build.py`, written by the auditor. It does not use Lake or the author's runner. It
  compiles serially, one lean process at a time with `-j 8`. Each module gets the lakefile `[leanOptions]`
  (`pp.unicode.fun=true`, `relaxedAutoImplicit=false`, `linter.unusedSimpArgs=false`) plus the owning
  lean_lib's `moreLeanArgs` (`-s 32768`), using Lake's `isBuildableModule` rule. Every command line is
  recorded at the top of each module log.
- **Toolchain:** `lean.exe` v4.28.0, commit 7e01a1bf, sha256 6a66c4a5…
- **Sources:** a fresh extraction of `LEAN_SOURCE_piv-v12-fb459343d234.zip` into `05_BUILD/main/src`
  (615/615 manifest hashes checked; no `.lake` directory, no `.olean`).
- **Objects:** written only to `05_BUILD/main/obj`, which started empty. No author `.olean`/`.ilean` was
  used.
- **Dependencies:** the shared package build directories (mathlib, plausible, LeanSearchClient, importGraph,
  proofwidgets, aesop, Qq, batteries), read-only via LEAN_PATH. A snapshot of 113 821 files taken before and
  after shows 0 changed, 0 added, 0 removed, with the same Mathlib.olean sha256 (`cache_diff.json`).
- **Attempts:** attempt 1 (15:07 UTC) failed on the auditor's own option-flattening bug (C-04) and is
  preserved. Attempt 2 ran 15:09–21:33 UTC (6.4 h).

## Results — main cut
- **607/607 modules PASS**, exit 0, with no failed, blocked or skipped module. `records.jsonl` has one row
  per module, including the source hash, dependency olean hashes, the command and the olean sha256.
- **All 19 FREEZE_SCOPE targets were executed fresh and PASS.** Each target log is identical to the
  author's segment-2 log apart from the command line (`target_log_analysis.json`).
- **Bit-for-bit reproduction:** all **607 .olean files are byte-identical** to the olean hashes recorded by
  the author across the two segments (`olean_vs_author.json`). Separately, a 37-module recompilation
  reproduced identical oleans (determinism). Together these independently corroborate the author's
  two-segment reuse (resolves X-21).
- **Axiom records:** 461 under the author's counting rule, of which 314 are genuine `#print axioms` outputs.
  Every set is a subset of {propext, Classical.choice, Quot.sound}.
- **Sorry and errors:** "sorry" occurs nowhere (case-insensitive) in any of the 608 auditor logs, or in the
  author's logs. No `error` appears in any target log. The negative control (`AuditorNegControl.lean`)
  shows that Lean 4.28 prints "declaration uses \`sorry\`" with backticks. The literal pattern in both
  runners would have missed it, so the explicit rescan and the axiom cones are the operative checks (C-07,
  finding X-28).
- **Exports:** `ReleaseExportCheck` (224 `#check` lines, import `PaperIV` only) compiled with 0 errors.

## Auditor's independent checks (`AuditorChecks.lean`, `AuditorChecks.log`)
- The elaborated types of the headline declarations were printed; their definitions (`RootedDefectAt`,
  `CliquePartition`, `IsDefectRoot`, `IsCanonicalPiece`, `defSplitGraph`) match E3_STATIC_RECORD.
- `#print axioms` on 18 headline declarations: all exactly [propext, Classical.choice, Quot.sound].
- **Own cone traversal** (type + value, transitive) of 50 public declarations: **0 non-standard axioms,
  0 `sorryAx`, 0 constants under the root `Erdos81`**.
- **Removal provenance** (`AuditorASProbe.lean`):
  - None of the six named removal keys (`AlonShapira.lemma_4_2`, `near_chordal_of_induced_cycles_littleO'`,
    `…few_induced_cycles'`, `EditRoute.editApproxAt_all`, `EditRoute.fixedL4Localization_unconditional`,
    `AFKS.strong_regularity`) occurs in the cones of the public Theorem C (`rooted_defect_eventual/_maximum`),
    `E35.theoremC_tower*`, `fixed_defect_stability_explicit`, `fixed_defect_joint_stability_real` or
    `sequence_arbitrary_orders_stability`. This confirms FDCheck.ASCheck independently.
  - Shared helpers (`AlonShapira.IsChordal.induce`, `EditRoute.*` arithmetic lemmas) do occur, as §7 discloses.
  - **However**, the cones of `E32.cp_classification_of_theoremCPrimeC` and `E32.ref15Theorem11_of_theoremCPrimeC`
    contain `AlonShapira.lemma_4_2`, `near_chordal_of_induced_cycles_littleO'`, `EditRoute.editApproxAt_all`,
    `EditRoute.fixedL4Localization_unconditional` and `AFKS.strong_regularity`. They enter through
    `E32.theoremC_at` := `DefectSharpPublication.rooted_defect_eventual`, the historical existential assembly.
    Appendix F.4 Table 9 cites `E32.cp_classification_of_theoremCPrimeC` for the "unrestricted equality
    classification" (Cor 6.3, (6.18)). The formal cp-part of that classification therefore depends on the
    Alon–Shapira route that §7 and [23] describe as historical and not selected. This is finding X-27
    (MODERATE, provenance/conformance). There is no correctness impact: that route is fully proved, with
    standard axioms.

## Results — annex (BoundedCliqueGap)
- Project: a fresh extraction of `LEAN_SOURCE_SNAPSHOT_v1.0.zip` (its lakefile, manifest and toolchain equal
  the bound freeze files), with the 38 annex files overlaid (38/38 manifest hashes OK), in its own objects
  directory `05_BUILD/annex/obj`. Run serially after the main build.
- **50/50 modules PASS** for the closure of `BoundedCliqueGap.AxiomCheck`, the same number as the internal
  report. The audit reports "633 declarations audited; axioms ⊆ [propext, Classical.choice, Quot.sound];
  no `Erdos81*` name". `chordal_gap_linear_cliqueFree` and four related declarations depend on exactly the
  three standard axioms.

## Limits
- Same machine and shared Mathlib/third-party oleans. The dependencies were not rebuilt, so this is not a
  clean-room Mathlib build. The `leanchecker` kernel replay was not performed (C-02 probe aborted).
- The build establishes that the formal statements are proved with standard axioms. It does not establish
  exposition adequacy (A.2) or manuscript correspondence beyond E3.

**E4 verdict: PASS** (with the limits above).
