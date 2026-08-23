# External adversarial audit request — Paper III preprint draft v1.3

## 1. Mandate

Perform an **independent external adversarial audit** of Paper III v1.3. The target is a candidate for Paper III's first formal public release. Do not edit, repair, rename, or replace any target artifact. Record defects against the frozen bytes supplied.

This is a new consolidated audit of v1.3 with explicit regression against the preceding external findings. The preceding audit evidence may guide attack selection, but no earlier PASS or author-side conclusion may be inherited without checking the v1.3 target.

The internal audit is evidence of preparation only. It is author-side and non-independent; it must not be treated as external proof.

## 2. Exact target

The target root is:

`preprints/PAPER_III/active/preprint_draft_v1.3/`

Audit these publication artifacts:

- `01_manuscript/PAPER_III_preprint_draft_v1.3.md`
- `01_manuscript/PAPER_III_preprint_draft_v1.3_en.tex`
- `01_manuscript/PAPER_III_preprint_draft_v1.3_en.pdf`
- `01_manuscript/PAPER_III_preprint_draft_v1.3_es.md`
- `01_manuscript/PAPER_III_preprint_draft_v1.3_es.tex`
- `01_manuscript/PAPER_III_preprint_draft_v1.3_es.pdf`
- `05_formalization/lean_v1.3_freeze/PAPER_III_lean_v1.3_freeze.zip`

`05_formalization/lean_v1.3_candidate/` is a local build workspace, not part of the
frozen target or delivery payload. Do not copy, trust, or use it during reproduction.

Before substantive work, verify `04_integrity/CURRENT_TARGET_SHA256.txt`, the manuscript sidecar, the freeze archive sidecar, `SOURCE_MANIFEST.sha256`, `PACKAGE_MANIFEST.sha256`, and ZIP CRC. A byte mismatch is a blocking intake failure.

Formal target facts that must be independently confirmed:

- Lean `4.28.0`.
- Mathlib `v4.28.0`, exact commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Freeze archive SHA-256 `2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300`.
- The author-side build record says `Build completed successfully (8719 jobs)` with exit 0. This record is not a substitute for the external build.

## 3. Verdict rules

Use `PASS`, `FAIL`, or `INCONCLUSIVE` for every gate and for the overall verdict.

- `PASS`: the auditor actually performed the mandated check and retained sufficient evidence.
- `FAIL`: a reproducible defect invalidates a claim, artifact, dependency boundary, or release requirement.
- `INCONCLUSIVE`: the required check could not be completed. State the exact blocker and what would resolve it.

No unresolved blocking, critical, major, or required-but-inconclusive gate is compatible with overall `PASS`. Minor editorial findings may coexist with `PASS` only if they do not create semantic ambiguity, provenance failure, or divergence among MD/TeX/PDF or EN/ES.

## 4. Required audit gates

### E0 — intake, provenance, and sealing

- Verify every declared hash and manifest entry.
- Verify archive CRC, entry count, absence of path traversal, and absence of compiled project artifacts or reparse/symlink payloads.
- Confirm that all evidence refers to v1.3, not a stale earlier label or archive.
- Record the auditor's own SHA-256 manifest of the received target.

### E1 — mathematical claims and scope

- Independently parse Theorem 1.1, Corollary 1.2, the three regimes, the complete-split benchmark, and the two distinct sharpness roles.
- Confirm that the paper claims the sharp quadratic coefficient and the `n^2/6+O(n)` scale for split graphs, not a solution of the full chordal problem and not an optimal uniform linear coefficient.
- Check hypotheses, quantifiers, asymptotic thresholds, endpoint cases, divisibility conditions, and every transition from local/eventual to global statements.

### E2 — independent mathematical rederivation

Do not merely read Lean declarations or rerun author scripts. Reconstruct, with the auditor's own reasoning and calculations:

1. the complete quantitative epsilon/tolerance ledger (`K-EPS`);
2. the corridor optimization, parity and boundary cases (`K-CORRIDOR`);
3. sparse-regime deletion, divisibility, threshold and correction estimates (`K-SPARSE`);
4. exhaustiveness and overlap of the low/middle/high-degree cover (`K-COVER`);
5. the eventual-to-all-orders induction and global closure (`K-GLOBAL`);
6. the analytic core of Sections 4--9; and
7. the hypergraph-to-graph passage and every use of fractional/integral triangle packing.

Retain derivations, independent scripts, counterexample searches, parameter sweeps, and exact-arithmetic outputs. Clearly distinguish full derivations from bounded computational stress tests.

### E3 — formal statement conformance and model equivalence

Independently compare the manuscript's AX1 and AX2 with the Lean types `AX1Assumption` and `AX2Assumption`, including all coercions, normalizations, graph encodings, thresholds, and quantifier order.

Independently validate—not just compile—the semantics of:

- `PaperIII.isFracPacking_iff_yuster`
- `PaperIII.nu3Star_eq_yuster`
- `PaperIII.tau3Star_eq_nu3Star`
- `PaperIII.AX1Assumption_iff_packing_form`

Compare these with an auditor-constructed bridge or direct unfolding proof. Confirm that `nu3` and `nu3Star` refer to the intended objects at every manuscript/Lean interface and that no inequality direction or feasibility condition is lost.

Trace the manuscript's main claims through AX1, AX2, the three regimes, the global induction, `PaperIII.Theorem_1_1_of_AX1_AX2`, and `PaperIII.Theorem_1_1`. Produce a manuscript-to-Lean claim map.

### E4 — external Lean reproduction and axiom boundary

Use the optimized clean-room procedure in `MATHLIB_REPRODUCTION_PROTOCOL.md`. Reuse of a separately verified official Mathlib dependency cache is permitted; reuse of compiled Paper III artifacts is prohibited.

Required work:

- build the frozen Paper III target from an absent/empty project `.lake/build`;
- run all eight `FreezeAxioms*.lean` query files independently;
- retain commands, stdout/stderr, exit codes, durations, versions, dependency commits, and environment data;
- confirm every canonical named surface has exactly `[propext, Classical.choice, Quot.sound]` or explain any discrepancy;
- search for `sorry`, `admit`, `sorryAx`, `native_decide`, unsafe escape routes, hidden local axioms, generated replacements, and import-boundary changes;
- independently verify that `Ax2.bklo_kthree_transfer` and `dross_fractional_flow_noHDT` are archived legacy comparison routes, unimported by canonical roots, and absent from canonical footprints;
- confirm that the public aggregate root and `PublicAPI` import the intended canonical theorem path.

The correct claim boundary is: **a clean rebuild of Paper III against the pinned, independently verified Mathlib dependency cache**. Do not describe this as a full source rebuild of Mathlib.

### E5 — bilingual, format, and render consistency

- Compare EN/ES semantics, theorem numbering, hypotheses, equations, notation, citations, tables, figure captions, release status, and formal identifiers.
- Compare MD with generated TeX and extracted PDF text.
- Render and visually inspect every page of both PDFs. Check all figures, tables, long equations, references, fonts, clipping, blank pages, glyphs, and links.
- Specifically regress `A_{2J}`, `[3,8]`, `[11,17]`, and the corrected split-case scope.

### E6 — citations, prior art, novelty, and overclaim

- Retrieve and check every cited source against the claim it supports.
- Conduct an independent specialist search through the audit date, including the Cavers survey, the Erdős #81 record, Chen--Erdős--Ordman, Erdős--Ordman--Zalcman, and relevant 2023--2026 literature.
- Test whether a published result already gives the same split-graph `1/6` quadratic coefficient, a stronger statement, or an equivalent method.
- Confirm that the full chordal problem remains distinguished from the split asymptotic result.
- Report search strings, databases, dates, positive and negative results, and corpus limitations. Novelty cannot PASS solely from the author's bibliography or internal ledger.

### E7 — release-package integrity

- Confirm that the manuscript is self-contained and does not require an earlier internal draft.
- Confirm that Paper III is described consistently as a candidate for its first formal public release.
- Check that filenames, hashes, build records, formal names, changelog, metadata and reproducibility documents agree.
- Repeat the final hash verification after completing the audit to show the target was not altered.

## 5. Mandatory regression matrix

The final report must give a new disposition, with evidence, for each of these items:

- stale integrity or axiom labels;
- overbroad “resolves the split case” wording;
- `A_{2,J}` / `A_{2J}` inconsistency and combined-citation divergence;
- incomplete citation retrieval and bounded novelty search;
- the two archived comparison-route axioms and dependency closure;
- missing graph/Yuster model bridge;
- `K-EPS`, `K-CORRIDOR`, `K-SPARSE`, `K-COVER`, and `K-GLOBAL`;
- correspondence of manuscript AX1/AX2 to `AX1Assumption`/`AX2Assumption`;
- quantitative tolerances and the hypergraph-to-graph bridge; and
- independent rederivation of Sections 4--9.

Do not mark a mathematical item closed merely because the relevant Lean declaration compiles. State separately: semantic correspondence, successful compilation, axiom footprint, and independent mathematical rederivation.

## 6. Required output structure

Write results under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.3/`

Use this structure:

```text
00_CONTROL/
  AUDIT_PROTOCOL.md
  ENVIRONMENT.md
  COMMAND_LEDGER.md
  TARGET_SHA256.txt
10_LOGS/
  lean/
  manuscript/
  literature/
20_EVIDENCE/
  E0_INTAKE/
  E1_CLAIMS/
  E2_MATHEMATICS/
  E3_FORMAL_CONFORMANCE/
  E4_LEAN_REPRODUCTION/
  E5_BILINGUAL_RENDER/
  E6_PRIOR_ART/
  E7_RELEASE_PACKAGE/
30_REPORT/
  FINAL_AUDIT_REPORT.md
  FINAL_AUDIT_REPORT.tex
  FINAL_AUDIT_REPORT.pdf
  AUDIT_SUMMARY.json
  FINDINGS_LEDGER.csv
  REGRESSION_MATRIX.md
40_PACKAGE/
  EXTERNAL_AUDIT_SHA256.txt
  EXTERNAL_AUDIT_PACKAGE.zip
  EXTERNAL_AUDIT_PACKAGE_SHA256.txt
  README.md
```

The Markdown report is the semantic source; TeX and PDF must be synchronized renderings. `AUDIT_SUMMARY.json` must contain target hashes, environment, per-gate verdicts, finding counts by severity, overall verdict, and unresolved items. The findings CSV must contain stable ID, severity, gate, claim/artifact, description, reproduction, evidence path, effect, required correction, and disposition.

Each evidence directory must contain an `AUDIT_RECORD.md` and `SHA256_MANIFEST.txt`. Preserve raw logs and independent scripts. The final ZIP must contain control, logs, evidence, and report trees; its sidecar must be LF-only and independently verifiable.

## 7. Stop and escalation conditions

Stop and report rather than silently repairing if:

- received hashes differ;
- the exact pinned dependency state cannot be established;
- a required build or axiom query cannot be completed;
- manuscript and formal statements cannot be mapped unambiguously;
- the target changes during audit; or
- an external service or literature source needed for a blocking conclusion is unavailable.

The final report must remain candid about any limit. An optimized dependency cache changes only download/compilation cost; it must not relax source, commit, clean-project-build, axiom, or independence checks.
