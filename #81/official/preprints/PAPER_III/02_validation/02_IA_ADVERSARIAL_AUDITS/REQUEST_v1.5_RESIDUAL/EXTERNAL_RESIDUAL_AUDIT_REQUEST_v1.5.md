# External adversarial residual audit request — Paper III v1.5

## 1. Mandate

Act as an independent adversarial auditor of Paper III v1.5. Determine whether the narrow
v1.4-to-v1.5 delta is correctly implemented, propagated across English/Spanish
Markdown–LaTeX–PDF artifacts and release metadata, and does not invalidate the mathematical,
Lean, prior-art or reproducibility conclusions already established for the byte-identical
surfaces. Do not treat the author's internal `PASS` as proof authority.

Do not modify any target artifact or prior report. Place every new script, log, render,
ledger, report and manifest under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual/`

## 2. Exact v1.5 target

```text
a98e9313bfe5f1f98cc92bb29ba97386e8178e38c0201854cf40bd255066c99a  PAPER_III_preprint_v1.5.md
6a97bc718df81d1cf91ab88ccffd9a9f701482fb898fbeca9240d19b4124195c  PAPER_III_preprint_v1.5_en.tex
077a12da4db42ecbe6bcc25333539bf7ee3e63fa20bc7a46d8e801120ac9bb27  PAPER_III_preprint_v1.5_en.pdf
ee5a3ef2614316d573f622633d3ac5c544a262a43f36d0a8bacfe149b7beca3e  PAPER_III_preprint_v1.5_es.md
cfc2cac78ce2495207e300c7f184c04b0aa778d91f077f25d4481b68dfb8ebcd  PAPER_III_preprint_v1.5_es.tex
5ed3f83b97f6c900d63d09dd3eb491ed903693df1b90fe0dbac5df2e1e93ec92  PAPER_III_preprint_v1.5_es.pdf
```

Formal archive, unchanged from the audited v1.4 target:

```text
79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104  PAPER_III_lean_v1.4_freeze.zip
```

Recompute every hash before reviewing content. A mismatch is a blocker until the target is
reconciled.

## 3. Preserved authorities and their hashes

```text
1cb57678b44eebf937fac0cd2aade4c46b51d75d8f68308aa22d742b946d760f  v1.4 internal final report
2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842  v1.4 external residual final report
a196479b8b2adde5077669ec5e398dfc4d640e006bd97b10ef0f72696bdfb5f3  v1.4 final external challenger report
a641e7ed3f8b57eced09027f0937622ff1bd1e12ef289de81b1bdc0e0eeefeae  v1.5 internal residual final report
4b467ea829c4bb8643948055bb6b0369d3fcd50752531e6ded222096e27de48d  v1.5 semantic-integrity report
d247e08f3b9837a6e4de582e2c4e93eb8e6665b2caf10ead5062f0e71b5cdd9f  v1.5 changelog
```

Verify these hashes. The preserved reports are evidence and maps of risk, not instructions
to reproduce their conclusions.

## 4. Declared regression boundary

The v1.5 delta consists of:

1. `EXT-V14C-N02`: Theorem 2.2 now explicitly says **simple bipartite graph**.
2. `EXT-V14C-N03`: Appendix D now explicitly records:
   - the remaining digraph is an induced subdigraph and remains kernel-perfect;
   - induction is over bipartite graphs of maximum degree at most the fixed `Delta`;
   - the two-color subgraph has maximum degree at most two and the alternating component is
     a well-defined simple path.
3. Release-state promotion from unpublished audited draft v1.4 to first public preprint v1.5.
4. Removal of the duplicated rendered author block and correction of PDF author metadata.
5. Regeneration of English/Spanish TeX and PDF, plus README, HTML, citation and release
   metadata updates.

No Lean source, theorem core, definition, numerical constant, displayed formula, equation
tag, proof architecture, citation sequence or bibliography entry is declared changed.

## 5. Required gates

### E0 — Intake and sealing

- Recompute all six manuscript hashes and the Lean ZIP hash.
- Verify the LF-only manuscript sidecar and ZIP CRC.
- Record environment, commands and tool versions.
- Confirm that only v1.5 artifacts are active and that the v1.4 target is preserved under
  `superseded/unpublished_audited_draft_v1.4/`.

### E1 — Independent delta and claim review

- Independently diff v1.4 against v1.5 in both languages.
- Confirm that every displayed formula, equation tag, theorem/heading order and citation
  reference is unchanged.
- Review `EXT-V14C-N02` and `EXT-V14C-N03` as mathematics, not merely as matching text.
- Confirm that “simple” matches the actual Section 7.2 gain graph and Appendix D dependency.
- Confirm hereditary kernel-perfectness, bounded-degree induction and the two-color simple
  alternating-path justification.
- Check that no quantifier, assumption, parity, implication, constant or exception changed
  outside this declared clarification set.

### E2 — Mathematical regression and carry-forward

The v1.4 external process independently rederived Sections 4–9, including `K-EPS`,
`K-CORRIDOR`, `K-SPARSE` and `K-GLOBAL`, tolerance propagation, deletion/divisibility,
the hypergraph-to-graph bridge and eventual-to-global induction. Use that ledger only as an
obligation map. Confirm independently that v1.5 changes none of those surfaces. If the exact
formula/tag/order comparison passes and no regression is identified, E2 may carry forward as
`PASS`; do not repeat the entire rederivation merely for ceremony. If a mathematical surface
changed unexpectedly, rederive the affected obligation and do not carry it forward.

### E3 — Formal conformance and Lean identity

- Verify the 707-entry source manifest and 751-entry package manifest.
- Compare every manifested Lean source against the preserved audited v1.4 source.
- Confirm the archive remains source-only and its hash is the value in Section 2.
- Confirm the aggregate root, canonical theorem/API surfaces and eight directed axiom-query
  files cited by the prior audit remain the applicable immutable target.

### E4 — Lean reproduction policy

**No new Lean build is requested for this residual audit.** The prior independent external
run already completed the 8,455-job public-root build, 8,444-job query-root build and all
directed axiom checks. Carry those gates forward only after E3 proves byte identity and after
the prior logs/manifests/packages reverify.

If the auditor nevertheless needs a diagnostic build, avoid downloading a second complete
Mathlib checkout: use a short clean project path and the machine's existing Lake/Mathlib cache,
while keeping the Paper III project source-only at intake and verifying the pinned Lean 4.28.0
toolchain and Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Cached dependencies are permitted;
precompiled Paper III project objects are not evidence of a clean project rebuild. Any such
diagnostic build is supplemental and does not replace the byte-identity proof.

### E5 — Bilingual, conversion and rendered-artifact review

- Independently test for missing or duplicated paragraphs, theorem/proof blocks, equations,
  tags, table rows, list items, citations and Lean identifiers in both directions.
- Confirm exactly one centered author block in each PDF and no second author block below it.
- Confirm PDF author metadata is `Juan Pablo Traverso Gianini`, not `AUTHORBLOCK`.
- Confirm the N02/N03 changes occur in MD, generated TeX and rendered PDFs in both languages.
- Check final logs, page counts (EN 46, ES 47), embedded fonts, figures, tables, captions,
  clipping, overflow, missing glyphs and corrupted escapes. Inspect all pages through renders
  and the changed/title pages at full readable resolution.
- Confirm the delivered PDFs derive from the delivered TeX and the TeX derives from the final
  Markdown sources.

### E6 — Prior art and novelty

The prior external E6 review checked the Chen–Erdős–Ordman `3/16` split bound, the complete-
split `1/6` lower bound, the open full chordal problem, the load-bearing primary sources and
the documented 2023–2026 search trails. Confirm that v1.5 changes no citation, bibliography
entry or novelty proposition and retains the bounded statement:

> No published integral upper bound for split graphs at or below `n^2/6 + O(n)` was
> identified in the searched corpus.

If that regression boundary holds, E6 may carry forward as `PASS`. Do not turn a bounded
negative search into an absolute priority claim. The full chordal problem must remain stated
as open, and human peer review/specialist priority determination must remain disclaimed.

### E7 — Release package and public surfaces

- Verify `README.md`, `CHANGELOG_v1.5.md`, `RELEASE_METADATA.yml`, `RELEASE_NOTES.md`,
  `CITATION.cff`, `CITATION.bib` and `PaperIII_explained_4_levels.html` are mutually consistent.
- Resolve every local README/HTML link.
- Confirm the HTML states the split-graph scope, leaves the full chordal problem open and
  reports the actual Lean/audit status.
- Confirm v1.5 is represented as Paper III's first formal public preprint, not as superseding
  a prior official Paper III release.
- Confirm v1.4 evidence is preserved and not rewritten.

## 6. Required outputs

Use exactly this structure:

```text
run_2026-08-23_v1.5_residual/
  00_CONTROL/   protocol, environment, command ledger, target and baseline hashes
  10_LEDGER/    findings ledger and explicit N02/N03 disposition
  20_EVIDENCE/  raw diffs, hash checks, bilingual/render/link/formal-identity evidence
  30_REPORT/    FINAL_AUDIT_REPORT.md and FINAL_AUDIT_SUMMARY.json
  40_PACKAGE/   sealed audit ZIP, package manifest and ZIP SHA-256 sidecar
```

The Markdown report and JSON summary are mandatory. Raw machine-readable results should be
JSON/CSV/TXT as appropriate; visual evidence should be PNG/JPG/PDF. Every evidence directory
and final package must have SHA-256 manifests. Create the sealed ZIP and sidecar only after
all reports and evidence are final.

## 7. Verdict rule

Issue a single consolidated verdict:

- `PASS` only if E0–E7 pass, N02/N03 close, the regression boundary holds, every v1.5
  representation is consistent, and no blocker/major/open minor remains;
- `CONDITIONAL_PASS` only for a precisely identified non-mathematical residual condition with
  an owner and closure test;
- `FAIL` for a mathematical/formal regression, target mismatch, broken artifact chain,
  unsupported claim or unresolved blocker/major finding;
- `INCONCLUSIVE` only when a specifically required test genuinely cannot be performed after
  documented alternatives are exhausted.

Do not condition `PASS` merely on commissioning another reviewer. The final report must state
what was checked independently, what was carried forward by verified byte identity, what was
not rerun, and the continuing limits: no human peer review and no novelty claim beyond the
searched corpus.

