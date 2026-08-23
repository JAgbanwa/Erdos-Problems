# External residual adversarial audit request — Paper III v1.4

## Mandate

Audit the immutable, unpublished Paper III v1.4 package as the candidate for Paper III's
first formal public release. The auditor must independently test the corrected release
surface, run a general regression against the complete paper and deliver one consolidated
verdict. Internal evidence is intake material, not authority.

Target root: `preprints/PAPER_III/active/preprint_draft_v1.4/`  
Formal archive: `05_formalization/lean_v1.4_freeze/PAPER_III_lean_v1.4_freeze.zip`  
Expected SHA-256: `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`

## Required gates

1. Verify all target hashes, manifests, archive entries and package provenance.
2. Regress every headline claim, definition, constant, regime, equality/sharpness clause,
   boundary case and proof dependency.
3. Compare the English and Spanish MD/TeX/PDF chains; specifically test for lost,
   duplicated or reordered paragraphs, formulas, table rows, citations and Lean names.
4. Inspect both rendered PDFs, figures, tables, references, margins and glyphs.
5. Reproduce the formal project independently from the source-only archive. Build the
   public `PaperIII` root uninterrupted, then the query roots and all eight axiom files.
6. Confirm that the aggregate root reaches `PaperIII.Theorem_1_1_Final` and
   `PaperIII.PublicAPI`, and that canonical roots exclude the archived project-axiom modules.
7. Confirm the exact semantics of the canonical integral/fractional graph-to-Yuster bridges,
   AX1/AX2 correspondence and all quantitative/load-bearing surfaces.
8. Perform independent citation retrieval, open-status and novelty review through the audit
   date, with explicit search queries, corpora, dates and negative results.
9. Regress all findings in the v1.3 baseline report and incorporate the result into the new
   consolidated verdict; do not issue only a correction memo.

## E2 hint — independent mathematical rederivation

The prior external addendum already records `E2: PASS`, and the v1.4 internal package adds
a structured ledger under
`02_validation/01_INTERNAL_AUDITS/E2_RESIDUAL_v1.4/`. Use it as a map of obligations, not
as proof authority. Independently rederive `K-EPS`, `K-CORRIDOR`, `K-SPARSE` and
`K-GLOBAL`, including tolerance propagation, parity/boundary cases, deletion/divisibility,
the hypergraph-to-graph passage and the eventual-to-global induction. Compare your formulas
and domains with the ledger only after deriving them. The accompanying 315,183 exact checks
may be rerun or replaced by independently written tests. The final report must state a full
E2 verdict and explain the independent work performed; `carry-forward`, `not attempted` or
`INCONCLUSIVE` is not sufficient for overall `PASS`.

## E6 hint — citations, openness and novelty

The preserved addendum at
`02_validation/02_IA_ADVERSARIAL_AUDITS/baseline_v1.3/E2_E6_ADDENDUM_v1.3.txt` records the
successful prior search. Reuse its bibliographic leads but independently refresh them
through the audit date. The precise claim to test is: Chen--Erdős--Ordman gave the earlier
split-graph coefficient `3/16`; Paper III improves the split-graph quadratic coefficient to
the sharp `1/6`, matching the complete-split lower bound and establishing
`n²/6 + O(n)` for split graphs; it does not claim the least uniform linear coefficient and
does not solve the full chordal problem, which remains open. Search the Cavers survey lead,
Erdős Problems #81, primary cited papers, MathSciNet/zbMATH or equivalent indexes, arXiv,
Google Scholar/Semantic Scholar/citation trails, and 2023--2026/in-preparation records as far
as accessible. Record exact queries, dates, hits, exclusions and limitations. The final
report must give E6 a complete verdict rather than relying silently on the prior addendum.

## Faster clean-room Lean reproduction on this machine

Use a short working path such as `C:\p3a` and enable Windows long paths before dependency
operations. It is acceptable to reuse an existing Mathlib/dependency checkout or binary
cache from this machine, because independence concerns the Paper III source/build result,
not redownloading immutable third-party bytes, provided that the auditor:

1. starts from a fresh extraction of the source-only v1.4 ZIP with no project `.lake/build`;
2. records the origin of every reused dependency/cache;
3. verifies all nine dependency `HEAD` revisions against `lake-manifest.json` and records
   clean `git status` for each;
4. verifies Mathlib commit
   `8f9d9cff6bd728b17a24e163c9402775d9e6a365` before using its cache;
5. runs `lake exe cache get` when available, then performs the complete project-root build;
6. does not copy or reuse Paper III `.olean`/`.ilean` objects from any author build.

This is a warm-dependency clean room: third-party compiled caches may be reused after pin
verification, but all Paper III project objects must be created during the auditor's own
uninterrupted run. If dependency reuse cannot be proven exact and clean, fetch them afresh.

Required command sequence:

```text
lake build PaperIII
lake build BKLO.MainDenseUnconditional Nibble.AX1Closed PaperIII.CanonicalTrianglePacking PaperIII.Obstructions PaperIII.PaperImprovementsGate PaperIII.PublicAPI PaperIII.Theorem_1_1_Final
lake env lean FreezeAxioms.lean
lake env lean FreezeAxiomsAuditClosure.lean
lake env lean FreezeAxiomsAX1.lean
lake env lean FreezeAxiomsAX1Closure.lean
lake env lean FreezeAxiomsAX2.lean
lake env lean FreezeAxiomsByproducts.lean
lake env lean FreezeAxiomsCanonical.lean
lake env lean FreezeAxiomsObstructions.lean
```

Capture complete stdout/stderr, commands, start/end timestamps, exit codes, machine/toolchain,
dependency revisions, clean-state evidence, object counts and `#print axioms` outputs. The
headline `PaperIII.Theorem_1_1` must show no project-local axiom or `sorryAx`.

## Required output location and formats

Place results only under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/`

Use this structure:

```text
00_CONTROL/   protocol, target hashes, environment, commands, regression matrix
10_LEDGER/    claim/proof/citation/novelty/E2 ledgers
20_EVIDENCE/  per-gate raw logs, scripts, JSON, rendered-page evidence and manifests
30_REPORT/    FINAL_AUDIT_REPORT.md, FINAL_AUDIT_SUMMARY.json, optional PDF
```

Every executed script or command must retain its exact input, full output and exit code.
Every evidence directory and the final report package must have LF-only SHA-256 manifests.
The final report must list every finding with severity, affected artifact/line, reproduction,
impact and required correction; distinguish mathematical/formal defects from provenance or
editorial defects; and give one overall verdict among `PASS`, `CONDITIONAL_PASS`, `FAIL` or
`INCONCLUSIVE`.

Overall `PASS` requires every blocking gate—including uninterrupted Lean reproduction, E2,
E6, bilingual/PDF integrity and regression of the v1.3 findings—to be `PASS`, with no open
blocker or major finding.
