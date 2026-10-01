# Paper IV — preprint v1.23 (editorial revision)

**Title:** *Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds*  
**Author:** Juan Pablo Traverso Gianini  
**Status:** author-approved GitHub release; v1.22 is the audited predecessor  
**External adversarial audit:** PASS for v1.22-r4, E0–E8, zero open corrective actions; no new external audit of v1.23  
**Human peer review:** not performed; a separate future milestone

## Read the paper

- [English PDF](01_manuscript/PAPER_IV_preprint_v1.23_en.pdf)
- [Spanish PDF](01_manuscript/PAPER_IV_preprint_v1.23_es.pdf)
- [English Markdown](01_manuscript/PAPER_IV_preprint_v1.23_en.md)
- [Spanish Markdown](01_manuscript/PAPER_IV_preprint_v1.23_es.md)
- [English TeX](01_manuscript/PAPER_IV_preprint_v1.23_en.tex)
- [Spanish TeX](01_manuscript/PAPER_IV_preprint_v1.23_es.tex)
- [Explanation at four levels, EN/ES](PaperIV_explained_4_levels.html)

Version 1.23 relocates administrative history out of the manuscript opening
and shortens process descriptions; mathematical content and frozen Lean sources
are unchanged. Its regenerated PDFs are new artifacts, not the six files audited
as v1.22-r4. See the [changelog](CHANGELOG_v1.23.md) and
[editorial checks](02_validation/03_EDITORIAL_CHECKS/v1.23/EDITORIAL_REPORT.md).
The [exact v1.22 publication](02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/published_v1.22/)
is retained as audit evidence, as is the public tag `paper-IV-v1.22`.

## Results and scope

The all-orders chordal conclusion is c₄(G) ≤ M(n) + b, for an absolute b,
where M(n) = floor(n(n+1)/6). The sharp bound and maximum hold for sufficiently
large n. The paper also gives the fixed-rooted-defect extension, quantitative
same-root stability for graphs and near-optimal partitions, a uniform
sublinear-defect statement and explicit tower-type thresholds. The
manuscript specifies all hypotheses, coefficients, witnesses and limits.

The bounds and related stability results of the other preprints are explicitly
attributed. The proof uses infrastructure of Papers I–III and the cited
mathematical literature. We do not claim b = 0 for every order, a practical
global threshold, a universal linear mixed gap or priority for the extremal bound.

## Audit evidence

- [Consolidated final external report — English translation](02_validation/translations/v1.22_r4/FINAL_CONSOLIDATED_AUDIT_REPORT_en.md)
- [Unchanged Spanish original (MD)](02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md)
- [Unchanged Spanish original (PDF)](02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.pdf)
- [Machine-readable final summary](02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/SUMMARY.json)
- [Internal audit and continuity](02_validation/README.md)
- [Publication checks](04_integrity/PUBLICATION_CHECKS.json)

E4 reuses the verified external build of the unchanged frozen source:
607 modules, 19 explicit targets, 224 export checks and the separate
50-module annex. Later cycles revalidated identity; they did not run new
builds. The audited foundational axioms are propext, Classical.choice and
Quot.sound, or subsets, with no sorryAx on the checked surfaces. Counts of
axiom records are not counts of distinct theorems.

The report discloses its same-family model and continuation of the audit
session, shared machine/cache, and the limits of its prose review. These
remain visible despite the PASS. Human peer review is not a pending
criterion of this completed E0–E8 process.

## Package and history

```text
01_manuscript/       Current v1.23 only: ES/EN sources, PDFs and figures
02_validation/      Internal/external reports, evidence and historical audit inputs
03_reproducibility/ Frozen build evidence and required supplemental log verifier
04_integrity/       Release manifest, relocation map and verification results
05_formalization/   Selected immutable Lean source and separate gap annex
superseded/         The previously public v0.8 draft, unchanged
```

The [superseded index](superseded/README.md) identifies v0.8 as historical.
Intermediate versions are not public alternatives: they are retained only
where required as [audit inputs](02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/README.md).
Their reports, manifests and ZIPs have not been rewritten. A relocation map
resolves original paths without changing their contents.

See [reproduction](03_reproducibility/README.md), [formal sources](05_formalization/README.md),
[trust and provenance](04_integrity/PROVENANCE_AND_TRUST.md), and
[release checklist](RELEASE_CHECKLIST_v1.23.md).

## Citation and license

The series concept DOI remains https://doi.org/10.5281/zenodo.21273143.
The DOI supplied by the author for the new version is
https://doi.org/10.5281/zenodo.23089131. Its public record was not yet
available at the 1 October 2026 check; this does not assert a completed deposit.
The published
v1.22 tag points to `cfcd5cf57cadc8583a218caaa1476911efe6158a`.
See [CITATION.cff](CITATION.cff). Written materials follow the series'
CC BY-NC 4.0 license. Upstream software retains its notices and licenses;
see [LICENSE.md](LICENSE.md).
