# Paper IV — preprint v1.22

**Title:** *Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds*  
**Author:** Juan Pablo Traverso Gianini  
**Status:** audited author preprint selected for publication; local preparation, not yet pushed or deposited  
**External adversarial audit:** PASS, E0–E8, zero open corrective actions (v1.22-r4, 1 October 2026)  
**Human peer review:** not performed; a separate future milestone

## Read the paper

- [English PDF](01_manuscript/PAPER_IV_preprint_v1.22_en.pdf)
- [Spanish PDF](01_manuscript/PAPER_IV_preprint_v1.22_es.pdf)
- [English Markdown](01_manuscript/PAPER_IV_preprint_v1.22_en.md)
- [Spanish Markdown](01_manuscript/PAPER_IV_preprint_v1.22_es.md)
- [English TeX](01_manuscript/PAPER_IV_preprint_v1.22_en.tex)
- [Spanish TeX](01_manuscript/PAPER_IV_preprint_v1.22_es.tex)

These are byte-for-byte the six files approved as v1.22-r4. Their dated
candidate-status passages are preserved as part of that audited identity.
The final status is recorded here and in the consolidated report, not by
silently rewriting the approved PDFs.

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

- [Consolidated final external report (MD)](02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md)
- [Consolidated final external report (PDF)](02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.pdf)
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
01_manuscript/       Current v1.22 only: ES/EN sources, PDFs and figures
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
[release checklist](RELEASE_CHECKLIST_v1.22.md).

## Citation and license

The series concept DOI remains https://doi.org/10.5281/zenodo.21273143.
No version DOI for the new four-paper deposit or release commit is assigned
here. See [CITATION.cff](CITATION.cff). Written materials follow the series'
CC BY-NC 4.0 license. Upstream software retains its notices and licenses;
see [LICENSE.md](LICENSE.md).
