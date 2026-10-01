# Editorial integrity report — v1.22-r3

Release ID: Paper IV v1.22-r3. Manuscript version remains 1.22.

Baseline: v1.22-r2, manifest SHA-256 `0fcaf0589c389f70fdb85959f4c69c45f97a131a64a7234a78e40328f7509c0a`.

Input/output MD hashes: STATUS_DELTA.json; final TeX/PDF hashes: ARTIFACT_CHECKS.json. Full package identity: MANUSCRIPT_REVIEW_MANIFEST.json and its sidecar.

| Protected element | Scope | Change |
|---|---|---|
| Mathematical statements, quantifiers, hypotheses, constants and proofs | All manuscript sections and appendices | None; only five identified status paragraphs per language were replaced. |
| Formula blocks, inline mathematics, equation labels, code blocks | Whole ES and EN sources | Identical to r2 by extraction and diff checks. |
| Tables, figures, bibliography, citation scope and novelty claims | Whole ES and EN sources | Unchanged. |
| Formal definitions, declarations, proof dependencies, toolchain | 615 frozen entries, including 607 Lean modules | Byte-identical; no Lean execution. |
| Audit-status prose | Front matter, §7, A.1, A.2, F.4 | Updated to the actual r2 consolidated verdict and its stated limits. |

The change log is STATUS_DELTA.json with complete before/after paragraphs and the two CHANGES diff files. No semantic ambiguity requiring mathematical repair was found in this limited edit. The supplemental semantic map is author evidence to be checked independently; it does not extend formal claims or silently add hypotheses to the manuscript.

Derived artifacts regenerated after final manuscript edit: yes, both languages. Final PDFs compiled from delivered TeX: yes. Rendered QA follows those compilations: yes, 145 pages in contact sheets and every changed page at full size. Compiler/layout checks and hashes are in ARTIFACT_CHECKS.json and VISUAL_REVIEW_v1.22_r3.md. Sealing is performed only after final reports.

Academic voice / AI-style scope: this is a documentary correction, not a rewrite of mathematical exposition. No promotional claim, stronger priority claim or unsupported independence claim was added. No journal-fit or mathematical reorganization was attempted.

Formal build-target/root note: no new compilation or export check. The historical external E4 and its literal target inventory remain the evidence; a file being included in the package is not itself proof of export or semantic correspondence. The supplementary log reader is outside the Lean source cut and is not a substitute for the kernel.

Open gate: independent revalidation of r3, including E6, the new E1/E3 rows and E8 postcontrol. Accepted historical limitations are explicitly retained in CORRECTIONS_AND_HANDOFF_v1.22_r3.md. No permission to publish is implied.

Verdict: **EDITORIAL_DRAFT_WITH_OPEN_GATES — prepared for external revalidation**.
