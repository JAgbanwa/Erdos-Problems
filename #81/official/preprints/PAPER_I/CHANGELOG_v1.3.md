# Paper I v1.3 release changelog

Paper I v1.3 supersedes the public Paper I v1.0 release. The complete v1.0
package is retained under `superseded/preprint_v1.0/`.

## Changes from the current official release

- Provides synchronized English and Spanish Markdown, LaTeX and PDF artifacts.
- Makes the manuscript self-contained; internal version history is confined to package documentation.
- Aligns Section 10 with the delivered `PAPER_I_lean_v1.2_freeze.zip` name and SHA-256.
- Expands the frozen axiom query/report to cover `PaperI.assembly_sharp` and `PaperI.Split.residual_duality` in addition to the theorem surfaces and reusable interfaces.
- Corrects the tightness remark: the lower bound (1/4) in the (s=2) boundary regime requires (o\ge 1); the equality case ((p,q,s)=(2,4,2)) remains explicit.
- Regenerates the portable six-artifact hash sidecar with LF-only line endings.
- Records the successful external clean-room reproduction of the unchanged Lean freeze without representing it as peer review of the manuscript.
- Removes five duplicated Spanish blocks and regenerates the complete Spanish artifact chain.
- Makes the accounting behind equation (4.7) explicit, including the substitution `z = x` and the contribution of the edges in `H`.
- Restricts the Appendix A.2 excess formula to `o >= 3` and points the boundary cases `o = 0,1,2` to Appendix A.3.
- Clarifies that `sharp` refers to the quadratic coefficient `1/6`, not to the unoptimized additive term.
- Replaces the unverified Schrijver pinpoint with the supported chapter-level citation and supplies the author-hosted Chen--Erdős--Ordman scan for the `3/16` bound.
- Removes the unused repository bibliography entry that described an obsolete public bound.
- Rebuilds the v1.3 integrity baseline, bilingual/visual QA, hashes and internal-audit package.
- Records the final independent residual verdict `PASS` and promotes the
  canonical artifacts from audited-draft names to public-preprint names.
- Updates repository navigation, citation metadata, the GitHub-rendered HTML
  explainer and release manifests for v1.3.

No theorem statement, leading constant or proof architecture changes in this correction.

The intermediate v1.x working packages were internal and were not official releases.
The release promotion changed status prose and derived artifacts only; protected
mathematics and the Lean v1.2 freeze are unchanged from the externally audited target.
