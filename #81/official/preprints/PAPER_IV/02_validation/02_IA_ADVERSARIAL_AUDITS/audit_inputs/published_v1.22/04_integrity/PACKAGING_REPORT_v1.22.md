# Packaging report — Paper IV v1.22

Editorial verdict: **EDITORIALLY_READY** for the exact audited artifacts.
Operational status: prepared locally for author review; no commit, push, tag
or deposit performed. The machine-readable packaging results are in
PUBLICATION_CHECKS.json.

## Selected and protected artifacts

The six ES/EN MD/TeX/PDF artifacts are exactly the v1.22-r4 target that received
the consolidated E0–E8 PASS. The protected-element index for packaging is the
whole-file hash list from the audit SUMMARY.json: no prose, mathematics,
metadata inside the manuscripts, proof, citation, figure, numbering or layout
was edited. The semantic diff is empty. Visual and parity evidence is inherited
from the same byte-identical PDFs; no new typesetting is claimed.

The selected Lean source is still piv-v12-fb459343d234 and its separate
bounded-gap annex. No theorem, source, pinned dependency, audited log or
historical verdict was changed. The supplemental verifier required to mitigate
X-28 is preserved verbatim; only a new external wrapper supplies the relocated
package root. It was rerun on the same 1266 logs.

## Publication layout

- Current manuscripts: only v1.22 in 01_manuscript.
- Prior public version: v0.8 in superseded/draft_v0.8, restored from its actual
  public Git commit. The enclosing index marks it SUPERSEDED without changing
  the historical package's bytes.
- Intermediate versions that were audit inputs: only inside
  02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs.
- Other working drafts, obsolete proof trees, preparation documents and build
  workspaces: excluded from the repository, retained recoverably outside it.
- Internal and external reports retain their block/gate evidence, scripts,
  results, MD/PDF reports and ZIPs. The audit manifests and ZIP hashes remain
  unchanged; a separate relocation map supplies the new locations.

The series-level README, preprint index and citation metadata now point to
v1.22. Paper IV's manuscript, validation, reproducibility, integrity,
formalization and history indices describe the final audited scope. Papers
I–III are unchanged. No unprovided version DOI or release date was invented.

The manuscripts' dated candidate-status passages remain historical statements;
the current status belongs to the package README and consolidated final
report. This avoids creating a new, unaudited PDF just to promote its label.

## Recovery and exclusions

The local recovery record is outside the repository at
C:/Users/jtraverso/e81p4-release-backup/20261001_pre_v1.22/.
The backup has PAPER_IV and PAPER_IV_REMAINDER: read-only frozen files were
retained during relocation and copied with hash checks. No audit evidence was
discarded to obtain PASS. Dependency caches were excluded from the new public
tree; they are not part of any claim of source reconstruction here.

The published relocation map contains only original/current relative paths
and hashes, not credentials. Historical absolute paths inside sealed evidence
are preserved as provenance; they are not portable release instructions.

## Remaining decision

The author must review this prepared layout and explicitly authorize any
publication. Human peer review remains a separate possible milestone, not an
unmet E0–E8 condition. No new mathematical question is introduced by packaging.
