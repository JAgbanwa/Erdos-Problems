# Gate M - Target and audit-package integrity (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS_WITH_RESIDUALS`

## Target integrity

| Check | Result |
|---|---|
| sidecars verified by content, resolving each entry against the correct base | part of an 82-sidecar sweep across the three packages: **79 verify fully, 3 do not** |
| the 3 exceptions | `04_integrity/INITIAL_SOURCE_SHA256.txt`, one per paper - see `EXT-PII-M-001` |
| manuscript sidecar | **LF-only**, all 6 entries verify |
| zero-byte files | **0** |
| stray `$o` file | **absent** |
| paths into `superseded/` | **0** |
| Lean archive vs protocol anchor | **match** (`ee2d05cc...`) |
| archive name and hash printed in the manuscript vs delivered file | **match**, EN and ES |
| stale `v1.0.1` / nonexistent freeze / nonexistent gate log / mislabeled table | **none** - the v1.1 defect is corrected; Table 4 reads "Lean v1.2" |
| `PACKAGE_MANIFEST.sha256` in the freeze | **62 entries, all verify** |
| `SOURCE_MANIFEST.sha256` in the freeze | **45 entries, all verify** |

## The one residual

`EXT-PII-M-001` (MINOR): `04_integrity/` is stale v1.1 content carried unchanged into the
v1.2 package. `INITIAL_SOURCE_SHA256.txt` has 2 entries, of which 1 names
`01_manuscript/PAPER_II_preprint_draft_v1.1.md`, absent from the v1.2 package, so
`sha256sum -c` reports a failure for it. `README.md` says "Pending for v1.1" and refers to
manifests "under `superseded/`", a directory the package does not contain.
`INITIALIZATION_DIFF.md` documents the v1.1 initialization, not v1.1 to v1.2. No
documented semantic diff exists for the v1.1 to v1.2 transition.

Protocol Section 4.1 requires all supplied sidecars to verify by content; this one cannot.
It does not affect the mathematics.

## Audit-package integrity

| Requirement | Status |
|---|---|
| reports and scripts end normally | verified |
| every referenced log exists as a directly visible file | verified - Lean logs are plain files under `../H_LEAN_REPRODUCTION/results/` |
| scripts run from documented commands | verified; each gate record states its invocation |
| manifests generated after content is final | yes |
| no placeholder text in files named final | verified by inspection |
