# Gate G0 - Target, identity and independence (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## Anchor verification

All three protocol anchors for Paper II were recomputed from the delivered bytes and
**all three match**:

| Anchor | Expected (protocol Section 2) | Result |
|---|---|---|
| EN Markdown | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` | MATCH |
| Lean archive | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` | MATCH |
| Internal-audit ZIP | `e6f625486db867582da72fff9e71fa0f600dcce40e43ef885ce01756282b24e2` | MATCH |

Note on the internal-audit anchor: the package contains **two** files named
`INTERNAL_AUDIT_PACKAGE.zip`. The protocol anchor matches the one under
`02_validation/01_INTERNAL_AUDITS/`; the copy under
`02_validation/00_BASELINE_INTERNAL_AUDIT_v1.1/` is a different file (`b3227c6d...`).
Recorded so the anchor is unambiguous; not itself a defect.

## Input freeze

Sealed before any substantive analysis, with the audit-output subtree
`02_validation/02_IA_ADVERSARIAL_AUDITS/**` excluded from the target as protocol
Section 2 requires: **197 files, 3,411,262 bytes**. Inventory in
`00_REQUEST/INPUT_INVENTORY.json`; manifest in `00_REQUEST/INPUT_FREEZE_MANIFEST.sha256`.

## Section 4.1 regression controls at this gate

| Control | Result |
|---|---|
| no target path resolves into `superseded/` | **PASS** - 0 of 197 |
| no unexpected zero-byte file | **PASS** - 0 |
| no stray `$o` file | **PASS** - absent |
| manuscript sidecar verifies, LF-safe | **PASS** - `PAPER_II_preprint_draft_v1.2_SHA256.txt` is LF-only, all 6 entries verify |
| every archive name and SHA-256 printed in the manuscript exists and matches | **PASS** - the single printed hash resolves to the delivered `PAPER_II_lean_v1.2_freeze.zip`, in both EN and ES |
| **no stale `v1.0.1` reference, nonexistent freeze filename or hash, nonexistent gate-log path, or mislabeled formalization table** | **PASS** - 0 hits for `v1.0.1` or `lean_v1.1_freeze` in either language; Table 4 is captioned "Lean v1.2"; no gate-log path is referenced |

This last control is the one Paper II specifically failed at v1.1, where the manuscript
documented a v1.0.1 freeze absent from the package. **The defect is corrected.** The
regression was re-established from scratch on the v1.2 bytes, not carried forward.

## Clean room

Archive hash verified **before** extraction; extracted into the new empty short root
`C:\erdos_audit\PII`; `find` confirmed **no inherited `.lake` and no `.olean`** before
any build step. `lean-toolchain` reads `leanprover/lean4:v4.28.0`; `lake-manifest.json`
pins Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Both match the protocol.
`lake update` completed with exit 0 and did not mutate the pin.

Disclosed: `git config --global core.longpaths true` was set by the auditor, and the
shared Mathlib dependency cache was used (protocol Section 3.3 permits it when disclosed;
it holds no compiled project module). Paper II has its own clean room and its own build
directory; nothing was shared with Paper I or Paper III.

## Independence

Two isolated reasoning contexts, same model family, same operator - disclosed in
`00_REQUEST/AUDITOR_DECLARATION.md`. "External" means separation from the authoring
workflow, not human peer review.

## Gate verdict

`PASS`. Target exactly identified, all anchors match, input sealed with audit output
excluded, clean room provably free of inherited build state, and every Gate G0 regression
control of Section 4.1 passes - including the one Paper II previously failed.
