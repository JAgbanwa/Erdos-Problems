# Final external package-residual re-audit request -- Paper II v1.2

**Request ID:** `PAPER_II_EXTERNAL_PACKAGE_RESIDUAL_v1.0`  
**Target:** `preprint_draft_v1.2`, corrected in place  
**Prior external verdict:** `PASS_WITH_RESIDUALS`  
**Required final verdict if all controls pass:** plain `PASS`  
**Audit class:** independent external residual adversarial re-audit

## 1. Purpose and scope

The full external audit found zero mathematical or formal defects, zero
blockers, zero majors, one package-integrity MINOR (`EXT-PII-M-001`) and one
nonblocking access NOTE (`EXT-P2-I-001`). This run must independently verify
the correction of that MINOR and perform a general package regression.

Do not repeat the 30-minute Lean build, the full mathematical falsification or
the 47-page rendered analysis when the protected anchors below are
byte-identical. Reuse the prior external evidence under explicit byte identity.
Rerun a heavy gate only if an anchor differs or the residual regression exposes
a claim-relevant inconsistency.

This request does not authorize a manuscript, mathematical, bibliographic,
translation, figure, LaTeX, PDF or Lean change.

## 2. Target freeze and reproducible manifest

Audit the active package root:

`preprints/PAPER_II/active/preprint_draft_v1.2/`

Exclude the complete subtree:

`02_validation/02_IA_ADVERSARIAL_AUDITS/`

The resulting frozen target is:

- files: **245**;
- bytes: **3,940,779**;
- manifest: `00_REQUEST/INPUT_TARGET_MANIFEST.sha256`;
- inventory: `00_REQUEST/INPUT_TARGET_INVENTORY.json`;
- SHA-256 of the exact manifest bytes:
  `4b41f7e2e9415ca55514c6997dc6bff4e952b830282f46012c5214b04f688c1e`.

The manifest algorithm is not implicit: the manifest consists of UTF-8,
LF-only lines

`<file_sha256><two spaces><target-relative_posix_path>\n`

sorted case-insensitively by target-relative POSIX path. Recompute every file
hash, byte count and path before analysis, then hash the exact manifest bytes.
Any file-entry mismatch is a blocker. Report a manifest-summary mismatch
separately from an entry mismatch.

## 3. Protected anchors

| Artifact | Required SHA-256 |
|---|---|
| English Markdown | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` |
| Spanish Markdown | `d0d1df05eb267a51db2ccc100dd9725dcde9b03dbb95c8a730742e357eb0f4dc` |
| English LaTeX | `bb5f76c3ce56dbb0bff11242a3a8787f9c8ba3d9f0ad23973fc2f26cc5fc3cf0` |
| Spanish LaTeX | `d3f0c6301a48d6553ebad222fa685f152119cb61b5efd3e8be55e389f9d606ae` |
| English PDF | `d05c4cab1262357fddd21e4aab399bdb92d5bcf139172897c80595e781049052` |
| Spanish PDF | `d525d02a6e911cb23f7e1f28e1de7648441eccea6de206e76e5321161c86c2db` |
| Lean v1.2 archive | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` |
| Previous external report | `1e7afd3e9394bf83beb7e33ce19ff5227072fcd6b0eb3fd21e571329564e3ded` |
| Internal residual-audit ZIP | `779c8453e0ec3666bd8a7564d2e1251b6f2acf586815cd43470c202fa657eb13` |

The previous external report remains at
`run_2026-08-21_v1.2/30_REPORT/FINAL_AUDIT_REPORT.md` and is outside the input
target by design. It must not be relabelled or overwritten.

## 4. Authorized delta from the previous external freeze

The previous freeze had 197 files and 3,411,262 bytes. The only authorized
changes to files that existed in that freeze are:

1. `04_integrity/INITIAL_SOURCE_SHA256.txt`;
2. `04_integrity/INITIALIZATION_DIFF.md`;
3. `04_integrity/README.md`;
4. `DRAFT_METADATA.yml`;
5. `DRAFT_NOTES.md`;
6. the package-root `README.md`.

The only authorized additions are:

1. `04_integrity/CURRENT_TARGET_SHA256.txt`;
2. `04_integrity/SEMANTIC_INTEGRITY_REPORT_v1.2.md`;
3. `04_integrity/EXTERNAL_AUDIT_V1.2_RESIDUAL_MATRIX.md`;
4. the complete internal residual run under
   `02_validation/01_INTERNAL_AUDITS/residual_run_2026-08-21_v1.2_pkgfix/`.

No deletion is authorized. Diff the current target against the previous
external inventory and classify every changed, added or missing path. Any
unannounced change is at least a MINOR; any manuscript or formal change is a
blocker for evidence reuse.

## 5. Mandatory residual controls

### Control A -- close `EXT-PII-M-001`

Verify all of the following independently:

- `04_integrity/INITIAL_SOURCE_SHA256.txt` is LF-only and all three entries
  resolve from the package root and match;
- it contains no absent `PAPER_II_preprint_draft_v1.1.md` path;
- `04_integrity/CURRENT_TARGET_SHA256.txt` is LF-only and all nine entries
  resolve and match;
- `04_integrity/README.md` describes v1.2, not a pending v1.1 workspace;
- `04_integrity/INITIALIZATION_DIFF.md` explicitly documents v1.1 to v1.2 and
  does not claim a protected mathematical change;
- the semantic-integrity report and residual matrix agree with the actual
  hashes and external findings;
- no sidecar anywhere in the target fails by content.

The corrected integrity-document anchors are:

| File | SHA-256 |
|---|---|
| `INITIAL_SOURCE_SHA256.txt` | `1d5f8d91cb5d459eb0678e0a9ed2299a5b10b8ad69ae1a0640fa39fe4e220323` |
| `INITIALIZATION_DIFF.md` | `4b88e30639bc91cb71ab3ea88adad758604c2c96bae3722e40e2d14a92550c2c` |
| `README.md` | `d7ed1d33556de1f0ec2b79ba769b9ed255d4df8101d51fa3aa425f6ccb011e85` |
| `CURRENT_TARGET_SHA256.txt` | `79fd65426d03a77867f6591b7580651c98d3ce14580aed3d1e68e69b477a315d` |
| `SEMANTIC_INTEGRITY_REPORT_v1.2.md` | `5c9d6dc4694987fdc4f070b19eb1c3362083834ada009fd6227bb402526d817e` |
| `EXTERNAL_AUDIT_V1.2_RESIDUAL_MATRIX.md` | `a004b4fec8520c14ba55b812d4231c8863088bbc988b2c3fb8a3dd04f4350857` |

### Control B -- inspect, do not trust, the internal residual PASS

Inspect the raw R0--R6 evidence, not only the report label. Verify:

- R0: 17/17 controls and canonical manifest algorithm;
- R1: 58/58 common static controls;
- R2: exit-zero exact regression over the unchanged Markdown hash;
- R3: zero exact or near duplicate blocks in all six artifacts;
- R4: copied external raw logs are byte-consistent with the previous external
  run and show build exit 0, 8,063 jobs and 16 axiom surfaces;
- R5: all six publication artifacts match the prior anchors;
- R6: report compilation evidence, gate manifests, ZIP members and sidecar.

The internal report Markdown hash is
`3fac92e65b2a9f44bafb81e959f7ed46be041ddcd467d72a1b54ab13ec3a0fe0`;
the internal report PDF hash is
`dfdfe4f6316c8707b2c9f260feddc77b095b1fc5c02b859dc76f2897c90a6761`.

### Control C -- general package regression

Check at least:

- no `tmp`, compiler scratch, zero-byte file, stray `$o`, dollar-sign filename
  or unexpected hidden file;
- every supplied hash sidecar verifies from its documented base;
- manuscript self-containment remains intact;
- no stale v1.0.1 formal-package reference reappeared;
- no truncation, placeholder or malformed final report;
- no unannounced target delta;
- package status consistently says internal residual PASS and external
  residual pending.

## 6. Evidence reuse

Once all nine protected anchors match, classify the full prior mathematical,
formal, citation, novelty, bilingual, duplicate and rendered-PDF evidence as
`REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`. Do not state that those gates were
rerun. Preserve the prior scope limitations and the disclosure that the prior
Paper II audit used one reasoning context.

The HTTP 403 observation `EXT-P2-I-001` remains a nonblocking NOTE. It must not
be represented as repaired unless direct authoritative access is actually
obtained; the primary EOZ evidence already supports the substantive open-status
claim.

## 7. Verdict rule

Issue a plain `PASS` only if:

1. `EXT-PII-M-001` is independently closed;
2. the 245-file target inventory and every manifest entry verify;
3. all protected anchors match;
4. the package regression finds no new blocker, major or minor;
5. reused evidence satisfies byte identity;
6. `EXT-P2-I-001` is preserved as a NOTE unless independently resolved.

Otherwise issue the protocol-appropriate weaker verdict and identify every
open item. State explicitly that the audit is not human peer review and does
not prove global novelty.

## 8. Required deliverables and locations

Place all new output under this run only:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2_pkgfix/`

Required:

- `00_REQUEST/AUDITOR_DECLARATION.md`;
- `10_CONTROL/CLAIM_AND_FINDING_MAP.md`;
- gate evidence, scripts, commands and directly visible raw results under
  `20_EVIDENCE/`;
- `30_REPORT/FINAL_AUDIT_REPORT.md`;
- `30_REPORT/FINAL_AUDIT_REPORT.tex`;
- `30_REPORT/FINAL_AUDIT_REPORT.pdf`;
- `30_REPORT/FINAL_AUDIT_SUMMARY.json`;
- final manifests, tree inventory, sealed audit ZIP and LF-only ZIP sidecar
  under `40_PACKAGE/`.

The report must be standalone, identify the exact target hashes, distinguish
fresh residual work from reused evidence, list findings by severity and status,
and end with the auditor/model/configuration/date signature. Do not overwrite
the previous `PASS_WITH_RESIDUALS` run.
