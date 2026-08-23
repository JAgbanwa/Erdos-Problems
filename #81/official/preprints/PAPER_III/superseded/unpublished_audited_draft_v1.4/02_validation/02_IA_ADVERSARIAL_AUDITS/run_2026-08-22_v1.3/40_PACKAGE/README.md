# External adversarial audit package -- Paper III v1.3

**Run:** `run_2026-08-22_v1.3`  **Overall verdict:** `FAIL`
**Auditor:** Claude (Anthropic), `claude-opus-5`. No adversarial challenger.

Only v1.3 was evaluated; no earlier verdict was inherited.

## Contents

| Tree | What is in it |
|---|---|
| `00_CONTROL/` | the protocol as executed, environment, command ledger, and the auditor's own SHA-256 manifest of the received target |
| `10_LOGS/lean/` | raw build and axiom-query logs, including the failed first pass of the queries |
| `20_EVIDENCE/E0..E7/` | one `AUDIT_RECORD.md`, `scripts/`, `results/` and `SHA256_MANIFEST.txt` per gate |
| `30_REPORT/` | the report in Markdown (semantic source), TeX and PDF, plus `AUDIT_SUMMARY.json`, `FINDINGS_LEDGER.csv` and `REGRESSION_MATRIX.md` |
| `40_PACKAGE/` | this file, the flat SHA-256 list, the sealed ZIP and its LF-only sidecar |

## Verification

```
sha256sum -c 40_PACKAGE/EXTERNAL_AUDIT_SHA256.txt      # every file in the run
sha256sum 40_PACKAGE/EXTERNAL_AUDIT_PACKAGE.zip        # compare to the sidecar below
```

ZIP SHA-256:

```
c60b1b74300b44e568be42d128d23eab3a3f18696ad9b418428798a774b3ff65
```

74 files, 766,084 bytes. The sidecar is LF-only. The ZIP
is generated last, so `package_sha256` inside `AUDIT_SUMMARY.json` points at the sidecar rather
than carrying a value: a hash of the ZIP cannot live inside the ZIP it hashes.

## Findings

3 major, 4 minor, 0 blocking, 0 critical. **No mathematical or formal defect.** See
`30_REPORT/FINDINGS_LEDGER.csv`.
