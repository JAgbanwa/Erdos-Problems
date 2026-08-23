# Paper II v1.2 external-audit residual matrix

External report:
`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2/30_REPORT/FINAL_AUDIT_REPORT.md`

External report SHA-256:
`1e7afd3e9394bf83beb7e33ce19ff5227072fcd6b0eb3fd21e571329564e3ded`.

Original verdict: `PASS_WITH_RESIDUALS` with zero blockers, zero majors, one
minor and one note.

| Finding | Severity | Disposition | Correction |
|---|---|---|---|
| `EXT-PII-M-001` | MINOR | Corrected; internal residual verification required | Replaced all stale v1.1 files in `04_integrity/`; all supplied sidecars now point to present v1.2 files; added a v1.1 to v1.2 semantic diff and current-target manifest. |
| `EXT-P2-I-001` | NOTE | Preserved, nonblocking | The auditor received HTTP 403 from the Erdős Problems page. The open-status claim remains supported by the verified primary EOZ source; no manuscript change is required. |

The six publication artifacts and the Lean archive are protected anchors for
the residual audit. No mathematical, bibliographic, translation, figure,
LaTeX, PDF or Lean source change is authorized by this correction.
