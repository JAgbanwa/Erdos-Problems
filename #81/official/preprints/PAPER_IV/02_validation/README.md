# Paper IV — validation evidence

## Current editorial revision

Version 1.23 changes administrative prose only. Its local semantic, bilingual,
typesetting and navigation checks are recorded in
[EDITORIAL_REPORT.md](03_EDITORIAL_CHECKS/v1.23/EDITORIAL_REPORT.md).
These checks do not constitute a new external audit. The original report is
also available as an [English translation](translations/v1.22_r4/FINAL_CONSOLIDATED_AUDIT_REPORT_en.md),
clearly identified as an editorial translation rather than a new auditor statement.

## Final external result

The [v1.22-r4 consolidated report](02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md)
records **PASS for E0–E8, zero open corrective actions**, with NEW-05 closed.
It includes the complete history and distinguishes newly executed checks
from conclusions inherited and revalidated by identity. The final
[summary](02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/SUMMARY.json)
is the current verdict; original historical verdicts are not rewritten.

## Internal audit

The [author-side internal report](01_INTERNAL_AUDITS/run_20260929_v1.2_fb459343d234_r1/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md)
is PASS_INTERNAL_AUTHOR_SIDE for its frozen v1.2 inputs. Its block/gate
reports, scripts, results and ZIPs are retained. It is not relabelled as a
fresh v1.22 audit. Subsequent manuscript changes were checked in the external
editorial revalidation chain, ending with v1.22-r4.

## Scope and controls

The external build is the recorded v1.2 run on source identity
piv-v12-fb459343d234: 607 main modules, 19 targets, 224 export checks and
50 annex modules. No newer editorial cycle rebuilt it. Mathematical
falsification checks are finite regression evidence, not proof premises.
The supplemental log verifier remains mandatory; see
[reproduction](../03_reproducibility/README.md).

Human peer review is a distinct future milestone, not an unmet condition
of this completed audit. Same-family/session and shared-cache limitations
remain declared. PASS is not authorization to publish.

Historical audit inputs were relocated, not edited. See
[audit input map](02_IA_ADVERSARIAL_AUDITS/audit_inputs/README.md).
