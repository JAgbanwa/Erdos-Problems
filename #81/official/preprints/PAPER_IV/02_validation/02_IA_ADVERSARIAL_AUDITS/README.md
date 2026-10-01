# External adversarial audit — consolidated PASS

Current result: [run_v1.22_r4](run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md),
**PASS, all E0–E8, no open corrective actions**.

| Cycle | Original verdict |
| --- | --- |
| v1.0.1 r2 | FAIL on attribution; retained historical cycle, no Lean build |
| v1.2 r1 | INCONCLUSIVE |
| v1.21 r1 | INCONCLUSIVE |
| v1.22 r1 | PASS with non-blocking minor findings |
| v1.22 r2 | PASS_WITH_OBSERVATIONS |
| v1.22 r3 | PASS_WITH_FINDINGS |
| v1.22 r4 | PASS |

The final report consolidates all applicable prior checks, rather than
certifying only the last two Spanish corrections. Historical reports,
manifests, targets, evidence and packaged ZIPs remain unchanged. Scripts
and original inputs are evidence, not currently pending audit requests.

E4 is inherited from the verified external build and revalidated by source
identity. E8's historical runner defect remains documented; its mandatory
supplemental verifier is unchanged and passed on 1266 logs. No human review
or new build is claimed. The auditor records continuation of the same
session and model family, not blind or cross-family independence.

[Audit inputs](audit_inputs/README.md) contain the intermediate manuscripts
solely as backups. The [relocation map](../../04_integrity/RELOCATION_MAP_v1.22.json)
maps former paths to their published locations. Targets inside the historical
record continue to name their original paths. Use that map or the
[restoration procedure](../../03_reproducibility/README.md) for a replay;
do not edit the targets to disguise relocation.

[Final archive](run_v1.22_r4/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r4.zip)
and its [SHA-256](run_v1.22_r4/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r4.zip.sha256)
are the consolidated audit deliverable.
