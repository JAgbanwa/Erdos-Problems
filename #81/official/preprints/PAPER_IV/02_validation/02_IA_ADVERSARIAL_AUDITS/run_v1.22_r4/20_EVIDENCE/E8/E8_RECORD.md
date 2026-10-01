# E8 — Mandatory verifier and history (r4)

- **Identity.** `verify_frozen_logs.py` (c55225f3…) and `LOG_INVENTORY.json` (938dcdcc…) are byte-identical to r3 (E0). The r4 reproduction profile (`RESPONSE_AND_REPRODUCTION_PROFILE_v1.22_r4.md`, «Reproducción limitada», item 3) keeps the verifier **mandatory**.
- **Repetition with the auditor's own output (log reader only, no Lean).** `python verify_frozen_logs.py --inventory LOG_INVENTORY.json --output <run_v1.22_r4>/20_EVIDENCE/E8/VERIFY_FROZEN_LOGS_AUDITOR_OUTPUT_r4.json` returned **PASS, 1266 logs, 0 errors**, exit 0. The output is identical to that of run_v1.22_r3. Nothing was written in the r4 directory: `__pycache__` keeps only its earlier file, timestamp unchanged.
- **Inherited and revalidated by identity** from run_v1.22_r3, because the verifier and inventory are identical:
  - 15/15 unit cases and 4/4 CLI corruptions (test copy);
  - the error rule is case-sensitive, identical to the frozen runner (E8-02 closed);
  - 1266 = 608 + 50 + 422 + 186 files, counted once; the author's old script covered 844 (E8-01).
- **X-28.** The historical defect is that the frozen runners `audit_publication.py` and `paperiv_build.py` keep their insufficient pattern; they were not patched, and their hashes equal the manifest. That stays recorded as history. **Current compliance:** the control action was closed by the mitigation validated in r3, and it is still in force, unchanged and mandatory. The axiom and cone evidence (18 headline declarations, 50 public cones) also remains in force. **There is no open action.** The historical antecedent does not make E8 fail its criteria today.

**E8 verdict (r4): PASS.**
