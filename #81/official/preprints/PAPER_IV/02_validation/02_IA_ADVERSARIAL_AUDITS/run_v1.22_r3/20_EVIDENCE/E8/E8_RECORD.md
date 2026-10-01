# E8 — Supplementary verifier, X-28, E8-02 and attribution (r3)

## Verifier inspection (`verify_frozen_logs.py`, sha256 in the r3 manifest)
- **Fail-closed design.** It requires the inventory. A directory whose `.log` set differs from the expected one (missing or extra files) fails. A hash mismatch fails. An alert (sorry or error) fails. A total count ≠ `expected_total` fails. It writes its output only to a new file (`open('x')`) and does not run Lean. It checks logs, not mathematical validity or the kernel.
- **Sorry rule.** `\bsorryAx\b|declaration\s+uses\s+[`'"‘’“”]*sorry\b` with `re.I`. It is stronger than the frozen rules:
  - `audit_publication.py:52` uses `sorryAx|declaration uses 'sorry'` and is case-sensitive;
  - `paperiv_build.py:400` uses the literal `"declaration uses 'sorry'"`.
- **Error rule** (E8-02). Pattern `^.*error(?:\(|:)` with `re.M` and **without `re.I`**. It is literally the error alternative of the frozen `audit_publication.py`. On the probe table (`E8_R3_CHECK.json`), "ERROR:" and "Error:" are not alerted by either rule, so **case sensitivity is identical** to the historical rule. The sorry reinforcement uses a separate regex and does not change the error rule. **E8-02 CLOSED** (the concern about adding `re.I` to errors does not apply).

## Repetitions with the auditor's own output
1. **In place (read-only).** `python verify_frozen_logs.py --inventory LOG_INVENTORY.json --output <run_v1.22_r3>/20_EVIDENCE/E8/rerun_in_place/VERIFY_FROZEN_LOGS_AUDITOR_OUTPUT.json`: **PASS, 1266 logs checked, 0 errors**, exit 0. Running it wrote nothing in the r3 folder; the pre-existing `__pycache__` keeps its 10:56 timestamp.
2. **Test copy** (`20_EVIDENCE/E8/testcopy/`). The verifier and harness were copied. The only change is the Paper IV root path in the copy of the verifier, documented in `testcopy_verifier_patch.diff`; the harness is unchanged. `test_log_verifier.py` reproduced:
   - **15/15 unit cases**: the real negative log; backtick, quote and curly-quote variants; uppercase; line breaks; `[sorryAx]`; 3 negatives (`no_sorry_used`, `sorryish`, clean axioms); 2 lowercase errors; and uppercase `ERROR:` not alerted.
   - **4/4 CLI corruptions** (sorry, error, changed hash, missing file): exit 1 and FAIL in every case.
   - The historical scan: PASS, 1266.
   - Comparison with the sealed files: the regenerated inventory equals `LOG_INVENTORY.json`; the unit cases equal `LOG_VERIFIER_TESTS.json`; the CLI outcomes and the historical scan are identical. The sealed package was not overwritten.
3. **Independent recount** (`10_SCRIPTS/e8_r3_check.py`).
   - Four groups: 608 + 50 + 422 + 186 = **1266**, with 0 duplicates and 0 hash mismatches.
   - These are the same four directories as the E8 scan of run_v1.21_r1 and run_v1.22_r2.
   - The same 1266 files have now been scanned four times (v1.21, r2, verifier in place, test copy). **They are counted once**: 1266 files, not 1266 proofs.

## Historical nuance
The frozen `audit_publication.py` rule does detect the real negative log, but only through `sorryAx` in an axiom printout (`'AuditorNeg.uses_sorry' depends on axioms: [sorryAx]`). It does not detect the warning itself, which Lean 4.28 prints with backticks. `paperiv_build.py` does not detect it at all.

## X-28 decision
The supplementary verifier is designated as a **mandatory control** of the r3 reproduction profile (`CORRECTIONS_AND_HANDOFF_v1.22_r3.md`). It is fail-closed, pinned by hash and reproducible, and its tests pass.
- **The control action of the delivery is CLOSED.**
- **The historical observation is kept:** the frozen runners still carry their insufficient pattern; they were not patched and this is not claimed.
- The axiom and cone evidence (18 headline declarations, 50 public cones) remains the substantive check against `sorryAx`.
- X-28 → MITIGATED, with the control in place. **No action is needed before publication**, provided the reproduction profile cites the verifier as mandatory.

## Other items
- 1266/844 attribution (E8-01): the auditor's scan covers 1266; the author's old script covered 844 = 1266 − 422. Resolved in r1; kept.
- Editor documents (ARTIFACT_CHECKS, VISUAL_REVIEW, STATUS_DELTA, EDITORIAL_INTEGRITY_REPORT, CORRECTIONS_AND_HANDOFF) were contrasted with the auditor's own evidence: the page lists, diff, protected content, 615 entries and figures all agree. They are not used as an inherited PASS.
- The claim «Los párrafos de estado conservan paridad» is correct in meaning; the ES terminology issue is NEW-05 (E6).

**E8 verdict (r3): PASS_WITH_OBSERVATIONS.** X-28's historical observation is kept; the control is closed.
