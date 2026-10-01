# E5 — lead-auditor verification
- Predeclaration (E5_PREDECLARATION.md) written by the lead auditor before any computation; the delegated implementation followed it (T01–T25).
- Reproduction: `t_scalar.py` and `t_integer.py` rerun by the lead auditor on 2026-09-30; outputs identical to the delegated results (excluding timings). Logs: `lead_rerun/`.
- Graph/LP/ILP tests (T10–T17, T15 LP certificates) were not rerun by the lead auditor (runtime); their outputs carry exact certificates re-verified in-script.
- Process deviation C-03/AUD-P1 recorded (lost first-run output of supplementary T06s).
- Status: **E5 PASS within finite scope** (24 PASS, T25 NOT_APPLICABLE: no Certo certificate is bound to any claim). Finite tests do not establish universal claims.
