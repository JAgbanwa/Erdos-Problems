# Independent AI adversarial audit

Independent, automated (AI) adversarial review of the theorem in a clean context,
following the adversarial-math-audit protocol.

Gate: `ERDOZ81-P1-FRAC-THM-01` — the finite fractional split-graph theorem (Theorem 1.1).

**Verdict: PASS** (`PAPER_I_EXT_AUDIT_2026-07-10`). All gates checked; the analytic
proof was independently re-derived, the Lean certificate re-elaborated in a **fresh
source tree** (independent rebuild, 8027 jobs; `paperI_main` + `residual_duality`
axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`), and the theorem
falsification-tested over 622 split graphs with no defeater. See
`20_EVIDENCE/ERDOZ81-P1-FRAC-THM-01/PAPER_I_EXT_AUDIT_2026-07-10/FINAL_AUDIT_REPORT.{md,pdf}`.
The `20_EVIDENCE/*/audits/INDEPENDENT_AUDIT_RECORD_v1.0.pdf` files are the earlier
(lighter) independent audit records from the original release.

**Level of assurance.** Independent AI adversarial audit — an intermediate tier,
stronger than self-audit. It is **not** external human peer review or jou