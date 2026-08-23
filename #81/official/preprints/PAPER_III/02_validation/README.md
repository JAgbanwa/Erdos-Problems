# Paper III v1.5 validation

This directory preserves the complete internal and independent adversarial AI
audit history for the v1.5 release and its byte-identical v1.4 Lean freeze.

- [`01_INTERNAL_AUDITS/run_2026-08-22_v1.4/`](01_INTERNAL_AUDITS/run_2026-08-22_v1.4/)
  contains the full v1.4 internal audit (`PASS`, 144/144).
- [`01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/`](01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/)
  covers the protected v1.5 editorial delta and package regression (`PASS`,
  79/79).
- [`02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/`](02_IA_ADVERSARIAL_AUDITS/run_2026-08-22_v1.4_residual/)
  contains the external mathematical review and uninterrupted clean-room Lean
  reproduction.
- [`02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/`](02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/)
  contains the final v1.4 challenger report (`PASS`).
- [`02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual/`](02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual/)
  is the sealed v1.5 residual run. Its original `CONDITIONAL_PASS` is retained
  unchanged as the record that identified `EXT-V15-M01`.
- [`02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual_closure/`](02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual_closure/)
  independently closes `EXT-V15-M01` after 10/10 checks and records the
  consolidated current verdict `PASS`.

Audit reports and their manifests are historical evidence and are not rewritten
when a later run closes a finding. These AI audits are not human peer review or
a specialist priority determination; literature conclusions remain bounded by
the corpus examined.
