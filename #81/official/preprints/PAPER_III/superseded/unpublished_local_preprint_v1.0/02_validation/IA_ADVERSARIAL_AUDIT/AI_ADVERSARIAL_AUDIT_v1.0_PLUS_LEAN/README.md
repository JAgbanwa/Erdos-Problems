# AI Adversarial Audit v1.0 + Lean — Paper III

This folder defines the external adversarial AI audit package for Paper III, following the repository's prior adversarial-audit standard and adding mandatory Lean verification.

## Audited inputs

- Frozen manuscript input copied for this audit: `INPUTS\Papers_I_II_III_v1.1.5_near_final_editorial\PAPER_III_preprint_v1.1.5_near_final_editorial_en.md`
- Full copied editorial package: `INPUTS\Papers_I_II_III_v1.1.5_near_final_editorial`
- Paper manuscript SHA-256: `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- Frozen Lean package: `C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\05_formalization\lean_v1.0_freeze`
- Frozen Lean ZIP SHA-256: `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Mandate

The auditor must attack the paper and try to break every load-bearing claim. This includes proof architecture, regime split, constants, finite corridor checks, statement-to-Lean fidelity, and the scope of external asymptotic inputs.

AX1 and AX2 are in scope as external inputs, but they must be treated correctly:

- they are not arbitrary project assumptions;
- they are standard recognized theorems from the cited literature;
- the audit must verify that Paper III states and uses them no more strongly than the literature supports.

Lean verification is mandatory and must distinguish between internal closed Lean nodes and declarations conditional on AX1/AX2.

Do not reinstall Mathlib. Use the existing local Lean/Mathlib environment and cache on this machine.

## Required result location

The complete result must be placed under:

`C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\02_validation\IA_ADVERSARIAL_AUDIT\AI_ADVERSARIAL_AUDIT_v1.0_PLUS_LEAN\RESULTS`

See `DELIVERABLE_SPEC.md` and `LEAN_VERIFICATION_PROTOCOL.md`.
