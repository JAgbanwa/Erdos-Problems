# Paper I v1.3 package-residual internal audit protocol

**Protocol:** `PAPER_I_INTERNAL_PACKAGE_RESIDUAL_v1.0`  
**Date:** 2026-08-21  
**Audit class:** internal / author-side / not external  
**Target:** the active `preprint_draft_v1.3` package after the two package-only
corrections identified by the external `PASS_WITH_RESIDUALS` report.

## Scope

This audit must establish that:

1. `RES-V13-001` is closed: no `tmp/` compiler scratch remains in the
   active target and no forbidden TeX scratch extension remains outside excluded
   audit-output trees.
2. `RES-V13-002` is closed: the changelog uses
   `PaperI.assembly_sharp` and `PaperI.Split.residual_duality`, matching the
   manuscript and frozen axiom source; both transposed names are absent.
3. All six manuscript artifacts and the Lean archive remain byte-identical to
   the externally audited anchors.
4. The complete v1.3 static, mathematical, bilingual/duplicate, artifact and
   recorded-formal regressions still pass.
5. The new residual audit evidence and report are sealed only after all gates
   pass.

The target inventory excludes:

- `02_validation/02_IA_ADVERSARIAL_AUDITS/`, because it is external audit
  output rather than audited input;
- this residual audit run directory, because its files are generated while the
  audit executes.

No manuscript, figure, PDF or Lean source edit is authorized. Lean is not rerun.
The unchanged external clean-room build and theorem-level axiom evidence are
reviewed by exact archive hash.

## Gates

| Gate | Required result |
|---|---|
| R0 Package corrections | both open MINOR findings closed; package inventory clean |
| R1 Static/general | existing v1.3 static runner PASS |
| R2 Mathematics | existing exact/regression harness PASS |
| R3 Bilingual/duplicates | known-block and general exact/near-duplicate checks PASS |
| R4 Formal reuse | archive hash, recorded build and axiom evidence PASS; no Lean execution |
| R5 Artifacts | six artifact hashes, PDF structure/fonts/pages and unchanged-byte proof PASS |
| R6 Seal | report, manifests and final audit ZIP verify |

A final internal `PASS` requires all seven gates to pass, zero unresolved
blocker or major finding, and zero open minor finding from the external report.
The third-party certificate accessibility note remains a nonblocking external
NOTE and is not represented as repaired.

