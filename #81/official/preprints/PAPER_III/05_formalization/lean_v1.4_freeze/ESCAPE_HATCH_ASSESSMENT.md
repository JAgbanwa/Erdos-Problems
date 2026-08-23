# Escape-hatch assessment — Paper III v1.3 candidate

Status: `LOCAL_PREPARATION_PASS_NOT_AUDITED`.

## Claim perimeter

The release claim is declaration-level: the canonical theorem, the AX1 and AX2 discharge surfaces,
the canonical triangle-packing bridges, the manuscript-facing corollaries, and the explicit closure
surfaces listed in the eight `FreezeAxioms*.lean` files. It is not a claim that every historical or
exploratory module retained in the source archive is itself a release theorem surface.

## Recorded results

- The consolidated incremental verification completed successfully with 8,719 jobs and exit code 0.
- The build log contains no `declaration uses 'sorry'` or `declaration uses 'sorryAx'` warning.
- All eight axiom-query files exit successfully. Every queried declaration reports a subset of
  `[propext, Classical.choice, Quot.sound]`.
- No queried footprint contains `sorryAx`, `Lean.ofReduceBool`, or a project-local mathematical axiom.
- No active use of `native_decide` was found. The two raw textual matches are prose inside comments.
- The visually indented `sorry` examples in `Nibble/AdaptiveAssembly.lean` and
  `Nibble/RoundOracleKernel.lean` occur inside block-commented descriptions of refuted historical
  endpoints and are not parsed declarations.

## Retained legacy declarations

Two real project-local axioms remain in archived legacy modules:

- `Ax2.bklo_kthree_transfer` in `Ax2/PartB/Axioms.lean`;
- `dross_fractional_flow_noHDT` in `Ax2/PartA/Wlog.lean`.

No source file imports either legacy module, and neither declaration appears in any recorded theorem
footprint. They are therefore outside the canonical release proof closure. Their presence must remain
visible to auditors; the package must not be described as having no `axiom` token anywhere in the
archived tree. The accurate claim is that the canonical release surfaces have no project-local axiom.

## Evidence

- `gate_logs/BUILD_LOG_FINAL_INCREMENTAL.txt`
- `gate_logs/BUILD_EXIT_FINAL_INCREMENTAL.txt`
- `gate_logs/AXIOM_CHECK_SUMMARY.json`
- `gate_logs/AXIOMS_*.txt`
- `gate_logs/ESCAPE_HATCH_SCAN_RAW.txt`
- `gate_logs/ESCAPE_HATCH_FOCUSED_CHECKS.txt`

This is a local preparation assessment. The internal audit must independently evaluate the recorded
evidence under G3 and G4; the external auditor must reproduce the canonical targets and axiom gates.
