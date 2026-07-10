# Reproducibility

- `ENVIRONMENT.md` -- toolchain and package versions.
- `BUILD.md` -- how to build the manuscript and the Lean formalization.
- `BUILD_VERIFICATION.md` -- how to reproduce the formal-verification certificate
  (`lake build` + `#print axioms`) and the computational audits.

No computation is used as a premise in the proof; the scripts and the build
corroborate and machine-check the analytic ar