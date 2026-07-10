# Open Risks — Paper II External Audit (PAPER-II-EXT-AUDIT-001)

Severity: CRITICAL / MAJOR / MODERATE / MINOR / OBSERVATION.

| ID | Severity | Risk | Status |
|----|----------|------|--------|
| R1 | MINOR | Lean build independence: Mathlib was taken from the project's pinned `lake-manifest.json` cache, not rebuilt from scratch on a clean machine. The PaperII modules were recompiled from source and the build succeeded (8057 jobs). | OPEN — recommend clean-room reproduction |
| R2 | MINOR | Commit-`5f2d448` SHA-256 match not verifiable here: git history unreachable (repo root = `C:/`, no `HEAD`, object not found) and the v1.0 release package does not bundle the `lean/` tree with a manifest. Auditor recorded its own source manifest (`lean_source_sha256.txt`). | OPEN — publish lean/ + SHA manifest in release |
| R3 | OBSERVATION | Exhaustive graph enumeration limited to n≤6 (n≥7 infeasible in Python); larger n covered by random/structured sampling + the analytic proof + the Lean certificate. | ACCEPTED (conclusive for n≤6; universal claim carried by proof + Lean) |
| R4 | OBSERVATION | `#print axioms` literal capture was slow to elaborate (Mathlib load); build success + sorry-free source + statement read corroborate H regardless of capture latency. | see H_report / print_axioms.log |

**No CRITICAL/MAJOR risk found.** No mathematical defect, no counterexample, no
over-claim. All residuals are provenance/reproducibility items on the formal
certificate, not on the 