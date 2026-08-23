# Environment & Independence Statement — Paper II External Audit

## Computational environment (auditor)
| Field | Value |
|-------|-------|
| Python | 3.14.4 (64-bit) |
| OS | Windows 11 (10.0.26200) |
| scipy | 1.17.1 (cover-LP via HiGHS) |
| numpy | 2.4.4 |
| networkx | 3.6.1 (chordality, isomorphism, graph generation) |
| reportlab | 5.0.0 (PDF; no LaTeX on host) |
| Master seeds | 20260710 (P1, P2) — per-instance seeds recorded |

## Lean environment
| Field | Value |
|-------|-------|
| elan | 4.2.3 |
| Lean toolchain (project) | leanprover/lean4:v4.28.0 (from `lean-toolchain`) |
| lake | 5.0.0 |
| Mathlib | pinned by the project's `lake-manifest.json` (v4.28.0 line) |
| Build target | `PaperII` (lib); checker `AuditCheck.lean` (`#print axioms`) |

## Independence statement (per spec §1) — honest scope
- **Math checks (gates A–G, I, J):** fully independent. `tau3*`, `Phi_tau`, the
  copy operation, chordality, complete-split tests, and the integer maximization
  were re-implemented from the definitions in the auditor's own Python; no Paper II
  script was reused.
- **Lean (gate H):** the `PaperII` library was **re-elaborated** by the auditor
  (`lake build PaperII`, 8057 jobs, "Build completed successfully"), and axioms
  were checked with an auditor-authored `AuditCheck.lean`. The Mathlib dependency
  came from the project's pinned `lake-manifest.json` cache (a full from-scratch
  Mathlib rebuild in a clean machine was **not** performed — this is the one
  residual on full independence, recorded honestly). The re-elaboration recompiled
  the PaperII modules from source (e.g. `Built PaperII.Unconditional` from source).
- **Commit / SHA match:** git history was **not accessible** in this environment
  (the enclosing repo root resolved to `C:/` with no reachable `HEAD`, and object
  `5f2d448` was not found), and the v1.0 release package does not bundle the
  `lean/` tree with a manifest. Therefore the SHA-256 match to commit `5f2d448`
  **could not be verified here**; instead the auditor recorded its own SHA-256
  manifest of the exact Lean source it built (`lean_source_sha256.txt`).

## Trusted computing base
Python + scipy/HiGHS + networkx (math checks); elan/lake/Lean 4 + Mathlib +
the Lean kernel (formal check). No independently-checkable proof certificate is
emitted beyond L