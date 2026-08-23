# Paper III — External Adversarial Audit (v1.0 + Lean) — Results

**Global verdict: PASS_WITH_OBSERVATIONS** · Audit date 2026-07-28 · Auditor Claude Opus 4.8 (Anthropic)

Independent seven-block adversarial audit of Paper III, "Linear-Error Clique Partitions of Split
Graphs via Structured Triangle Packing" (v1.1.5), with mandatory Lean verification and explicit
AX1/AX2 external-input scope analysis.

## Contents

- `ADVERSARIAL_AUDIT_REPORT.md` / `.pdf` — full report and global verdict.
- `ENVIRONMENT.md` — toolchain and reproduction environment.
- `SHA256_MANIFEST.txt` — hashes of all result files.
- `received_inputs/` — frozen manuscript copy + `SHA256.txt`; `received_inputs.sha256`.
- `findings/FINDINGS.csv` — 35 findings (34 CONFIRMED, 1 REFUTED; 1 minor, rest none).
- `blockA_claim_faithfulness/` — manuscript↔Lean mapping (all EXACT).
- `blockB_AX1_AX2_literature_scope/` — AX1/AX2 faithful to literature; not overstated.
- `blockC_bulk_sparse_corridor_proof_attack/` — 8 attacks, 0 vulnerabilities.
- `blockD_counterexample_and_boundary_search/` — no counterexample; hypotheses load-bearing.
- `blockE_independent_computation/` — `verify_paper3.py`, 60,541 checks, 0 failures.
- `blockF_audit_the_internal_audit/` — internal checks confirmed non-premise; full coverage.
- `blockG_lean_verification/` — build 8060 jobs, 2 axioms, corridor closed; 1 minor node-attribution observation.
- `EXTERNAL_AUDIT_RESULT.zip` (+ `.sha256`) — packaged deliverable.

## Headline

Theorem 1.1 (`Φ(G) ≤ n²/6 + C·n` for split graphs) and Corollary 1.2 (`cp(G) ≤ n²/6 + C·n`) are
sound and correctly stated as **conditional on AX1 (Haxell–Rödl/Yuster) and AX2 (Dross + BKLO)**. Both
axioms are faithful to the cited literature and not overstated — notably AX2 uses the *proven*
`δ ≥ (0.9+ε)n` threshold, not the conjectured `0.75n`. The near-extremal corridor is genuinely
unconditional (closed axiom footprints, verified). One minor, non-blocking observation: the formalized
sparse node `E_8` carries `AX1 + AX2` rather than the `AX2`-only attribution stated in §11.6.
