# Independent Environment Record — PAPER_I_EXT_AUDIT

**Audit ID:** PAPER_I_EXT_AUDIT_2026-07-10
**Date:** 2026-07-10
**Auditor:** external AI adversarial auditor (adversarial-math-audit protocol)
**Target (only):** Paper I — *Affine Profile Reduction for Fractional Triangle Packings
in Split Graphs*: `|E(G)| − 2·ν₃*(G) ≤ n²/6 + n` for split graphs `G` on `n` vertices.
**Ground truth of the statement:** `01_manuscript/PAPER_I_preprint_v1.0.{md,pdf,tex}`,
Theorem 1.1 (and Appendix C for the Lean statement).
**Canonical package audited:** `…/github-sync/#81/official/preprints/PAPER_I/`.

## Independence statement

All auditor code was written from scratch for this audit (`scripts/01–03`, `_lib/`).
The numerical/symbolic checks recompute `ν₃*`, the residual-cover LP, the orbit LP, and
every algebraic identity independently of the manuscript and its ledger. The Lean Gate-H
build (`scripts/04`) is run in a **fresh copy** of the release sources placed in a clean
directory with **no inherited `.lake` build artifacts**, using the community Mathlib
olean cache — not the author's build cache. The author's repo of record
(`C:\Users\jtrav\aristotle_lean`) was **not** used to produce any result here.

## Software environment

| Component | Version |
|---|---|
| OS | Windows 11 Home Single Language 10.0.26200 |
| Python | 3.14.4 |
| sympy | 1.14.0 (exact symbolic algebra — Script 01) |
| scipy | 1.17.1 (HiGHS LP — Scripts 02, 03) |
| numpy | 2.4.4 |
| reportlab | 5.0.0 (PDF rendering; no LaTeX/pdflatex available) |
| Lean toolchain | leanprover/lean4:v4.28.0 (pinned by `lean-toolchain`) |
| Mathlib | v4.28.0 (pinned rev per `lake-manifest.json`) |
| elan / lake | elan 4.2.3 ; lake 5.0.0 (Lean 4.28.0) |

**Master seed:** `20260710` (fixed in Scripts 02, 03).

## Objects (as computed)

- `ν₃*(G)` — fractional triangle packing: `max Σ_T w_T` s.t. per-edge load `≤ 1`, `w ≥ 0`.
- Residual cover LP `M(κ) = min_{z∈P_p} Σ_e (1−κ_e) z_e`, `P_p = {z∈[0,1]^{E(K)}:
  z(T) ≥ 1 ∀ clique triangle T}`.
- `R(p,q) = (2p²−2pq−q²)/12`; `A,B,C,U,D,H` as in §6.

## Gate-H build note (Windows long paths)

Mathlib contains file paths exceeding the Windows 260-char limit; with
`LongPathsEnabled = 0` and `core.longpaths` unset, a checkout under a deep path fails
(`git exit 128`, "Filename too long"). The independent build therefore uses (i) a short
build root `C:\Users\jtrav\l`, and (ii) `core.longpaths=true` passed to git via
`GIT_CONFIG_*` environment variables (no modification of the user's global git config).
This is an environment workaround only; it does not affect the Lean sources or result.

## Reproducibility

Each `scripts/NN_*/` folder holds the script, `results.txt` (full output), an English
`report.md`/`.pdf`, a `.zip` of the folder, and its `.sha256`. A top-