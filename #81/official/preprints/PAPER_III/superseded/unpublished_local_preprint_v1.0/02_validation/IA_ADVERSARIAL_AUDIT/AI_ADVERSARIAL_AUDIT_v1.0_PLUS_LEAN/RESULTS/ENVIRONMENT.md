# Audit Environment

**Paper III — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing** (v1.1.5)

- **Auditor:** Claude Opus 4.8 (Anthropic), via Claude Code
- **Date:** 2026-07-28
- **Manuscript SHA-256:** `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- **Lean freeze ZIP SHA-256:** `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78`

## Lean toolchain

| Component | Version / revision |
|---|---|
| Lean | `leanprover/lean4:v4.28.0` |
| Mathlib | `v4.28.0` (rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`) |

> **Note:** Mathlib was **not reinstalled**. The existing local cache was reused per audit protocol, to keep the verified dependency set fixed and reproducible.

## Python / computational stack

| Component | Purpose |
|---|---|
| Python 3.x | Driver for independent computational checks |
| `fractions` | Exact rational arithmetic (fractional margin, closed-form checks) |
| `scipy` | Linear-programming (LP) solves for `τ₃*` |
| `pulp` | Integer-programming (ILP) solves for integral `ν₃` |
| `reportlab` | PDF report generation |

## Platform

| Item | Value |
|---|---|
| Operating system | Windows 11 Home Single Language (10.0.26200) |
| Shell | PowerShell (primary); Git Bash for POSIX scripts |
| Auditor | Claude Opus 4.8 (Anthropic) via Claude Code |
| Audit date | 2026-07-28 |

## Reproducibility notes

- Both SHA-256 hashes above pin the exact manuscript and Lean freeze artifacts audited.
- The Lean freeze built with **8060 jobs, 0 errors, exactly 2 axioms (AX1, AX2), 0 `sorry` / 0 `admit`**.
- Independent computational reproduction totaled **60,541 checks** (Block E) using exact arithmetic, LP, and ILP as noted above.
