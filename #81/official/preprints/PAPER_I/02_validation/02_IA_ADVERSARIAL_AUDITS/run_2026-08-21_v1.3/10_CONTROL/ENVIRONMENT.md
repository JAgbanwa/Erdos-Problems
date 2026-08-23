# Environment — PAPER_II, run_2026-08-21_v1.2

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
Full disclosure is in `00_REQUEST/AUDITOR_DECLARATION.md`; this file records the
execution environment for this paper's gates.

## Host

| Item | Value |
|---|---|
| OS | Windows 11 Home Single Language 10.0.26200 |
| CPU | 12th Gen Intel Core i7-1255U, 10 cores / 12 logical |
| Memory | 15.7 GB |
| Architecture | x86_64 |
| Shells | Git Bash (MINGW64_NT-10.0-26200, 3.6.7); PowerShell 7 |

## Clean room for this paper

| Item | Value |
|---|---|
| Extraction root | `C:\erdos_audit\PII` (new, empty, outside the repository) |
| Archive hash verified before extraction | yes |
| Inherited `.lake` present | no (verified by `find` post-extraction, pre-build) |
| Inherited `.olean` present | no (same check) |
| `lean-toolchain` | `leanprover/lean4:v4.28.0` |
| Toolchain actually used | Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Mathlib revision pinned | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Build/axiom logs | `20_EVIDENCE/H_LEAN_REPRODUCTION/results/` |

Each paper has its own separate clean room and its own `.lake`. No build output was
shared between papers.

## Toolchain versions

Lean 4.28.0 (in-project) | Lake 5.0.0-src+7e01a1b | Elan 4.2.3 | Git 2.54.0.windows.1 |
Python 3.14.4 | Pillow 12.2.0 | MiKTeX-pdfTeX 4.23 (MiKTeX 25.12) | Poppler 24.04.0
(`pdftoppm`, `pdfinfo`, `pdftotext`)

**External LP/ILP solvers: none.** Every linear program recorded in this package was
solved by exact-rational code written for this audit. No floating-point solver produced
any recorded result.

## Determinism

No random seeds were used. All computational evidence is deterministic exhaustive
enumeration or deterministic exact-arithmetic evaluation. Swept domains are stated
explicitly in each gate record.

## Disclosed environment changes and caches

1. `git config --global core.longpaths true` — set by the auditor; previously unset.
   Required for Mathlib checkout on this host.
2. Shared network dependency cache `~/.cache/mathlib`, used by `lake exe cache get`.
   Permitted by protocol Section 3.3 when disclosed. Contains Mathlib dependency
   artifacts only, no compiled project module of any audited paper.

## Unavailable capabilities

erdosproblems.com (HTTP 403 to this auditor); MathSciNet/zbMATH; the 1994
Chen-Erdos-Ordman volume; Schrijver 1986; non-English literature search; independent
LuaLaTeX recompilation of the delivered PDFs. Each is declared as a limitation in the
gate it affects.
