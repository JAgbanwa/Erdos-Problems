# Environment (intake, 2026-09-28T11:00-03:00)

* OS: Windows 11 Pro 10.0.26200, 12 logical CPUs. Shells: Git Bash, Windows PowerShell 5.1.
* elan 4.2.3 (b6cec7e10 2026-06-08). Installed toolchains: `leanprover/lean4:v4.28.0`, `leanprover/lean4:v4.31.0`.
  No default toolchain; the project `lean-toolchain` file selects v4.28.0 (verified: file content `leanprover/lean4:v4.28.0`).
* Python 3.12.10 (sympy 1.14.0, networkx 3.6.1, scipy 1.16.1, pulp, PyMuPDF 1.28.2, pypdf 6.18.1).
* **No TeX engine found** (no pdflatex/xelatex/lualatex/tectonic/MiKTeX/TeX Live/TinyTeX on PATH or in standard
  locations). pdftotext (mingw64) available. Consequence: the final report PDF cannot be compiled from TeX
  without installing a TeX engine; this needs owner approval (download) and is otherwise recorded as a limitation.
* Heavy processes at intake: none named lean/lake running (tasklist check).

## Shared dependency installation (read-only checks only)

Root: `C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages`

| Package | frozen lake-manifest rev | installed HEAD | tracked changes |
|---|---|---|---|
| mathlib | 8f9d9cff6bd728b17a24e163c9402775d9e6a365 | same | 0 |
| plausible | 55c8532eb21ec9f6d565d51d96b8ca50bd1fbef3 | same | 0 |
| LeanSearchClient | c5d5b8fe6e5158def25cd28eb94e4141ad97c843 | same | 0 |
| importGraph | 85b59af46828c029a9168f2f9c35119bd0721e6e | same | 0 |
| proofwidgets | be3b2e63b1bbf496c478cef98b86972a37c1417d | same | 0 |
| aesop | f642a64c76df8ba9cb53dba3b919425a0c2aeaf1 | same | 0 |
| Qq | b8f98e9087e02c8553945a2c5abf07cec8e798c3 | same | 0 |
| batteries | 495c008c3e3f4fb4256ff5582ddb3abf3198026f | same | 0 |
| Cli | 4f10f47646cb7d5748d6f423f4a07f98f7bbcc9e | same | 0 |

(`git status --porcelain` line count; untracked build artefacts are not counted as tracked changes.)
No lake update, cache fetch, clone or compilation performed at intake.

## Auditor-owned directories (registered before use)

* Run directory: `preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-09-28_v1.0.1_r2/`
* Read-only extracted source copy: `C:/piv_r2/src/lean_v1.0_freeze` (from the verified main ZIP; used for static reading only)
* Isolated build directory (E4 only, created fresh at build time): `C:/piv_r2/build/`; its `.lake/packages`
  will be a junction to the shared root above; its project `.lake/build` must be absent at start.
