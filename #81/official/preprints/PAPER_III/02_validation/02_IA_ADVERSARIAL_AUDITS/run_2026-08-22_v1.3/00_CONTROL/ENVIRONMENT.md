# Environment

| Item | Value |
|---|---|
| OS | Windows 11, 10.0.26200 |
| CPU | Intel Core i7-1255U, 10 cores / 12 logical |
| RAM | 15.7 GB |
| Lean | 4.28.0, x86_64-w64-windows-gnu, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Lake | 5.0.0-src+7e01a1b |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (declared `v4.28.0`) |
| Python | 3.14.4, with sympy and Pillow |
| Poppler | 24.04.0 (`pdftotext`, `pdftoppm`, `pdfinfo`) |
| Clean room | `C:\ea\P3`, short path, chosen to avoid Windows MAX_PATH failures |
| Dependency cache | auditor-controlled, junctioned, all nine revisions verified clean |
| External solver | none. Every optimum and every inequality was computed by the auditor's own exact arithmetic. |
| Random seeds | **none anywhere**. Enumerations are deterministic; symbolic work is exact. |

## Dependency revisions, each verified by `git rev-parse HEAD` with an empty `git status --porcelain`

| Package | Revision |
|---|---|
| mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| batteries | `495c008c3e3f4fb4256ff5582ddb3abf3198026f` |
| aesop | `f642a64c76df8ba9cb53dba3b919425a0c2aeaf1` |
| Qq | `b8f98e9087e02c8553945a2c5abf07cec8e798c3` |
| proofwidgets | `be3b2e63b1bbf496c478cef98b86972a37c1417d` |
| importGraph | `85b59af46828c029a9168f2f9c35119bd0721e6e` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| plausible | `55c8532eb21ec9f6d565d51d96b8ca50bd1fbef3` |
| Cli | `4f10f47646cb7d5748d6f423f4a07f98f7bbcc9e` |

## Unavailable capabilities

No institutional bibliographic database. `erdosproblems.com` returns HTTP 403 to this auditor.
The delivered PDFs were not independently recompiled from their TeX.
