# Environment

| Item | Value |
|---|---|
| OS | Windows 11, 10.0.26200 |
| CPU | Intel Core i7-1255U, 10 cores / 12 logical |
| RAM | 15.7 GB |
| Lean | 4.28.0, x86_64-w64-windows-gnu, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Lake | 5.0.0-src+7e01a1b |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, verified before use |
| Python | 3.14.4, with sympy and Pillow |
| Poppler | 24.04.0 |
| Clean room | `C:\p3a`, short path; Windows long paths enabled before dependency operations |
| Dependency cache origin | `C:\erdos_audit\PIII\.lake\packages`, the auditor's own checkout from the v1.2 audit, junctioned and pin-verified |
| External solver | none |
| Random seeds | **none anywhere** |

## Dependency revisions: 9/9 exact, 9/9 clean `git status`

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

## Object counts

| Stage | Project objects |
|---|---|
| before the build | **0** |
| after `lake build PaperIII` | **429** |

## Unavailable capabilities

`erdosproblems.com` returns HTTP 403. No subscription bibliographic index (MathSciNet, zbMATH).
The 1994 World Scientific volume holding reference [5] is not openly accessible. The delivered
PDFs were not independently recompiled from their TeX.
