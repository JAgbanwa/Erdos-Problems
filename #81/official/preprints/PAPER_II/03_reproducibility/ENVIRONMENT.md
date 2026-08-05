# Environment

## Formalization
- Lean 4 with Mathlib **v4.28.0**
- Toolchain pinned in `05_formalization/lean/lean-toolchain`
- Dependencies pinned in `05_formalization/lean/lake-manifest.json`
- Verified at repository commit `5f2d448`

## Computational audits (`02_validation/PAPER_II_AUDIT/`)
- Python 3.x
- `numpy`, `scipy` (HiGHS LP/MILP via `scipy.optimize.linprog` / `milp`), `networkx`
- Exact/rational arithmetic where noted; see each audit's `requirements.txt`.

## Manuscript
- LaTeX (pandoc -> LuaHBTeX for the PDF); Latin 