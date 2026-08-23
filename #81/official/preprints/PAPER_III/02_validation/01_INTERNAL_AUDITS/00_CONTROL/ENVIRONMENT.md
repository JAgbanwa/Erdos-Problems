# Internal-audit environment — Paper III v1.3

- Audit class: internal, author-side, non-independent.
- Audit date: 2026-08-22.
- Operating system: Windows / PowerShell.
- Lean rebuild during audit: **not run**.
- Recorded build reviewed: Lean 4.28.0, Mathlib v4.28.0 at commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, exit 0, 8,719 jobs.
- Formal archive: `PAPER_III_lean_v1.3_freeze.zip`, SHA-256
  `2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300`.
- Non-Lean regression tools: Python 3, exact rational arithmetic, PuLP/CBC.
- Publication tools: Pandoc, LuaLaTeX, Poppler (`pdfinfo`, `pdffonts`, `pdftotext`,
  `pdftoppm`).

The local `lean_v1.3_candidate` build tree is excluded from the public freeze and audit
deliverable. It was not treated as the immutable target.
