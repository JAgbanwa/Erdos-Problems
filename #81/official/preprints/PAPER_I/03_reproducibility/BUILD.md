# Build instructions

Run from `01_manuscript/`.

## Recommended

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error PAPER_I_preprint_v1.0.tex
```

## Equivalent two-pass build

```bash
xelatex -interaction=nonstopmode -halt-on-error PAPER_I_preprint_v1.0.tex
xelatex -interaction=nonstopmode -halt-on-error PAPER_I_preprint_v1.0.tex
```

The build should complete without LaTeX errors. Binary PDF hashes can differ across
TeX distributions because of metadata and engine versions; compare rendered content
rather than requiring bit-for-bit identity.
