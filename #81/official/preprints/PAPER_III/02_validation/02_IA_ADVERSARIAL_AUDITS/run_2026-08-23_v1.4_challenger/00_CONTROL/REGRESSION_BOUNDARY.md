# Regression boundary — prior external target vs corrected target

Every hash below was recomputed by this auditor. Raw output:
`20_EVIDENCE/C_REGRESSION/regression_boundary.txt`.

## Declared baseline, verified

| Artifact | Declared SHA-256 | Recomputed | Match |
|---|---|---|---|
| prior report `FINAL_AUDIT_REPORT.md` | `2c19bf1c…8842` | same | yes |
| prior ledger `FINDINGS_LEDGER.csv` | `17db6da2…fe39` | same | yes |

## Corrected target, verified

All six declared manuscript hashes recomputed and matched.

| Artifact | Status vs prior external target |
|---|---|
| `PAPER_III_preprint_draft_v1.4.md` (EN) | unchanged |
| `PAPER_III_preprint_draft_v1.4_en.tex` | unchanged |
| `PAPER_III_preprint_draft_v1.4_en.pdf` | unchanged |
| `PAPER_III_preprint_draft_v1.4_es.md` | **changed** |
| `PAPER_III_preprint_draft_v1.4_es.tex` | **changed** |
| `PAPER_III_preprint_draft_v1.4_es.pdf` | **changed** |

Comparison is against the prior external run's own 1,194-entry target manifest, so the
"unchanged" verdicts are anchored to what that run actually examined, not to a redeclaration.
The request's claim that the English artifacts are byte-identical is therefore **confirmed**,
and the change set is confined to the three Spanish artifacts.

## Lean archive

`PAPER_III_lean_v1.4_freeze.zip` = `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`,
matching the declared value and the prior external target. No Lean source byte changed.

## Prior external build evidence, still present and sealed

`02_build_public_root_clean` predecessor log, `03_build_PaperIII.log`,
`04_build_query_roots.log`, `02_pre_build_clean.txt`, `G5_LEAN/SHA256_MANIFEST.txt`,
`FINAL_AUDIT_SUMMARY.json`, `EXTERNAL_AUDIT_PACKAGE.zip` and its sidecar: all present. The
prior package re-verifies **60/60 files** against its own `PACKAGE_MANIFEST.json`, and the ZIP
matches its sidecar. The prior run's evidence is intact and unaltered.

## Consequence for carry-forward

- **E2** — the rederivation of Sections 4–9 was performed against English mathematical text
  that is byte-identical here. No English mathematical byte changed; the Spanish change is one
  explanatory sentence in Section 2.4, carrying no mathematical content. Carry-forward `PASS`
  is sound. Independently corroborated in this run: all 205 displayed formulas agree between
  the two languages after masking `\text{...}` operands, with zero residual mathematical
  difference, so the Spanish edit introduced no formula drift either.
- **E6** — no citation, bibliography entry, novelty sentence or English byte changed. Carry-
  forward `PASS` is sound, restated in corpus-bounded form.
- **Lean gates** — archive byte-identical, prior build logs and manifests present and sealed.
  Carry-forward is sound and a rebuild would add no regression information.
