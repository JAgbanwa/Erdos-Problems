# Paper III — Official preprint release v1.0

**Title:** *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing*  
**Author:** Juan Pablo Traverso Gianini  
**Release date:** 2026-07-25  
**Release status:** official preprint release  
**Peer-review status:** not externally peer-reviewed  
**Novelty status:** subject to specialist literature review

This directory is the canonical public package for Paper III, preprint v1.0.

## Interactive explainer

A bilingual (EN/ES), five-level plain-language explainer of the paper (no JavaScript; renders on GitHub Pages):

- File: [`PaperIII_explained_4_levels.html`](PaperIII_explained_4_levels.html)
- Rendered preview: [PaperIII_explained_4_levels.html](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_III/PaperIII_explained_4_levels.html)


## Directory structure
```
01_manuscript/       manuscript (EN/ES: md/tex/pdf) + figures
02_validation/       internal adversarial audits and validation records
03_reproducibility/  reproducibility material
04_integrity/        SHA-256 integrity manifest
05_formalization/    Lean 4 / Mathlib v4.28.0 development + reports
```

## Formalization note
The Lean development is **not axiom-clean by design**: it retains two named external asymptotic inputs
as axioms `AX1` (Haxell–Rödl / Yuster) and `AX2` (Dross + Barber–Kühn–Lo–Osthus). See
`RELEASE_METADATA.yml` and Section 11.6 of the manuscript.

## File locations in this repository
- Manuscript (EN/ES): `01_manuscript/PAPER_III_preprint_v1.0.{md,tex,pdf}` (and `_es`).
- Figures: `01_manuscript/paperIII_figures_v0.9.12/`; standalone copies in `figures/`.
- Lean: `05_formalization/lean/PaperIII/`, `PaperIII.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`; reports `05_formalization/AXIOM_REPORT.txt`, `FORMALIZATION_REPORT.md`, `LEAN_STATUS.md`, `LEDGER.md`.
- Appendix C computational scripts (locations in this release):
  - `audit_c_fast.py`, `audit_c_ilp.py`, `audit_c_ilp_results.txt` → `02_validation/IA_ADVERSARIAL_AUDIT/EXTERNAL_ADVERSARIAL_AUDIT_PACKAGE/RESULTS (DRAFT PAPER VERSION)/`.
  - `verify_common_profile_LP.py` → `02_validation/IA_ADVERSARIAL_AUDIT/EXTERNAL_ADVERSARIAL_AUDIT_PACKAGE/OUR_INTERNAL_AUDIT/block02_common_profile_LP/`.
  - internal verification suite → `02_validation/INTERNAL_AUDIT/block0*/` (`verify_identities.py`, `verify_common_profile_LP.py`, `verify_margin.py`, `verify_corridor_ILP.py`).
- Appendix C scripts (recreated from the manuscript descriptions, run, PASS): `03_reproducibility/appendix_C_scripts/` — `verify_fractional_margin.py`, `verify_factor_rounding.py`, `verify_shifted_center.py`, `verify_polarization.py`, `verify_divisibility_correction.py` (each with a `*_results.txt`). **Open reconciliation (editor gate):** these recreated scripts still need to be matched to the exact Appendix C names/counts, and the pre-existing internal-audit scripts (`verify_common_profile_LP.py`, `verify_margin.py`, `verify_identities.py`, `verify_corridor_ILP.py`) cross-checked against them, before the package is frozen.
