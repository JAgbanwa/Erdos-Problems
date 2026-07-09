# Paper I — Official preprint release v1.0

**Title:** *Affine Profile Reduction for Fractional Triangle Packings in Split Graphs*  
**Author:** Juan Pablo Traverso Gianini  
**Release date:** 2026-07-06  
**Release status:** official preprint release  
**Peer-review status:** not externally peer-reviewed  
**Novelty status:** subject to specialist literature review

This directory is the canonical public package for Paper I, preprint v1.0.

Historical drafts, superseded proofs, private audit records, sealed materials,
and unverified formalizations should remain outside this release directory.

## Directory structure

```text
01_manuscript/       Official PDF and source files
02_validation/       Public calculation ledger and validation status
03_reproducibility/  Build instructions and environment notes
04_integrity/        Hashes, manifest, and provenance
05_formalization/    Verified Lean 4 formalization of Theorem 1.1 (sorry-free, axiom-clean)
```

## Canonical files

- `01_manuscript/PAPER_I_preprint_v1.0.pdf`
- `01_manuscript/PAPER_I_preprint_v1.0.tex`
- `01_manuscript/PAPER_I_preprint_v1.0.md`
- `02_validation/CALCULATION_LEDGER_FINITE_FRACTIONAL_preprint_v1.0.md`
- `05_formalization/lean/PaperI/PaperI_Statement.lean` (Lean theorem `paperI_main` = Theorem 1.1)
- `05_formalization/lean/gate_logs/print_axioms_residual_and_main.log`

## Validation boundary

The main theorem is recorded by the project as `FINAL_PASS / FROZEN / CLEAN`
and was approved for preprint release by the editor and researcher. The public
validation material does **not** constitute external peer review, journal
refereeing, or a specialist priority review.

## Integrity check

From the root of this directory, run:

```bash
sha256sum -c 04_integrity/SHA256SUMS.txt
```

On Windows PowerShell, compare file hashes with:

```powershell
Get-FileHash -Algorithm SHA256 <path-to-file>
```

## Licensing

This package inherits the repository-level license. If the package is
distributed outside the repository, copy the complete repository `LICENSE`
file into this directory before redistribution.
