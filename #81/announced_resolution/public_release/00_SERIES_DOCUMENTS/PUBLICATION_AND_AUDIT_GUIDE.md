# Publication and Audit Guide

This package separates public release material from internal working records.

## Publishable material

Everything under:

`01_PUBLIC_RELEASE/`

may accompany the papers publicly.

For each paper, the recommended public release contains:

1. `01_MANUSCRIPT/`
   - PDF for reading and citation;
   - LaTeX source;
   - Markdown source.

2. `02_PUBLIC_AUDIT/`
   - final closure audit;
   - proof-dependency ledger;
   - submission claims matrix;
   - AI-assisted review or series disclosure where available.

3. `03_REPRODUCIBILITY/`
   - exact regression scripts;
   - corresponding outputs;
   - a statement that scripts are supplementary and not proof premises.

4. `04_INTEGRITY/`
   - SHA-256 manifest;
   - static and PDF inspections;
   - visual contact sheet where available.

## Internal material

Everything under:

`02_INTERNAL_WORKING_RECORD/`

is retained for traceability but should not be published by default.

It contains:

- editorial plans;
- proof gates and intermediate memos;
- build scripts;
- previous closure candidates;
- original historical package snapshots.

## Mathematical status

The scripts and finite enumerations are not logical premises of the theorems. The proofs are analytic, modulo the external mathematical theorems identified in each dependency ledger.

## What remains outside this package

- independent human peer review;
- journal refereeing;
- a definitive specialist novelty and forward-citation search;
- publication licenses, which must be chosen separately by the author.
