# Deliverable Specification

Return a self-contained result folder and ZIP:

```text
RESULTS/
  README.md
  ADVERSARIAL_AUDIT_REPORT.md
  ADVERSARIAL_AUDIT_REPORT.pdf
  ENVIRONMENT.md
  SHA256_MANIFEST.txt
  received_inputs.sha256
  received_inputs/
    PAPER_III_preprint_v1.1.5_near_final_editorial_en.md
    SHA256.txt
  findings/
    FINDINGS.csv
  blockA_claim_faithfulness/
  blockB_AX1_AX2_literature_scope/
  blockC_bulk_sparse_corridor_proof_attack/
  blockD_counterexample_and_boundary_search/
  blockE_independent_computation/
  blockF_audit_the_internal_audit/
  blockG_lean_verification/
  EXTERNAL_AUDIT_RESULT.zip
  EXTERNAL_AUDIT_RESULT.zip.sha256
```

Every block must include `README.md`, independent scripts or derivation notebooks where applicable, written outputs under `results/`, and a one-page PDF certificate. The auditor must not rely on console-only evidence.

## Verdicts

- `PASS`: no defect found in in-scope claims; AX1/AX2 usage is faithful to the cited literature; Lean gates match the stated conditional/unconditional scope.
- `PASS_WITH_OBSERVATIONS`: no blocking defect, but minor issues, coverage limitations, or editorial tightening opportunities remain.
- `FAIL`: blocking mathematical, computational, citation, dependency, AX1/AX2 overstatement, or Lean/manuscript mismatch.

## Findings CSV

```csv
id,claim_ref,block,attack,inputs_or_ranges,outcome,severity,reproduction_cmd,evidence_file
```

Allowed outcomes: `CONFIRMED`, `PLAUSIBLE`, `REFUTED`, `OUT_OF_SCOPE`.
Allowed severities: `none`, `minor`, `major`, `blocking`.

## PDF style guidance

The PDF report should stay close to the current audit-report style, but with clearer visual hierarchy. Use the local Python stack available on this machine:

- `reportlab` for primary PDF generation;
- `pypdf` for merge/stamp operations;
- `pdfplumber` for text/layout inspection;
- `Pillow` for any raster assets;
- `PyMuPDF` (`fitz`) for render-based QA.

Recommended presentation:

- title page with paper, version, date, and global verdict;
- a short summary table up front;
- consistent color accents for `PASS`, `PASS_WITH_OBSERVATIONS`, and `FAIL`;
- compact tables for claims, findings, and reproduction commands;
- monospaced font for paths, hashes, Lean identifiers, and shell commands;
- restrained use of color, enough to guide reading but not enough to obscure content;
- page numbers, section headings, and a reproduction appendix;
- no dependency on HTML-to-PDF tooling.

Before delivery, render-check the PDF to confirm that tables, headings, and long paths do not clip or overlap.
