# Paper IV v1.2 — bilingual manuscripts after full reconstruction

**EDITORIAL_DRAFT_WITH_OPEN_GATES.** Locally sealed for renewed audit, not a
publication or an internal/external audit PASS. Version 1.2 is retained.

## Current artifacts

- PAPER_IV_preprint_v1.2_en.{md,tex,pdf}: English; 68 PDF pages.
- PAPER_IV_preprint_v1.2_es.{md,tex,pdf}: Spanish; 69 PDF pages.
- BILINGUAL_FREEZE_REPORT.md: changes, checks and limitations.
- ARTIFACT_CHECKS.json, BILINGUAL_CHECKS.json, VISUAL_QA_RECORD.json: final checks.
- MANUSCRIPT_MANIFEST.json and detached MANUSCRIPT_FREEZE.json: package identity.
- NEXT_INTERNAL_AUDIT_SCOPE_v1.2.md: next audit, including E.4, F.3a, F.5 and A.2.
- FULL_REBUILD_RESEAL_EN.diff and FULL_REBUILD_RESEAL_ES.diff: this pass's delta.

The Markdown files are the semantic sources. Only status and build-evidence
prose changed in this pass. The already approved Figure 2 references remain.
No theorem, equation, hypothesis, constant, proof or attribution changed.

## Unchanged source and completed reconstruction

Source cut: **piv-v12-fb459343d234**. It contains 607 Lean modules and 615
manifest entries. The full serial reconstruction compiled all 607 modules
across two verified segments. After the restart, 421 freshly compiled objects
were verified and reused; the resumed segment compiled 186 modules. All 19
audit targets ran freshly in that segment. All 224 exports passed. There are
461 permitted-axiom records, not 461 distinct theorems. No pre-existing project
objects were used; no module failed, was blocked or was omitted.

- Source: ../../05_formalization/lean_piv-v12-fb459343d234/.
- Source record: ../../04_integrity/FREEZE_piv-v12-fb459343d234.json.
- Evidence seal: ../../03_reproducibility/full_rebuild_v12_20260929_seal/.
- Resumed evidence: ../../03_reproducibility/full_rebuild_v12_20260929_resume/.
- Preserved first segment: ../../03_reproducibility/full_rebuild_v12_20260929_r2/.

The older build_piv-v12-fb459343d234 records describe another execution of the
same sources. Source, execution-evidence and manuscript hashes are distinct.

## Reproduction and history

The two build_draft scripts use final Markdown, existing vector figures and
series templates with the installed Pandoc/Tectonic; they compile the delivered
TeX twice and render the PDFs. check_release_artifacts.py checks preservation,
parity and source/evidence bindings without running Lean. Translation-preparation
scripts are historical aids, not authority to overwrite the final Spanish text.

Regenerating a PDF requires rerendering, review and a new seal. Historical
ZIPs are not overwritten. The previous candidate remains in ../v1.2_candidate/;
the immediate baseline is in review_history/before-full-rebuild-reseal/.

Next is a **new internal audit** on this exact cut. The external mandate at
../../02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.2.md
is prepared but blocked until that audit completes, its evidence is bound,
and the owner requests the external cycle. Earlier verdicts do not certify
this revision. No Lean rebuild, Mathlib installation, external submission,
publication or DOI assignment occurs in this editorial pass.
