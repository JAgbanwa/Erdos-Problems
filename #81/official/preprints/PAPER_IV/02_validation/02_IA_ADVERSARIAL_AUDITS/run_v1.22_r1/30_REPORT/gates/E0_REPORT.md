# Gate E0 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E0/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E0 — Identity, integrity and preservation (initial and final)

Script: `e0_v122.py` (auditor-written, read-only). Runs: `E0_INITIAL.json` (2026-10-01T09:54Z, before any review) and `E0_FINAL.json` (2026-10-01T10:35Z, after E2–E8). **The two `checks` objects are identical.**

| Check | Result |
|---|---|
| `AUDIT_TARGET_v1.22.json` sha256 cbe0fd6e… matches its sidecar | True |
| Candidate manifest `MANUSCRIPT_REVIEW_MANIFEST.json` (d9e559a3…) sha and bytes as bound | True / True |
| Package `PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip` (2b87b746…) sha and bytes as bound; sidecar | True / True / True |
| Mandate (7dee0923…) and frozen source manifest (fb459343…) as bound | True |
| Earlier evidence: run_v1.2_r1 ZIP, run_v1.21_r1 ZIP, Lean source ZIP (cb274145…), annex ZIP (2847a422…) | all sha and bytes True |
| Manifest vs directory: 223 files, 0 mismatches | OK |
| ZIP: 225 members (= 223 + manifest + sidecar), testzip OK, no unsafe paths, no hash mismatch, no extra or missing member | OK |
| Other ZIPs in the candidate directory | none (single package; E8-03) |
| Lean cut `lean_piv-v12-fb459343d234`: 615/615 manifest entries match, no extra files | OK |
| run_v1.2_r1: 1097 manifest files unchanged on disk; ZIP sidecar matches; testzip OK | OK |
| run_v1.21_r1: 340 manifest files unchanged on disk; ZIP sidecar matches; testzip OK | OK |

The PDFs have 72 pages (EN) and 73 pages (ES).

**E0 verdict: PASS.** The identity is complete and matching, so the review was allowed to start. Neither the inputs nor the historical evidence changed during the review.
