# Gate E0 report — run_v1.2_r1 (Paper IV v1.2)

Verdict: **PASS**. Evidence directory: `20_EVIDENCE/E0/`.

---

## E0 Identity — initial pass (2026-09-30, ~12:25 UTC)

Scripts (auditor-written): `e0_identity.py`, `e0_source_consistency.py`, `e0_manifests.py`.
Raw outputs: `E0_IDENTITY.json`, `E0_SOURCE_CONSISTENCY.json`, `E0_MANIFESTS.json`,
`source_file_hashes.json`, `import_graph.json`. Logs in `10_LOGS/E0_*.log`.

## Readiness
1. Owner requested execution in chat on 2026-09-30 → met. (`AUDIT_TARGET_v1.2.json` still says
   `execution_authorized: false`; that field predates the request and is not modified by the auditor.)
2. Target status `READY_FOR_EXTERNAL_AUDIT`; all mandatory bindings present; target sha256
   `d1eb542d…fdc29` equals the value in `PREPARATION.json`.
3–5. Bound author validation / internal audit exist by hash (contents deferred per mandate §3).
   Readiness is not an E0 PASS.

## Source identity (piv-v12-fb459343d234)
- All 30+ bound files: sha256 and byte counts match (`all_bound_hashes_match: true`).
- Source ZIP: 615 members, no CRC errors, no unsafe paths/duplicates/symlinks.
- ZIP ↔ directory ↔ SOURCE_MANIFEST: 615 = 615 = 615, zero content mismatches.
- 607 `.lean` modules (recomputed); 8 non-Lean entries (FREEZE_SCOPE.json, docs/PUBLICATION_AUDIT.md,
  lakefile.toml, lake-manifest.json, lean-toolchain, 3 tools/*.py).
- FREEZE_SCOPE lists exactly the 19 targets named in the mandate; all exist as modules.
- Toolchain `leanprover/lean4:v4.28.0`; Mathlib rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
  All 9 packages in the shared cache have git HEAD equal to the frozen manifest revs with
  0 tracked modifications. Packages root is not a junction (realpath = itself).
- Import graph: union of the 19 target closures = **607** own modules (all modules), matching §7's
  statement that every local module lies in the closure of the 19 targets.
  **CORRECTION C-01 (auditor):** the first run of `e0_source_consistency.py` used an import regex that
  missed Lean module-system `public import` lines (21 occurrences, 20 files with `module` header) and
  reported 594 with 13 `RequestProject.AFKS/AS` modules outside every closure. That result was an auditor
  parsing error; the regex was fixed and rerun (`10_LOGS/E0_source_consistency_run2.log`). Original
  run log preserved (`10_LOGS/E0_source_consistency.log`). Static closure is still to be confirmed by E4's
  actual build graph.
- Lakefile declares `lean_lib` names `PaperV`, `E18`, `E19` etc.; no `PaperV.*` module exists in the cut
  (OBSERVATION E0-O2, configuration residue, no content).
- Textual scan for sorry/admit/axiom/unsafe/implemented_by/extern/native_decide/opaque/ofReduceBool:
  all hits are inside doc comments (`/-! … -/`); no code-level occurrence. Kernel-level confirmation deferred to E4.

## Manuscript identity (piv-v12-manuscripts-2451d43bface)
- MANUSCRIPT_MANIFEST (105 files) matches directory bytes; ZIP has 106 members = 105 + manifest, all hashes equal.
- Directory holds 212 additional unbound files (editorial reports, QA PNGs, history) — not part of the identity.
- PDFs: EN 68 pages, ES 69 pages (pymupdf, independently counted) — match the stated counts.

## Author-build evidence identity
- EVIDENCE_MANIFEST: 1238 entries; all present on disk with matching hashes; ZIP has 1239 members
  (1238 + manifest) and every manifest hash occurs in the ZIP. Contents not read yet (deferred to E8).

## Annex
- Annex ZIP: 40 members = 38 `BoundedCliqueGap/*.lean` + README + SOURCE_MANIFEST.sha256; all 39 manifest
  entries match ZIP content.
- v1.0 base ZIP: 508 members, 504 `.lean`, no BoundedCliqueGap files; its lakefile/manifest/toolchain equal
  the bound `lean_v1.0_freeze` files; lakefile declares BoundedCliqueGap; package revs equal v1.2's.

Status: **E0 initial checks PASS; final E0 requires the end-of-run immutability recheck.**
Status: **E0 initial checks PASS; final E0 requires the end-of-run immutability recheck.**

## Final recheck (2026-09-30 22:04 UTC)
`e0_identity.py` rerun: all 31 bound files and all ZIP integrity results identical to intake; source ZIP ↔ directory ↔ manifest still 615/615 with no mismatch (`10_LOGS/E0_identity_final.log`, `E0_IDENTITY_initial.json` vs `E0_IDENTITY.json`). **E0 = PASS.**
