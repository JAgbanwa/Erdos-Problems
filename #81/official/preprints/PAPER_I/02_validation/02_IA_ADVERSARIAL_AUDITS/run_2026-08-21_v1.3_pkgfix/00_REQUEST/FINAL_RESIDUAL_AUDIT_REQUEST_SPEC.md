# Paper I v1.3 — final external package-residual re-audit request

**Request date:** 2026-08-21  
**Audit class:** external residual adversarial re-audit  
**Target:** corrected `preprint_draft_v1.3` package  
**Required outcome:** a new standalone plain `PASS` if the two open MINOR
findings are closed and no regression is found  
**Input mutation:** prohibited

## 1. Purpose

The preceding external residual audit issued `PASS_WITH_RESIDUALS`: all nine
mandatory manuscript controls, the mathematical regression, bilingual and
duplicate analysis, artifacts, citations and byte-identical Lean reuse passed.
It left exactly two open MINOR package findings:

- `RES-V13-001`: compiler scratch under
  `tmp/internal_report_v1.3/`;
- `RES-V13-002`: two declaration namespaces transposed in
  `CHANGELOG_v1.3.md`.

This final residual run must verify those corrections, perform a package-level
regression, and issue a new standalone verdict for the corrected target. Do not
rewrite the earlier report and do not edit the target.

## 2. Corrected target freeze

Target root:

`preprints/PAPER_I/active/preprint_draft_v1.3/`

Exclude the complete
`02_validation/02_IA_ADVERSARIAL_AUDITS/` subtree from the input freeze because
it contains audit requests and outputs.

The supplied manifest contains **308 files**, **37,763,479 bytes**, with
aggregate path/hash-list SHA-256:

`f12e1060c0e8693a5702ae9a5c0d143a3025feadcf6a7289e90c061769c748b6`

Required intake files:

- `00_REQUEST/INPUT_TARGET_MANIFEST.sha256`
- `00_REQUEST/INPUT_TARGET_INVENTORY.json`

Recompute every entry before analysis. Any mismatch is a `BLOCKER`.

## 3. Controlling anchors

The mathematical, manuscript and formal artifacts did not change:

| Artifact | SHA-256 |
|---|---|
| English Markdown | `f3094b670c93ff622c3f573cdab61bdd0f5d84007f04b1888b364e0183565bea` |
| Spanish Markdown | `57ba967fc2de805b7bbb4cf5f937727bde43c2ada80fa794bcbb5a727db05b8b` |
| English LaTeX | `1a87de70548879ca90a714ec9e1b10c8576b380a749785916e5d59176e479465` |
| Spanish LaTeX | `f83ee709c1168b5b9afe504e6b6a43763bf3bb2a08f674f2031f83670ba9bb56` |
| English PDF | `7d04c47692b613c8d6e2cc4471f0205128b4ae06ca11d581a08d020eb2236db0` |
| Spanish PDF | `3ad16ae86e8fcad358bf964a6ae98ae053b0bde2fdf3140e008cedab78b90c2a` |
| Lean archive | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` |
| Previous external report | `f2ad1605f0a802932c07503bfad429a98b08af26844dd968aad6e3f145aee495` |
| Corrected changelog | `0850e518dc35bab0065ddb9f6b2a5850bc8c1d079ce7ed27872d6b09074349ef` |
| Internal residual audit ZIP | `0ac2fa306a2df8607b2d2d5d54ec4d9cdda8eca4f21dd8e47f1e36d8adae92e6` |

## 4. Authorized changes since the preceding external freeze

The target delta is package-only:

1. removed the three scratch files and their `tmp/internal_report_v1.3/`
   directory;
2. corrected one changelog line to
   `PaperI.assembly_sharp` and
   `PaperI.Split.residual_duality`;
3. added the correction matrix and new internal residual audit evidence;
4. updated package README/metadata status to record the internal residual PASS.

There is no manuscript, theorem, proof, citation, figure, LaTeX, PDF, formal
source, toolchain, dependency or axiom-query change.

## 5. Mandatory final controls

### A. RES-V13-001

- verify that no directory named `tmp` occurs in the input target;
- verify that no `.aux`, `.toc`, `.out`, `.fls`,
  `.fdb_latexmk`, `.synctex.gz`, `.nav` or `.snm` scratch file occurs;
- verify no zero-byte file, stray `$o`, hidden compiler output or duplicate
  internal-report copy remains;
- verify the removed files are not referenced by any target document.

### B. RES-V13-002

- verify `CHANGELOG_v1.3.md` contains exactly one occurrence each of
  `PaperI.assembly_sharp` and
  `PaperI.Split.residual_duality`;
- verify `PaperI.Split.assembly_sharp` and
  `PaperI.residual_duality` are absent;
- compare the corrected names with manuscript Appendix C,
  `FreezeAxioms.lean`, the recorded axiom report and the previous external
  verbatim theorem-level output.

### C. General package regression

- verify all 308 manifest entries, every supplied sidecar and the internal
  residual audit ZIP;
- verify the six publication-artifact and Lean hashes remain the controlling
  anchors above;
- verify no unannounced target delta, stale version/path/hash, truncated file or
  unresolved blocker/major/minor was introduced;
- inspect the internal residual report and raw gate evidence rather than relying
  on its PASS label;
- confirm that the manuscript remains self-contained and does not depend on
  audit documents.

## 6. Evidence reuse and prohibited unnecessary work

The previous external report already completed the full mathematical,
bilingual, duplicate, citation, artifact and formal regressions. Those results
may be reused only after the eight manuscript/formal anchors above match
exactly.

Do **not** rerun `lake update`, `cache get`, the 8,034-job Lean build, the full
mathematical enumeration or PDF compilation merely because package metadata
changed. Reopen the relevant gate only if an anchor mismatch or a new
claim-affecting delta is found. Label reused evidence
`REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE`.

The third-party certificate issue `RES-V13-004` remains a disclosed NOTE. The
previous report expressly found it nonblocking after the primary source and
`3/16` pinpoint were auditor-verified.

## 7. Verdict rule

A plain `PASS` is required if:

- both MINOR findings are independently closed;
- the target inventory and anchors verify;
- the package regression finds no new blocker, major or minor;
- reused evidence satisfies byte identity;
- the report preserves the accessibility NOTE and states that this is not human
  peer review and does not prove global novelty.

If any condition fails, issue the appropriate finding and stop. Do not modify
the target.

## 8. Required output

Write only under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.3_pkgfix/`

Required deliverables:

- `10_CONTROL/`: auditor declaration, environment, findings and gate status;
- `20_EVIDENCE/`: target verification, the two correction gates, package
  regression and byte-identity reuse records with manifests;
- `30_REPORT/FINAL_AUDIT_REPORT.md`: semantic source and standalone verdict;
- synchronized `FINAL_AUDIT_REPORT.tex` and compiled/visually checked
  `FINAL_AUDIT_REPORT.pdf`;
- `FINAL_AUDIT_SUMMARY.json`;
- `40_PACKAGE/`: final manifest, audit archive and SHA-256 sidecar generated
  last.

The new report must explicitly state whether Paper I v1.3 is externally closed
with a plain `PASS`. It must not relabel the earlier
`PASS_WITH_RESIDUALS` report.

