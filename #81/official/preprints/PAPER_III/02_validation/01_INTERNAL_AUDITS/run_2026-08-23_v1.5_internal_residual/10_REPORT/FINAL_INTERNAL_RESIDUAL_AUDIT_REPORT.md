# Paper III v1.5 final internal residual audit report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / non-independent / residual  
> **Date:** 2026-08-23  
> **Lean execution during audit:** no; recorded evidence and byte identity inspected

## Frozen target

| Item | Value |
|---|---|
| English MD / TeX / PDF | `a98e9313…` / `6a97bc71…` / `077a12da…` |
| Spanish MD / TeX / PDF | `ee5a3ef2…` / `cfc2cac7…` / `5ed3f83b…` |
| Formal archive | `PAPER_III_lean_v1.4_freeze.zip` |
| Formal archive SHA-256 | `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104` |
| Baseline | unpublished, externally audited v1.4 |
| Residual executable result | 79/79 checks passed |

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target and hashes | `PASS` | six v1.5 hashes verify; LF-only sidecar; no draft-named active manuscript |
| G1 Protected delta | `PASS` | displayed mathematics, equation tags, heading order and citation multiset unchanged; N02/N03 present in EN/ES |
| G2 Mathematical carry-forward | `PASS` | sealed v1.4 144/144 internal PASS, final external challenger PASS and E2 rederivation preserved |
| G3 Formal identity | `PASS` | archive CRC/hash, 707-source and 751-package manifests; all 707 manifested sources byte-identical |
| G4 Recorded build | `PASS_RECORDED_EXTERNAL_BUILD` | independent 8,455/8,444-job build and directed axiom evidence inspected; no rebuild performed |
| G5 Bilingual and duplication | `PASS` | 61/61 suite; 144 headings each; no duplicated long paragraph; scope/novelty synchronized |
| G6 TeX/PDF/render | `PASS` | clean final logs; EN 46 / ES 47 pages; embedded subset fonts; all 93 pages rendered and inspected |
| G7 E2/E6 and review limits | `PASS` | E2/E6 external PASS preserved; corpus-bounded novelty and no-human-review limitation explicit |
| G8 Release package | `PASS` | active target unique; draft controls removed; citation metadata and local HTML links current; no stale generic evidence shadows v1.5 |

## Findings and rerun history

The first executable pass reported four failed literal probes. Examination showed that all
four were harness false negatives: Markdown bold punctuation and semantically correct wording
variants (`reviewed corpus` / `corpus revisado`, and the actual peer-review and positioning
sentences). No manuscript, TeX, PDF or Lean source was changed. The probes were corrected to
test the actual semantic requirements, and the full suite was rerun.

After external finding `EXT-V15-M01`, four additional G8 controls were added. The historical
v1.3 logs were moved from generic names into `manuscript_build_logs/v1.3_legacy/`, and the
generic v1.4 consistency result was removed because its identical copy remains preserved in
the superseded v1.4 package. The versioned v1.5 logs and consistency result were unchanged.
The final result is 79/79 with no failed gate.

## Lean boundary

No Lean compilation was performed. The formal carry-forward is justified by the unchanged
archive hash, successful archive CRC, verified 707-entry source manifest, verified 751-entry
package manifest and byte comparison of every manifested source against the preserved v1.4
baseline. The prior external clean-room reproduction and directed axiom checks therefore
remain applicable to the identical formal bytes.

## Verdict

`PASS`. No internal blocker, major or minor finding remains. This internal verdict is not an
independent audit, human peer review or a new novelty certificate. The v1.5 package is ready
for a residual external adversarial audit focused on the declared editorial/proof-explication
delta and release-artifact chain.
