# Paper II v1.2 internal audit final report

> **Overall verdict:** `PASS`  
> **Audit class:** internal / author-side / not external  
> **Protocol:** `INTERNAL_AUDIT_STANDARD_v1.3`  
> **Date:** 2026-08-21  
> **Lean execution:** recorded builds reviewed; full builds not rerun

## Frozen target

| Item | Value |
|---|---|
| English manuscript SHA-256 | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` |
| Spanish manuscript SHA-256 | `d0d1df05eb267a51db2ccc100dd9725dcde9b03dbb95c8a730742e357eb0f4dc` |
| Formal archive | `PAPER_II_lean_v1.2_freeze.zip` |
| Formal archive SHA-256 | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` |
| Recorded builds | exit 0; 8,061 main jobs and 8,032 supplementary jobs |
| Recorded axiom footprint | `propext`, `Classical.choice`, `Quot.sound` |

## Gate results

| Gate | Verdict | Principal evidence |
|---|---|---|
| G0 Target | `PASS` | 57 static/integrity checks; six artifacts; 45 source and 62 package entries |
| G1 Claims | `PASS` | Exact theorem, branches, degeneracies, scope and quantifiers |
| G2 Mathematics | `PASS_AFTER_HARNESS_CORRECTION` | 195 LPs; exact maximization through (n=5000); 139 chordal atlas graphs; 931 copy pairs |
| G3 Formal conformance | `PASS` | `PaperII.theorem_1_2` and auxiliary surfaces match their manuscript roles |
| G4 Recorded build | `PASS_RECORDED_BUILD` | Both actual logs and 16-surface axiom output reviewed; no full rebuild |
| G5 Bilingual | `PASS` | 52/52 headings, three figures and 27 protected identifiers aligned |
| G6 TeX/PDF | `PASS` | EN 23 / ES 24 pages, embedded fonts and all pages visually inspected |
| G7 Prior art | `PASS_INTERNAL` | Scoped negative result; specialist external review remains open |
| G8 Package | `PASS` | Delivered archive and manuscript provenance are exact and self-contained |

## Corrective batch admitted before the rerun

The stale formal-package name, hash, directory and table labels were replaced by the delivered v1.2 archive and the two actual recorded build logs. All MD, TeX and PDF artifacts and hashes were regenerated. Internal version history was removed from the manuscript. No theorem statement, extremal value or proof step changed.

## Overall verdict

`PASS`. All nine blocking internal gates pass. There are no unresolved internal blocker or major findings. Independent reconstruction, external adversarial audit, specialist prior-art review, peer review, tagging and publication approval remain open external gates.
