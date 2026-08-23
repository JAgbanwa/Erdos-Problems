# Paper I v1.3 external-audit correction matrix

**Source audit:** Paper I v1.2 external adversarial audit, copied under
`02_validation/00_intake/EXTERNAL_AUDIT_v1.2_FINAL_REPORT.md`.

**Correction scope:** manuscript and package evidence only. The Lean v1.2
freeze is byte-identical and was not rebuilt internally.

| Finding | Severity | v1.3 disposition | Blocking regression |
|---|---:|---|---|
| `EXT-P1-L-001` | MAJOR | Removed all five duplicated Spanish blocks from Markdown and LaTeX; regenerated the Spanish PDF | Each marker must occur exactly once in Spanish Markdown, TeX and extracted PDF text; all Spanish pages rendered and inspected |
| `EXT-P1-M-001` | MINOR | Replaced the stale v1.1 integrity baseline with v1.3 source and target manifests plus this matrix | `CURRENT_TARGET_SHA256.txt` must verify every listed file |
| `EXT-P1-D-001` | MINOR | Added the explicit `z_e=x_e` substitution, the `H`-edge contribution to `|w_1|`, and the cancellation yielding (4.7) | The explanation and both displayed identities must occur in EN/ES Markdown and TeX |
| `EXT-P1-E-002` | MINOR | Restricted the Appendix A.2 excess formula to `o>=3`; routed `o=0,1,2` to A.3 | EN/ES source and PDF checks for the qualifier and boundary cross-reference |
| `EXT-P1-J-001` | MINOR | Clarified that `sharp` refers only to quadratic coefficient `1/6`; the additive term remains unoptimized | Bilingual wording check and unchanged theorem statement review |
| `EXT-P1-I-001` | MINOR | Added the author-hosted scan of Chen--Erdős--Ordman supporting the `3/16` constant | URL must occur in both languages and rendered PDFs |
| `EXT-P1-I-002` | MINOR | Replaced the unverified `Corollary 7.1g` pinpoint by the supported chapter-level reference `[4, Chapter 7]` | Obsolete pinpoint absent; chapter citation synchronized in EN/ES |
| `EXT-P1-I-003` | MINOR | Removed the unused repository bibliography entry that advertised an obsolete public bound | Repository URL absent from Markdown, TeX and PDF text |

The external audit reported no mathematical or formal defect: the theorem,
proof-critical identities, exact-rational checks and clean Lean reconstruction
survived. The internal audit nevertheless reruns its complete mathematical
regression suite against v1.3 and reviews the recorded Lean evidence without a
new build.
