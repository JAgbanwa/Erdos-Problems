# External challenger and correction review request - Paper III v1.4

## Mandate

Act as an independent adversarial challenger of the corrected Paper III v1.4 target. Review
the two open minor findings from the preserved external audit, perform the specified
regression checks, and issue a new consolidated verdict. Do not modify the preserved prior
audit or any manuscript/formalization artifact.

Place all new work under:

`02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.4_challenger/`

## Preserved baseline

- Prior report: `run_2026-08-22_v1.4_residual/30_REPORT/FINAL_AUDIT_REPORT.md`.
- Prior report SHA-256:
  `2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842`.
- Prior findings ledger SHA-256:
  `17db6da295c4e8bed225b20dd676fa09a2b766a4a84ccce0fd74810f35fe2b39`.
- The prior audit reached `PASS` on every blocking gate, including an uninterrupted clean
  Lean build, aggregate-root/import closure, 42 axiom surfaces, AX1/AX2 semantic bridges,
  E2 mathematical rederivation and E6 prior-art/novelty review. Its only substantive open
  items were `EXT-V14-M01` and `EXT-V14-M02`, both classified `MINOR`.

## Corrected target hashes

```text
eea753a4c352bafcb36f8bd09c262de0bfcae5379318264aa76c21628965136f *PAPER_III_preprint_draft_v1.4.md
5e3cf6da1d43a213bd5b2991c0916e045192b0574cf759129de009d99b64f90f *PAPER_III_preprint_draft_v1.4_en.tex
afd00647f22b97fd2f761ed052857e4273bc88cb265b9d1af8dad347ba943702 *PAPER_III_preprint_draft_v1.4_en.pdf
83e3844e5b62ddeb8cebed46d1557e692f94b5ed25bb683f6b6e173f8ebfe15c *PAPER_III_preprint_draft_v1.4_es.md
fbf30d758c849fb062f1619f18e2c2ca68b0e6ddaf69f8741b9fde8eee756910 *PAPER_III_preprint_draft_v1.4_es.tex
5804253aabc815bc0092048c47289f2956273a0a477b4e1b5a7c8906987ee8d4 *PAPER_III_preprint_draft_v1.4_es.pdf
```

The English artifacts are byte-identical to the prior external target. The Lean archive is
also byte-identical:

`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`

In addition, the author-side fast-machine reproduction at
`03_reproducibility/author_build_evidence/run_2026-08-23_clean_PASS/` now has a raw runner
verdict of `PASS_CLEAN_UNINTERRUPTED`: 8,455 public-root jobs, 8,444 query-root jobs, all
eight axiom files, 42 surfaces and a foundational-only axiom union. Its independent
postcheck passes 69/69. This supplements, rather than replaces, the prior external build.

## Required review A - EXT-V14-M01

1. Compare English and Spanish Section 2.4 in Markdown. Confirm that both say Sections 5--7
   and Proposition 10.5 use no asymptotic input, while using standard facts such as
   complete-graph edge coloring.
2. Confirm that the corrected Spanish sentence propagates to LaTeX and rendered PDF page 8.
3. Rerun or independently replace the bilingual loss/duplication checks. Explicitly report
   whether any long paragraph, theorem, proof, list item, table row, equation tag, citation,
   or Lean identifier is missing or duplicated.
4. Confirm the Spanish PDF has 47 pages, embedded fonts, no clipping or missing glyphs, and
   no fatal/undefined/missing-character/overfull diagnostic in the final build log.

## Required review B - EXT-V14-M02

Independently audit Appendix D as a proof, not merely as a statement matching Galvin's
theorem. At minimum check:

1. preservation and termination in the kernel coloring lemma;
2. both cases in the Gale--Shapley stability proof;
3. the alternating-path parity and recoloring step in the proof of Koenig edge coloring;
4. the `Delta-1` orientation out-degree bound;
5. the equivalence between kernels and stable matchings in every induced edge set; and
6. the Section 7.2 application, including simplicity/bipartiteness of the gain graph and
   `|L(v_i r)| >= max{rho,u} >= Delta`.

The internal ledger at
`run_2026-08-22_v1.4_editorial_residual/20_EVIDENCE/M02_APPENDIX_D/`
is a map of possible failure points only. Do not treat it as proof authority; derive the
argument independently before comparing conclusions.

## E2 and E6 carry-forward arguments

### E2

The prior external audit did not merely inherit E2. It independently rederived Sections
4--9, including `K-EPS`, `K-CORRIDOR`, `K-SPARSE` and `K-GLOBAL`, tolerance propagation,
parity/boundary cases, deletion/divisibility, the hypergraph-to-graph passage and the
eventual-to-global induction. The corrected target changes no English mathematical byte and
only repairs one Spanish explanatory sentence. Verify byte identity and treat E2 as a valid
carry-forward `PASS` unless the challenger identifies a specific mathematical regression.
The 315,183-check internal E2 ledger may be used only as an obligation map.

### E6

The prior external audit independently refreshed the Chen--Erdos--Ordman `3/16` split bound,
the complete-split `1/6` lower bound, the open status of the full chordal problem, the cited
primary sources and 2023--2026 search trails, and found no collision in its searched corpus.
No citation, novelty sentence, bibliography entry or English manuscript byte changed here.
Treat E6 as a valid carry-forward `PASS` after confirming that regression boundary.

The new consolidated report must correct two absolute formulations in the prior report.
Replace claims of the form "No published result exists/gives ..." with the corpus-bounded
form: "No such published result was identified in the searched corpus." Do not claim
novelty beyond the documented search perimeter.

## Lean regression - no rebuild requested

Do not rerun `lake build`. The Lean source/archive bytes did not change, and the preserved
external audit already completed an uninterrupted clean build of 8,455 public-root jobs and
8,444 query-root jobs plus all eight axiom files. For this correction review:

1. verify the Lean archive SHA-256 above;
2. verify the prior external build logs and result manifests remain present and sealed; and
3. verify the supplemental author-side raw-PASS ZIP and its 69/69 validation summary; and
4. carry forward the Lean gates if those checks pass.

A new multi-hour build would add no regression information for an editorial-only Spanish
change and an independent review of a written appendix.

## Deliverables

Use this structure:

```text
00_CONTROL/   protocol, environment, commands, target hashes, regression boundary
10_LEDGER/    updated findings ledger and Appendix D proof ledger
20_EVIDENCE/  raw comparison, render, hash and proof-review evidence with manifests
30_REPORT/    FINAL_AUDIT_REPORT.md and FINAL_AUDIT_SUMMARY.json
40_PACKAGE/   sealed review archive and SHA-256 sidecar
```

The final report must disposition `EXT-V14-M01`, `EXT-V14-M02` and `EXT-V14-N01`, state the
E2/E6/Lean carry-forward basis explicitly, use corpus-bounded novelty language, and issue one
consolidated verdict. `PASS` is required if both minor findings close, the regression boundary
holds, and no new blocker or major finding is discovered. The absence of an additional reviewer
beyond this commissioned challenger is not itself a blocker.
