# Paper III v1.4 changelog

Baseline: unpublished Paper III v1.3 external-review target.

## Formal release surface

- The public aggregate root now imports `PaperIII.Theorem_1_1_Final` and
  `PaperIII.PublicAPI` explicitly.
- The obsolete aggregate-root scaffold description was replaced by the public-root
  contract.
- The canonical triangle-packing interface and its integral/fractional bridges are
  explicit in the directed axiom gate.
- The build protocol now matches the actual public-root, query-root and eight-file axiom
  sequence.
- Freeze metadata records the exact v1.4 source and archive and truthfully classifies the
  author build as `PASS_CLEAN_ORIGIN_RESUMED`.

## Manuscript and bilingual corrections

- Spanish Proposition 7.4 was restored in full, including its quantitative hypotheses.
- Previously omitted Spanish clauses were restored at the exact benchmark, `q=0` case,
  formal API scope, obstruction remark, algorithmic limitation and open-problem sections.
- English and Spanish Markdown now have the same 144-heading hierarchy, section-block
  profile, 205 display-math sequence, equation tags, citation sequence and Lean identifier
  set.
- Both Markdown sources have zero duplicated long paragraphs.
- LaTeX and PDF were regenerated from the corrected Markdown sources and all 93 rendered
  pages passed visual QA.

## Audit closure

- Fresh mathematical regressions pass: 12 symbolic identities, 351 common-profile LP and
  exact-cover cases, 78,384 exact margin cases, 372 ILP sanity cases and 180/180 applicable
  packing/corridor bounds.
- The separate internal E2 residual passes 315,183 exact checks and records universal
  derivations for the previously unattempted analytic obligations.
- The full v1.4 internal audit passes 144/144 checks across G0--G8.
- External finding M01 was resolved in place by restoring the full Section 2.4 scope in
  Spanish, including Proposition 10.5 and the standard complete-graph edge-coloring
  background. The Spanish LaTeX and PDF were regenerated from the corrected Markdown.
- Appendix D was rederived internally from the stated definitions: the kernel-coloring
  induction, Gale--Shapley stability argument, König alternating-path step, orientation
  out-degree bound and kernel-perfectness identification all pass. Independent challenger
  confirmation remains required.
- The English manuscript artifacts and the complete Lean v1.4 freeze remain byte-identical
  to the externally audited target; no Lean rebuild was performed for these editorial and
  review-only corrections.
- A separate author-side clean uninterrupted reproduction now reports raw `PASS`: 8,455
  public-root jobs, 8,444 query-root jobs, eight axiom files and 42 surfaces, with axiom
  union exactly `[propext, Classical.choice, Quot.sound]`. Its received ZIP, logs and 69/69
  validation record are preserved outside the immutable freeze.

## Mathematical content

No theorem statement, definition, hypothesis, constant, proof branch, canonical bridge or
asymptotic conclusion changed in v1.4.
