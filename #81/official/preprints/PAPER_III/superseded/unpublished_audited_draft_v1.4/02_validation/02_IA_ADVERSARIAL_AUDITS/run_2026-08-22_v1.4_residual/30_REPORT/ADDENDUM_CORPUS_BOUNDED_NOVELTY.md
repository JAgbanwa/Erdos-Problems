# Addendum — corpus-bounded novelty language

**Applies to** `run_2026-08-22_v1.4_residual/30_REPORT/FINAL_AUDIT_REPORT.md`,
SHA-256 `2c19bf1ca74f77cc409b8d0102adf01b92d13db885ac81d15d156477abed8842`.
**Filed** 2026-08-23, by the external auditor, during
`run_2026-08-23_v1.4_challenger`.
**Reason** the report above is sealed. Under the standing rule that a sealed report is never
rewritten, this correction is filed alongside it rather than applied to it. The report's hash is
unchanged and remains the reference version.

## What is corrected

Two claims in the sealed report are stated absolutely, as claims about the published literature.
The evidence supports only a claim about the corpus that was actually searched. Both are
overreach by the auditor and are corrected here.

**1. Section 11, "Gate 8 — citations, openness and novelty".**

As written:

> No published integral upper bound for split graphs at or below `n^2/6 + O(n)` exists.

Corrected to:

> No such published result was identified in the searched corpus. No published integral upper
> bound for split graphs at or below `n^2/6 + O(n)` was identified in the searched corpus.

**2. Section 13, "What this audit does and does not establish".**

As written:

> No published result gives an integral split-graph bound at or below `n^2/6 + O(n)`.

Corrected to:

> No such published result was identified in the searched corpus.

## What is not corrected

The underlying findings stand unchanged. The six load-bearing references were verified at source;
the Cavers survey was retrieved in full and contains no occurrence of "chordal", `3/16`, `n^2/6`
or "Zalcstein"; arXiv:2608.11536 (Ning, 30 July 2026) was read and cites EOZ only as prior work;
and the four distinctions requested — fractional versus integral, `o(n^2)` statements, general
chordal, and the optimal linear coefficient — were each tested separately. The result of gate 8
remains `PASS` and the finding remains "no collision found **in the searched corpus**".

The sealed report already limited itself correctly in one place, listing "Novelty beyond the
corpus actually searched" under what the audit does not establish. This addendum brings the two
absolute formulations into line with that limitation.

## Effect on the verdict

None. Gate 8 remains `PASS`; the sealed report's overall verdict is untouched by this addendum.
The separate question of that verdict's `CONDITIONAL_PASS` status is addressed in
`run_2026-08-23_v1.4_challenger/30_REPORT/FINAL_AUDIT_REPORT.md`, section 2, and not here.
