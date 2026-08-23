# Gate K - Prior art and novelty (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS_WITH_RESIDUALS`
**Search cutoff:** 2026-08-21 (the audit date)

Gate K is separate from Gate I. Correct citations do not establish novelty. This gate does
not assume the manuscript's novelty conclusion.

## The claim under test

Paper II claims no earlier result determines the same **exact finite extremum** for the
fractional triangle-cover functional on chordal graphs, with the complete-split extremizers
and the symmetrization route proved there.

## Corpus

The searched corpus is shared across the three papers and is recorded once, with the full
query log, inclusion and exclusion criteria and collision log, in Paper III's Gate K
record. As it bears on Paper II:

| Work | Object and quantity | Relation to Paper II |
|---|---|---|
| Erdos-Ordman-Zalcstein 1993 (publisher record and abstract retrieved verbatim) | chordal graphs, **integral** clique partition: lower `n^2/6` by construction, upper `(1-c)n^2/4` | **different object.** Paper II bounds a *fractional cover functional* and determines it *exactly*; EOZ bound an integral partition number and leave it open. No collision. |
| Chen-Erdos-Ordman 1994 | **split** graphs, integral, `3n^2/16 + O(n)` | different object and a subclass. No collision. |
| Cavers 2005 (full text retrieved and searched) | general clique partitions and coverings | contains no occurrence of "chordal", "split graph", or the `n^2/6` bound. No collision. |
| Ning, arXiv:2608.11536, 30 July 2026 (retrieved) | **general** graphs, `cp - cc` difference | most recent relevant preprint located. Different object. No collision. Still cites EOZ as the chordal state of the art. |
| Barbados 2025 open problems (retrieved, text extracted) | - | no relevant problem listed. No collision. |
| Golumbic 2004; Blair-Peyton 1993 | standard chordal-graph theory | background, not competing results. Blair-Peyton retrieved and confirmed. |

## On the specific quantity

No retrieved work states an **exact** maximum of `|E(G)| - 2 tau_3^*(G)` over chordal
graphs of fixed order, nor identifies complete-split graphs as the extremizers, nor uses a
vertex-copy symmetrization to get there. The searched literature addresses integral clique
partitions and asymptotic bounds. Paper II's object - an exact finite fractional extremum
with an identified extremizer family - is of a different kind, and the manuscript draws that
distinction itself.

An independent point in favour of the framing: this audit verified the exact value by
exhaustive enumeration over all 19,048 chordal graphs on up to 6 vertices, and the closed
form `floor((2n+1)^2/24)` matched at every `n`. A result of that specific shape would be
hard to state without the closed form, and no retrieved source states it.

## Bounded conclusion

**No prior result with the same statement was found in the searched corpus as of
2026-08-21.** This is an evidence-bounded negative search result. It is **not** proof that
no such result exists and does **not** substitute for specialist confirmation of novelty.

## Residuals carried, not resolved

1. No institutional bibliographic database (MathSciNet, zbMATH) was available, and no
   citation-graph traversal of works citing EOZ was performed.
2. No non-English-language search was performed.
3. erdosproblems.com returned HTTP 403 on every path, so the official problem page was
   never read directly.
4. Specialist confirmation of novelty is outstanding. The manuscript itself declares
   independent prior-art review an open release gate, which is the correct posture.

## Verdict rationale

No collision found; the novelty framing is defensible against the corpus actually searched;
the residuals above are real and are disclosed rather than absorbed.
