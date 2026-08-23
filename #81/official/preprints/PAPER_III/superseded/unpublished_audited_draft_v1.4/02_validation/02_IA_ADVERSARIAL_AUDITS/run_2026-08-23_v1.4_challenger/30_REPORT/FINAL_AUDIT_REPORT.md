# Paper III v1.4 — external challenger and correction review

**Run** `run_2026-08-23_v1.4_challenger`
**Commissioned by** the principal researcher, `EXTERNAL_CHALLENGER_CORRECTION_REVIEW_REQUEST_v1.4.md`
(SHA-256 `06051b3fb31ba05b36c83ddae736f108fd04a374b9765531d976d48be2919ac5`)
**Mandate** review the two open minor findings, verify the regression boundary, audit Appendix D
as a proof, correct two absolute novelty formulations, issue one consolidated verdict.

## 1. Verdict

> **`PASS`**

Both minor findings close. The regression boundary holds exactly as declared. No blocker and no
major finding was discovered. Two new `NOTE`-level observations arose from the Appendix D review;
neither affects any proof step, and both are recorded rather than concealed.

| Item | Disposition |
|---|---|
| `EXT-V14-M01` Spanish Section 2.4 | **CLOSED** |
| `EXT-V14-M02` Appendix D self-containedness | **CLOSED** |
| `EXT-V14-N01` stale `internal_audit` field | **OPEN, ACCEPTED** — defensible under the declared `audit_lifecycle` policy |
| `EXT-V14C-N02` Theorem 2.2 omits "simple" | **NEW, NOTE** — expository, no proof step depends on it |
| `EXT-V14C-N03` three unstated standard steps in Appendix D | **NEW, NOTE** — each a one-line consequence |

## 2. A correction to the prior external report's reasoning

The prior external run, `run_2026-08-22_v1.4_residual`, returned `CONDITIONAL_PASS`. Its stated
reason was that no adversarial challenger had examined the package. **That reason is withdrawn
here as a category error.** An audit finding must be a property of the target. How many external
reviewers have been commissioned is a property of the review programme, and conditioning closure
on the existence of a further reviewer makes external closure unreachable in principle: the same
objection would apply to every subsequent reviewer in turn. The substance of the concern —
that this paper's external review has come from a single reasoning context, with the correlated
blind spots that implies — is real and is restated in section 7 as a **declared limitation**,
which is where it belongs. It is not a defect of Paper III and does not gate closure.

The prior report's verdict itself is not rewritten. It is corrected by addendum, per the standing
rule that a sealed report is never rewritten.

## 3. Regression boundary — confirmed as declared

Every declared hash was recomputed. Detail in `00_CONTROL/REGRESSION_BOUNDARY.md`; raw output in
`20_EVIDENCE/C_REGRESSION/regression_boundary.txt`.

- Both declared baseline hashes — the prior report and the prior findings ledger — **match**.
- All six declared manuscript hashes **match**.
- Compared against the prior external run's own 1,194-entry target manifest: the three English
  artifacts are **unchanged**, the three Spanish artifacts **changed**. The request's claim of
  English byte identity is confirmed, and the change set is confined to Spanish.
- The Lean archive is `79ee24c3…7104`, matching the declared value and the prior target. No
  Lean source byte changed.
- The prior external run's build logs, evidence manifests, summary and sealed package are all
  present. The prior package re-verifies **60/60 files** against its own manifest and its ZIP
  matches its sidecar. That evidence is intact and unaltered.

## 4. Review A — `EXT-V14-M01`: **CLOSED**

**Check 1, English and Spanish Section 2.4 in Markdown.** Both now state that Sections 5–7 and
Proposition 10.5 use no asymptotic input, each with the same caveat that standard facts such as
the edge colouring of complete graphs are used. The Spanish reads: *"Por tanto, las Secciones
5–7 y la Proposición 10.5 no utilizan insumos asintóticos, aunque emplean hechos estándar como
el coloreo de aristas de los grafos completos."* Content-equivalent to the English. **PASS.**

**Check 2, propagation to LaTeX and page 8.** The corrected sentence appears exactly once in the
Spanish `.tex`, in Section 2.4, and exactly once in the rendered PDF, on **page 8**. A scan of
pages 1–12 finds it on no other page. **PASS.**

**Check 3, bilingual loss and duplication — independently replaced, not rerun.** A fresh
comparator was written for this run (`20_EVIDENCE/A_BILINGUAL/v14c_bilingual.py`) rather than
reusing the prior run's. It compares, in document order, every structure that must be
language-invariant. Results:

| Structure | EN | ES | Outcome |
|---|---|---|---|
| headings | 144 | 144 | count and level sequence identical |
| displayed formulas | 205 | 205 | 5 positional differences; **0** after masking `\text{...}` operands |
| equation tags | 66 | 66 | identical multisets |
| citation references | 18 | 18 | identical multisets |
| Lean identifiers | 36 | 36 | identical multisets |
| table rows | 21 | 21 | identical after canonicalising digit-group separators |
| list items | 30 | 30 | equal |
| long paragraphs per section | — | — | 14 sections differ in count; all adjudicated |

Three differences were flagged and each was adjudicated
(`20_EVIDENCE/A_BILINGUAL/adjudication.json`):

1. **Formulas.** The five differing formulas differ only inside `\text{...}` operands —
   `chordal`/`cordal`, `even`/`par`, `odd`/`impar`, `for all`/`para todo`. After masking those
   operands, **zero** of the 205 formulas differ. Translation, not loss. This also independently
   confirms that the Spanish edit introduced no formula drift.
2. **Table rows.** `8,455` versus `8.455` — Spanish thousands separator. Localisation.
3. **Paragraph counts.** Character-length ratios across the 14 flagged sections run 1.02–1.11,
   the normal expansion of Spanish over English, so the count differences are the >120-character
   threshold tripping at different points, not splits or additions. Language-invariant anchors
   (inline math, displays, citations, code spans, tags) are identical in 13 of the 14. The
   fourteenth, Section 12.5, has one extra inline `\(r\)` in Spanish: English writes "for fixed
   \(K_r\)-and-edge partitions", Spanish restructures to "para particiones en \(K_r\) y aristas,
   con \(r\) fijo". Same content, one additional math span from the restructuring.

**No long paragraph, theorem, proof, list item, table row, equation tag, citation or Lean
identifier is missing or duplicated in either direction.** **PASS.**

**Check 4, Spanish PDF quality.** 47 pages. 13 fonts, **all embedded**, all subset, all with
Unicode maps. A 72 dpi grayscale raster of all 47 pages finds **no ink** in the left, right, top
or bottom margin bands, so no clipping and no content outside the 1-inch geometry.

No Spanish LaTeX build log was delivered with the target, so the requested log check could not be
performed as written. It was replaced with stronger evidence: **the auditor rebuilt the Spanish
PDF from the sealed `.tex`** using the same LuaTeX 1.24.0 that produced it. The auditor's own log
shows `0` fatal errors, `0` undefined control sequences, `0` missing characters, `0` overfull
boxes, `0` LaTeX or package errors, and `0` missing files; the only diagnostics are 5 underfull
boxes, which are cosmetic and outside the requested categories. The rebuild produced 47 pages and
is **text-identical to the sealed PDF on all 47 of 47 pages**. This establishes both that the
render is clean and that the sealed PDF is a faithful render of the sealed source — which the
author's log alone would not have shown. **PASS.**

## 5. Review B — `EXT-V14-M02`: **CLOSED**

Appendix D was derived independently from its own definitions, and the author-side ledger at
`01_INTERNAL_AUDITS/run_2026-08-22_v1.4_editorial_residual/20_EVIDENCE/M02_APPENDIX_D/` was
opened only afterwards. The full derivation is
`20_EVIDENCE/B_APPENDIX_D/independent_derivation.md`, also filed as
`10_LEDGER/APPENDIX_D_PROOF_LEDGER.md`. (The request located that ledger under
`02_IA_ADVERSARIAL_AUDITS/`; it is in fact under `01_INTERNAL_AUDITS/`. Path detail only.)

| Requested check | Result |
|---|---|
| 1. Lemma D.1 preservation and termination | **valid.** The invariant `\|L(v)\| >= d+(v)+1` survives because a vertex losing the colour also loses an out-neighbour in the kernel — the one place domination is used. Kernels of nonempty digraphs are nonempty, so each round colours at least one vertex; no stall state exists |
| 2. Gale–Shapley, both cases | **valid.** Case A rests on monotone improvement of the edge held at `r` and on `r` never reverting to unmatched. Case B concludes `u` is matched, forced by the loop guard, then uses decreasing proposal order. The cases are exhaustive and the stability notion is the domination form Step 3 later needs |
| 3. König alternating-path parity and recolouring | **valid, and the parity is the right way round.** A path ending at `r` must end on `alpha` since `r` misses `beta`, hence have even length; bipartite adjacency of `u` and `r` forces odd. Not reversible. The swap preserves properness by maximality, leaves `r` untouched, and frees `beta` at `u` |
| 4. `Delta-1` out-degree bound | **valid.** At most `Delta-c` higher-coloured edges at `u` and `c-1` lower-coloured at `r`, summing to `Delta-1` independently of `c`. The two counts are disjoint precisely because `B` is simple — this is where simplicity is load-bearing |
| 5. kernels ↔ stable matchings in **every** induced edge set | **valid.** Incident edges are always joined by exactly one arc because properness of `phi` makes each endpoint order strictly total; domination is verbatim the D.2 stability condition; and D.2 applies to every subgraph `(V(B),S)`, so the quantifier over all induced subdigraphs is genuinely discharged |
| 6. Section 7.2 application | **valid.** Gain graph simple and bipartite by construction. Recomputed from the Section 2.1 and Section 7 definitions: `G_i = R ∩ N_i` so `d(v_i) = g_i <= rho`; `d(r) <= \|U\| = u`; and `\|L(v_i r)\| = \|N_i ∩ Q\| = b - t_i` exactly. With (7.2), `b - t_i >= max{rho,u} >= Delta` against the actual maximum degree. The triangles `v_i r z` are legitimate and the family is edge-disjoint by properness at both endpoints |

**No circularity.** D.1 needs only kernel-perfectness; D.3 derives kernel-perfectness from D.2;
D.2 is self-contained; König's theorem is reproved in Step 1 rather than assumed. The dependency
order is acyclic and every ingredient is proved inside the appendix.

**The self-containedness claim is established.** No step of Theorem 1.1 rests on Galvin's theorem
[10] as an unproved external input, and the Borodin–Kostochka–Woodall local refinement [4] is
correctly described as unnecessary — (7.2) does bound every list by the gain graph's maximum
degree, as recomputed above.

**Agreement with the author-side ledger, and where this review goes further.** The internal
ledger reaches `PASS_INTERNAL` on all six areas and this review agrees point for point,
including its identification of the parity step as the one most susceptible to reversal. Two
observations are new here, both raised in `20_EVIDENCE/B_APPENDIX_D/independent_derivation.md`:

- **`EXT-V14C-N02` (NOTE).** Theorem 2.2 is stated for "a bipartite graph"; Theorem D.3 proves
  the **simple** case, and Step 2's out-degree additivity genuinely requires simplicity. Under
  the usual convention that "graph" means simple graph the statements coincide, but the
  manuscript never declares that convention and Remark D.4 itself treats the multigraph version
  as a separate result. Nothing in the proof chain depends on the difference — the sole
  application is the gain graph, verified simple. Recommended repair: insert "simple" into
  Theorem 2.2. Notably, the internal ledger already states the claim under review as being about
  a *simple* bipartite graph, so author and auditor read Theorem 2.2 the same way; only its
  wording lags.
- **`EXT-V14C-N03` (NOTE).** Three standard steps are left unstated: that the reduced digraph in
  Lemma D.1 is still kernel-perfect, needed for the recursion; that the `alpha`/`beta` subgraph
  has maximum degree 2 with `u` of degree 1 in it, which is what makes "the maximal path" well
  defined and simple; and that the Step 1 induction runs over graphs of maximum degree *at most*
  `Delta`. Each is a one-line consequence and none affects validity.

## 6. Carry-forward — E2, E6 and the Lean gates

**E2 — `PASS`, carried forward.** The prior external run rederived Sections 4–9 from definitions
against English text that is byte-identical here, and the Spanish change is one explanatory
sentence carrying no mathematical content. Independently corroborated in this run: all 205
displayed formulas agree across the two languages after masking `\text{...}` operands, so the
Spanish edit introduced no formula drift either. No mathematical regression identified.

**E6 — `PASS`, carried forward, in corpus-bounded form.** No citation, bibliography entry,
novelty sentence or English byte changed. The prior run verified six load-bearing references at
source, retrieved the Cavers survey in full, and read the most recent adjacent work
(arXiv:2608.11536, Ning, 30 July 2026). Restated correctly:

> **No published integral upper bound for split graphs at or below `n^2/6 + O(n)` was identified
> in the searched corpus.** The state of the art as found in that corpus is a gap — lower bound
> `n^2/6 + O(n)`, best identified split-graph upper bound `3/16 n^2 + O(n)`, problem open — and
> Paper III addresses exactly that gap for split graphs.

**Lean gates — `PASS`, carried forward.** Archive byte-identical; prior build logs, evidence
manifests and sealed package present and re-verifying 60/60. No rebuild was requested and none
was performed; for a Spanish editorial change and a review of a written appendix, a rebuild would
add no regression information. This carry-forward rests on byte identity, not on trust.

## 7. Correction of two absolute novelty formulations

The prior external report contains two claims stated absolutely rather than bounded by the corpus
actually searched:

1. § "Gate 8": *"No published integral upper bound for split graphs at or below `n^2/6 + O(n)`
   exists."*
2. § "What this audit does and does not establish": *"No published result gives an integral
   split-graph bound at or below `n^2/6 + O(n)`."*

Both overreach: the evidence supports a statement about a searched corpus, not about the
published literature in full. Each is replaced by the corpus-bounded form — *"No such published
result was identified in the searched corpus"* — filed as
`ADDENDUM_CORPUS_BOUNDED_NOVELTY.md` against the sealed prior report, which is not rewritten.
This report uses the bounded form throughout. Novelty is claimed nowhere beyond the documented
search perimeter.

## 8. What this review establishes, and what it does not

**Establishes.** The corrected target is exactly what the request declares, with the change set
confined to three Spanish artifacts and the English and Lean bytes untouched. The Spanish
Section 2.4 defect is repaired in Markdown, LaTeX and on page 8 of the PDF, and the Spanish PDF
is a clean 47-page render that this auditor reproduced page-for-page from the sealed source with
no fatal, undefined, missing-character or overfull diagnostic. The two documents carry no
structural loss or duplication in either direction. Appendix D is a complete and correct
self-contained proof of the maximum-degree case of Galvin's theorem for simple bipartite graphs,
and it discharges exactly what Section 7.2 uses, so the paper's list-edge-colouring dependency
is genuinely internal. The prior run's evidence is intact and its E2, E6 and Lean conclusions
carry forward on verified byte identity.

**Does not establish.** The **truth** of Theorem 1.1 — no audit establishes that, and failed
falsification is not proof. The Lean nibble chain's internal parameter ledger. Novelty beyond the
corpus actually searched. **Human peer review.**

**Declared limitation on this review's own weight.** Paper III's external review, across five
runs including this one, has come from a single reasoning context, so its blind spots are
correlated rather than independent. This is a statement about the coverage of the review
programme, not a defect of Paper III, and it does not gate closure — but a reader should weigh
the `PASS` accordingly, and a genuinely independent reviewer would still add information that
this run cannot supply.

## 9. Signature

Verdict: **`PASS`**. Two minor findings closed, regression boundary confirmed, no blocker or
major finding, three notes outstanding of which two are new and both expository.
