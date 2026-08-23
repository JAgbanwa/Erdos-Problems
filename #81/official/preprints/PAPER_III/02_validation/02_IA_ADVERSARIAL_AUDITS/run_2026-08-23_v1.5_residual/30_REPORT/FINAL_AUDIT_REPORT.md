# Paper III v1.5 — external adversarial residual audit

**Run** `run_2026-08-23_v1.5_residual`
**Request** `EXTERNAL_RESIDUAL_AUDIT_REQUEST_v1.5.md`, SHA-256
`75c82bd4cbb027408218bcc8e758ebc96b70c9fb0297544ba6f7394a76f1931c`
**Target** Paper III v1.5, six manuscript artifacts plus the unchanged v1.4 Lean freeze

## 1. Verdict

> **`CONDITIONAL_PASS`**

Every mathematical, formal, bilingual, render and release-consistency gate passes. `E0`–`E7`
pass. Both clarifications this release implements — `EXT-V14C-N02` and `EXT-V14C-N03` — close on
their mathematics, not merely on matching text. The declared regression boundary holds exactly.

The verdict is not plain `PASS` because of one open `MINOR` finding, `EXT-V15-M01`: the release
package carries generically-named stale copies of version-specific evidence that shadow the
current ones. It is non-mathematical, precisely identified, and has a one-step closure test. Per
the request's own verdict rule, `PASS` requires that no open minor remain, and I am not going to
reclassify a real defect downward to reach it.

| Gate | Result |
|---|---|
| `E0` intake and sealing | **`PASS`** |
| `E1` delta and claim review | **`PASS`** |
| `E2` mathematical regression | **`PASS`**, carried forward on verified invariance |
| `E3` formal conformance and Lean identity | **`PASS`** |
| `E4` Lean reproduction policy | **`PASS`**, carried forward; no rebuild performed |
| `E5` bilingual, conversion, rendered artifacts | **`PASS`** |
| `E6` prior art and novelty | **`PASS`**, carried forward on verified regression boundary |
| `E7` release package and public surfaces | **`PASS`** with one open `MINOR` |

## 2. The single open condition

**`EXT-V15-M01` — `MINOR`. Owner: the author. Closure test: stated below.**

Two instances of one pattern.

1. `03_reproducibility/manuscript_build_logs/LUALATEX_FINAL_en.log` and `..._es.log` build
   `PAPER_III_preprint_draft_v1.3_en.tex` / `_es.tex`, dated 22 August 2026 10:31, and report
   **45 and 46 pages with 2 overfull boxes**. The delivered v1.5 PDFs have **46 and 47 pages**
   and their real logs, in `manuscript_build_logs/v1.5/` under **identical filenames**, report
   46 and 47 pages with **zero** overfull boxes, zero missing characters and zero errors. The
   sibling `LUALATEX_{en,es}_PASS{1,2}.txt` at the same level are likewise v1.3.
2. `03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json` records
   `md_en.sha256 = eea753a4…36f`, which is the **v1.4** English Markdown, alongside the correct
   `MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json` recording `a98e9313…c99a`.

**What this is not.** No release surface, manifest or QA report cites the stale copies, and
`CURRENT_TARGET_SHA256.txt` does not list build logs at all, so **nothing in the package asserts
anything false**. The author's `RENDERED_PDF_QA_REPORT_v1.5.md` is accurate in every claim I
tested. The delivered PDFs are correct: I rebuilt both from the delivered TeX and got page-for-
page identical text.

**Why it is nevertheless a finding.** This package is being promoted to first public preprint. A
reader asked to check "the final logs" or "the consistency results" reaches a superseded artifact
first, and that artifact contradicts the shipped PDF on page count and on overfull-box count. It
misled this audit for one pass before I found the `v1.5/` subdirectory. It is a pattern rather
than a slip: two independent instances, both generically named, both shadowing correctly
versioned siblings.

**Closure test.** Remove or version-rename the four stale files in
`manuscript_build_logs/` (`LUALATEX_FINAL_{en,es}.log`, `LUALATEX_{en,es}_PASS{1,2}.txt`) so that
no generically-named log describes a version other than v1.5, and either delete
`MANUSCRIPT_CONSISTENCY_RESULTS.json` or regenerate it from the v1.5 target. Verification: no
file in `03_reproducibility/` outside a `v1.3`/`v1.4`-labelled path names a non-v1.5 artifact or
quotes a non-v1.5 hash. Nothing else in the release needs to change, and no manuscript,
formalization or prior-audit byte is affected.

## 3. `E0` — intake and sealing: `PASS`

All six declared manuscript hashes recomputed and **matched**. The Lean archive is
`79ee24c3…7104` as declared, 751 members, CRC clean, and **source-only** — no `.olean`,
`.ilean`, object file or `.lake` path. The manuscript sidecar is **LF-only**, six entries, and
agrees with the declaration. All **six preserved authorities matched** their declared hashes.
Only v1.5 artifacts are active in `01_manuscript/` — no stray v1.2/v1.3/v1.4 manuscript — and
the v1.4 target is preserved under `superseded/unpublished_audited_draft_v1.4/`.

One provenance check worth recording: the declared "v1.4 final external challenger report",
`a196479b…b5f3`, is **byte-identical to this auditor's own copy** of that report. The chain of
authorities is genuine, not a transcription.

## 4. `E1` — delta and claim review: `PASS`

**Structural invariance, as ordered sequences.** Identical in both languages across
v1.4 → v1.5:

| | v1.4 | v1.5 | sequence identical |
|---|---:|---:|---|
| displayed formulas | 205 | 205 | yes |
| equation tags | 66 | 66 | yes |
| in-text citation references | 42 | 42 | yes |
| theorem/lemma/proposition blocks | 34 EN / 36 ES | 34 / 36 | yes |
| headings | 144 | 144 | yes |
| bibliography entries | 17 | 17 | yes |

Sequences, not multisets, so a reordering would have been caught as readily as a loss.

**Delta containment.** 14 changed hunks per language — symmetric, same sections in both — and
every one classifies into the declared delta set: 1 hunk for `N02`, 3 for `N03`, and 11 for the
release-state promotion. **Zero unclassified changes.**

**Location.** **Zero hunks fall inside the mathematical core** — Sections 3 through 10 and
Appendices A, B, C, E are untouched. Exactly **two** hunks lie in Appendix D, which is exactly
the declared clarification count. The remaining twelve are in the front matter, the abstract,
§1.1, §2.4 (Theorem 2.2), §11.6 and §13. No quantifier, assumption, parity, implication,
constant or exception changed outside the declared set.

**The clarifications as mathematics.** Full derivation in
`10_LEDGER/N02_N03_DISPOSITION.md`. Summary:

- **`N02`.** "simple" is *true and necessary*: Step 2 adds the count of higher-coloured edges at
  `u` to the lower-coloured at `r` as disjoint sets, which holds exactly because no other edge
  shares both endpoints with `e`; in a multigraph the `Δ−1` bound can fail. It is also *not a
  weakening of anything used*: the Section 7.2 gain graph joins `v_i` to `r` when `r ∈ G_i`, so
  at most one edge per pair — simple by construction — and §7.2 is byte-identical. Remark D.4
  still records the multigraph version as separate and unneeded, so nothing is silently
  asserted. Section 2.4's claim that Theorem 2.2 is "proved in Appendix D" is now literally true
  rather than true-under-convention. **CLOSED.**
- **`N03`(i).** "The remaining digraph is an induced subdigraph of `D`, and hence is
  kernel-perfect" is true at every round, since an induced subdigraph of an induced subdigraph is
  induced in the original, and it sits exactly where the recursion needs it — after the deletion,
  before "Repeat." **CLOSED.**
- **`N03`(ii).** Inducting "among bipartite graphs of maximum degree at most `Δ`" is the correct
  statement: that class is closed under edge deletion, which is what makes the hypothesis
  applicable to `B − e`, whereas "maximum degree exactly `Δ`" would not be. **CLOSED.**
- **`N03`(iii).** Properness of `φ` gives the `α ∪ β` subgraph maximum degree at most two; `u`
  misses `α` and, since no colour is missed by both endpoints, has a `β`-edge — degree exactly
  one. A degree-one vertex in a max-degree-two graph is an end of a path component, so `P` exists,
  is unique and is simple. This is precisely what "the maximal path `P`" had presumed. The parity
  argument and the swap are unchanged and remain correct. **CLOSED.**

None of the four insertions introduces a claim beyond closing its gap.

**Claims v1.5 newly makes about this audit, checked against the sealed logs.** v1.5's new §11.6
and §13 text asserts an uninterrupted external reproduction from an absent project build
directory with 8,455 public-root jobs, 8,444 query-root jobs and eight passing axiom-query
files. Verified in the sealed external evidence: `03_build_PaperIII.log` reaches `[8454/8455]`
with `EXIT_BUILD=0`, `04_build_query_roots.log` reaches `[8444/8444]` with `EXIT_BUILD=0`, and
all eight `05_FreezeAxioms*.log` exit 0. `RELEASE_METADATA.yml`'s `axiom_queries: 42` and
`distinct_axiom_surfaces: 35` are also exact: 42 `depends on axioms:` lines over 35 distinct
constants. **Every release claim about the external audit is accurate.**

## 5. `E2` — mathematical regression: `PASS`, carried forward

The v1.4 external process rederived Sections 4–9 from definitions — `K-EPS`, `K-CORRIDOR`,
`K-SPARSE`, `K-GLOBAL`, tolerance propagation, parity and boundary cases, deletion and
divisibility, the hypergraph-to-graph passage, the eventual-to-global induction. Those surfaces
are **byte-identical** here: zero hunks in Sections 3–10 or Appendices A/B/C/E, and the displayed
formula, tag and citation sequences are identical. Per the request, the rederivation was not
repeated for ceremony. The only mathematical text that changed is the four Appendix D and
Theorem 2.2 clarifications, and each was rederived independently in `E1`. **No mathematical
regression identified.**

## 6. `E3` and `E4` — formal identity: `PASS`; no rebuild

`SOURCE_MANIFEST.sha256` has **707** entries and `PACKAGE_MANIFEST.sha256` has **751**, as
declared. Archive-versus-manifest by **exact key**: **751/751 match**, zero absent, zero hash
mismatch, zero archive members outside the manifest, CRC clean. Source-only confirmed. Against
the freeze preserved under `superseded/`, both manifests are **identical** and the archive ZIP is
**byte-identical**. The aggregate root `PaperIII.lean` and the canonical surfaces
`PaperIII/Theorem_1_1_Final.lean` and `PaperIII/PublicAPI.lean` remain in the archive, so the
applicable immutable target is unchanged.

The eight directed axiom-query logs all exit 0 with **no `sorryAx`**. Of 42 queries, 41 report
`[propext, Classical.choice, Quot.sound]`; the one exception,
`PaperIII.isTrianglePacking_iff_yuster`, reports `[propext, Quot.sound]` — a **strict subset**,
which is stronger, not weaker.

No `lake build` was run, as requested. `E4` is carried forward on that byte-identity proof plus
re-verification of the prior sealed evidence: the v1.4 residual package re-verifies **60/60**
files against its own manifest and the v1.4 challenger package **24/24**.

## 7. `E5` — bilingual, conversion and rendered artifacts: `PASS`

**Loss and duplication, both directions.** Headings 144/144 with identical level sequence;
equation tags 66/66; citations 18/18 distinct; Lean identifiers 36/36; table rows 20/20; list
items 30/30. Displayed formulas 205/205 with **zero** residual difference after masking
`\text{...}` operands — five raw differences, all translated prose inside `\text{}`. Fourteen
sections differ in long-paragraph count; all fourteen are benign, with length ratios 1.02–1.11
(normal Spanish expansion) and identical language-invariant anchors in thirteen. The fourteenth,
§12.5, carries one extra inline `\(r\)` because Spanish restructures "for fixed \(K_r\)-and-edge
partitions" as "para particiones en \(K_r\) y aristas, con \(r\) fijo" — same content.
**Nothing missing or duplicated in either direction.**

**Propagation.** All five clarification strings are present in **all three layers in both
languages** — 30 of 30 layer-language-clarification combinations confirmed in Markdown, generated
TeX and rendered PDF.

**Rendered artifacts.**

| | EN | ES |
|---|---|---|
| pages (expected 46 / 47) | 46 | 47 |
| fonts, non-embedded | 13, **0** | 13, **0** |
| author name / ORCID occurrences | 1 / 1 | 1 / 1 |
| `AUTHORBLOCK` placeholder token | **0** | **0** |
| PDF `Author` metadata | `Juan Pablo Traverso Gianini` | `Juan Pablo Traverso Gianini` |
| escape artifacts in rendered text | **none** | **none** |
| embedded images | 4 | 4 |
| pages with ink in a margin band | **0 of 46** | **0 of 47** |

**Exactly one centered author block per PDF, on page 1, with no second block below it** — one
name occurrence and one ORCID occurrence in the whole document, confirmed visually at 130 dpi.

**Derivation chain established by reproduction.** I rebuilt both PDFs from the delivered TeX with
the same LuaTeX 1.24.0 that produced them. My logs show **zero** fatal errors, undefined control
sequences, missing characters, overfull boxes, LaTeX or package errors, and missing files. The
rebuilds are **46/46 and 47/47 pages text-identical** to the delivered PDFs. The correct author
logs in `manuscript_build_logs/v1.5/` agree: 46 and 47 pages, zero diagnostics. So the PDFs
derive from the TeX, and the TeX from the Markdown, by reproduction rather than assertion.

**Visual inspection at readable resolution.** Title pages, the Theorem 2.2 page (page 8 in both
languages) and the changed Appendix D pages (EN 39–40, ES 40–41) were rendered at 130 dpi and
inspected. All four insertions typeset cleanly in both languages; the Spanish keeps
"kernel-perfect" as a term of art, consistent with the rest of the translation. No clipping, no
overlap, no displaced caption, no missing glyph. All 46 + 47 pages were additionally rastered for
the margin scan.

## 8. `E6` — prior art and novelty: `PASS`, carried forward

Regression boundary confirmed: **17 bibliography entries identical**, **42-reference in-text
citation sequence identical**, no novelty proposition changed in substance. The bounded form is
retained in both languages, and the front matter states it explicitly — "This is a
corpus-bounded negative search, not a proof of priority or a substitute for specialist review."
The full chordal problem is stated as open in both languages. Human peer review is disclaimed in
both — "not human peer-reviewed" in English, "sin revisión humana por pares" in Spanish. A
targeted scan for absolute formulations ("no published result exists/gives", "first ever",
"establishes priority") returns **none**.

Restated in the only form the evidence supports:

> **No published integral upper bound for split graphs at or below `n²/6 + O(n)` was identified
> in the searched corpus.**

No fresh literature sweep was performed and none was requested; this gate is a regression check,
and the perimeter remains the corpus documented in the v1.4 external runs.

## 9. `E7` — release package and public surfaces: `PASS`, one open `MINOR`

All seven surfaces present. All seven reference v1.5. Author present in six of seven
(`RELEASE_NOTES.md` omits the name, which is not an inconsistency). All **4** quoted 64-hex
hashes across the surfaces resolve to real files in the package. **Zero broken local links**
across 15 README links and 10 HTML links.

The HTML states the split-graph scope, leaves the full chordal problem open, does not claim the
chordal problem solved, reports the Lean and audit status, discloses the absence of human peer
review, and makes no absolute priority claim. `RELEASE_METADATA.yml` is exemplary on framing:
`first_formal_public_release: true`, `supersedes_public_version: null`,
`external_peer_review: false`, `specialist_priority_review: false`, and
`independent_residual_audit_v1_5: PENDING` — correctly pending, since this audit is that item.
README, changelog and release notes all frame v1.5 as the first formal public preprint and
describe v1.4 as unpublished; **none claims to supersede a public release.**

v1.4 evidence is preserved and not rewritten: both prior external reports match their declared
hashes, and both prior sealed packages re-verify in full.

The one defect is `EXT-V15-M01`, in section 2.

## 10. What this audit establishes, and what it does not

**Establishes.** The v1.5 target is exactly what the request declares. The delta is 14 hunks per
language, fully contained in the declared set, with zero incursion into the mathematical core.
Both clarifications this release implements are true, correctly placed, sufficient, and free of
new claims — checked as mathematics, from the definitions. The Lean artifact is byte-identical to
the audited v1.4 freeze, manifests verify 751/751 by exact key, and the eight axiom queries hold
with no `sorryAx`. Every factual claim v1.5 makes about the external audit is accurate against
the sealed logs. Both PDFs are clean 46- and 47-page renders that this auditor reproduced
page-for-page from the delivered source, each with exactly one author block and correct metadata.
The two documents carry no structural loss or duplication. Citations, bibliography and the
bounded novelty statement are unchanged, and the release surfaces are mutually consistent with
every quoted hash and local link resolving.

**Does not establish.** The **truth** of Theorem 1.1 — no audit establishes that, and failed
falsification is not proof. The Lean nibble chain's internal parameter ledger. Novelty beyond the
searched corpus; no priority determination is made or implied. **Human peer review**, which has
not occurred.

**Declared limitation on this review's weight.** This auditor raised `EXT-V14C-N02` and
`EXT-V14C-N03` and has now reviewed their fixes, and Paper III's external review across all five
runs has come from a single reasoning context, so its blind spots are correlated rather than
independent. This is a property of the review programme, not a defect of Paper III, and
consistent with the request it does not gate the verdict — but a reader should weigh the result
accordingly.

## 11. Signature

**`CONDITIONAL_PASS`.** `E0`–`E7` pass. `EXT-V14C-N02` and `EXT-V14C-N03` closed on their
mathematics. Regression boundary confirmed as declared. No blocker, no major, no mathematical or
formal regression. One open `MINOR`, `EXT-V15-M01`, non-mathematical, with the owner and closure
test stated in section 2. On its closure this becomes `PASS` with no further work required.
