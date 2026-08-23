# Paper III v1.5 — closure of `EXT-V15-M01` and consolidated verdict

**Run** `run_2026-08-23_v1.5_residual_closure`
**Request** `EXTERNAL_PASS_CLOSURE_REQUEST_v1.5.md`, SHA-256
`37118ecff3894b8c018c1031cd619f88e05e449e6fd685cce14ff3920bbaf034`
**Scope** the residual closure test only. No gate of the source run was repeated.

## 1. Verdict

> **`PASS`**

`EXT-V15-M01` is **CLOSED**. All six checks the request enumerates pass, and so do four
additional checks this auditor added because the correction was a file relocation and a
deletion — the two edits most likely to break something silently. **10 of 10.** No new defect
was introduced by the correction, no blocker, no major, no open minor, no open note.

The preserved `CONDITIONAL_PASS` report is **not rewritten**. It remains the record of the audit
that produced the finding; this report records the finding's closure and the resulting current
verdict.

| Item | Disposition |
|---|---|
| `EXT-V14C-N02` | CLOSED in the source run, on its mathematics |
| `EXT-V14C-N03` | CLOSED in the source run, on its mathematics |
| `EXT-V15-M01` | **CLOSED here** |
| Consolidated current verdict | **`PASS`** |

## 2. The closure test, as this auditor stated it

The source report set one test: *"no file in `03_reproducibility/` outside a `v1.3`/`v1.4`-
labelled path names a non-v1.5 artifact or quotes a non-v1.5 hash."*

That test is met. It is worth being explicit that this is the test I wrote, and the correction
satisfies it exactly. Having declined to reclassify a real `MINOR` downward to reach `PASS` in
the source run, I am equally not going to invent a further requirement now that the stated one
has been met.

## 3. The six required checks

**1 — no file directly under `manuscript_build_logs/`.** Confirmed: **zero** loose files. The
directory now contains exactly three version-labelled subdirectories, `v1.3_legacy/`, `v1.4/`
and `v1.5/`.

**2 — the 29 relocated logs.** `v1.3_legacy/` contains exactly **29** files; the supplied
manifest has exactly **29** entries; **29/29 hashes match**; none absent; no extra file outside
the manifest. Content genuineness was tested on the **output job name**, not on any occurrence
of a version string: every one of the 29 names a v1.3 job, and **none** names a v1.5 job. So the
relocation was byte-preserving in both directions — nothing lost, nothing misfiled.

**3 — the six current v1.5 logs.** All six in `manuscript_build_logs/v1.5/` name the correct
v1.5 output artifact, report **46 pages for English and 47 for Spanish**, and contain **zero**
prohibited diagnostics — no fatal error, no undefined control sequence, no missing character, no
overfull box, no LaTeX error. All **6/6 hashes match** the supplied manifest. These are the same
page counts and the same clean diagnostics that this auditor independently reproduced in the
source run by rebuilding both PDFs from the delivered TeX.

**4 — the consistency JSON.** The generic `MANUSCRIPT_CONSISTENCY_RESULTS.json` is **absent**.
The versioned `MANUSCRIPT_CONSISTENCY_RESULTS_v1.5.json` reports `PASS`, **61 checks, zero
failed**, and its English Markdown hash is `a98e9313…c99a` — exactly the v1.5 English Markdown
accepted in the source report. The stale v1.4 hash `eea753a4…36f` no longer appears in any
active location.

**5 — the target is unchanged.** All **six** manuscript hashes and the Lean archive
`79ee24c3…7104` recomputed and matched, exactly the values accepted in the source external
report. The correction touched no manuscript, TeX, PDF, figure, mathematical text, citation or
formal source byte.

**6 — no prior audit report modified.** The v1.4 external residual report
(`2c19bf1c…8842`), the v1.4 external challenger report (`a196479b…b5f3`) and the v1.5 external
residual report (`4f453781…7596`) all match their declared hashes. All three sealed packages
re-verify in full against their own manifests: **60/60**, **24/24** and **45/45**.

## 4. The four checks the request did not ask for

A relocation and a deletion fail in specific ways, so these were added.

**A — nothing in the release points at a moved or deleted file.** Every one of the **1,572
entries in `TREE.txt`** was reconstructed from its indentation and resolved against the
filesystem: **all 1,572 resolve**. `TREE.txt` was in fact regenerated, listing the 29 logs under
`v1.3_legacy/`, and `04_integrity/CURRENT_TARGET_SHA256.txt` was updated to its new hash
`2f5ae5a6…f310`, so the integrity record stayed consistent with the move. Across the 122 text,
Markdown, HTML, YAML, JSON, CITATION and manifest files scanned, **zero** references to the
moved or deleted files fail to resolve.

**B — local links still resolve.** **Zero broken local links** across the 15 README links and 10
HTML links. A relocation is a common way to break these; it did not.

**C — the deleted evidence is genuinely preserved, not lost.** The v1.4 consistency result
survives at
`superseded/unpublished_audited_draft_v1.4/03_reproducibility/MANUSCRIPT_CONSISTENCY_RESULTS.json`,
describing v1.4 (`md_en = eea753a4…36f`, `PASS` 51/51) — the same version the removed file
described. **Stated limitation:** byte-identity between the deleted file and this one cannot be
proved, because the file is gone and neither the source audit nor the closure packet recorded its
hash. What is established is that the v1.4 evidence itself was not destroyed, which is what
matters; the deletion removed a duplicate from the active tree, not a unique record.

**D — the pattern does not recur.** A sweep of the release surfaces for the shadowing pattern —
a filename present both at a version-labelled and at an unlabelled path — returns **zero**. The
defect class is eliminated, not merely its two known instances.

## 5. Contrast with the author's own verification

The author's `verify_EXT_V15_M01_closure.py` was run **after** the independent checks, as a
contrast only, and reports `PASS` 16/16, including "no stale generic compiler-log name survives
outside v1.3_legacy". It agrees with this run on every overlapping point. It was not used as
evidence for any conclusion above. The closure packet ZIP matches its sidecar
(`7972a0b5…20e4`), 13 members, CRC clean.

## 6. Consolidated current verdict

> **`PASS`**

Carried forward from the source external run, on evidence produced there and re-verified here as
unchanged: `E0` intake, `E1` delta and claim review, `E2` mathematical regression, `E3` formal
conformance and Lean identity (751/751 by exact key, byte-identical to the audited v1.4 freeze,
eight axiom queries with no `sorryAx`), `E4` Lean carry-forward with no rebuild, `E5` bilingual
and rendered artifacts (46 and 47 pages, all fonts embedded, one author block each, correct
metadata, no clipping, auditor rebuild page-for-page identical), `E6` prior art with the bounded
statement retained, and `E7` release surfaces. Established in this run: the one open `MINOR` is
closed and the correction introduced nothing new.

**What this does not establish**, unchanged from the source report: the **truth** of Theorem 1.1
— no audit establishes that, and failed falsification is not proof. The Lean nibble chain's
internal parameter ledger. Novelty beyond the searched corpus; no priority determination is made
or implied, and the bounded form stands — *no published integral upper bound for split graphs at
or below `n²/6 + O(n)` was identified in the searched corpus*. **Human peer review**, which has
not occurred. And the full chordal problem remains open.

**Declared limitation on this review's weight**, unchanged: this auditor raised `EXT-V14C-N02`,
`EXT-V14C-N03` and `EXT-V15-M01` and has now reviewed all three fixes, and Paper III's external
review across six runs has come from a single reasoning context, so its blind spots are
correlated rather than independent. That is a property of the review programme, not a defect of
Paper III, and consistent with the request it does not gate the verdict — but a reader should
weigh the `PASS` accordingly.

## 7. Signature

`EXT-V15-M01` **CLOSED**, 10/10 independent checks. Source `CONDITIONAL_PASS` report preserved
byte-identical. Consolidated current verdict: **`PASS`**.
