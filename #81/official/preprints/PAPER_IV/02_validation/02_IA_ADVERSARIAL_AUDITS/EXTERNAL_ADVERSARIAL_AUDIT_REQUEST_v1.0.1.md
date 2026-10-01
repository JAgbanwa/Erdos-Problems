# External AI adversarial audit request — Paper IV v1.0.1 editorial candidate

**Request status:** r3 prepared, not executed; r2 remains **FAIL** on attribution, with E4 not run. **Audit class:** external AI adversarial review on the author's Windows machine. **Target:** the unchanged Lean source cut `piv-v1.0-f1769273dd2c` and the six corrected English/Spanish v1.0.1 manuscript files. Historical manuscripts and audits are retained, not relabelled as reviews of this target. This request neither certifies the paper nor authorizes publication.

**Handoff revision:** `r3` (28 September 2026); manuscript version remains
**1.0.1**. This corrected target supersedes r2 for further review, without
overwriting its findings or evidence. Do not start a build until the
pre-build checkpoint in §4.1 passes.

Read `04_integrity/revision_r3/AUTHOR_RESPONSE_r2.md` as an author response,
not a clearance. The r2 package is preserved with SHA-256
`06a31a2765a29028ca34159bb919ae29b43f0a08071be0bef14972bd1bbe9097`.
Start with E0, independently reconsider F-01/E7, and review the changed
bilingual files under E6. The seven F-02 proof-coverage items remain OPEN;
their new disclosure in Appendix A.2 does not discharge E2. No gate inherits
PASS without a recorded identity/dependency justification. Complete the
previously unreviewed Certo certificate and internal-evidence checks too.

## 1. Mandate and independence

Try to invalidate the mathematical statements, the manuscript-to-Lean correspondence, the formal trust boundary, the quantitative accounts and the release evidence. Reconstruct proof-critical arguments independently; do not turn the author's internal `PASS_INTERNAL_AUTHOR_SIDE` into an external verdict by rerunning its scripts. Treat the internal audit as an attack map and as evidence to challenge, not as an authority. Preserve failed tests and contrary evidence.

Do not edit the target, silently repair a proof, replace a frozen source, push to GitHub or submit a PR. Work in a separate audit directory. Disclose the auditor's model, operator, tools, access to prior discussions and any assistance from the author's scripts. Because the auditor uses the **same computer and dependency cache**, this is not a separate-machine or dependency-clean-room reproduction; independence must be demonstrated for the project build, mathematical reasoning and tests.

### 1.1 Auditor identity and prior exposure

Use a fresh agent/session without the proof-development or editorial chat
history. Prefer a model not used to produce the proofs, formalizations or
editorial reviews (including Aristotle and the participating writing/review
agents). If this is not possible, disclose the overlap **before starting**;
do not label a new session of the same model as a different model. Record
model/provider/version when available, prior participation, supplied memory,
operator and uncertainty about earlier exposure. A different model is a
useful precaution, not a guarantee of independence.

The r2 auditor declared the same model family as part of the preparation.
Prefer a different family for this cycle, at least for E7 and E2. A same-family
continuation must retain that limitation and must not call itself the requested
cross-family review. Do not transmit materials to another service automatically.

### 1.2 Local reading boundary and access record

Read only the declared inputs in `LOCAL_INPUT_SCOPE_v1.0.1.json`, the
technical dependencies needed to inspect/build them, and the auditor's own
outputs. The general research workspace is **not** an authorized input.
Do not search or inspect `ar_*`, `handoff_*`, Aristotle working trees,
unpublished Paper V documents, other proof-development chats or the internal
editorial-history directory. Do not traverse those trees to find additional
proofs or favorable results. Do not read credentials or `.env` files.

Cited literature and an independent search for relevant published prior
work are allowed; limiting the search to cited papers would prevent testing
omitted antecedents. Save retrieved versions, URLs, access dates and hashes
inside the audit directory. Public literature is not authorization to read
the author's unpublished local working copies.

Create `00_CONTROL/INPUT_ACCESS_LOG.csv` with path/URL, hash or version,
purpose, phase, first-access time and authorization basis. Enumerate the
document/source files inspected; deterministic batches may use a retained
file-list manifest. Runtime libraries and build dependencies may be logged
by resolved root plus pinned manifest/version, not every OS file open.
Any additional local research file requires owner approval **before** access.
Record accidental exposure immediately, identify the material and affected
reasoning, and stop for direction if it could materially bias the review.
Do not erase that exposure from the final declaration.

This is an operational reading restriction, not an OS-enforced sandbox.
State that limitation. At intake the auditor may hash the internal archive
and read target/build metadata, but must defer reading the internal and
editorial **verdicts, derivations and test conclusions** until an independent
first pass of E1/E3, E7, E2, E5 and E6 has been recorded. Then challenge those
reports in E8. Existing author PASS assertions in this mandate/manuscript
are disclosed prior exposure, never evidence for an independent verdict.

For this correction cycle only, the r2 auditor's run and the author response
are declared intake inputs. Log this prior-finding exposure. The deferral of
the author's internal verdicts and derivations otherwise remains in force.

## 2. Exact input cut

All paths below are relative to `preprints/PAPER_IV/`. Verify hashes *before* reading the internal verdict. A mismatch is an intake failure, not a reason to substitute a newer working tree.

| Artifact | Path | SHA-256 |
|---|---|---|
| Main Lean source ZIP | `05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip` | `0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd` |
| Distinct triangular-gap annex ZIP | `05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` | `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d` |
| English Markdown / TeX / PDF | `01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_en.{md,tex,pdf}` | `d2175d22d2388e718d00cee1cd09571d3075820cddae3af0b92ec3638abe03fb` / `8a197ec9565ad15126c3450b0bcfd37c80140eea33ec8d949bcdee3b1a7517b3` / `c88a3f7fe890e6e7d562a242aea1a625f02a80b761e2b7966c9b7f62a84a5f3f` |
| Spanish Markdown / TeX / PDF | `01_manuscript/v1.0.1_candidate/PAPER_IV_preprint_v1.0.1_es.{md,tex,pdf}` | `4c2e28d6c0b443c1dcce88658ae45258b0aee93078a8406688d4896a342d952f` / `55f9b39fd7375111cc946b5c715ac4a3279479d32bf0513728d18a4fbdaac1b4` / `7a0b9acaf71442b3cd45000b760c975628f711c5cf4a4a049f66bc7d54f663d2` |
| Author-side internal-audit ZIP | `02_validation/01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/30_PACKAGE/INTERNAL_AUDIT_piv-v1.0-f1769273dd2c.zip` | `1911f29e1072accfe8df4fbec0a3b02d1cd9ef274a06bd1957f9b61034301847` |

The main source archive has 504 Lean files plus four configuration/build files. Its 13 recorded targets are listed literally in `03_reproducibility/build_v1.0_20260927/RUN_META.json`; the 195 `#check` commands are in the frozen `ReleaseExportCheck.lean`, with their build result under `modules/ReleaseExportCheck.log`. The recorded run is 504/504 PASS with exit code zero. These are **author-run facts to verify**, not the external build result. `05_formalization/LEAN_FREEZE_v1.0.md`, the internal `00_CONTROL/TARGET.json`, `CLAIM_MAP.csv`, `20_EVIDENCE/G1_CLAIMS/PUBLIC_HEADERS.md` and `10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md` identify the cut and claims. The triangular-gap annex has a separate historical 579-module build record and is **not** part of the main `PaperIV` import closure. The public v0.8 draft and other working trees are not audit substitutes.

The v1.0.1 front matter records completion of the author's internal audit and explicitly leaves the external review open. It names the unchanged series concept DOI `10.5281/zenodo.21273143`; **no version DOI for a future Papers I–IV deposit is asserted**. Compare the v1.0 and v1.0.1 texts against `01_manuscript/v1.0.1_candidate/EDITORIAL_DELTA_REPORT.md` and verify `01_manuscript/v1.0.1_candidate/MANIFEST_SHA256.md`, rather than transferring the old PDF checks to the new bytes. Do not modify either manuscript during this audit.

## 3. Same-machine Mathlib rule — mandatory

Before starting, run the read-only `verify_audit_target.py` in this request's
directory. It checks `AUDIT_TARGET_v1.0.1.json`, the candidate manifest and
archive checksums without compiling Lean or installing dependencies. Save
its output in the auditor's own intake evidence. It is an identity check,
not a substitute for gates E0–E8. The exact candidate PDFs have **52 English
pages and 53 Spanish pages**. Internal review labels 1.0.2 and 1.0.3 are not
alternative audit or publication targets.

**Do not install or clone another Mathlib.** Reuse the existing source tree on this computer, possibly through a junction/link, and record its resolved path. Verify every dependency HEAD against the frozen `lake-manifest.json`; do not change the pinned manifest with `lake update`. Existing compiled dependency artifacts may be reused. If a missing official binary-cache artifact must be fetched into the *same* verified dependency installation, record precisely what was fetched and confirm that no second Mathlib source tree was created. The recorded Lean toolchain is `leanprover/lean4:v4.28.0`; Mathlib is pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

`RUN_META.json` records the existing dependency path under `C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages/mathlib`. Treat this as a location to inspect on this machine, not as a substitute for resolving the link and checking the manifest commit at audit time.

For a genuinely fresh **Paper IV project** rebuild, extract the source ZIP into a short isolated directory; its project `.lake/build` must initially be absent or empty. Reuse only verified *dependency* artifacts, never author-built Paper IV `.olean`/`.ilean` files. Record the junction, source and package hashes, version output, commands, exit codes, timings and complete logs. Run at most one heavy build at a time; inspect existing work before starting and do not stop another team's process. Run the 13 targets separately or with an explicitly logged command that covers all of them, then test the public declarations and axiom queries. The root `PaperIV` alone does not imply that every supplementary target was imported.

At intake check only availability, toolchain version, dependency pins and
source identity. Do **not** launch the full project build, trigger implicit
compilation through a query, fetch caches or rebuild Mathlib at this stage.
The expensive isolated project build belongs to the final phase in §4.1.

If the pinned Mathlib source installation is absent or incompatible, mark the reproduction gate `INCONCLUSIVE` and ask the owner rather than installing a second copy. A fresh project build against a shared verified Mathlib cache is not a build of Mathlib from source and must be described accurately.

## 4. Required adversarial gates

Use `PASS`, `FAIL` or `INCONCLUSIVE` for each gate and overall. A required uncompleted gate, byte mismatch, unresolved material mathematical defect or unexplained axiom forbids overall `PASS`. Cite raw evidence beside every conclusion.

| Gate | Independent obligation |
|---|---|
| E0 — identity | Recompute all input hashes, ZIP CRC and member hashes; check traversal, hidden payloads, freeze/configuration consistency and source immutability at the end. Distinguish the main ZIP, annex and historical v0.8. |
| E1 — claim semantics | Map Theorems A–C and every public corollary/byproduct to literal hypotheses, definitions and Lean declarations. Distinguish all orders/additive `b`, eventual sharp `M(n)`, eventual maximum, rooted defect `s`, integral stability, extremal rigidity, explicit tower threshold and the triangular-only annex. Test small orders, empty graphs and quantifier order. |
| E2 — independent mathematics | Reconstruct the gain/loss identity; mixed fractional LP and weight 2/5; Paper III nibble transfer and RC01's marked selection, codegrees, cleanup and parameter order; near-regime descent, root localization, physical host assignment, palette/width and budget ledger; branch coverage; all-orders induction; complete-split lower bound; rooted-defect induction and witnesses; stability/rigidity and the explicit bound's propagation. Identify any step known only through Lean or an imported paper and test whether the prose suffices for human review. |
| E3 — formal conformance | Compare every displayed manuscript theorem/quantitative corollary with its Lean type and import cone. Check exact edge-partition semantics, chordality, mixed versus unrestricted gain, coercions, strict inequalities, root predicates, threshold dependence and whether premises are discharged rather than passed as interfaces. Verify the 195 root export checks and separately identified supplementary targets; inspect the code and method provenance rather than inferring independence from namespace names. |
| E4 — Lean/trust boundary | Perform the isolated project rebuild under §3; inspect all 13 target exits, type/axiom queries, `sorryAx`, `sorry`, `admit`, `native_decide`, `@[implemented_by]`, unsafe escapes and project axioms. Verify that headline declarations use only subsets of `propext`, `Classical.choice`, `Quot.sound`, and that no mathematical premise is hidden in a type. Do not relabel the separate annex as part of the main build. |
| E5 — independent falsification | Write new exact-arithmetic scripts and counterexample searches for quantitative constants and edge accounting; stress both regimes and boundary cases. Include negative controls that must fail. A bounded test can refute a claim, but cannot prove a universal theorem. Re-examine the internal Certo certificate as exact cover, not as an unrecorded optimality certificate. |
| E6 — bilingual artifacts | Compare English/Spanish statements, qualifiers, numbers, captions, references and formal identifiers against MD, TeX and both PDFs. Render and inspect every PDF page after verifying the frozen hashes; record missing glyphs, clipping, stale audit-status language and any semantic divergence. Do not silently regenerate target PDFs. |
| E7 — citations and priority | Retrieve and verify the cited papers and the Erdős #81 record; compare the published solutions and Paper IV's two-regime mechanism, prior Papers I–III, Paper V material if cited, and upstream Lean contributions. Separate logical independence, code provenance, mathematical antecedents and bibliographic novelty. Search through the audit date and record sources, queries and coverage limits. |
| E8 — audit of the audit/package | Challenge internal G0–G8 and B01–B10, including timeouts and negative controls. Verify that the 19 part archives and the 2,480-entry general ZIP match their sidecars, and that reports, scripts, raw results and hashes correspond to the same cut. Check for obsolete assertions in repository documentation. |

In particular, attempt to falsify the asserted optimal quadratic and linear coefficients without confusing them with the unknown least additive constant. Do not report universal `b=0`, a universal linear mixed packing gap, a practical threshold, or a classification outside the stated graph class as proved. The improved B7 copy-cleanup term must not be presented as a full improved gate unless its profile/fibre link is also verified. Check that the `BoundedCliqueGap` annex asserts only its stated triangular/clique-restricted result.

### 4.1 Execution order — full build last

| Phase | Work | Exit condition |
|---|---|---|
| Intake | E0 and lightweight environment/pin checks only | Exact target identified; usable existing dependency installation |
| Substantive review | E7 attribution/version recheck, E1/E3 static claim/type inspection, then E2 independent mathematics including all seven F-02 items | No unresolved blocking finding; E3 dynamic checks explicitly reserved for E4 |
| Tests and presentation | E5 independent falsification, E6 bilingual artifacts, then E8 preliminary challenge of internal evidence | Pre-build checkpoint recorded; no blocking findings |
| Final reproduction | E4 isolated build and dynamic types/axioms/cones; finish E3 and E8, recheck E0 hashes, seal final reports | All required gates complete or an explicit FAIL/INCONCLUSIVE report |

Before E4 write `00_CONTROL/PREBUILD_CHECKPOINT.json`: target hashes,
completed obligations, reserved dynamic checks, findings, resolutions and
the decision `PROCEED_TO_BUILD` or `STOP`. Static E3 review is not yet an
overall E3 PASS. No unresolved blocker, including a material attribution
problem, permits `PROCEED_TO_BUILD`. The build is deferred, not optional.

### 4.2 Blockers, time limits and correction cycles

Record planned time/resource limits at intake. Do not silently extend them
to keep an incomplete run alive. Save gate evidence incrementally and seal
a checkpoint package after each phase; never accumulate the entire review
without a recoverable result.

- **Confirmed blocker:** stop new expensive work and the affected line of
  review. Examples include input/hash mismatch, false or materially
  unsupported mathematical statement, manuscript/Lean mismatch, unexplained
  mathematical axiom, or materially incorrect attribution/independence claim.
  Deliver a blocking finding with a reproducible witness or exact source
  locations. Mark the affected gate `FAIL`; retain completed supported
  verdicts and mark uncompleted gates `INCONCLUSIVE`. Overall is `FAIL` if
  a confirmed required-gate defect remains. Do not run the full build merely
  to finish the checklist after finding such a blocker.
- **Serious unresolved concern:** spend at most 30 minutes on a focused
  diagnostic check unless the owner authorizes more. If unresolved, stop
  with `INCONCLUSIVE` for the affected obligation; do not claim a proven
  error. Environment failure alone is not proof of mathematical falsity.
- **Minor issue:** record it and continue when it does not compromise
  mathematics, conformance, identity or material attribution. Distinguish
  typography from release-blocking misrepresentation.
- **Time/resource cutoff:** immediately preserve raw evidence and write
  `PARTIAL_REPORT.md`, `SUMMARY.json` and `FINDINGS.csv` with per-gate status.
  Seal the partial package and its hash. A brief reporting-only phase may
  generate the required PDF; if interrupted, explicitly mark that PDF as
  pending rather than delaying the partial report or fabricating completion.
  Preserve existing FAILs; a cutoff does not turn them into INCONCLUSIVE.

On a blocker, do not start repairs or overwrite the target. The author
decides the correction. A corrected target requires a **new run/revision ID
and hashes**, even if the public manuscript stays v1.0.1. Preserve the old
finding and package. On resumption rerun E0 and all affected checks; reuse
an unaffected result only with an explicit dependency/identity justification.
The final build must certify the final Lean cut. Never silently patch source
in the auditor's build tree and attribute its PASS to the original archive.

## 5. Evidence and report standard

The revised title and introduction put quantitative stability first. Give
special attention to Theorem 6.1's large-order and small-deficit hypotheses,
the constant 16, and Corollary 6.1a's quantifier order: one root precedes
**every** eligible partition, with nonnegative excess and no restriction
on piece order. Test the constant 48 against the retained account, not just
the abstract. Independently verify the comparison with [15, Theorem 1.3
and Corollary 5.5]; the text does not claim that stability is exclusive to
this work. Explicit thresholds are claimed to be ineffective in practice,
not small. The editorial report is evidence to challenge, not a verdict
the auditor should inherit.

Determine whether **Theorem C coincides in statement with a result of [15]
for fixed rooted defect**, and check that the manuscript's attribution in
§8.1 matches that finding. Compare the graph class and defect definition,
quantifiers, threshold dependence, bound, attainment and permitted piece
orders. Do not infer equivalence from similar notation, nor novelty from a
different proof or implementation.

Specifically trace the cutoff L through [15, Theorem 3.3, Lemma 3.4,
Theorem 1.3, Proposition 5.4 and Theorem 1.1]. Distinguish its separate
L=4 approximation (1.5) from the exact maximum. Test the corrected claim
of a piece-size strengthening without assuming that [15]'s method could
not be adapted. Proposition D.2 gives a uniform obstruction already at
s=0, not a minimality theorem separately for every positive s. Verify [21]
as an announcement of Cipollini's partial result, not an audited input.

Reference [15] is pinned to **arXiv:2609.20871v1**; [5] is pinned to commit
`cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. Record whether later public
versions exist **as of the actual audit date**, their identifiers and any
relevant changes. Compare §8 first against the cited versions, then state
whether it remains accurate against later versions. Do not silently replace
the cited snapshot; if a version cannot be accessed, record that limitation.

Create a new run under `02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.0.1_r3/` (use a new suffix if it exists); do not alter r2, the author-side run, v1.0 baseline or earlier public draft. Keep:

```text
00_CONTROL/       target hashes, auditor declaration, access log, environment, commands, gate plan, pre-build checkpoint
10_LOGS/          complete Lean, computation, literature and document logs
20_EVIDENCE/E0…E8/  own derivations, scripts, inputs, results, negatives, gate records
30_REPORT/        FINAL_AUDIT_REPORT.md/.tex/.pdf, SUMMARY.json, FINDINGS.csv
40_PACKAGE/       per-gate ZIPs, general ZIP, manifests and external SHA-256 sidecar
```

Each gate record must state obligation, exact input hashes, independent method, raw output, negative control or reason inapplicable, result and limitations. Supply a Markdown/PDF report and ZIP per tested gate, plus a consolidated Markdown/TeX/PDF report and ZIP. Markdown is the report's semantic source; compile the final PDF from the final TeX, inspect every page, then seal hashes and archives **last**. No empty evidence directories or copied internal PASS statements as a substitute for work. `SUMMARY.json` must include per-gate verdicts, findings by severity, target hashes, build status and independence limitations. `FINDINGS.csv` needs stable ID, severity, gate, location/claim, reproduction, evidence, impact and disposition. Preserve failures and timed-out experiments.

An existing TeX engine is available at
`C:/Users/jtraverso/.cache/e81-editorial-tools/tectonic/tectonic.exe`;
Pandoc is at
`C:/Users/jtraverso/.cache/e81-editorial-tools/pandoc/pandoc-3.11/pandoc.exe`.
Inspect and reuse those binaries/cached resources under the technical access
exception; do not install another engine. If a required package is unavailable,
report that limitation. Do not relabel the r2 report PDF as TeX-compiled.

Also record the handoff revision, read-scope exceptions/exposure, actual
reference versions, stop reason if any, and the status of dynamic checks
deferred to E4. A resumed run must identify the previous run and every
carried-forward result; keep author responses separate from auditor findings.

The final report must state separately: mathematical rederivation; manuscript/Lean semantic match; isolated project build against a shared dependency cache; axiom footprint; bilingual PDF QA; source/provenance review; and literature scope. If only some gates finish, deliver a scoped `INCONCLUSIVE` or `FAIL` report, not a nominally complete PASS. This AI audit is not human peer review, a proof of universal novelty or authorization to release.
