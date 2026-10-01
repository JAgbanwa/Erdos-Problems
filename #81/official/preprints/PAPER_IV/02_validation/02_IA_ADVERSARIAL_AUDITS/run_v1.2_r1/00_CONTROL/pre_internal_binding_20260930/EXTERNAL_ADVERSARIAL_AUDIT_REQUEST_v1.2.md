# External adversarial audit of Paper IV v1.2

**Preparation status: BLOCKED_PENDING_INTERNAL_AUDIT. Not started.**
This is the mandate for a new review of the v1.2 manuscripts and their selected
Lean source cut. It does not authorize starting that review now. The final
manuscript seal and complete author-build evidence are now bound in
`AUDIT_TARGET_v1.2.json`; the renewed internal audit must still be completed
and bound before execution. Never substitute the v1.0.1 inputs or
the earlier v1.2 manuscript ZIP to fill a missing field.

Prepared on 29 September 2026. Handoff revision: **v1.2-r1**. Manuscript version:
**1.2**. The run's actual start date must be recorded when it starts, not inferred
from this preparation date. This request does not authorize publication.

## 1 Purpose and independence

Attempt to invalidate the statements, quantitative estimates, proof dependencies,
manuscript-to-Lean correspondence, attribution and reproducibility claims.
Reconstruct the critical mathematics independently. Do not convert an author's
successful build or internal verdict into an external PASS merely by repeating
the author's scripts. Preserve failures and contrary evidence.

Use a fresh session, preferably a different model family from those involved in
proof development, Aristotle formalization and editorial review. Declare model,
provider/version when known, operator, prior participation, memory/context,
exposure to earlier discussions and use of author scripts before starting.
A fresh session of the same family is not cross-family independence. Disclose
overlap without claiming a stronger separation than actually exists.

This review runs on the author's machine with shared pinned dependency caches.
It is neither separate-machine reproduction nor a clean-room Mathlib build.
Do not send files to other services, create external jobs, publish, push, tag,
deposit, repair the proofs or modify any audit target. Further external services
require separate owner authorization.

## 2 Readiness and exact inputs

All relative paths in this mandate are relative to
`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/` unless stated otherwise.
The companion target and reading-scope files are in this mandate's directory.

Before substantive review, require all of the following:

1. The owner has requested execution of this new external cycle.
2. `AUDIT_TARGET_v1.2.json` says `READY_FOR_EXTERNAL_AUDIT`, with no unresolved
   mandatory binding, and identifies the final six manuscript files, figures,
   source ZIP/manifest, author-build evidence and new internal-audit package.
3. The full project reconstruction has a validated final result. Interrupted
   progress markers alone never meet this condition.
4. The manuscripts have been updated to that actual evidence, regenerated,
   visually reviewed and sealed after their last change.
5. The renewed v1.2 internal audit is complete and has no unresolved blocker.
   Its verdict is an intake prerequisite, not an external conclusion to inherit.

If any condition is missing, record `NOT_STARTED` and request the missing input.
Do not begin the substantive review or launch Lean. Do not invent hashes or
copy hashes from a prior revision. A readiness check is not an E0 PASS.

The selected source content is currently **piv-v12-fb459343d234**:

- Source directory: `05_formalization/lean_piv-v12-fb459343d234/`.
- Source ZIP: `05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip`.
- Source manifest: `03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json`.
- Recorded manifest SHA-256:
  `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`.
- Recorded ZIP SHA-256:
  `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6`.
- Expected scope: **607 own Lean modules**, **615 source/configuration/documentation
  entries**, **19 selected targets** and **224 export checks**. Recompute these;
  target counts are not distinct-theorem counts or axiom-record counts.

The sealed manuscript directory is
`01_manuscript/v1.2_full_rebuild_candidate/`, identified as
**piv-v12-manuscripts-2451d43bface**. Its manifest SHA-256 is
`2451d43bfacee76791a10bcd115100d6a7dfa68e4e3bda9de62032179151f8be`;
the source/figure/report manuscript ZIP SHA-256 is
`422b0be34cfec130eaece95d077975d4e01d7e3d4501461b8db64931e0d2e663`.
The target record binds its manifest, detached freeze record, ZIP and six
MD/TeX/PDF files. The final PDFs have 68 English and 69 Spanish pages; verify
these counts independently. A later changed file is not part of this identity.

The earlier `01_manuscript/v1.2_candidate/` and its sealed ZIP remain historical.
The v1.0.1 r2 external FAIL also remains historical; its findings must not be
erased or reported as resolved solely because a later manuscript exists.

Appendix G.1 still invokes the distinct `BoundedCliqueGap` source annex:
`05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip`, SHA-256
`2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d`.
Its versioned filename does not make it part of the 607-module main cut. Bind
its own reproduction inputs and inspect the `chordal_gap_linear_cliqueFree`
statement and axiom footprint separately. E4 must reproduce this claimed
supplement too, serially after the main build; if its declared inputs are
insufficient, report INCONCLUSIVE rather than silently merging working trees.

The annex has no standalone Lake configuration. Reproduce it by overlaying its
38 BoundedCliqueGap source files onto a fresh extraction of the historical
`05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip`, SHA-256
`0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd`.
That archive's lakefile declares the BoundedCliqueGap library. Use the bound
annex README and source manifest, verify the pinned configuration, and run
`lake build BoundedCliqueGap.AxiomCheck` in this separate auditor-owned project,
serially after the main build. This historical base is authorized solely for
annex reproduction; it is not a replacement for the v1.2 main source cut.
Reuse the existing pinned third-party cache, never either author's project objects.

### 2.1 Source identity and resumed reconstruction

Source hashes identify source bytes, not an uninterrupted execution. Evidence
hashes identify logs and provenance; a package hash also changes when those
records or the manuscripts change. Keep these three identities separate.

The fresh author reconstruction began with no project objects. The PC restarted
after 422 modules had completed. Its first-segment evidence is
`03_reproducibility/full_rebuild_v12_20260929_r2/`. Recovery evidence and the
second segment are in `03_reproducibility/full_rebuild_v12_20260929_resume/`.
`03_reproducibility/REBOOT_RECOVERY_v12_20260929.md` describes the protocol.

The reconstruction completed with 421 first-segment objects verified and reused
and 186 modules compiled after resumption, covering 607 distinct modules. One
first-segment completion was reexecuted as a final target. All 19 targets ran
freshly in the second segment, which reports 461 permitted-axiom records.
Recount those records; they are not distinct theorems. The evidence manifest,
seal and archive in `03_reproducibility/full_rebuild_v12_20260929_seal/` bind the
1238 evidence files. Their hashes are in the target record. The author's
validation is not an external or internal audit verdict.

Require the final `FULL_REBUILD_VALIDATION.json` and
`COMBINED_FRESH_PROVENANCE.json`, not just `RECOVERY_CHECK.json`. Independently
check that every reused object maps to a successful fresh compilation in the
first segment with the same source, direct dependencies, options and toolchain;
that all other modules have successful second-segment records; and that the
19 audit targets were executed in the final segment. Check complete logs and
exit codes, current hashes and preservation of the interrupted evidence.

Do not say the resumed run alone compiled all 607 modules afresh. Do not reject
a valid two-segment reconstruction solely because its second segment reports
verified cache reuse. These author records still do not replace the auditor's
own isolated project build in E4.

## 3 Reading boundary and existing tools

Follow `LOCAL_INPUT_SCOPE_v1.2.json`. It is an operational reading restriction,
not an OS-enforced sandbox. Read only declared target files, technical
dependencies, public literature and your own audit outputs. The entire machine
or research repository is not an input. Do not search `ar_*`, `handoff_*`, other
Aristotle projects, unpublished Paper V/B=0 work, development chats, credentials
or `.env` files. Do not import a proof from a newer working tree.

Maintain `00_CONTROL/INPUT_ACCESS_LOG.csv`: path/URL, version/hash, purpose,
phase, access time and authorization basis. Deterministic source batches may
use a retained file-list manifest. Record runtime/dependency access by resolved
root and pinned version. Additional local research material requires approval
before reading; record accidental exposure and stop if it materially biases
the review. Public prior-art search is allowed and must not be restricted to
papers already cited by the author.

At intake, hashes and technical build metadata may be read. Defer author
internal verdicts, derivations, computational conclusions and editorial review
reports until independent first-pass findings for E1/E3, E7, E2, E5 and E6 are
saved. The previous r2 external findings are explicitly allowed intake inputs;
declare this exposure. Any author PASS text already encountered is disclosure,
not independent evidence. Read the new internal report only in E8.

**Do not install or clone another Mathlib, change dependency pins, run
`lake update`, delete shared caches or stop another team's processes.**
Reuse the verified installed packages at
`C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages/`.
Resolve any junction and verify every dependency HEAD against the frozen
`lake-manifest.json`. Lean is pinned to `leanprover/lean4:v4.28.0`; the selected
Mathlib revision is `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Validate, do not
assume, these values. If required dependencies are unavailable, report the
limitation and request direction; do not download another installation.

Reuse existing document tools if reports need them:
`C:/Users/jtraverso/.cache/e81-editorial-tools/tectonic/tectonic.exe` and
`C:/Users/jtraverso/.cache/e81-editorial-tools/pandoc/pandoc-3.11/pandoc.exe`.
Do not install another TeX engine. Read-only inspection of their configuration,
binaries and runtime libraries is permitted. A fallback PDF must disclose how
it was generated; do not claim it was compiled from TeX if it was not.

## 4 Required gates and order

Use `PASS`, `FAIL` or `INCONCLUSIVE` for each gate and the overall verdict.
An unresolved required gate prevents overall PASS. Distinguish a confirmed
defect from an inability to finish the check.

| Gate | Required independent work |
|---|---|
| E0 Identity | Verify all bound hashes, ZIP CRC/member identities, safe paths and source/configuration consistency; recheck immutability at the end. Separate source identity, two-segment author-build evidence and final manuscript identity. |
| E1 Claims | Map Theorems A, B, C and C′ and every quantitative corollary/byproduct to literal definitions and hypotheses. Distinguish all-order additive bounds, eventual exact maxima, fixed-defect and uniform-in-defect statements, sublinear sequences, unrestricted partitions and actual versus optimally resized roots. |
| E2 Mathematics | Independently reconstruct the fractional gain accounts, RC01, marked selection, physical compatibility, local constructor and branch coverage; retained same-root accounts, defect extensions, E34/E35, square-root obstruction and threshold propagation. Complete the itemized checks in §5. State which steps are rederived, imported with attribution or still only formally inspected. |
| E3 Conformance | Compare every public statement with its actual Lean type, assumptions and dependency cone. Check exact edge coverage, capacities, gains, chordality/rooted defect, coercions, quantifier order and discharged interfaces. Verify all 224 exports and the exact 19-target scope. Namespaces do not prove originality or absence of relocated code. |
| E4 Formal reproduction | After the pre-build checkpoint, compile the isolated source project with no author project objects. Reuse only pinned third-party artifacts. Check every selected target, complete logs/exit codes and types/axioms; inspect `sorryAx`, `sorry`, `admit`, mathematical axioms and executable/unsafe escape mechanisms. Only subsets of `propext`, `Classical.choice`, `Quot.sound` are allowed in the public theorem footprints. |
| E5 Falsification | Write independent exact-arithmetic tests and boundary/counterexample searches for the stated constants, branches, small orders and resource accounting. Include corrupt/negative controls. Audit any Certo certificate by its actual specification; feasibility is not optimality, finite tests are not universal proofs. |
| E6 Bilingual artifacts | Compare final English/Spanish MD, TeX and PDF for all statements, qualifiers, numbers, captions, references and identifiers. Render and inspect all final PDF pages; check the Figure 2 reference, prime notation, line breaks and evidence/status text. Do not regenerate or repair target PDFs. |
| E7 Attribution | Verify the cited snapshots and later public versions as of the actual audit date. Compare [5], [15], [22], [23], the earlier series and cited contributions. Distinguish statement inclusion, method adaptation, code provenance, formal dependency and novelty. Complete §6. |
| E8 Internal evidence and packaging | After recording independent first-pass conclusions, challenge the new v1.2 internal reports, scripts, certificates, negatives, timeouts and archives. Check that all evidence belongs to the final cut. Recompute inventory/part counts instead of importing the v1.0 counts. |

Recommended execution order:

1. Readiness, E0 and lightweight environment checks. No implicit Lean builds.
2. E7, E1/static E3, then E2.
3. E5, E6 and preliminary E8, after the independent-pass restriction is met.
4. Record `00_CONTROL/PREBUILD_CHECKPOINT.json` with exact target hashes,
   completed checks, unresolved issues and `PROCEED_TO_BUILD` or `STOP`.
5. Only with no blocker: E4; finish dynamic E3/E8, recheck E0 and seal reports.

The external full build remains last, not optional. Do not start it merely
because the author build passed. Inspect current machine load first; use one
heavy process at a time. Build a separate project under the run's own build
directory, with no author `.olean`/`.ilean` files. Record the actual compiler
commands and verify that any reused author runner passes the intended options
and covers the source/import graph. `lake build PaperIV` alone is not evidence
that all 19 compatible audit closures were executed.

An auditor build interrupted by a reboot may resume only from its own verified
records, preserving both segments and revalidating source/object/dependency
hashes and options. Never silently switch to author-built objects.

## 5 Mathematical obligations specific to v1.2

### 5.1 Retained accounts and public extensions

- **E.4, block by block:** compare `StrictParams`, `StrictBudget`,
  `ResidualExcess`, `CoreCliqueAlternative`, `LargeCliqueCore`, `TemplateDistance`
  and `RootPartition`. Track the same witnesses and resources across combined
  inequalities. Test fixed-s thresholds, deficit windows and strict cases.
- **F.3a:** locate `exists_clique_additive_defect` and compare its precise graph,
  clique, edit and defect assumptions. Do not replace clique recovery with a
  weaker induced-subgraph or template assertion.
- **F.5:** review `l11_caseA`, `l11_caseB1`, `l11_caseB2` individually, their
  case conditions, exhaustiveness and common conclusion. Check the adaptations
  from [22], not merely the existence of similarly named lemmas.
- Check Theorem C′'s one-root quantifier before all eligible unrestricted
  partitions, exact defect-dependent constants, and the difference between
  linear edit bounds to an actual-root comparator and the extra square-root
  cost of resizing. Reconstruct Proposition 6.3a's obstruction and quantifiers.
- Check uniform fractional bounds including the stated small orders, the
  arbitrary-order sublinear sequence theorem, and E35's uniform range. Never
  substitute a growing parameter into a theorem valid only for each fixed s.
- Trace the selected public Theorem C through `PaperIV.DefectExplicitPublication`,
  `E34.L11Main` and `E35.Theorem`; check `ExplicitFixedStability` (namespace
  `PaperIV.SublinearResearch.FixedExplicit`) and `PaperIV.OptimalTemplateObstruction`.
  Verify the claimed exclusion of Alon–Shapira on the specified public cones,
  not on the entire repository. Historical alternatives may remain present.
- Check B7's full cleanup-to-realization link, tower propagation and any inverse
  threshold hypotheses. An explicit threshold is not necessarily useful in
  practice. Separate the two `gainOf` conventions where piece order is unrestricted.

### 5.2 Exposition checks for Appendix A.2

Produce a row for each of the following, with its manuscript location, literal
Lean declarations, independent derivation attempted, evidence and explanation:

| Item | Derivation |
|---|---|
| A2-1 | Regularization mass, degree, palette and width estimates |
| A2-2 | Discard counts and retention under the partition conventions |
| A2-3 | Fibre lower bounds and normalization |
| A2-4 | Nibble constants and tower-iteration domination |
| A2-5 | Normalization preceding the terminal construction |
| A2-6 | Terminal estimates and the three-case budget |
| A2-7 | Bose/Skolem frame constructions behind the residue table |

Give each an exposition verdict `ACCEPTABLE_SUMMARY`, `REQUIRES_EXPANSION` or
`INCONCLUSIVE`, separately from formal correctness. State why an omitted
derivation is or is not adequate for a human referee. Neither disclosure of
the omission nor a successful build settles that judgment. A missing essential
argument may block release even without a counterexample to the theorem.

## 6 Attribution and previous findings

The v1.0.1 r2 audit reported an attribution blocker concerning Theorem C and
[15, Theorem 1.1], and left seven prose-coverage items unresolved. Inspect those
findings as prior issues, not as verdicts for v1.2. Independently verify the
new attribution and expanded proofs. Do not copy the old claim map: v1.2 has
new fixed-defect stability and uniform/sublinear results.

Compare Theorem C to [15, Theorem 1.1] component by component: graph class and
rooted defect, target, quantifiers, all-order/eventual scope, attainment,
extremal classification, witness family and piece-size bound. Trace the actual
role of the clique cutoff in [15]; do not assume an order-four strengthening
solely from a difference in notation, or assert that the other proof cannot
be adapted. State exactly what the current paper proves about classification
and what it does not. Check the scope of the order-three obstruction.

Compare C′ and the sublinear results with [15, Theorem 1.3 and Corollary 5.5],
including fixed versus growing defect and quantitative versus asymptotic claims.
Inspect the attribution of the star-dual method to [15, Lemma 3.1], and the
chordal-removal argument to de Joannis de Verclos [22]. Check that the historical
use of Alon–Shapira [23] is not confused with the selected explicit proof.
An independently compiled implementation is not evidence of methodological
or bibliographic originality. Check the antecedent roles of Papers I–III,
the Cipollini partial announcement, [5], and any code moved between namespaces.

The manuscript pins [15] to arXiv:2609.20871v1 and [22] to arXiv:1902.06135v1.
Record the exact snapshot of [5] cited by the final target as well. Verify each
comparison first against its cited version, then record whether later public
versions exist on the actual audit date and whether they affect the comparison.
Save source versions, URLs, access dates, hashes, search queries and coverage
limits. Do not silently replace the cited text or claim a complete novelty search.

No review may report universal b=0, a universal linear mixed packing gap,
unqualified superiority over another work or a small effective threshold
unless it is literally proved by the bound target.

## 7 Stopping rules

Record time/resource limits before starting. Save gate evidence incrementally.

- A confirmed blocker stops the affected review and new expensive work. Report
  the exact witness or source location; mark its gate FAIL, retain supported
  completed results and mark unfinished gates INCONCLUSIVE. Do not run E4 just
  to complete a checklist after a mathematical, attribution or identity blocker.
- A serious unresolved concern gets at most 30 minutes of focused diagnosis
  without further owner authorization. If still unresolved, report INCONCLUSIVE,
  not a fabricated counterexample or PASS.
- Minor issues may be recorded while review continues if they do not undermine
  mathematics, semantic correspondence, identity or material attribution.
- A time limit or interruption requires an immediate partial Markdown report,
  SUMMARY.json and FINDINGS.csv, with per-gate status and preserved raw evidence.
  Seal a partial archive. Record any pending PDF honestly; do not delay all
  reporting because typesetting or the build is unfinished.

Do not repair targets. The author decides corrections; corrected bytes require
a new target binding/revision and rerunning E0 plus every affected gate. Never
overwrite the r2 findings or silently transfer PASS between differing files.

## 8 Result directory and deliverables

The reserved result directory for this cycle is:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/`

It contains preparation controls only until execution is authorized and the
readiness conditions pass. Do not label that reservation as a started review.
Use the following layout, adding evidence directories when they are actually used:

```text
00_CONTROL/       bound target, declaration, access log, environment, plan, checkpoints
05_BUILD/         auditor's isolated source/project objects; shared dependency link
10_LOGS/          complete build, calculation, literature and document logs
20_EVIDENCE/E0...E8/  gate scripts, inputs, outputs, certificates and negative controls
30_REPORT/        per-gate reports; FINAL_AUDIT_REPORT.md/.tex/.pdf; SUMMARY.json; FINDINGS.csv
40_PACKAGE/       per-gate ZIPs; final/partial ZIP; manifests and detached SHA-256
```

Do not include `05_BUILD` compiled caches, linked Mathlib, credentials or runtime
installations in the report ZIPs. Include original scripts, relevant input
identities, raw results and evidence necessary to reproduce each test. Preserve
all failed tests. Each tested gate needs a Markdown/PDF report and ZIP; supply
also a consolidated Markdown/TeX/PDF report and ZIP. Inspect the report PDFs,
then generate final hashes and archives after the last packaged edit.

`SUMMARY.json` must distinguish mathematical rederivation, conformance, isolated
project build with shared dependencies, axiom footprint, bilingual QA,
attribution, independence limitations, input identities and uncompleted gates.
`FINDINGS.csv` needs stable ID, gate, severity, claim/location, evidence,
reproduction, impact and disposition. An empty directory is not evidence.

A final PASS requires all required obligations, not only successful Lean
compilation. This AI audit is not human peer review, a proof of universal novelty
or permission to publish. Send the report to the owner for the release decision.
