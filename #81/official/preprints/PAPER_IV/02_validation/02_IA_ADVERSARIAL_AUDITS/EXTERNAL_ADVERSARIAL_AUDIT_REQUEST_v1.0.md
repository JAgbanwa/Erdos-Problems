# External AI adversarial audit request — Paper IV v1.0 candidate

**Request status:** prepared, not executed. **Audit class:** external AI adversarial review on the author's Windows machine. **Target:** source cut `piv-v1.0-f1769273dd2c` and the six corresponding English/Spanish v1.0 manuscript files. This request neither certifies the paper nor authorizes publication.

## 1. Mandate and independence

Try to invalidate the mathematical statements, the manuscript-to-Lean correspondence, the formal trust boundary, the quantitative accounts and the release evidence. Reconstruct proof-critical arguments independently; do not turn the author's internal `PASS_INTERNAL_AUTHOR_SIDE` into an external verdict by rerunning its scripts. Treat the internal audit as an attack map and as evidence to challenge, not as an authority. Preserve failed tests and contrary evidence.

Do not edit the target, silently repair a proof, replace a frozen source, push to GitHub or submit a PR. Work in a separate audit directory. Disclose the auditor's model, operator, tools, access to prior discussions and any assistance from the author's scripts. Because the auditor uses the **same computer and dependency cache**, this is not a separate-machine or dependency-clean-room reproduction; independence must be demonstrated for the project build, mathematical reasoning and tests.

## 2. Exact input cut

All paths below are relative to `preprints/PAPER_IV/`. Verify hashes *before* reading the internal verdict. A mismatch is an intake failure, not a reason to substitute a newer working tree.

| Artifact | Path | SHA-256 |
|---|---|---|
| Main Lean source ZIP | `05_formalization/LEAN_SOURCE_SNAPSHOT_v1.0.zip` | `0a13c01cc4cf0198d5d138082d45b25df4c5ac0684c0ed85e7cc758575f8a7dd` |
| Distinct triangular-gap annex ZIP | `05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` | `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d` |
| English Markdown / TeX / PDF | `01_manuscript/v1.0_candidate/PAPER_IV_preprint_v1.0_en.{md,tex,pdf}` | `af7aa303405f554f25d14774bbba3ed115746c17452beb837860c0692777d23b` / `22571d4914488243b55d3053d3b20f18df0f95fb7d95a3203d8a0a742633c89f` / `52ba66cc66dd6be49bd9f8790ea6b69a8d5022e6aea4912acd45712f30db54cc` |
| Spanish Markdown / TeX / PDF | `01_manuscript/v1.0_candidate/PAPER_IV_preprint_v1.0_es.{md,tex,pdf}` | `35a578303030992801f3086e9d1927f3d44a37e28676b706f1420503335434ac` / `85be67e80d1b02aed5d5abfd7162ac432bb677d0e42d776de0d9a14e914540d7` / `af9e419db35299dda0f6fe2dbbfd663ee6fe623dc3bc6d360e45d29c9e98513f` |
| Author-side internal-audit ZIP | `02_validation/01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/30_PACKAGE/INTERNAL_AUDIT_piv-v1.0-f1769273dd2c.zip` | `1911f29e1072accfe8df4fbec0a3b02d1cd9ef274a06bd1957f9b61034301847` |

The main source archive has 504 Lean files plus four configuration/build files. Its 13 recorded targets are listed literally in `03_reproducibility/build_v1.0_20260927/RUN_META.json`; the 195 `#check` commands are in the frozen `ReleaseExportCheck.lean`, with their build result under `modules/ReleaseExportCheck.log`. The recorded run is 504/504 PASS with exit code zero. These are **author-run facts to verify**, not the external build result. `05_formalization/LEAN_FREEZE_v1.0.md`, the internal `00_CONTROL/TARGET.json`, `CLAIM_MAP.csv`, `G1_CLAIMS/PUBLIC_HEADERS.md` and `10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md` identify the cut and claims. The triangular-gap annex has a separate historical 579-module build record and is **not** part of the main `PaperIV` import closure. The public v0.8 draft and other working trees are not audit substitutes.

The manuscript's front-matter audit-status sentence was fixed before completion of the later internal audit. The auditor should distinguish that time-stamped statement from the current dossier and report whether release-facing synchronization is needed. Do not modify the manuscript during this audit.

## 3. Same-machine Mathlib rule — mandatory

**Do not install or clone another Mathlib.** Reuse the existing source tree on this computer, possibly through a junction/link, and record its resolved path. Verify every dependency HEAD against the frozen `lake-manifest.json`; do not change the pinned manifest with `lake update`. Existing compiled dependency artifacts may be reused. If a missing official binary-cache artifact must be fetched into the *same* verified dependency installation, record precisely what was fetched and confirm that no second Mathlib source tree was created. The recorded Lean toolchain is `leanprover/lean4:v4.28.0`; Mathlib is pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

`RUN_META.json` records the existing dependency path under `C:/Users/jtraverso/e81p4/preprints/PAPER_IV/05_formalization/lean/.lake/packages/mathlib`. Treat this as a location to inspect on this machine, not as a substitute for resolving the link and checking the manifest commit at audit time.

For a genuinely fresh **Paper IV project** rebuild, extract the source ZIP into a short isolated directory; its project `.lake/build` must initially be absent or empty. Reuse only verified *dependency* artifacts, never author-built Paper IV `.olean`/`.ilean` files. Record the junction, source and package hashes, version output, commands, exit codes, timings and complete logs. Run at most one heavy build at a time; inspect existing work before starting and do not stop another team's process. Run the 13 targets separately or with an explicitly logged command that covers all of them, then test the public declarations and axiom queries. The root `PaperIV` alone does not imply that every supplementary target was imported.

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

## 5. Evidence and report standard

Create a new run under `02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.0/`; do not alter the author-side run or earlier public draft. Keep:

```text
00_CONTROL/       target hashes, auditor declaration, environment, commands, gate plan
10_LOGS/          complete Lean, computation, literature and document logs
20_EVIDENCE/E0…E8/  own derivations, scripts, inputs, results, negatives, gate records
30_REPORT/        FINAL_AUDIT_REPORT.md/.tex/.pdf, SUMMARY.json, FINDINGS.csv
40_PACKAGE/       per-gate ZIPs, general ZIP, manifests and external SHA-256 sidecar
```

Each gate record must state obligation, exact input hashes, independent method, raw output, negative control or reason inapplicable, result and limitations. Supply a Markdown/PDF report and ZIP per tested gate, plus a consolidated Markdown/TeX/PDF report and ZIP. Markdown is the report's semantic source; compile the final PDF from the final TeX, inspect every page, then seal hashes and archives **last**. No empty evidence directories or copied internal PASS statements as a substitute for work. `SUMMARY.json` must include per-gate verdicts, findings by severity, target hashes, build status and independence limitations. `FINDINGS.csv` needs stable ID, severity, gate, location/claim, reproduction, evidence, impact and disposition. Preserve failures and timed-out experiments.

The final report must state separately: mathematical rederivation; manuscript/Lean semantic match; isolated project build against a shared dependency cache; axiom footprint; bilingual PDF QA; source/provenance review; and literature scope. If only some gates finish, deliver a scoped `INCONCLUSIVE` or `FAIL` report, not a nominally complete PASS. This AI audit is not human peer review, a proof of universal novelty or authorization to release.
