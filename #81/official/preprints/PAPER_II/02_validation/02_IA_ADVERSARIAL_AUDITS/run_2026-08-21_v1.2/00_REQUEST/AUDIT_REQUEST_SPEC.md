# External AI Adversarial Audit Instructions — Papers I, II and III

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`  
**Protocol date:** 2026-08-21  
**Audit target revision:** corrected and internally sealed `preprint_draft_v1.2` packages  
**Supersession rule:** this protocol replaces v1.0 only for new v1.2 audit runs; it does not rewrite earlier audit records  
**Repository:** `jtraverso/erdos-81-chordal-clique-partitions`  
**Targets:** the active `preprint_draft_v1.2` packages of Papers I, II and III  
**Audit class:** external, adversarial and independently reproduced  
**Normative status:** this file is the single source of truth for the three audits

## 1. Purpose and boundary

These instructions define the external AI adversarial audit of three unpublished
preprint-draft packages. The auditor must try to falsify, not merely summarize,
the mathematical, formal, bibliographic, editorial and packaging claims of each
paper. Each paper receives a separate verdict and evidence package. A final
cross-paper check is performed only after all three individual audits are complete.

This audit is materially different from the author-side internal audit:

- the internal audit reviewed the recorded local build; this external audit must
  reproduce the Lean development in a clean environment;
- the internal audit used author-side tests as evidence; this external audit must
  design and execute independent tests before consulting those tests in detail;
- the internal literature review was preliminary; this external audit must perform
  a current, specialist prior-art and novelty search;
- this audit does not replace anonymous human peer review, specialist confirmation
  of novelty, or the final release decision.

The auditor must not edit the manuscripts, Lean sources, figures, internal-audit
records or package metadata. A defect is reported as a finding. If the owner issues
a corrected target, it is a new immutable audit target and requires a new audit run;
evidence from different target hashes must never be merged into one `PASS`.

## 2. Audit targets and source of truth

All paths in this protocol are relative to the repository root. The only normative
targets are the exact v1.2 contents received and frozen at Gate G0. The later audit-output
subtree is not part of the input target and must never be included in its target hash:

| Paper | Active package | Canonical English semantic source |
|---|---|---|
| I | `preprints/PAPER_I/active/preprint_draft_v1.2/` | `01_manuscript/PAPER_I_preprint_draft_v1.2.md` |
| II | `preprints/PAPER_II/active/preprint_draft_v1.2/` | `01_manuscript/PAPER_II_preprint_draft_v1.2.md` |
| III | `preprints/PAPER_III/active/preprint_draft_v1.2/` | `01_manuscript/PAPER_III_preprint_draft_v1.2.md` |

The following anchor hashes must match before substantive work begins:

| Paper | English Markdown SHA-256 | Frozen Lean archive SHA-256 | Sealed internal-audit ZIP SHA-256 |
|---|---|---|---|
| I | `da7e48196a03a8698a9c5a503976b43780cb9e5309558f1b7d3e06b4af35ee9e` | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` | `34d41bb9fec6fdc1adb6e544d7f5974438c7453ef7f7eb217f857489987d32e6` |
| II | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` | `e6f625486db867582da72fff9e71fa0f600dcce40e43ef885ce01756282b24e2` |
| III | `d4ca630d0966928b5b4d71ba6afcd34043fc33507757e8a817e3f42f245c80a1` | `9bff12f0c8279ae4485de960c01be322a423d8fd2f17592ebb7327b2c890fcb8` | `a5963462cf5c06283420135dcd6925a89e98a487e0b60890ff491a2b4079ccf2` |

For every paper, the target includes the complete active package: manuscript
artifacts, figures, validation material, formalization freeze, release metadata and
integrity files. Folders under `superseded/` are historical records only. They may
be consulted for version-history questions but must not supply missing premises,
proofs, declarations or evidence for the active target.

The authoritative manuscript chain is:

1. English Markdown semantic source;
2. English LaTeX derived from that source;
3. English PDF compiled from that LaTeX;
4. human-produced Spanish Markdown translation;
5. Spanish LaTeX derived from the Spanish Markdown;
6. Spanish PDF compiled from the Spanish LaTeX.

The auditor must not treat a PDF as the semantic source or infer that similarly
named files are identical without hashing and comparison.

### 2.1 Required execution order

Run and seal the audits sequentially: Paper I, then Paper II, then Paper III. Do not
reuse a verdict, unverified lemma or mutable result directory from an earlier paper.
After the Paper III package is sealed, run the cross-paper consistency check in
Section 10. This order follows the logical series while preserving three independent
paper-level verdicts.

## 3. Independence requirements

### 3.1 Minimum independent configuration

The audit must use at least two isolated reasoning contexts:

- **Primary auditor:** performs the claim map, analytic rederivation, formal
  reproduction, computational attacks and literature review.
- **Adversarial challenger:** receives the immutable target and this protocol, but
  not the primary auditor's conclusions until it has produced its own attack plan,
  kill switches and preliminary findings.

The two contexts may use the same model family only if this limitation is disclosed.
A different provider or model family is preferable. If the same operator launches
both contexts, that fact must be recorded; “external” then describes separation from
the authoring workflow, not independent human peer review.

### 3.2 Required disclosure

`00_REQUEST/AUDITOR_DECLARATION.md` must record:

- auditor/operator name or stable pseudonym;
- organization, if any;
- AI provider, model name, exact model/version identifier where exposed, service
  date and reasoning configuration;
- task or session identifiers where exposed;
- operating system, CPU architecture and available memory;
- all material tools and versions: Lean, Elan, Lake, Git, Python, solvers, TeX,
  Poppler and PDF validators;
- audit start/end timestamps and timezone;
- whether the auditor had prior involvement with the project;
- whether internal reports were hidden during the independent first pass;
- conflicts of interest, limitations and any unavailable capability;
- the SHA-256 of this protocol and the frozen inputs received.

### 3.3 Clean-room rules

- Extract each Lean archive into a new, empty directory outside the repository. On Windows,
  prefer short roots such as `C:\erdos_audit\P1`; record any `core.longpaths` setting.
- Do not copy or inherit `.lake`, build caches, compiled `.olean` files or author
  result directories from the active package.
- A network dependency cache may be used only if its use is disclosed; it must not
  contain compiled project modules.
- Run the pinned toolchain and dependency revisions from the received package.
- Write independent adversarial scripts from the definitions and claims. Internal
  scripts may be inspected only after the first independent test pass and must be
  labelled `AUTHOR_SIDE_COMPARISON`, never primary independent evidence.
- Record every random seed. Deterministic enumeration is preferred where feasible.
- Preserve failed attempts and counterexample searches, including failures caused
  by environment or import-closure defects.

## 4. Intake freeze: mandatory before analysis

No substantive audit work may begin until Gate G0 has frozen the received target.
For each paper:

1. copy this protocol into `00_REQUEST/AUDIT_REQUEST_SPEC.md` without editing it;
2. inventory every received file with relative path, byte count and SHA-256;
3. verify all supplied SHA-256 sidecars and manifests;
4. record the repository commit and working-tree state, if a Git checkout was
   supplied;
5. record the exact manuscript, figure and Lean-archive hashes;
6. verify that no target path resolves into `superseded/`;
7. seal `INPUT_FREEZE_MANIFEST.sha256` before opening the internal verdicts;
8. create a read-only copy or content-addressed snapshot used for the audit;
9. reject any unexpected zero-byte file and explicitly scan for the historical stray filename `$o`;
10. verify the six-entry manuscript sidecar with a standard cross-platform checker and confirm LF-safe parsing.

Any target mutation after this step invalidates the run. A missing, ambiguous or
contradictory version identifier is a `BLOCKER` until the owner supplies a new,
unambiguous frozen target. The auditor may report metadata inconsistencies but may
not silently repair them. Audit results must be written only to the run directory
specified in Section 7, after the input snapshot has been sealed; they are outputs,
not retroactive members of the audited input.

### 4.1 Mandatory corrective regression controls

The v1.2 intake must independently establish all of the following; an auditor may not
carry forward a prior conclusion:

- every Lean archive name and SHA-256 printed in each manuscript exists in the received
  package and matches the delivered archive byte for byte;
- Paper I's axiom gate directly queries `PaperI.assembly_sharp` and
  `PaperI.Split.residual_duality`, in addition to both headline theorem surfaces;
- Paper I's tightness discussion is tested at `(p,q,s)=(2,4,2)` and distinguishes
  the `s=2, o=0` equality case from the positive-slack `o>=1` boundary;
- Paper II contains no stale `v1.0.1`, nonexistent freeze filename/hash, nonexistent
  gate-log path, or mislabeled formalization table; its manuscript must identify the
  delivered v1.2 archive and the actual main and supplement build records;
- all supplied SHA-256 sidecars are verified by content and by portable line-ending
  behavior, not merely inspected visually;
- no paper contains an unexpected empty payload or unexplained file, including `$o`.

These are regression controls, not a reduced audit scope. Gates A–M remain mandatory.

## 5. Required audit architecture

Every paper must be audited through the following common gates. Gates B–G have
paper-specific attack requirements in Section 9.

| Gate | Required question | Minimum evidence |
|---|---|---|
| G0 | Is the exact target frozen, identifiable and independently handled? | hashes, inventory, declaration, attack plan |
| A | Are definitions, notation, hypotheses and headline statements coherent? | independent claim map and definition table |
| B–G | Does the critical mathematical proof chain survive rederivation and falsification? | derivations, boundary cases, scripts and raw results |
| H | Does the formal artifact reproduce and match the manuscript claims? | clean build, import graph, theorem statements, axiom output, scans |
| I | Are citations accurate and is the current open-problem status supported? | source-by-source citation ledger |
| J | Are scope, conditionality, verification status and release status stated without overclaim? | claim-language audit |
| K | Is the novelty/prior-art claim independently defensible? | dated search protocol, corpus, comparison matrix, residuals |
| L | Are English/Spanish and Markdown/LaTeX/PDF/figures semantically and visually consistent? | semantic diff and rendered-page QA |
| M | Is the audit package complete, reproducible, non-truncated and cryptographically sealed? | manifests, archive comparison and final hashes |

### 5.1 Gate G0 — target, identity and independence

Verify Section 4 in full. Produce an attack plan with explicit **kill switches**:
conditions that immediately prevent `PASS`, such as target-hash drift, a failed
clean build, a mismatched theorem statement, a project axiom in a headline theorem,
an unreconciled counterexample, a materially false citation, a broken PDF semantic
chain or an unresolved novelty collision.

### 5.2 Gate A — definitions and claims

Build a fresh claim map. For every theorem, corollary and headline claim, record:

- exact manuscript location and statement;
- all hypotheses and quantifier domains;
- formal declaration, if claimed;
- whether the declaration is a premise, bridge, final theorem, interface or
  byproduct;
- proof dependencies and imported roots;
- prior-art comparator, where the claim is comparative;
- falsification strategy and outcome.

The map must distinguish “source present”, “target compiled”, “aggregate root
imports target”, “public API re-exports declaration” and “headline theorem has the
claimed axiom footprint”. These are different facts.

### 5.3 Gates B–G — analytic and computational adversarial review

The auditor must independently rederive the proof-critical identities and
inequalities, trace hypotheses at every bridge, and attack all boundary regimes.
At minimum:

- test empty, smallest admissible, parity and threshold cases;
- test equality and near-equality families;
- test every floor, ceiling, residue-class and denominator convention;
- test branch joins and strict/non-strict inequality transitions;
- use exact rational/integer arithmetic where possible;
- enumerate small instances or solve independent LP/ILP models where feasible;
- reconcile every computational result with the displayed manuscript formula;
- retain the full search domain, solver status, seed, code and raw output.

A random search alone is insufficient for a finite domain that can reasonably be
exhausted. A successful script is not a proof and may not override a failed analytic
derivation or formal mismatch.

### 5.4 Gate H — independent Lean reproduction and conformance

For each paper the auditor must:

1. verify the archive SHA-256 before extraction;
2. extract into an empty directory and prove there is no inherited `.lake`;
3. run `lake update` and `lake exe cache get`, recording all output;
4. run the exact paper-specific build command in Section 9;
5. record command, working directory, exit code, elapsed time and complete stdout/
   stderr in directly visible log files;
6. inspect the root-import graph and distinguish explicit multi-target builds from
   declarations actually imported by an aggregate root;
7. run every supplied frozen axiom file and independently query `#print axioms` for
   each headline theorem and critical bridge;
8. record the verbatim theorem statements with `#check`/`#print` or equivalent;
9. scan active source for `sorry`, `admit`, `axiom`, `opaque` used as an escape,
   `unsafe`, `native_decide`, untrusted code generation and suspicious commented
   substitutes; classify true code separately from prose/comments;
10. verify no undeclared local path dependencies or missing source components;
11. compare the formal statements, hypotheses and constants with the manuscript;
12. preserve import-collision and failed-attempt logs; do not suppress them merely
    because a later compatible closure succeeds.

The expected foundational footprint is exactly
`[propext, Classical.choice, Quot.sound]` on each named headline theorem unless the
paper-specific appendix explicitly says otherwise. A clean build of dependencies
does not establish the footprint of the final theorem; the final theorem itself must
be queried.

### 5.5 Gate I — citations and current problem status

Create a citation ledger covering every mathematical and historical citation. For
each entry record the manuscript claim, cited source, page/theorem where available,
source type, access date and verdict (`SUPPORTED`, `PARTIAL`, `MISSTATED`,
`UNVERIFIED`). Prefer original papers, official problem pages, journal records,
Mathlib source/PR records and authoritative surveys. Search-result snippets are not
evidence.

Verify separately:

- the current status of Erdős Problem #81;
- the distinction between the full chordal problem and the split-graph case;
- the exact constants and error terms attributed to earlier work;
- whether cited results are integral, fractional, asymptotic, finite, conditional or
  unconditional;
- whether references and URLs resolve and bibliographic metadata is accurate.

### 5.6 Gate J — scope and overclaim

Audit the abstract, introduction, theorem statements, formalization section,
conclusion, metadata and captions for inconsistent status language. In particular:

- `preprint draft`, `unpublished`, `verified`, `formally verified`, `axiom-clean`,
  `unconditional`, `sharp`, `optimal`, `resolves` and `independent` must be supported
  in their exact scope;
- a formal byproduct is not automatically novel or ready for Mathlib;
- an obstruction that motivates a hypothesis must not be presented as a premise;
- “sharp quadratic coefficient” must not imply an optimal linear coefficient;
- author-side recorded evidence must not be described as independent reproduction;
- `PASS` from this audit must not be described as human peer review.

### 5.7 Gate K — prior art and novelty

Gate K is separate from Gate I. Correct citations do not establish novelty. The
auditor must conduct a current search through the audit date, including work from
2023 onward and recent preprints, citations to and from the principal antecedents,
surveys, author/project pages, conference records, Mathlib, open pull requests and
relevant discussion archives.

Deliver:

- dated queries, databases and search engines used;
- inclusion/exclusion criteria and languages searched;
- a corpus bibliography with stable links/identifiers;
- a comparison matrix: present claim versus closest known result, hypotheses,
  object, finite/asymptotic status, constant, error term and proof mechanism;
- a collision log for superficially similar results;
- a specialist-inquiry list for items not decidable by database search;
- a bounded conclusion.

Permitted conclusion language is evidence-bounded, for example: “No prior result
with the same statement was found in the searched corpus as of DATE.” A negative
search must never be stated as proof that no such result exists. An “in preparation”
project or unresolved attribution remains a disclosed residual and may require
specialist confirmation before release.

### 5.8 Gate L — bilingual and artifact consistency

Audit the full English and Spanish manuscripts, not a spot sample. Protect theorem
statements, hypotheses, constants, equation labels, cross-references, citations,
formal declaration names and status language. Idiomatic Spanish is expected; exact
semantic equivalence is required for protected mathematical content.

Verify both chains independently:

`English Markdown -> English LaTeX -> English PDF`

`Spanish Markdown -> Spanish LaTeX -> Spanish PDF`

The TeX must follow the repository template and the PDF must be compiled from the
final TeX. Render every PDF page to images and inspect:

- missing or substituted glyphs;
- black squares, broken mathematics or literal Markdown markup;
- clipped equations, tables and figures;
- blank or duplicated pages;
- caption, numbering and cross-reference defects;
- figure resolution, legibility and correspondence with prior approved figures;
- metadata, title, version, language and audit-status consistency;
- malformed PDF structure, including cross-reference/startxref errors.

Any upstream correction invalidates downstream TeX, PDF, QA and hashes. Regenerate
in that order. Do not independently hard-code a PDF summary that can diverge from
the canonical report or manuscript.

### 5.9 Gate M — audit-package integrity

Before assigning the final verdict:

- ensure every report and script ends normally and is not truncated;
- ensure every referenced log exists as a directly visible file, not only inside a
  ZIP archive;
- ensure direct files and their copies inside the final ZIP are byte-identical;
- ensure all scripts execute from documented commands;
- ensure all relative paths resolve on a clean extraction;
- generate manifests only after content is final;
- generate the archive last, then hash it;
- independently extract and verify the final archive against its manifest;
- prohibit files named as final that contain placeholders or template text.

## 6. Finding and verdict policy

### 6.1 Finding severity

| Severity | Meaning |
|---|---|
| `BLOCKER` | Target cannot be identified/reproduced, headline claim is false or unsupported, clean build/axiom gate fails, or evidence integrity is broken. |
| `MAJOR` | Material proof, formal, novelty, citation, translation or scope defect that can affect acceptance or interpretation. |
| `MINOR` | Real but localized defect that does not alter the main result or its evidentiary basis. |
| `NOTE` | Observation, limitation or optional improvement; not a defect. |

Every finding must have a stable ID, paper, gate, severity, exact location, claim
affected, reproduction steps, evidence paths, expected/observed result, impact,
proposed disposition and status. `FINDINGS.csv` is mandatory even when it contains
only a header and zero findings.

### 6.2 Allowed verdicts

| Verdict | Criteria |
|---|---|
| `PASS` | Every mandatory gate passes; no unresolved `BLOCKER` or `MAJOR`; the exact target clean-builds; headline theorem statements and axiom footprints match; no claim-critical residual remains. |
| `PASS_WITH_RESIDUALS` | No known mathematical/formal defect and no unresolved `BLOCKER`/`MAJOR`, but a non-claim-critical external residual remains. This does **not** close a release gate that explicitly requires that residual. |
| `FAIL` | At least one claim-critical defect or failed mandatory gate. |
| `INCONCLUSIVE` | Evidence is insufficient, a required capability/source is unavailable, or conflicting evidence cannot be resolved. |
| `NOT_AUDITABLE` | Target identity, completeness or integrity prevents a meaningful audit. |

Plain `PASS` must never conceal residuals. Each gate receives its own verdict and
the overall verdict is no stronger than the weakest mandatory gate. A corrected
target must not be marked “resolved” inside the old run; close the old run with its
actual verdict and begin a new run with new hashes.

## 7. Mandatory output structure and exact destinations

Place each paper's results under its own active package:

- Paper I: `preprints/PAPER_I/active/preprint_draft_v1.2/02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.2/`
- Paper II: `preprints/PAPER_II/active/preprint_draft_v1.2/02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.2/`
- Paper III: `preprints/PAPER_III/active/preprint_draft_v1.2/02_validation/02_IA_ADVERSARIAL_AUDITS/run_YYYY-MM-DD_v1.2/`

Use this exact tree in each destination:

```text
run_YYYY-MM-DD_v1.2/
├── 00_REQUEST/
│   ├── AUDIT_REQUEST_SPEC.md
│   ├── AUDITOR_DECLARATION.md
│   ├── ATTACK_PLAN_AND_KILL_SWITCHES.md
│   ├── INPUT_INVENTORY.json
│   └── INPUT_FREEZE_MANIFEST.sha256
├── 10_CONTROL/
│   ├── AUDIT_INDEX.md
│   ├── CLAIM_MAP.md
│   ├── ENVIRONMENT.md
│   ├── OPEN_RISKS.md
│   ├── FINDINGS.csv
│   └── GATE_STATUS.json
├── 20_EVIDENCE/
│   ├── G0_TARGET_INDEPENDENCE/
│   ├── A_DEFINITIONS_CLAIMS/
│   ├── B_PROOF_CHAIN/
│   ├── C_PROOF_CHAIN/
│   ├── D_PROOF_CHAIN/
│   ├── E_PROOF_CHAIN/
│   ├── F_PROOF_CHAIN/
│   ├── G_FALSIFICATION/
│   ├── H_LEAN_REPRODUCTION/
│   ├── I_CITATIONS_STATUS/
│   ├── J_SCOPE_OVERCLAIM/
│   ├── K_PRIOR_ART_NOVELTY/
│   ├── L_BILINGUAL_ARTIFACTS/
│   └── M_PACKAGE_INTEGRITY/
├── 30_REPORT/
│   ├── FINAL_AUDIT_REPORT.md
│   ├── FINAL_AUDIT_REPORT.tex
│   ├── FINAL_AUDIT_REPORT.pdf
│   ├── FINAL_AUDIT_SUMMARY.json
│   ├── SEMANTIC_EQUIVALENCE_REPORT.md
│   └── PDF_QA_REPORT.md
└── 40_PACKAGE/
    ├── PACKAGE_MANIFEST.json
    ├── SHA256_MANIFEST.txt
    ├── TREE.txt
    ├── EXTERNAL_AI_ADVERSARIAL_AUDIT_PACKAGE.zip
    └── EXTERNAL_AI_ADVERSARIAL_AUDIT_PACKAGE.zip.sha256
```

Every evidence directory must contain:

- `AUDIT_RECORD.md`: objective, inputs/hashes, method, commands, result, gate
  verdict, limitations and links to raw evidence;
- `scripts/`: independently written executable code, if code was used;
- `results/`: raw stdout/stderr, solver exports, tables and machine-readable results;
- `SHA256_MANIFEST.txt`: hashes of that gate's final evidence.

Empty evidence directories are forbidden. If a method is inapplicable, provide an
`AUDIT_RECORD.md` explaining why and assign `INCONCLUSIVE` or an explicit
`NOT_APPLICABLE` subtest; a mandatory gate itself cannot pass solely by being called
inapplicable.

## 8. Mandatory formats and report-generation chain

### 8.1 Human-readable outputs

- Markdown (`.md`, UTF-8) is the canonical report source.
- LaTeX (`.tex`, UTF-8) must be generated from the final canonical Markdown using
  the same preprint/audit visual conventions as the repository.
- PDF (`.pdf`) must be compiled from that final LaTeX and visually inspected page by
  page.
- The canonical final report should be in English for public repository use. A
  Spanish executive summary may be added, but it is non-normative unless a full
  semantic-equivalence check is supplied.
- Raw logs use `.txt` or `.log`, UTF-8 where the producing tool allows it.

The mandatory chain is:

`FINAL_AUDIT_REPORT.md -> FINAL_AUDIT_REPORT.tex -> FINAL_AUDIT_REPORT.pdf -> rendered-page QA -> hashes -> ZIP -> ZIP hash`

### 8.2 Machine-readable outputs

`FINAL_AUDIT_SUMMARY.json` must include at least:

```json
{
  "protocol": "EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1",
  "paper": "PAPER_I | PAPER_II | PAPER_III",
  "target": "preprint_draft_v1.2",
  "target_sha256": "...",
  "audit_class": "EXTERNAL_AI_ADVERSARIAL",
  "independence_level": "...",
  "start_utc": "...",
  "end_utc": "...",
  "overall_verdict": "PASS | PASS_WITH_RESIDUALS | FAIL | INCONCLUSIVE | NOT_AUDITABLE",
  "gates": {"G0": "...", "A": "...", "B": "...", "C": "...", "D": "...", "E": "...", "F": "...", "G": "...", "H": "...", "I": "...", "J": "...", "K": "...", "L": "...", "M": "..."},
  "unresolved": {"blocker": 0, "major": 0, "minor": 0, "note": 0},
  "lean": {"clean_build": "...", "axiom_gate": "...", "root_imports_verified": true},
  "novelty": {"cutoff_date": "...", "verdict": "...", "specialist_residuals": []},
  "package_sha256": "..."
}
```

`FINDINGS.csv` columns are mandatory:

```text
finding_id,paper,gate,severity,status,claim_id,location,title,expected,observed,impact,reproduction,evidence_paths,proposed_disposition
```

Use JSON/CSV for structured data, plain text for verbatim logs, and PDF only as a
rendered presentation layer. Do not place the only copy of raw evidence in PDF.

## 9. Paper-specific audit instructions

### 9.1 Paper I

**Title:** *Affine Profile Reduction for Fractional Triangle Packings in Split Graphs*

**Headline target:** the corrected finite split-graph bound with additive term
`n^2/6 + n/2`, together with the affine-profile reduction and its formal interfaces.
The obsolete `+n` form may exist historically but must not be substituted for the
v1.2 headline claim.

**Frozen Lean archive:**
`05_formalization/lean_v1.2_freeze/PAPER_I_lean_v1.2_freeze.zip`  
**Expected archive SHA-256 at protocol date:**
`0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`

**Mandatory claim surfaces:**

| Claim ID | Manuscript content | Formal declarations |
|---|---|---|
| `P1-FRAC-THM-V1_2` | corrected split-graph fractional bound | `PaperI.paperI_main`; `PaperI.Split.paperI_main_sharp` |
| `P1-ASSEMBLY-V1_2` | corrected final assembly | `PaperI.assembly_sharp`; `PaperI.Split.paperI_main_sharp` |
| `P1-DUALITY` | finite covering/packing duality and residual duality | `FiniteLPDuality.covering_packing_duality`; `PaperI.Split.residual_duality`; `Contrib.Submission.covering_packing_duality` |
| `P1-INTERFACES` | reusable value-function and centered interfaces | `Contrib.lpVal_*`; `Contrib.tuza_split_centered_scalar` |

**B–G attack plan:**

- **B:** reconstruct split-graph, triangle-packing, fractional-cover and residual
  definitions; check all normalizations and factors of two/three.
- **C:** rederive the affine dependence on neighborhood profiles and justify the
  concavity/extreme-profile reduction, including domain and compactness assumptions.
- **D:** independently verify the finite LP/Farkas duality orientation, feasibility,
  boundedness, primal/dual normalization and transfer to the residual problem.
- **E:** solve or certify the reduced pure-profile LP independently; test all branch
  boundaries and equality configurations, including `(p,q,s)=(2,4,2)` and the
  distinction between `s=2,o=0` and `s=2,o>=1`.
- **F:** rederive the final assembly yielding `n^2/6+n/2`; explicitly search for the
  earlier `+n` leakage in prose, equations, translations and formal interfaces.
- **G:** enumerate small split graphs/neighborhood-type multisets and independently
  solve the relevant rational LPs; include equality and near-equality cases.

**Clean reproduction commands:**

```text
lake update
lake exe cache get
lake build PaperI.PaperI_Statement PaperI.PaperI_Arith FiniteLPDuality Contrib.PaperISharp Contrib.LpStability Contrib.TuzaSplitCentered Contrib.Submission.FarkasLP Contrib.Submission.FgConeClosed
lake env lean FreezeAxioms.lean
```

Expected environment: Lean `4.28.0`; Mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

Explicitly determine which `Contrib` results are premises and which are byproducts.
A clean build does not establish that a contribution is absent from Mathlib or novel.

### 9.2 Paper II

**Title:** *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on
Chordal Graphs*

**Headline target:** the exact finite chordal maximum, attainment by complete-split
graphs, extremizer/tie structure and stated arithmetic corollaries.

**Frozen Lean archive:**
`05_formalization/lean_v1.2_freeze/PAPER_II_lean_v1.2_freeze.zip`  
**Expected archive SHA-256 at protocol date:**
`ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895`

**Mandatory claim surfaces:**

| Claim ID | Manuscript content | Formal declarations |
|---|---|---|
| `P2-MAIN-V1_2` | exact chordal maximum and attainment | `PaperII.theorem_1_2` |
| `P2-EXTREMIZER` | unique/tied maximizers, level sets and copy defects | `PaperII.Fsat_argmax_unique`; `Fsat_argmax_tie`; `level_set_iff`; `copyDefect_nonneg`; `copyGamma_ge_half_copyDefect` |
| `P2-ASYM-COR` | asymptotic, modular and Paper-I comparison corollaries | `phiTau_max_sandwich`; `odd_sq_emod_24`; `phiTau_max_closed`; `phiTau_max_le_paperI_bound` |
| `P2-FORMAL-CONFORMANCE` | full v1.2 surface and reusable components | `PaperII`; `Contrib.Submission.Chordal`; `Contrib.Submission.GeodesicChordless` |

**B–G attack plan:**

- **B:** reconstruct chordal, complete-split and fractional triangle-cover
  definitions, including the exact functional and all finite-domain conventions.
- **C:** rederive the symmetrization/vertex-copy argument and verify that chordality,
  vertex count and the objective are preserved in every case.
- **D:** verify monotonicity and termination of the copy process, including ties,
  equality cases, level sets and copy-defect inequalities.
- **E:** independently compute the complete-split value as a function of the split
  parameter and verify the closed form.
- **F:** independently solve the integer maximization, parity/tie cases,
  `floor((2n+1)^2/24)`, residue-class formulas, bounded remainder and comparison with
  Paper I. Check every stated domain restriction.
- **G:** exhaust small chordal graphs where feasible and compare exact LP values with
  the theorem; separately test the one-dimensional integer optimizer over a broad
  deterministic range.

**Clean reproduction commands:**

```text
lake update
lake exe cache get
lake build PaperII PaperII.AsymptoticCorollaries PaperII.AxiomCheckCorollaries PaperII.Extremizer PaperII.CopyDefect Contrib.Submission.Chordal Contrib.Submission.GeodesicChordless
lake env lean FreezeAxioms.lean
```

Expected environment: Lean `4.28.0`; Mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The auditor must also search the complete manuscript and package for stale `v1.0.1`
freeze references and reconcile the documented main and supplement build logs with
the delivered v1.2 freeze.

The aggregate `PaperII` target does not by itself prove that `Extremizer` and
`CopyDefect` are imported. Produce an import-root graph and report the explicit
multi-target build separately from aggregate-root coverage. Preserve and explain
any first axiom attempt that fails because an explicit target was not built.

### 9.3 Paper III

**Title:** *Linear-Error Clique Partitions of Split Graphs via Structured Triangle
Packing*

**Headline target:** an unconditional `n^2/6+O(n)` clique-partition upper bound for
split graphs, the discharge of AX1 and AX2, and the claim that the quadratic
coefficient `1/6` is sharp. The optimal uniform linear coefficient is not claimed.

**Frozen Lean archive:**
`05_formalization/lean_v1.2_freeze/PAPER_III_lean_v1.2_freeze.zip`  
**Expected archive SHA-256 at protocol date:**
`9bff12f0c8279ae4485de960c01be322a423d8fd2f17592ebb7327b2c890fcb8`

**Mandatory claim surfaces:**

| Claim ID | Manuscript content | Formal declarations |
|---|---|---|
| `P3-MAIN-V1_2` | unconditional split bound and clique-partition corollary | `PaperIII.Theorem_1_1`; `PaperIII.Corollary_1_2` |
| `P3-AX1-DISCHARGE` | fractional-integral packing-gap input | `PaperIII.AX1_holds`; `Nibble.AX1.ax1Statement_holds` |
| `P3-AX2-DISCHARGE` | dense exact triangle-decomposition input | `PaperIII.AX2_holds`; `BKLO.triangle_decomposition_dense`; `Ax2.BKLOBridge.triDecomp_iff` |
| `P3-PUBLIC-API` | unconditional `SimpleGraph` entry point/downstream interface | `PaperIII.Theorem_1_1_of_splitPartition_uncond`; `PaperIII.PublicAPI_*` |
| `P3-SHARPNESS` | complete-split benchmark and quadratic sharpness | `PaperIII.Corollary_1_2_sharp`; `Byproduct_completeSplit_cp_sharp`; `Byproduct_leading_constant_forced` |
| `P3-OBSTRUCTIONS` | examples motivating AX2 density | `ax2_divisibility_degree_insufficient`; `ax2_density_necessary_K7_minus_two_triangles` |
| `P3-BYPRODUCTS` | curated paper-level byproducts and standalone library | `PaperIII.PaperImprovementsGate`; `Contrib.*` |
| `P3-FORMAL-PROVENANCE` | four frozen components assembled into one project | commits and hashes in `FREEZE_METADATA.json` |

**B–G attack plan:**

- **B:** reconstruct the split presentation, clique-partition functional, fractional
  and integral triangle packing quantities, and every normalization linking them.
- **C:** audit the complete AX1/nibble dependency closure, hypotheses, quantitative
  tolerances and the bridge from hypergraph matching to the graph statement.
- **D:** audit the complete AX2/BKLO dependency closure, divisibility, density,
  exact-decomposition predicates and the `triDecomp_iff` bridge. Verify AX2 as one
  component of the proof, not as the whole paper.
- **E:** independently rederive the three-regime proof, regime coverage, branch
  joins, common-profile LP, unified margin and mesoscopic corridor closure.
- **F:** verify the exact complete-split benchmark and distinguish two roles of
  `1/6`: the exact/asymptotic quadratic coefficient and the separately forced
  uniform linear coefficient statement. Verify the public API and absence of a
  hidden Paper V dependency. Confirm that obstructions motivate rather than premise
  the main theorem, and that byproducts are correctly curated/classified.
- **G:** independently test algebraic identities, the common-profile LP, unified
  margin, corridor ILP, complete-split values and obstruction examples. Inspect the
  full scripts and domains rather than trusting certificate PDFs.

**Clean reproduction commands:**

```text
lake update
lake exe cache get
lake build PaperIII PaperIII.Theorem_1_1_Final PaperIII.PublicAPI PaperIII.OfPartition PaperIII.Obstructions PaperIII.PaperImprovementsGate Ax2 Nibble BKLO Contrib
lake env lean FreezeAxioms.lean
lake env lean FreezeAxiomsByproducts.lean
lake env lean FreezeAxiomsObstructions.lean
lake env lean FreezeAxiomsAX1.lean
lake env lean FreezeAxiomsAX2.lean
```

Expected environment: Lean `4.28.0` at commit
`7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`; Mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The freeze records four source components. Verify their boundaries, recorded commits
and assembled hashes. The five axiom files intentionally use compatible import
closures because a broad monolithic import has name collisions. Report each closure
separately; do not misdescribe the result as a single collision-free monolithic
environment. Preserve all failed collision attempts as evidence.

The novelty gate must independently test the quantified historical claim: improvement
from the Chen–Erdős–Ordman split coefficient `3/16` to the sharp coefficient `1/6`
with linear error, matching the benchmark lower bound. Verify that the full chordal
problem remains open and search current literature through the audit date, including
the Cavers survey, the principal EOZ/CEO chain, 2023–current work and any project
listed as “in preparation.” Do not assume the manuscript's novelty conclusion.

For `Contrib.*`, separately answer:

1. Is it a premise, bridge, public interface or independent byproduct?
2. Is the declaration already present in Mathlib under another name or generality?
3. Is there an open Mathlib PR or discussion covering it?
4. Does it build and have the claimed axiom footprint?
5. Is manuscript inclusion proportionate to mathematical value?

Formal correctness alone does not establish novelty or upstream readiness.

## 10. Cross-paper audit after the three individual audits

After sealing the three individual reports, create:

`preprints/EXTERNAL_AI_ADVERSARIAL_AUDIT_CROSS_PAPER_REPORT_v1.2.md`

and, if a rendered public report is desired, derive corresponding `.tex` and `.pdf`
from that Markdown. The cross-paper report must not replace or weaken any individual
verdict. It must check:

- shared notation and definitions across Papers I–III;
- consistency of constants, theorem numbering and references to the other papers;
- that Paper II's comparison uses Paper I v1.2's corrected `+n/2` surface;
- that Paper III states exactly what Papers I and II establish and does not import
  unpublished mathematical authority from them without an explicit dependency;
- consistent distinction between the full chordal problem and the split case;
- consistent `draft`, `unpublished`, `formalized`, `independently reproduced` and
  novelty language;
- consistent English/Spanish names and bibliography entries;
- no hidden dependence on Paper IV, Paper V or an unshipped local tree;
- each paper's package, report and hashes remain independently reproducible.

If the cross-paper check discovers a defect, add a finding to every affected paper's
already sealed report by issuing an addendum with its own hash; never rewrite a
sealed report in place.

## 11. Required final report contents

`FINAL_AUDIT_REPORT.md` must contain, in order:

1. target identity and all controlling hashes;
2. audit class, independence disclosure and limitations;
3. executive verdict and exact meaning of that verdict;
4. protocol compliance statement and deviations;
5. claim map;
6. gate-by-gate methods, evidence, findings and verdicts G0/A–M;
7. analytic rederivations and computational falsification summary;
8. clean Lean reproduction, import graph, verbatim headline `#print axioms` output
   and escape-hatch assessment;
9. citation ledger and open-status assessment;
10. prior-art/novelty search, closest-result matrix and bounded conclusion;
11. bilingual/artifact semantic and visual QA;
12. unresolved findings and residual risks;
13. explicit statements of what the audit does **not** establish;
14. package manifest and reproduction instructions;
15. signatures/identifiers, dates and final hashes.

The report must cite direct evidence paths near every verdict. Claims such as “all
tests passed” without enumerated tests, domains and raw outputs are insufficient.

## 12. Acceptance checklist for delivery

The owner should reject the audit delivery unless all answers below are `YES`:

- Was the input frozen before analysis and did its hash remain unchanged?
- Are the primary and challenger contexts disclosed and meaningfully isolated?
- Is every headline claim mapped to mathematics, formal declarations and tests?
- Were proof-critical steps independently rederived rather than summarized?
- Are computational scripts, domains, seeds and raw results directly visible?
- Was each Lean archive rebuilt cleanly with no inherited project cache?
- Is the aggregate-root/import-closure distinction explicit?
- Is verbatim theorem-level axiom output present for the headline declarations?
- Are failed attempts and import collisions retained and explained?
- Are citation correctness and novelty assessed as separate gates?
- Is the literature search current through the audit date and evidence-bounded?
- Were the complete English and Spanish versions compared?
- Were both PDFs compiled from final TeX and visually inspected page by page?
- Are the Markdown, TeX and PDF final reports semantically synchronized?
- Do all referenced logs exist outside the ZIP?
- Are direct files byte-identical to the corresponding ZIP members?
- Do every Markdown file and script end normally, with no truncation?
- Was the ZIP built last and independently verified against its SHA-256 manifest?
- Does the verdict use the exact taxonomy in Section 6 and disclose all residuals?
- Does the report state that it is not human peer review or proof of global novelty?

Only a complete delivery satisfying this protocol may be labelled
`EXTERNAL_AI_ADVERSARIAL_AUDIT`. Anything narrower must be labelled by its actual
scope, for example `LEAN_REPRODUCTION_ONLY`, `LITERATURE_REVIEW_ONLY` or
`FORMAT_QA_ONLY`.



