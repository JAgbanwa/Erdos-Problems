# Paper IV v1.2 — inputs for the next internal audit

**PLANNED_NOT_EXECUTED.** This note identifies the enlarged scope; it does not
activate an audit and does not replace the internal standard.

## Exact inputs

1. The six manuscripts and their assets listed in MANUSCRIPT_MANIFEST.json.
2. The manuscript ZIP identified by MANUSCRIPT_FREEZE.json.
3. Lean cut `piv-v12-fb459343d234`, its source manifest/archive and recorded
   combined build, identified in the same freeze record.
4. V1.2_CLAIM_MAP.md, the manuscript's statement/implementation tables, and
   the existing `../../02_validation/INTERNAL_AUDIT_STANDARD_v1.0.md`.

The final manuscript identity is recorded in MANUSCRIPT_FREEZE.json. The renewed
full reconstruction is complete: 607 modules across two verified segments,
19 reexecuted targets, 224 exports and 461 permitted-axiom records. Its checked
logs and provenance are sealed in
`../../03_reproducibility/full_rebuild_v12_20260929_seal/`.
Verify that binding before this audit starts. The earlier manuscript freeze
remains intact in `../v1.2_candidate/` and its ZIP.

Begin by checking hashes and using a new execution directory. Never overwrite
the earlier audits. The earlier protocol's version-specific module counts,
targets and claim inventory must be replaced by this cut's literal inputs,
not carried forward as assertions. Review the full protocol before execution.

## Content requiring renewed coverage

- Theorem A, B, C and C′, with their different ranges and quantifiers.
- Chordal and fixed-defect same-root bounds, unrestricted partition counts,
  edge mass, and the distinction between an actual clique root and resizing
  to an optimal-size template.
- Proposition 6.3a: the formal square-root obstruction, its family, constants
  and universal quantification over optimally sized comparison templates.
- The uniform finite fractional bounds and the arbitrary-order sublinear
  sequence result; no substitution of a growing parameter into a fixed-parameter
  theorem is permitted.
- Explicit public E34/E35 chains, tower propagation, the selected-removal audit,
  and the exact scope of the exclusion of Alon–Shapira from selected public cones.
- Expanded retained accounts in E.4, clique recovery in F.3, and the three-case
  pinned-sample argument in F.5. Prose-to-Lean verification remains required.
- Attribution to [5], [15] and [22], including what coincides, what is adapted
  and what the restricted order of pieces strengthens. No priority assertion.
- Bilingual semantic and visual parity after the last typesetting pass.

## Mandatory prose-to-Lean checks

Record a separate conclusion for every item below, with literal declarations,
hypotheses, constants, manuscript locations and the evidence inspected.

- **E.4, block by block:** compare the retained accounts with `StrictParams`,
  `StrictBudget`, `ResidualExcess`, `CoreCliqueAlternative`, `LargeCliqueCore`,
  `TemplateDistance` and `RootPartition`. Verify that the witnesses and resources
  remain the same where the prose combines conclusions. A module inventory alone
  does not discharge this check.
- **F.3a:** compare the clique-recovery argument with the actual declaration
  `exists_clique_additive_defect`, including its ambient graph and defect bounds.
- **F.5:** check each of `l11_caseA`, `l11_caseB1` and `l11_caseB2`, the hypotheses
  selecting its case, coverage of the cases and their common conclusion.
- **A.2:** issue an individual exposition verdict for each of the seven entries:
  (1) regularization mass/degree/palette/width; (2) discard counts and retention;
  (3) fibre bounds and normalization; (4) nibble/tower numerical domination;
  (5) pre-terminal normalization; (6) terminal estimates and three-case budget;
  (7) Bose/Skolem frame constructions. State explicitly whether each summary is
  acceptable for human review, or requires expansion. Compilation is not an
  exposition verdict. Use `ACCEPTABLE_SUMMARY`, `REQUIRES_EXPANSION` or
  `INCONCLUSIVE`, with reasons; do not merge all seven into one PASS.

## Fresh reconstruction before the renewed freeze

The owner explicitly requested a complete reconstruction on 29 September 2026.
Use an isolated exact copy of the source manifest, with an initially empty
project artifact directory. Compile all 607 project modules, including all 19
selected audit/export targets, in dependency order. Reuse only the pinned
third-party packages and their existing cache; no second Mathlib installation.

In particular, require fresh successful module logs for
`PaperIV.DefectExplicitPublication`, `E34.L11Main`, `E35.Theorem`,
`ExplicitFixedStability` (namespace `PaperIV.SublinearResearch.FixedExplicit`)
and `PaperIV.OptimalTemplateObstruction`; resolve these
names against the actual source graph before the run. A cache hit is not a
fresh compilation. Require all 607 rows to be PASS (zero UP-TO-DATE), source
hashes unchanged, complete exit records, all 19 audit targets, all 224 export
checks and only the permitted foundational axioms. Preserve the previous build
as historical evidence rather than overwriting its records.

**Restart recovery amendment (29 September):** the PC restarted after 422 fresh
PASS modules. Their source/object/dependency hashes, build traces and success
logs were independently rechecked before resumption. Apply the full-rebuild
criterion across both segments, not as zero UP-TO-DATE rows in the resumed run
alone. Every reused object must map to its verified fresh PASS in the first
segment; all remaining modules and all 19 audit targets must complete in the
resumed segment. Require the recovery wrapper's combined provenance and final
validation, as detailed in `../../03_reproducibility/REBOOT_RECOVERY_v12_20260929.md`.
Do not accept the interrupted run's stale RUNNING marker as success.

If a compilation or axiom gate fails, stop, preserve its logs and diagnose;
do not freeze or start the internal audit. Any source repair creates a new
source identity. If sources remain identical, retain their content identity
and attach the new full-build evidence under a distinct run identifier.

## Execution limits

Reuse pinned dependencies and the existing Mathlib installation; no additional
Mathlib download. The complete reconstruction above is explicitly authorized;
once it is validated, the subsequent internal audit need not repeat it by default.
Maximum one heavy process. Certo checks must have explicit specifications and
independently verifiable certificates, and finite tests are not universal proofs.

Produce the standard per-block scripts, inputs, outputs, MD/PDF reports and ZIPs,
followed by a general report and sealed archive. New audit outcomes must not be
inferred from ARTIFACT_CHECKS.json: that file only checks editorial artifacts
and the integrity of existing evidence. No publication or external submission
is authorized by this note.
