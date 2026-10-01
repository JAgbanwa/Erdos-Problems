# Paper IV v1.2 — selected local Lean source freeze

Identity: **piv-v12-fb459343d234**. Created 29 September 2026.
This is a local source identity, not a release, Git commit or audit of the
revised manuscripts. Historical freezes remain unchanged.

## Contents and checks

- 607 Lean modules; 615 source, configuration and instruction entries.
- 19 targets executed afresh, serially; 588 dependency objects reused after
  source, options, dependency, pinned-version and successful-build hash checks.
- 224 literal publication export checks through `import PaperIV` alone.
- 461 printed axiom records restricted to `propext`, `Classical.choice` and
  `Quot.sound`, or subsets. This is not a count of distinct theorems.
- No failed, blocked or omitted modules, or sources changed during the run.
- Source scan found no proof placeholders or new mathematical axioms.
- All copied source files and all ZIP members match the manifest; ZIP CRC passed.
- The existing pinned Mathlib and package cache was reused; no new installation.

The selected results include E35's improved explicit thresholds, the public
Theorem C through E34, fixed-defect same-root stability, the uniform sublinear
extension and the square-root obstruction for distance to optimal-size templates.
The public result statements were not weakened or renamed in this pass.

Only five unused, superseded modules were removed: E35L.Far, E35L.Gate,
E35L.Poly, E35L.Sched and FDCheck.TowerAudit. The stronger E35 versions remain.
The removed files are recoverable in the historical cut and at
`C:/Users/jtraverso/e81p4/retired_v12_20260929/`.

## Files and identity

- Tree: `lean_piv-v12-fb459343d234/`.
- Source ZIP: `LEAN_SOURCE_piv-v12-fb459343d234.zip`.
- Evidence: `../03_reproducibility/build_piv-v12-fb459343d234/`.
- Record: `../04_integrity/FREEZE_piv-v12-fb459343d234.json`.
- Source-manifest SHA-256:
  `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`.
- Archive SHA-256:
  `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6`.

The archive contains no compiled caches or credentials. The evidence includes
the complete fresh target logs and the successful build provenance of every
local object reused by the run.

## One audit command

After attaching the existing pinned dependency cache to a working copy:

```text
python tools/audit_publication.py
```

Read `docs/PUBLICATION_AUDIT.md` first. The exact 19 targets are in
FREEZE_SCOPE.json. Requested targets execute afresh; an import of a cached
aggregate alone is not substituted for their execution. Use at most one build
process for this work. If the pinned dependency cache is unavailable, stop and
resolve its location; do not fetch another Mathlib or run dependency updates.
The frozen source tree is source-only and is not itself a second build cache.

## Remaining gates

English v1.2 is still an editorial review candidate. Spanish synchronization,
TeX/PDF generation and full visual/parity review precede the new internal and
external manuscript audits. Those audits must name this cut and the final
manuscript identities. No historical audit PASS is transferred to them.

Nothing was pushed, tagged, deposited or published.
