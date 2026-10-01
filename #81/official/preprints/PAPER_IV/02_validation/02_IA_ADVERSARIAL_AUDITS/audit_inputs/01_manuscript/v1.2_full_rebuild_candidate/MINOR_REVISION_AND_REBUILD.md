# Paper IV v1.2 — final minor corrections and reconstruction

**EDITORIAL_DRAFT_WITH_OPEN_GATES.** No mathematical changes; renewed freeze
and internal audit remain pending the complete reconstruction.

## Editorial changes

- Added `(Figure 2)` / `(Figura 2)` to the first paragraph of §5.2.
- Kept the version at 1.2 and all mathematical statements, constants, equations,
  proof dependencies and literal Lean blocks unchanged.
- Regenerated both TeX/PDF pairs from their Markdown sources. English has 68
  pages; Spanish has 69. Both compile with two TeX passes, without overfull
  boxes, missing glyphs, fatal errors or undefined references. Existing
  underfull warnings and the nonfatal Fontconfig notice are retained in logs.
- Reran protected-token and bilingual checks: 486 corresponding blocks,
  227 English displays, five unchanged literal Lean blocks, four figures in
  each edition; no mismatch in protected content, headings or equation labels.
- Regenerated all page images. Pixel-file SHA comparison against the previously
  inspected final renders changes only page 15 in each language. Both changed
  pages were inspected at readable resolution and show the new reference
  correctly. Final full rendered QA must be repeated after §7 is rebound to
  the actual new build evidence; no final visual seal is claimed here.

The skill's semantic lock limited the manuscript edit to a cross-reference.
Its artifact invalidation rule requires the new manuscript seal after the
full-build evidence is available; the old freeze was not overwritten.

## Expanded audit scope

`NEXT_INTERNAL_AUDIT_SCOPE_v1.2.md` requires individual prose-to-Lean checks for
E.4 (all seven named modules), F.3a, the three F.5 cases, and an exposition verdict
for every one of the seven A.2 rows. A successful build does not automatically
make any prose summary adequate for human review.

`FixedExplicit` is the namespace `PaperIV.SublinearResearch.FixedExplicit`,
implemented in `ExplicitFixedStability.lean`. The other four requested module
names resolve directly. All five occur in the full 607-module target closure.

## Reconstruction and release gates

The exact 615 source-manifest entries were copied into
`C:/Users/jtraverso/e81p4/piv_v12_full_rebuild_20260929/`. No old project objects
were copied. The shared pinned dependency directory is linked, not duplicated.
The wrapper checks source hashes and dependency revisions before execution,
then requires 607 fresh successful compilations, zero project cache hits, all
19 audit targets and 224 export checks, and approved axiom output. It stops on
failure. It does not perform the manuscript audit or publish anything.

The first preflight's overly broad cache check rejected the uncompiled `Cli`
tooling dependency before any Lean module was compiled. No project source was
changed: the runner now records that this tooling library is not imported by
the project. Other dependency caches are present. The failed preflight is
preserved separately; attempt r2 uses a new evidence directory.

Current evidence directory:
`../../03_reproducibility/full_rebuild_v12_20260929_r2/`.

After a successful validated run: update §7's historical build counts in both
languages, regenerate and review all artifacts, attach the new evidence to the
unchanged source identity (or a new identity if any source repair is needed),
and create the new manuscript manifest/archive. Only then begin the new
internal audit. The old manuscript freeze and Lean source archive stay intact.

## Research status checklist

- Plan activo: complete fresh serial reconstruction, then renew the freeze.
- Resultado: minor bilingual cross-reference and audit-scope changes applied.
- Estado matemático: unchanged; no new theorem or stronger audit verdict claimed.
- Dependencias: existing pinned Lean/Mathlib installation, no new installation.
- Pendiente: full-build result, evidence update, final QA/reseal, internal audit.
- Siguiente acción: inspect the complete fresh-build result before freezing.
