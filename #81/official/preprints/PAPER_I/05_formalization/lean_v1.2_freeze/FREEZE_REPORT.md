# Paper I v1.2 corrective freeze report

Status: `LOCAL_CORRECTIVE_FREEZE_PREPARED`.

## Perimeter

The mathematical Lean sources and pinned dependencies are unchanged from the
v1.1 freeze. The v1.2 correction extends `FreezeAxioms.lean` to query the two
claim surfaces omitted from the earlier gate: `PaperI.assembly_sharp` and
`PaperI.Split.residual_duality`.

## Local preparation result

- Toolchain: Lean 4.28.0; Mathlib v4.28.0 at
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Full build: not rerun; the preserved baseline log records exit 0 and
  `Build completed successfully (8034 jobs).`
- Corrective axiom gate: exit 0; 15 declarations checked.
- Reported footprint: only `propext`, `Classical.choice`, `Quot.sound`.
- Theorem and proof sources are byte-identical to the v1.1 freeze.

## Scope limitation

This is an author-side corrective freeze, not a clean-room reproduction. The
v1.2 internal audit and independent external reproduction remain separate gates.
