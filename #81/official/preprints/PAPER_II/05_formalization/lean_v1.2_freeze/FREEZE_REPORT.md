# Paper II v1.1 local freeze report

Status: `LOCAL_FREEZE_PREPARED_NOT_AUDITED`.

## Perimeter

The snapshot was extracted from tracked Git `HEAD`
`25df96b06fe4614ae02f25ae968cc1d791c380e9`. It consolidates the main Paper II
library, tracked reusable chordal/geodesic modules, and the tracked
asymptotic/extremizer/copy-defect surfaces. Dirty Route-A experiments in the
source worktree are outside the snapshot.

## Local preparation result

- Toolchain: Lean 4.28.0; Mathlib v4.28.0 at
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Main build: exit 0; `Build completed successfully (8061 jobs).`
- Supplement: exit 0; `Build completed successfully (8032 jobs).`
- Axiom gate: exit 0; 16 declarations checked.
- Reported footprint: subsets of `propext`, `Classical.choice`, `Quot.sound`.
- Escape-hatch text scan: matches occur only in comments/reporting labels; the
  theorem-level axiom output contains no `sorryAx` or project axiom.

The first axiom command failed because `PaperII.Extremizer` had not been built
by the aggregator. The attempt is retained, the missing v1.1 modules were built
explicitly, and the repeated axiom gate passed.

## Scope limitation

This report records package construction and local conformance only. The
internal adversarial audit and independent reproduction remain `NOT_STARTED`.
