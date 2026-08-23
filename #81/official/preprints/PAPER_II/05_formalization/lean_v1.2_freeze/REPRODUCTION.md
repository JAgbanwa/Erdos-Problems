# Reproducing the Paper II v1.1 formal freeze

Prerequisites: Git, Elan, and network access for the pinned Mathlib dependency.

From this directory:

```powershell
lake update
lake exe cache get
lake build PaperII PaperII.AsymptoticCorollaries PaperII.AxiomCheckCorollaries PaperII.Extremizer PaperII.CopyDefect Contrib.Submission.Chordal Contrib.Submission.GeodesicChordless
lake env lean FreezeAxioms.lean
```

Expected toolchain: Lean `4.28.0`; expected Mathlib revision:
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` (`v4.28.0`).

The build must exit `0`. The axiom command must list no `sorryAx` or project
axiom. The local preparation split the build into a main command and an
explicit supplement after discovering that the aggregator does not import
`Extremizer`/`CopyDefect`; both successful records and the initial failed axiom
attempt are retained under `gate_logs/` for traceability.
