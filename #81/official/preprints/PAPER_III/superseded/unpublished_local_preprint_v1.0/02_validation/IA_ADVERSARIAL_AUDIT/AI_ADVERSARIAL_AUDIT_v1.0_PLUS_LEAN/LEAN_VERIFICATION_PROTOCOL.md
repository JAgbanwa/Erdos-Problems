# Lean Verification Protocol — Paper III

## Rule

Do not reinstall Mathlib. Do not run `lake exe cache get` unless explicitly authorized by the project owner. Reuse the local Lean/Mathlib state already present on this machine.

## Required Lean checks

From:

`C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\05_formalization\lean_v1.0_freeze`

run:

```powershell
lake build PaperIII
```

Then run independent `#check` and `#print axioms` gates over the public theorem declarations and the two external inputs:

- `PaperIII.AX1`
- `PaperIII.AX2`
- `PaperIII.Theorem_1_1`
- `PaperIII.Corollary_1_2`

Expected interpretation:

- AX1 and AX2 are declared Lean axioms because they represent imported external literature results.
- The audit must verify that every theorem depending on them depends only on the intended external result and standard Lean/Mathlib foundations.
- Closed corridor/effective lemmas must be audited separately for absence of AX1/AX2 in their axiom footprint where the manuscript claims they are unconditional.

## Required evidence

The auditor must deliver:

- full `lake build` stdout/stderr log;
- Lean gate file used for `#check` and `#print axioms`;
- captured Lean gate output;
- source scan for `sorry`, `admit`, `axiom`, and `unsafe`, with AX1/AX2 separately classified;
- table mapping theorem statements to manuscript claims;
- table classifying each major Lean node as `closed`, `depends on AX1`, `depends on AX2`, or `depends on AX1+AX2`;
- literature-scope memo for AX1/AX2.
