# Reproducing the Paper I v1.2 corrective freeze

Prerequisites: Git, Elan, and network access for the pinned Mathlib dependency.
Use a short clean-room path on Windows and enable Git long paths when required.

```text
git config --global core.longpaths true
lake update
lake exe cache get
lake build PaperI.PaperI_Statement PaperI.PaperI_Arith FiniteLPDuality Contrib.PaperISharp Contrib.LpStability Contrib.TuzaSplitCentered Contrib.Submission.FarkasLP Contrib.Submission.FgConeClosed
lake env lean FreezeAxioms.lean
```

Expected toolchain: Lean `4.28.0`; expected Mathlib revision:
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

The archive contains no `.lake` directory. A reproducer must extract it into an
empty directory and retain complete stdout/stderr and exit codes.
