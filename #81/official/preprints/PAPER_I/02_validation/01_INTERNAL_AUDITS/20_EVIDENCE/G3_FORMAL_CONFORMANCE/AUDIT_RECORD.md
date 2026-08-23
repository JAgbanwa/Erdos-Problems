# G3 FORMAL CONFORMANCE — Paper I v1.3 audit record

**Verdict:** `PASS`

Read-only source review matches manuscript Theorem 1.1 to
`PaperI.Split.paperI_main_sharp`, with bound
`G.Phi <= (G.n : Real)^2 / 6 + (G.n : Real) / 2`. The companion
`PaperI.paperI_main` is correctly distinguished. The final assembly is
`PaperI.assembly_sharp`, and Proposition B.1 matches
`PaperI.Split.residual_duality`. Stability and centered-Tuza declarations are
classified as interfaces/byproducts rather than hidden premises.

The exact formal archive and its SHA-256 are unchanged from the independently
rebuilt target. This gate reviewed source and dependency conformance only;
Lean was not rerun.

