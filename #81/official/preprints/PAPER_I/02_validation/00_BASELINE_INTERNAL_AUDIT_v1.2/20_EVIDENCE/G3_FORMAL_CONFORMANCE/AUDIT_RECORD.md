# G3 FORMAL-CONFORMANCE -- Paper I audit record

**Verdict:** `PASS`

Static source review matched manuscript Theorem 1.1 to
`PaperI.Split.paperI_main_sharp`:

```text
G.Phi <= (G.n : Real)^2 / 6 + (G.n : Real) / 2
```

The companion `PaperI.paperI_main` has the weaker additive term `n` and is
correctly distinguished from the headline theorem. The sharp assembly is
`PaperI.assembly_sharp`; its side condition `1 <= b1 -> 1 <= p` matches
the degree-one argument in Section 8. Proposition B.1 matches the finite
covering/packing duality surface `PaperI.Split.residual_duality`. Stability and centered-Tuza declarations are
classified as interfaces/byproducts, not hidden premises of Theorem 1.1.

This was a source and dependency review only; Lean was not rerun.
