# Validation

- `PAPER_II_CALCULATION_LEDGER_v1.1.md` -- line-by-line calculation ledger of the
  proof (definitions, the vertex-copy inequality, the discrete-convexity lift,
  the terminal complete-split characterization, the two-variable cover program,
  and the integer maximization). Every formula matches the manuscript.
- `PAPER_II_AUDIT/` -- independent per-section computational audits (A-F), each a
  self-contained script that recomputes the section's claims from scratch, with a
  report and SHA-256 manifest.
- `VALIDATION_STATUS.md` -- the validation boundary and status.
- `SHA256SUMS.txt`, `MANIFEST.json` -- integrity of the validation artifacts.

Computation here is corroboration of the analytic proof and the formalization; it
is not its