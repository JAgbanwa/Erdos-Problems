# Internal audit protocol — Paper III v1.3

Status: `EXECUTED_PASS`.  
Normative standard: `../../../../../../INTERNAL_AUDIT_STANDARD_v1.3.md`.  
Audit class: internal / author-side / non-independent.

This run uses the same blocking gates, finding severities, evidence schema and
non-rebuild rule as the completed Paper III v1.2 internal audit. The internal audit
will review the recorded v1.3 build and axiom evidence; it will not rerun the full
Lean build. Clean reconstruction remains an external adversarial gate.

## v1.3-specific mandatory regressions

In addition to G0–G8 of the normative standard, this run must:

1. verify `PaperIII.CanonicalTrianglePacking` as an explicit target;
2. verify that the aggregate root and `PaperIII.PublicAPI` import the canonical module;
3. match the manuscript-side `nu3`, `nu3Star`, and `tau3Star` quantities to the
   Nibble/Yuster encodings through recorded two-sided bridges;
4. query axioms for the canonical bridges and the load-bearing formal surfaces mapped
   to `K-EPS`, `K-CORRIDOR`, `K-SPARSE`, `K-COVER`, and `K-GLOBAL`;
5. distinguish formal-surface coverage from the independent mathematical rederivations
   that the previous external auditor did not perform;
6. incorporate the provenance regressions already required by the common standard;
7. reject any attempt to treat the interrupted preparation stage as a successful build;
   G4 requires a later recorded verification command with exit zero.

The consolidated recorded build, axiom and escape-hatch records, publication artifacts, and
target hashes were complete before execution. All G0–G8 gates passed. The five prior external
kill switches pass internal formal-coverage review but remain assigned to independent
rederivation in the residual external audit.
