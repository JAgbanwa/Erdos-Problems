# EXTERNAL_AUDIT_RESULT — Paper III (v0.9.5) adversarial audit deliverable

Independent, adversarial audit of *Linear-Error Clique Partitions of Split Graphs*
(Erdős #81, Paper III, review v0.9.5), per the engagement's
`MANIFESTO/{AUDIT_MANDATE,ADVERSARIAL_CHECKLIST,DELIVERABLE_SPEC}.md`.
The Lean 4 / Mathlib formalization is **out of scope** and was not consulted.

**Executive verdict: PASS_WITH_OBSERVATIONS** — see `ADVERSARIAL_AUDIT_REPORT.md`
(§1 verdict, §2 per-claim table, §3 findings, §5 honest coverage statement).

## Layout

```
README.md                          <- this file
ADVERSARIAL_AUDIT_REPORT.md/.pdf   <- the report
ENVIRONMENT.md                     <- tools + independence statement
received_inputs.sha256             <- SHA-256 of the audited package (proof of version)
SHA256_MANIFEST.txt                <- SHA-256 of every delivered file
findings/FINDINGS.csv              <- machine-readable findings (schema per spec)
blockA_faithfulness/               <- paper<->ledger + DAG + external-input census
blockB_external_inputs/            <- AX1/AX2 vs literature
blockC_counterexample_search/      <- C1..C7 attack scripts + results
blockD_algebra_rederivation/       <- 38 algebra checks, no CAS
blockE_audit_the_audit/            <- reproduction, script defects, boundary stress
block*.zip (+ .sha256)             <- per-block archives
```

## Reproduce everything

See `ADVERSARIAL_AUDIT_REPORT.md` §7 (one command per script; deterministic seeds;
every script writes its log under its block's `results/` and exits nonzero on failure).
Tool versions in `ENVIRONMENT.md`.

## Independence

No verdict in this deliverable depends on the internal audit's tooling: exact
rational certificates replace their float LP; a self-written polynomial engine
replaces SymPy; pure-integer grids replace their Fraction loops; a self-written
branch-and-bound and explicit verified packings replace CBC (which is used only as a
cross-validated *target* in Block E).
