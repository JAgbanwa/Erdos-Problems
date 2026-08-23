# External Adversarial Audit Package — Paper III

You have been engaged to perform an **independent, adversarial** audit of *Linear-Error
Clique Partitions of Split Graphs* (Erdős #81, Paper III), review version v0.9.5.

## Start here
1. Read `MANIFESTO/AUDIT_MANDATE.md` — your objective, stance, and scope.
2. Read `MANIFESTO/ADVERSARIAL_CHECKLIST.md` — the mandatory attack tasks (Blocks A–E).
3. Read `MANIFESTO/DELIVERABLE_SPEC.md` — exactly what you must return and in what shape.
4. The claims to attack are enumerated in `CLAIMS/STATEMENT_OF_CLAIMS.md`; the frozen
   spec is `CLAIMS/LEDGER.md`; the manuscript is in `CLAIMS/PAPER_v0.9.5/` (EN + ES).
5. `OUR_INTERNAL_AUDIT/` is a **worked example** of the expected deliverable shape and
   also a **target** (Block E: break it). Do not reuse its scripts — re-derive.

## Contents
```
README.md                     ← this file
MANIFESTO/
  AUDIT_MANDATE.md            ← objective, adversarial stance, scope (Lean OUT of scope)
  ADVERSARIAL_CHECKLIST.md    ← Blocks A–E, mandatory tasks
  DELIVERABLE_SPEC.md         ← required output repo + report format + verdict criteria
CLAIMS/
  PAPER_v0.9.5/               ← final review manuscript (EN + ES, md/tex/pdf, figures)
  LEDGER.md                   ← frozen specification of every named result
  STATEMENT_OF_CLAIMS.md      ← enumerated claim list (C-1 … C-16), AX1/AX2 flagged
OUR_INTERNAL_AUDIT/           ← our internal computational audit (reference + target)
ENVIRONMENT.md                ← tool versions; independence guidance
SHA256_MANIFEST.txt           ← SHA-256 of every file in this package
```

## Scope, in one line
Audit the **mathematics** and the **finite/computational evidence**, adversarially.
The Lean 4 / Mathlib formalization is **explicitly out of scope** for this engagement
(a separate formalization audit will be commissioned later). Assume nothing from it.

## What we expect back
`EXTERNAL_AUDIT_RESULT.zip`: a repository mirroring `OUR_INTERNAL_AUDIT/` (one folder per
block with README + your independent scripts + written results + PDF certificate + zip +
SHA), plus `ADVERSARIAL_AUDIT_REPORT.pdf/.md` with a per-claim verdict and an honest
coverage statement, and a `SHA256_MANIFEST.txt`. See `MANIFESTO/DELIVERABLE_SPEC.md`.

A well-earned **FAIL** with a counterexample is a successful audit. So is a well-earned,
reproducible **PASS** with an honest coverage boundary. A rubber stamp is not.
