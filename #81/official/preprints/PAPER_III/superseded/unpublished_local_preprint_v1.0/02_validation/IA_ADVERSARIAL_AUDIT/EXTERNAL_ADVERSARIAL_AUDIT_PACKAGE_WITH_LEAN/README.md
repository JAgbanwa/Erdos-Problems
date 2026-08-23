# External Adversarial Audit Package — Paper III (LEAN-INCLUSIVE edition)

You have been engaged to perform an **independent, adversarial** audit of *Linear-Error
Clique Partitions of Split Graphs* (Erdős #81, Paper III). This is the **Lean-inclusive**
edition: unlike the draft-version package, the **Lean 4 / Mathlib formalization is IN
scope** (Block F). **The formalization is now FROZEN and sorry-free** at release commit
`fcb49bb25ccc31f44908b8fd2a17a9bb8e678f97` (2026-07-24; `lake build` = 8058 jobs, 0 errors,
0 `sorry`, trusted base = exactly the two Layer-X axioms `AX1`,`AX2`). **Block F is live —
run it in full.** The frozen sources are bundled in `CLAIMS/LEAN_FORMALIZATION/lean_snapshot/`
and independently reproducible from the release commit (see `CLAIMS/LEAN_FORMALIZATION/RELEASE.txt`).

## Start here
1. Read `MANIFESTO/AUDIT_MANDATE.md` — objective, stance, scope (Lean now IN scope).
2. Read `MANIFESTO/EXECUTION_PROTOCOL.md` — **binding** run rules: background execution,
   incremental progress printing (never let a job look hung), and the single new output
   folder that holds ALL results.
3. Read `MANIFESTO/ADVERSARIAL_CHECKLIST.md` — the mandatory attack tasks (Blocks A–**F**).
4. Read `MANIFESTO/DELIVERABLE_SPEC.md` — exactly what you must return and in what shape.
5. Claims: `CLAIMS/STATEMENT_OF_CLAIMS.md`; frozen spec: `CLAIMS/LEDGER.md`; manuscript:
   `CLAIMS/PAPER_v0.9.12/` (EN + ES); Lean: `CLAIMS/LEAN_FORMALIZATION/` (frozen snapshot +
   `RELEASE.txt` + `gate.lean`, Block F).
6. `OUR_INTERNAL_AUDIT/` is a **worked example** of the deliverable shape and also a
   **target** (Block E: break it). Do not reuse its scripts — re-derive.

## Contents
```
README.md                     ← this file
MANIFESTO/
  AUDIT_MANDATE.md            ← objective, adversarial stance, scope (Lean IN scope)
  EXECUTION_PROTOCOL.md       ← MANDATORY: background + incremental progress + new output folder
  ADVERSARIAL_CHECKLIST.md    ← Blocks A–F (F = Lean formalization), mandatory tasks
  DELIVERABLE_SPEC.md         ← required output repo + report format + verdict criteria
CLAIMS/
  PAPER_v0.9.12/              ← review manuscript v0.9.12 (EN + ES, md/tex/pdf, figures)
  LEDGER.md                   ← frozen specification of every named result
  STATEMENT_OF_CLAIMS.md      ← enumerated claim list (C-1 … C-16), AX1/AX2 flagged
  LEAN_FORMALIZATION/         ← FROZEN sorry-free snapshot (lean_snapshot/) + RELEASE.txt +
                                toolchain + lakefile + gate.lean + module map (Block F)
OUR_INTERNAL_AUDIT/           ← our internal computational audit (reference + target)
ENVIRONMENT.md                ← tool versions incl. Lean toolchain; independence guidance
SHA256_MANIFEST.txt           ← SHA-256 of every file in this package
```

## Scope, in one line
Audit the **mathematics**, the **finite/computational evidence**, AND the **Lean 4 /
Mathlib formalization**, adversarially. For Block F: confirm the build is genuinely
sorry-free, the axiom report is exactly what is claimed (Layer E clean; Layer X = only
AX1/AX2), every Lean statement matches its ledger node verbatim, and there is no escape
hatch. A hidden axiom or a `sorryAx` in the chain is a **blocking** finding.

## How to run (see `EXECUTION_PROTOCOL.md`)
- Create **one new output folder** where the operator tells you (default
  `EXTERNAL_AUDIT_RESULT/`); put **all** results inside it; never overwrite a prior run.
- Launch every long script **in the background** and have it **print progress
  incrementally** to `results/<name>_progress.txt` (and flush stdout), so you can monitor
  and nothing looks stuck. Cap expensive computations and log what was skipped.

## What we expect back
`EXTERNAL_AUDIT_RESULT.zip`: one folder per block (A–F) with README + your independent
scripts + written results (incl. progress files) + PDF certificate + zip + SHA, plus
`ADVERSARIAL_AUDIT_REPORT.pdf/.md` with a per-claim table (**including a Lean column**),
an honest coverage statement (naming the exact Lean release commit / toolchain / Mathlib
rev, or marking Block F deferred), and a `SHA256_MANIFEST.txt`.

A well-earned **FAIL** with a counterexample or a localized Lean defect is a successful
audit. So is a well-earned, reproducible **PASS** with an honest coverage boundary. A
rubber stamp is not.
