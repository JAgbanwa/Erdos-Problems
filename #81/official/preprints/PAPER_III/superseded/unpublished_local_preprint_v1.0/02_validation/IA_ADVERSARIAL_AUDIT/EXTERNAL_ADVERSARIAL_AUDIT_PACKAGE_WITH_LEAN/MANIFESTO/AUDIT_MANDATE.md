# Adversarial Audit Mandate — Paper III

## What you are auditing
*Linear-Error Clique Partitions of Split Graphs* (Erdős problem #81, Paper III), editorial
review version **v0.9.12** (in `CLAIMS/PAPER_v0.9.12/`, English and Spanish). The frozen
specification of every named result is `CLAIMS/LEDGER.md`; the enumerated list of claims
you must attack is `CLAIMS/STATEMENT_OF_CLAIMS.md`.

## Your stance: adversarial
You are **not** asked to confirm the paper. You are asked to **break it**. Assume every
claim is wrong until your own evidence forces you to concede it. A negative finding
(counterexample, gap, mis-citation, overclaim, circular dependency, arithmetic error) is a
**success** of the audit, not a failure. Rubber-stamping is the only outcome that is
unacceptable.

Both positive and negative verdicts must be **earned** with reproducible evidence.

## Scope — this package INCLUDES the Lean formalization audit
This is the **Lean-inclusive** edition of the audit package. The Lean 4 / Mathlib
formalization **is complete and FROZEN**: sorry-free build (8058 jobs, 0 errors, 0 `sorry`)
at release commit `fcb49bb25ccc31f44908b8fd2a17a9bb8e678f97` (2026-07-24), trusted base =
exactly the two Layer-X axioms `AX1`,`AX2`. **Run Block F in full** against the frozen
snapshot in `CLAIMS/LEAN_FORMALIZATION/` (see its `RELEASE.txt` and `README.md`). Do not
defer it.

**IN scope:**
- The mathematical manuscript: statements, proofs, dependency structure, constants,
  asymptotic orders, and the finite/closed-form claims.
- The two declared external inputs, **AX1** (Theorem 2.1, Haxell–Rödl / Yuster) and
  **AX2** (Theorem 2.3, Dross + Barber–Kühn–Lo–Osthus): whether they are stated
  faithfully to the cited literature and are **not stronger** than what is published.
- Our own internal computational audit (`OUR_INTERNAL_AUDIT/`): reproduce it and try to
  break it. Treat it as a target, not as ground truth.
- **The Lean 4 / Mathlib formalization (Block F) — NOW IN SCOPE.** Reconstruct the
  sources from the git object at the frozen release commit (see
  `CLAIMS/LEAN_FORMALIZATION/README.md`), build with the pinned toolchain, and audit:
  the build is genuinely sorry-free; the axiom report is exactly what is claimed
  (Layer E = `{propext, Classical.choice, Quot.sound}`; Layer X results additionally
  and *only* `AX1`, `AX2`); every Lean statement matches its ledger node verbatim; the
  two `axiom`s are the ledger's AX1/AX2 and no stronger; no escape hatch
  (`sorry`, `admit`, `native_decide` as a proof, `unsafe`, `opaque`, `implemented_by`).
  A hidden extra axiom or a `sorryAx` in the chain is a **blocking** finding.

## Execution rules (binding)
Follow `MANIFESTO/EXECUTION_PROTOCOL.md` for **every** script: run long jobs in the
background, print progress incrementally to a progress file (never let a job look hung),
cap and log expensive computations, and write **all** outputs into a single **new**
output folder created where the operator instructs (nothing outside it).

## What "correct" would mean here
- **Theorem 1.1** (main): there is an absolute constant `C` with `Φ(G) ≤ n²/6 + C·n` for
  every split graph `G`. This is **relative to** AX1 and AX2 (bulk and sparse regimes).
- **Proposition 10.1** (effective corridor): explicit, **unconditional** bounds
  (`Φ ≤ n²/6 + 2n` for `p≥36, 0≤s≤6√p`; `Φ ≤ n²/6` for `p≥2304, 6√p≤s≤p/8` under the
  stated degree condition) — no external input.
- **Corollary 1.2**: the same linear-error bound for `cp(G)`.
- The finite closed forms (F of Theorem 3.1; the margin of Theorem 4.2; Lemma 5.1 etc.)
  hold exactly on their stated ranges.

Your job is to test each of these against reproducible evidence and report a verdict.

## Deliverable (summary; full spec in `DELIVERABLE_SPEC.md`)
A self-contained repository mirroring the structure of `OUR_INTERNAL_AUDIT/`: one
subfolder per audited block with a README, your **own independent** scripts, their written
outputs, and a per-block PDF certificate; plus a top-level
`ADVERSARIAL_AUDIT_REPORT.pdf`/`.md` with a per-claim verdict and an honest coverage
statement, and a `SHA256_MANIFEST.txt` of everything you produce.

## Ground rules
- Independence: prefer tools/methods **different** from ours (e.g. an exact rational
  simplex or a different CAS/ILP solver) so agreement is corroborating, not shared-bug.
- Reproducibility: every numeric claim must be regenerable by running your scripts; every
  script must write its full output to a file and return a non-zero exit code on failure.
- Honesty of coverage: state precisely what you checked, at what ranges, and what you did
  **not** check. Do not imply coverage you did not achieve.
- No appeal to authority: "the paper says" or "the internal audit says" is not evidence.
