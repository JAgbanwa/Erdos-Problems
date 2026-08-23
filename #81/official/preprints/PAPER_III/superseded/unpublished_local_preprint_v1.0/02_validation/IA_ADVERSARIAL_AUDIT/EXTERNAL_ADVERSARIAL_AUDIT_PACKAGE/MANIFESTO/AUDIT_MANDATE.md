# Adversarial Audit Mandate — Paper III

## What you are auditing
*Linear-Error Clique Partitions of Split Graphs* (Erdős problem #81, Paper III), final
review version **v0.9.5** (in `CLAIMS/PAPER_v0.9.5/`, English and Spanish). The frozen
specification of every named result is `CLAIMS/LEDGER.md`; the enumerated list of claims
you must attack is `CLAIMS/STATEMENT_OF_CLAIMS.md`.

## Your stance: adversarial
You are **not** asked to confirm the paper. You are asked to **break it**. Assume every
claim is wrong until your own evidence forces you to concede it. A negative finding
(counterexample, gap, mis-citation, overclaim, circular dependency, arithmetic error) is a
**success** of the audit, not a failure. Rubber-stamping is the only outcome that is
unacceptable.

Both positive and negative verdicts must be **earned** with reproducible evidence.

## Scope
**IN scope:**
- The mathematical manuscript v0.9.5: statements, proofs, dependency structure,
  constants, asymptotic orders, and the finite/closed-form claims.
- The two declared external inputs, **AX1** (Theorem 2.1, Haxell–Rödl / Yuster) and
  **AX2** (Theorem 2.3, Dross + Barber–Kühn–Lo–Osthus): whether they are stated
  faithfully to the cited literature and are **not stronger** than what is published.
- Our own internal computational audit (`OUR_INTERNAL_AUDIT/`): reproduce it and try to
  break it. Treat it as a target, not as ground truth.

**OUT of scope (explicitly excluded for this engagement):**
- The Lean 4 / Mathlib formalization. It is **not** included and must **not** be assumed,
  cited, or relied upon. A separate formalization audit will be commissioned later.

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
