# Paper III v1.4 — internal E2 residual report

## Verdict

**`PASS_INTERNAL` for the mathematical E2 residual.**

This author-side result closes, at the internal-review level, every item that
the external v1.3 report marked `NOT ATTEMPTED` or `PARTIAL`: `K-EPS`,
`K-CORRIDOR`, `K-SPARSE`, `K-GLOBAL`, and the missing Lemma 7.1 hypothesis
chain.  It does not convert the external verdict to `PASS`; the external
auditor must independently reproduce the derivations.

The audited English manuscript is byte-identical to the external v1.3 target:
SHA-256 `ef410252009f55aa1e0ccbec1873f8d838cf4f9b54e7478befe71459f68440ca`.
Consequently the earlier successful rederivations of Sections 4 and 9 remain
valid regression evidence rather than evidence imported from a changed text.

## Results

| Kernel | Status | Principal evidence |
|---|---|---|
| `K-EPS` | `PASS_INTERNAL` | explicit manuscript absorption argument; complete formal parameter and loss ledger; total coarse-cell coefficient `151/192<1` |
| `K-CORRIDOR` | `PASS_INTERNAL` | independent counting proofs of Lemmas 5.1, 5.2 and 6.1; reconstruction of Lemma 7.1; §9.3 hypotheses closed |
| `K-SPARSE` | `PASS_INTERNAL` | degree threshold, successive matchings, parity correction, mod-3 correction, `p>=125` density threshold, and packing algebra |
| `K-GLOBAL` | `PASS_INTERNAL` | deletion inequality, zero/small-order branches, and strong induction with constant `max(2,N)` |
| exact regression | `PASS` | 315,183 exact checks, zero failures |
| integration with §§4 and 9 | `PASS_REGRESSION` | no changed mathematical source; all input/output inequalities match the previously rederived assembly |

## Independence boundary

The universal derivations in `10_DERIVATIONS` were reconstructed directly
from definitions and displayed claims.  The finite program was written as a
falsifier and uses exact rational/symbolic arithmetic; it is not cited as a
proof of a universal statement.  Formal theorem names are reconciled only
after the mathematical derivations in `00_CONTROL/FORMAL_SURFACE_MAP.md`.

Because this is performed by the author-side team, the epistemic label is
`PASS_INTERNAL`, not `INDEPENDENT_EXTERNAL_PASS`.

## Regression and release consequences

- No manuscript change was required by this internal rederivation.
- No Lean source was changed.
- The slow clean build remains a separate E4 gate and is not implied here.
- The residual external request may reuse the prior §§4 and 9 evidence, but
  must independently audit the four residual derivations and their
  interfaces.

## Acceptance decision

No reversed inequality, uncovered parity, circular parameter choice, or loss
budget overflow was found.  The internal E2 gate is therefore closed.  Paper
III v1.4 as a whole is not yet `PASS`: it still awaits the clean-build result
and the remaining non-E2 editorial/external gates.
