# Paper III v1.3 — draft changelog

Baseline: unpublished Paper III v1.2 draft package.

## Formalization

- Added `PaperIII.CanonicalTrianglePacking` as the manuscript-facing canonical interface.
- Proved the equality of the integral packing implementations.
- Proved equivalence of the two fractional feasible-set presentations.
- Proved `PaperIII.nu3Star = Nibble.YusterE.nu3star`.
- Proved finite-LP identification `PaperIII.tau3Star = PaperIII.nu3Star`.
- Exposed AX1 in the packing-side form used in the manuscript.
- Added a dedicated statement and axiom gate.
- Imported the canonical module from the aggregate root and `PaperIII.PublicAPI`.

## Mathematical content

No theorem statement, hypothesis, constant, proof branch, or asymptotic conclusion is
changed.

## Release state

The complete target set has a recorded 8,719-job build with exit code 0. Eight axiom-query
files pass with foundational-only footprints for the canonical release surfaces. The
formal source freeze and SHA-256 seal are complete. Manuscript artifact regeneration and
QA and the G0–G8 internal audit pass. Independent reproduction, external audit, and public
release remain open.

## Internal-audit corrections and closure

- Replaced the potentially overbroad “resolves the split-graph case” wording by the precise
  statement that the paper determines the sharp quadratic coefficient and establishes the
  `n^2/6+O(n)` scale.
- Normalized `A_{2J}` and synchronized `[3,8]` and `[11,17]` across English and Spanish.
- Regenerated and visually checked the complete Markdown → LaTeX → PDF chain.
- Completed the common G0–G8 internal audit with 133/133 static/formal/artifact controls and
  fresh non-Lean mathematical regressions passing.
- Recorded explicit internal coverage and external residual work for the five previously
  untested kill switches.
