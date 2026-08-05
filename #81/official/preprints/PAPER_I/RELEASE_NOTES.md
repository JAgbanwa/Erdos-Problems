# Release notes — preprint v1.0

This is the first official public preprint release of Paper I.

## Included

- publication PDF;
- LaTeX source;
- Markdown source;
- calculation ledger;
- public validation-status record;
- build instructions;
- cryptographic integrity manifest;
- verified Lean 4 formalization of Theorem 1.1 (sorry-free; axiom report reduces to Lean's three standard axioms, with no project-specific axiom).

## Excluded

- superseded manuscript versions;
- private or sealed audit artifacts;
- exploratory computations not used as logical premises;
- legacy Lean files or formalizations not certified against this exact theorem version;
- series-level announcements, which belong at the repository or series level.

## Mathematical scope

The release proves the finite fractional inequality

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n
\]

for split graphs. It does not claim an integral packing theorem, a clique-partition
theorem, an asymptotic transfer result, or a theorem for all chordal graphs.
