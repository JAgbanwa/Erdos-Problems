# E3 -- formal statement conformance and model equivalence

**Verdict: `PASS`.**

The request forbids settling this by compiling the target's lemmas, and asks for comparison
against an auditor-constructed bridge. `scripts/AuditorE3.lean` does exactly that: it restates
the manuscript forms from the manuscript text, proves them with the auditor's own arguments,
and only then asserts the target's statements and discharges them with those proofs. Exit 0,
every declaration `[propext, Classical.choice, Quot.sound]`.

The substantive content of the auditor's bridge: the two fractional-packing predicates differ
in their capacity quantifier -- PaperIII imposes capacities on `H.edgeFinset`, the Nibble side
on **every** two-element vertex set, including non-edges. The extra constraints are vacuous
because a 3-clique containing both ends of a pair forces those ends adjacent
(`auditor_no_clique_contains_nonedge`). Hence the feasible sets coincide, hence the optima, and
with the target's weak duality and its finite LP strong-duality instantiation,
`tau3Star = nu3Star` at PaperIII's own names.

AX1 conformance is an **`iff`**, proved in both directions, which is what rules out a
one-directional weakening: `AX1Assumption <-> ManuscriptAX1`. AX2 is an implication with both
coercions checked explicitly (`0.9` against `9/10`, `3 divides card` against `card % 3 = 0`).
`HasTriangleDecomposition` unfolds by `Iff.rfl` to an exact edge decomposition into 3-cliques,
whose uniqueness clause forces edge-disjointness without a separate hypothesis.

No inequality direction or feasibility condition is lost at any manuscript/Lean interface, and
`nu3` and `nu3Star` refer to the intended objects throughout.

The claim map from manuscript Theorem 1.1 to `PaperIII.Theorem_1_1` is in the final report,
Section 5, with every compiled statement quoted verbatim.

Evidence: `scripts/AuditorE3.lean`, `results/08_AuditorE3.log`.
