# Audit Record — ERDOZ81-P1-DEF-01

Audit ID: ERDOZ81-P1-DEF-01-AUD-01
Gate ID: ERDOZ81-P1-DEF-01
Statement version: 0.1
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT
Independence level: NOT_INDEPENDENT
Auditor: Researcher — auditor role, separated from producer pass
Date: 2026-07-05
Materials supplied: Gate candidate, Definition Registry v0.1, proof candidate
Materials withheld: historical proof narrative during line-by-line audit
Protocol version: 1.0

## Scope

Attempt to reject the foundational definitions or expose missing domains, inconsistent notation, hidden assumptions, or invalid existence claims.

## Adversarial checks

### A1. Non-unique split presentations

A graph may admit multiple split presentations. The definitions bind all parameters to a chosen ordered presentation and do not claim presentation invariance.

Verdict: PASS.

### A2. Cases \(p=0,1,2\)

- For \(p=0,1\), the clique-edge coordinate set is empty.
- For \(p=2\), one clique edge exists but no clique triangle exists.
- The definition \(\mathcal P_p=[0,1]^{E(K_p)}\) in these cases follows from vacuous triangle constraints.

Verdict: PASS.

### A3. Case \(q=0\)

The aggregate neighborhood profile may have zero total mass. The registry prohibits normalization unless the mass is positive.

Verdict: PASS.

### A4. Degrees \(0\) and \(1\)

The type vector \(a^S\) is defined only for \(|S|\ge2\), matching the future denominator \(|S|-1\). Vertices of degree \(0\) and \(1\) are recorded separately and are not silently inserted into the profile sum.

Verdict: PASS.

### A5. Fractional packing boundedness

The candidate proof says each triangle variable is at most one. For any triangle \(T\), selecting any one of its three edges gives

\[
w(T)\le\sum_{T'\ni e}w(T')\le1.
\]

Thus boundedness is valid.

Verdict: PASS.

### A6. Upper bounds \(z_e\le1\)

These upper bounds are part of the declared polytope. The audit does not assume they follow from triangle-cover inequalities. Their later use in Lipschitz estimates is therefore legitimate if this same polytope remains authoritative.

Verdict: PASS, with dependency warning: later duality must prove that imposing the cap does not alter the relevant dual optimum.

### A7. Baseline signs

The definition allows arbitrary real \(b\) and \(\kappa\). Compactness makes the minimum finite even if coefficients are negative.

Verdict: PASS.

### A8. Ambiguity of \(K\)

The same symbol can denote the clique vertex set and the induced clique graph. The registry resolves formulas through \(K_p\) for abstract edge-coordinate objects and through \(K\) for the selected vertex class. This is usable but should be monitored.

Verdict: PASS WITH NOTATION WARNING.

### A9. Small falsification instances

Checked directly:

- empty graph with \(p=0\);
- one isolated clique vertex with \(p=1\);
- \(K_2\) with \(p=2\);
- \(K_3\) with \(I=\varnothing\);
- one independent vertex of degree \(0\);
- one independent vertex of degree \(1\);
- one independent vertex of degree \(2\).

All counting and domain statements agree with the definitions.

Verdict: NO COUNTEREXAMPLE.

## Material objections

None.

## Non-material warnings

1. Later dual reduction must separately justify coordinate capping at one.
2. Later profile reduction must branch explicitly on \(q=0\).
3. Later claims must not assume the chosen split presentation is canonical.
4. Notation \(K\) versus \(K_p\) should remain controlled.

## Audit verdict

`PASS_FOR_CURRENT_SCOPE`.

This is a self-audit, not independent validation. It supports a provisional gate decision but does not authorize downstream mathematical claims beyond foundational well-definedness.
