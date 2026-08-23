# Audit Record — Exact orbit program by existence regime

Audit ID: ERDOZ81-P1-3ORBIT-01-AUD-001  
Gate ID: ERDOZ81-P1-3ORBIT-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT  
Independence level: Same agent, separated producer and auditor roles  
Auditor: Researcher (auditor role)  
Date: 2026-07-05  
Protocol version: 1.0

## Scope

Attempt to reject the claimed equivalence between the invariant
fixed-polytope problem and the regime-specific orbit linear programs.

## Materials supplied

- Gate statement.
- Candidate proof `EXACT_ORBIT_PROGRAM_PROOF_v0.1.md`.
- Definitions and prior Gate Records through
  `ERDOZ81-P1-SYMMETRY-01`.

## Claims checked

1. Edge-orbit classification is exhaustive.
2. Triangle-type classification is exhaustive.
3. Existence conditions are exact.
4. No constraint is imposed for a nonexistent triangle type.
5. No existing triangle constraint is omitted.
6. Objective coefficients and orbit multiplicities are correct.
7. Both directions of equivalence hold.
8. Boundary regimes \(o=0,1,2\) and \(s=2\) are correctly separated.
9. Negative \(SS\)-coefficient does not invalidate equivalence.

## Adversarial checks

### A. Edge-orbit exhaustion

For a two-part partition \(K=S\sqcup O\), an edge has exactly one of the
endpoint patterns \(SS,SO,OO\). The classification is exhaustive and
disjoint.

### B. Triangle-type exhaustion

A triangle has \(0,1,2,\) or \(3\) vertices in \(S\), producing exactly
\(OOO,SOO,SSO,SSS\). No fifth type exists.

### C. Minimal cases

- \(p=s=2,o=0\): one \(SS\) edge, no triangle. The feasible interval is
  \(0\le\alpha\le1\); imposing \(3\alpha\ge1\) would be false.
- \(s=2,o=1\): one triangle of type \(SSO\). The only triangle inequality
  is \(\alpha+2\beta\ge1\).
- \(s=2,o=2\): triangle types \(SSO\) and \(SOO\) exist; neither \(SSS\)
  nor \(OOO\) exists.
- \(s=3,o=0\): only type \(SSS\), giving exactly \(3\alpha\ge1\).
- \(s=2,o=3\): types \(SSO,SOO,OOO\) exist, but \(SSS\) does not.

These cases agree with the regime table.

### D. Objective multiplicities

- \(SS\): \(\binom s2\) edges, coefficient
  \(1-q/(s-1)\).
- \(SO\): \(so\) edges, coefficient \(1\).
- \(OO\): \(\binom o2\) edges, coefficient \(1\).

The coefficient simplification

\[
\binom s2\left(1-\frac q{s-1}\right)
=\frac{s(s-1-q)}2
\]

is correct because \(s\ge2\).

### E. Negative coefficient stress test

When \(q>s-1\), \(A_{s,q}<0\). The equivalence proof groups equal
coordinates and does not use monotonicity of the objective. A negative
coefficient may affect the optimizer but not the reduction.

### F. Reverse-direction completeness

Given orbit variables, every edge receives one value and every triangle is
covered by the constraint for its unique type. This establishes all
triangle inequalities, not merely representatives, because the assigned
vector is constant on edge orbits.

### G. Box constraints

The original polytope includes \(0\le z_e\le1\). Therefore every existing
orbit variable requires both lower and upper bounds. The candidate proof
includes them in every regime.

### H. Potential hidden issue: empty variable with written coefficient

The proof explicitly omits terms for absent orbits. It does not use dummy
variables whose unconstrained values could alter the optimum.

### I. Potential hidden issue: \(q=0\)

The gate assumes \(q>0\), exactly matching the pure-profile normalization
branch. The separate gate `ERDOZ81-P1-Q0-01` handles \(q=0\).

## Findings

No mathematical counterexample was found.

The observation from the previous iteration is resolved: the exact program
must be indexed by existence regimes. The corrected formulation is neither
a relaxation nor a strengthening of the invariant problem.

## Material objections

None against the local equivalence proof.

## Dependency objection

The conclusion still inherits unverified upstream dependencies, notably
the incomplete finite-LP strong-duality certificate used in
`ERDOZ81-P1-PHASE2-DUAL-01`. This prevents a clean downstream dependency
status.

## Verdict

`PROVISIONAL_PASS`.

The gate is self-audited and locally complete, but not independently
audited and not dependency-clean.

## Required actions

1. Use only these corrected regime-specific programs in the solution gate.
2. Do not reinstate nonexistent triangle constraints for convenience.
3. Preserve the \(s=2\) split throughout optimization.
4. Complete the upstream LP-duality certificate before final promotion.
