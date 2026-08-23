# Audit Record

Audit ID: ERDOZ81-P1-FRAC-THM-01-AUD-CC-001  
Gate ID: ERDOZ81-P1-FRAC-THM-01  
Statement version: 0.2  
Audit type: CLEAN_CONTEXT_AUDIT  
Independence level: Same agent, fresh audit pass with exploratory narrative withheld; not independent review  
Auditor: Researcher  
Date: 2026-07-05  
Protocol version: 1.0

## Materials supplied

- Exact theorem statement in Gate Record version 0.2.
- Definition Registry version 0.1.
- Candidate proof `FRACTIONAL_THEOREM_PROOF_v0.2.md`.
- Proof-critical upstream proof records:
  - Phase-I feasibility and value v0.1.
  - Internal Farkas/strong-duality proof v0.2.
  - Phase-II exact dual reduction v0.2.
  - Fixed-polytope concavity v0.1.
  - Affine profile reduction v0.1.
  - Zero-active-mass branch v0.1.
  - Pure-profile symmetrization v0.1.
  - Exact orbit program v0.1.
  - Exact orbit solution v0.1.
  - Quantitative envelope proof v0.1.
- Current dependency graph and loss ledger.

## Materials withheld

- The exploratory conversation and route-development narrative.
- Historical superseded proof versions, except where needed to check statement identity.
- Prior self-audit conclusions as authority.
- The future integral/asymptotic transfer material, which is outside this gate.

## Scope

Attempt to reject the finite fractional theorem

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n
\]

for every finite split graph \(G\), by checking the proof-critical chain rather than merely restating the final proof.

## Claims checked

1. Phase-I feasibility on clique and cross edges.
2. Exact value of Phase I.
3. Strong duality for the finite residual triangle LP.
4. Exact signed transformation from residual capacities to \(M(\kappa)\).
5. Aggregate-load identity and exact deficit identity.
6. Concavity and reduction to pure neighborhood profiles.
7. Separation of the \(q=0\) branch.
8. Symmetrization and exact orbit-program equivalence.
9. Exhaustive solution of every orbit regime, including \(s=2\).
10. Algebraic comparisons of \(U,D,H\) with \(R(p,q)\).
11. Final parameter conversion and loss accounting.
12. Absence of external proof-critical dependencies.

## Methods

- Line-by-line algebra and sign checking.
- Quantifier and domain review.
- Independent reconstruction of the key deficit identity.
- Case analysis for \(q=0\), \(s=2\), and \(o=0,1,2,\ge3\).
- Verification of the endpoint minimizations in the orbit program.
- Symbolic re-expansion of the formulas for \(U-R\), \(D-R\), \(H-R\), and the final normalization identity.
- Search for circular dependencies and hidden uses of global optimality.
- Review of the loss ledger for double charging.

## Findings

### F1 — Phase-I construction

The construction is feasible. Clique-edge loads are exactly
\(\min\{\kappa_e,1\}\); cross-edge loads are at most one. Every positive
Phase-I triangle contains exactly one clique edge, so the value identity is
correct.

Verdict: CONFIRMED.

### F2 — Internal strong duality

The specialized Farkas proof is logically complete in finite dimension.
The finitely generated cone is shown closed; nearest-point separation yields
the stated alternative; the multiplier used for normalization is proved
strictly positive. Capping dual coordinates in \([0,1]\) preserves feasibility
and supplies compactness for the limiting argument.

Verdict: CONFIRMED.

### F3 — Exact Phase-II and deficit identity

The signed extension over hot edges is valid because their coefficients are
nonpositive and setting the corresponding \(y_e\) to zero preserves
feasibility. The reconstructed equality is

\[
\nu_{\mathrm{con}}=\frac{b_{\ge2}}2+M(\kappa)
\]

and hence

\[
|E(G)|-2\nu_{\mathrm{con}}
=\binom p2-2M(\kappa)+b_1.
\]

No cross-edge capacity is reused by Phase II, because Phase-II triangles lie
entirely in \(K\).

Verdict: CONFIRMED.

### F4 — Profile reduction

For \(q>0\), the aggregate load vector is a convex combination of pure
profiles with the same \(q\). The direction of concavity is correct:

\[
M(\kappa)\ge\sum_S\lambda_SM(\kappa^S).
\]

The \(q=0\) case is not normalized and is handled separately.

Verdict: CONFIRMED.

### F5 — Orbit reduction and solution

The stabilizer averaging preserves both feasibility and objective value.
The orbit program includes exactly the triangle types that exist. The solution
minimizes over all feasible points, not only the named candidates. The
exceptional interval \(0\le\alpha<1/3\) when \(s=2\) cannot create a new
minimum.

Verdict: CONFIRMED.

### F6 — Quantitative envelope

The corrected formula is

\[
12(U-R)=q(2o+q)-2p.
\]

The bounds

\[
U-R\ge-p/6,\qquad D-R\ge-p/2,\qquad H-R\ge-p/2
\]

follow with the stated domains. The branch \(q=0\) is valid, including
\(p\le2\).

Verdict: CONFIRMED.

### F7 — Final assembly and losses

The exact normalization

\[
\binom p2-2R(p,q)+p
=\frac{(p+q)^2}{6}+\frac p2
\]

is correct. Since \(n=p+q+b_1+b_0\),

\[
p+q\le n,\qquad p/2+b_1\le n.
\]

The envelope loss \(p/2\) and the exact degree-one term \(b_1\) are charged
once. The final replacement of \(\nu_{\mathrm{con}}\) by \(\nu_3^*(G)\)
has the correct inequality direction.

Verdict: CONFIRMED.

## Material objections

None found.

## Non-material observations

1. Several upstream artifacts remain at admission level `CANDIDATE`.
2. The dependency graph is historically cumulative and should eventually be
   normalized into a single authoritative edge list for the Assembly Gate.
3. This clean-context pass was performed by the same agent that produced the
   proof. It reduces narrative anchoring but is not an independent audit.
4. The theorem statement is independent of the chosen split presentation,
   while the intermediate parameters are presentation-dependent; the proof
   is valid for any fixed presentation.

## Exclusions

- No claim about integral triangle packings or clique partitions was audited.
- No novelty claim was assessed.
- No Lean formalization was performed.
- No human-expert or peer review occurred.

## Verdict

`CONFIRM_PROVISIONAL_PASS`

The candidate proof survives the clean-context adversarial audit. The
appropriate validation event is `CLEAN_CONTEXT_AUDITED`, not
`INDEPENDENTLY_AUDITED`.

The gate must remain:

- Mathematical status: `PROVISIONAL_PASS`;
- Lifecycle: `ACTIVE`;
- Dependency health: `UNVERIFIED`;

until upstream evidence is admitted, an Assembly Gate is completed, and the
T3 independence requirement is satisfied.

## Required actions

1. Build the formal Assembly Gate with exact authoritative component versions.
2. Normalize and verify all proof-critical dependency edges and evidence
   admission states.
3. Obtain an independent or human-expert audit before promotion to `PASS`.

## Unresolved dissent

None within this audit. The absence of dissent does not substitute for an
independent reviewer.
