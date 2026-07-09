# Audit Record

Audit ID: ERDOZ81-P1-LOAD-01-AUD-01  
Gate ID: ERDOZ81-P1-LOAD-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT  
Independence level: same model, separated producer and auditor roles  
Auditor: Researcher  
Date: 2026-07-05  
Materials supplied: exact statement, Definition Registry v0.1, candidate proof  
Materials withheld: historical proof wording from the manuscript during the substantive check  
Protocol version: 1.0  

## Scope

Attempt to reject the aggregate load identity and identify hidden domain assumptions or accounting errors.

## Claims Checked

LOAD-C1 through LOAD-C4.

## Adversarial Checks

### A1. Denominator check

A summand occurs only for \(v\in I_{\ge2}\). Therefore \(d_v-1\ge1\).
No division by zero occurs.

Verdict: PASS.

### A2. Empty case

If \(I_{\ge2}=\varnothing\), then every \(\kappa_e=0\), and both sides are zero.

Verdict: PASS.

### A3. Small clique cases

If \(p<2\), then \(E(K)=\varnothing\). A vertex of \(I\) cannot have degree
at least two into \(K\), so \(I_{\ge2}=\varnothing\). Both sides are zero.

If \(p=2\), every \(v\in I_{\ge2}\) has \(d_v=2\) and contributes \(1\)
to the unique clique edge. The left side is \(|I_{\ge2}|\), while the
right side is \(\frac12(2|I_{\ge2}|)=|I_{\ge2}|\).

Verdict: PASS.

### A4. Minimal nonempty profile

One vertex with \(d_v=2\) contributes

\[
\binom22/(2-1)=1=d_v/2.
\]

Verdict: PASS.

### A5. Universal neighborhood

For one vertex with \(N(v)=K\) and \(d_v=p\ge2\), each of the
\(\binom p2\) clique edges receives \(1/(p-1)\). The total is

\[
\binom p2/(p-1)=p/2=d_v/2.
\]

Verdict: PASS.

### A6. Overlapping neighborhoods

Take two vertices \(u,v\) with overlapping or identical neighborhoods.
The definition of \(\kappa_e\) adds their contributions separately.
Regrouping the finite double sum counts each pair \((v,e)\) exactly once;
overlap does not merge or duplicate any incidence pair.

Verdict: PASS.

### A7. Split-presentation dependence

Changing the split presentation may change the data \(K,I,d_v,\kappa\).
The gate does not assert invariance under such a change; it asserts the
identity for any fixed chosen presentation.

Verdict: PASS with scope warning.

### A8. Notational attack on \(b_{\ge2}\)

The subscript could be misread as cardinality. Definition Registry v0.1
defines it as a degree sum. The proof and gate now repeat that definition.

Verdict: PASS after explicit clarification.

### A9. Quantifier and finiteness check

The regrouping uses finiteness. The graph convention supplies this
hypothesis. No infinite-sum theorem is being used implicitly.

Verdict: PASS.

### A10. Stronger conclusions not proved

The identity does not imply \(\kappa_e\le1\) for each edge, nor does it
imply phase-I feasibility. The proof does not make either inference.

Verdict: PASS.

## Findings

No mathematical defect found.

One material notation risk was contained: \(b_{\ge2}\) is the degree sum,
not \(|I_{\ge2}|\).

## Material Objections

None active.

## Exclusions

- independent audit;
- phase-I cross-edge feasibility;
- LP duality;
- external quantitative bounds.

## Verdict

`PASS` for the internal adversarial audit of statement version 0.1.

This audit supports `PROVISIONAL_PASS`, not `FINAL_PASS`, because it is not independent and the definition dependency remains provisional.

## Required Actions

- Preserve the exact definition of \(b_{\ge2}\).
- Do not use this identity to infer coordinatewise bounds.
- Reassess dependency health after ERDOZ81-P1-DEF-01 changes state.

## Unresolved Dissent

None.
