# Audit Record — ERDOZ81-P1-PHASE1-01

Audit ID: ERDOZ81-P1-PHASE1-01-AUD-01  
Gate ID: ERDOZ81-P1-PHASE1-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT  
Independence level: NOT_INDEPENDENT  
Auditor: Researcher — auditor role separated from producer pass  
Date: 2026-07-05  
Materials supplied: exact statement, definitions, candidate proof  
Materials withheld: historical manuscript wording during substantive audit  
Protocol version: 1.0  

## Scope

Attempt to refute feasibility or the exact value formula by finding an
uncovered triangle type, an overloaded edge, a bad denominator, or a
double-counting error.

## Claims Checked

PH1-C1 through PH1-C7.

## Adversarial Checks

### A1. Are all triangle types covered?

Since \(I\) is independent, a triangle contains zero or one vertices of
\(I\). A triangle with one such vertex requires two distinct neighbors in
\(K\), hence that vertex lies in \(I_{\ge2}\). No type is omitted.

Verdict: PASS.

### A2. The branch \(\kappa_e=0\)

The definition sets \(\lambda_e=1\), avoiding \(1/0\). Yet no active
vertex has \(e\subseteq N(v)\), so no positive triangle uses that edge and
its load is zero.

Verdict: PASS.

### A3. Threshold point \(\kappa_e=1\)

Both conceptual branches give \(\lambda_e=1\), and the load is exactly one.
The use of \(H=\{\kappa_e\ge1\}\) and \(L=\{\kappa_e<1\}\) is disjoint and
exhaustive.

Verdict: PASS.

### A4. Minimal active degree \(d_v=2\)

For \(N(v)=\{x,y\}\), the two cross edges each lie in one positive triangle
of weight \(\lambda_{xy}\le1\). The clique edge load receives the expected
contribution \(\lambda_{xy}\).

Verdict: PASS.

### A5. Large degree and heterogeneous \(\lambda\)

For a fixed cross edge \(vx\), the load is the arithmetic mean of
\(d_v-1\) numbers \(\lambda_{xy}\in[0,1]\). It cannot exceed one even when
the values are highly nonuniform.

Verdict: PASS.

### A6. Many vertices sharing one clique edge

If many active vertices contain the same clique edge \(e\), then
\(\kappa_e\) may be large. Multiplication by
\(\lambda_e=1/\kappa_e\) caps the total clique-edge load exactly at one.
This does not increase cross-edge loads because \(\lambda_e\le1\).

Verdict: PASS.

### A7. Vertices of degree zero or one

A degree-zero vertex has no cross edge. A degree-one vertex has a cross
edge but belongs to no triangle, so its edge load is zero. No undefined
factor \(1/(d_v-1)\) is used.

Verdict: PASS.

### A8. Small cliques \(p=0,1\)

No active vertex exists and \(w_1=0\).

For \(p=2\), every active vertex has degree two. The single clique edge has
load capped at one; every cross edge has load equal to the same
\(\lambda\le1\).

Verdict: PASS.

### A9. Exact objective accounting

Every positive triangle has exactly one clique edge. Therefore summing
clique-edge loads counts each triangle weight once, not three times. By
contrast, summing all edge loads would count it three times; the proof does
not make that mistake.

Verdict: PASS.

### A10. Attempted counterexample search by symbolic extremization

For a cross edge \(vx\), the only free quantities relevant to its load are
\(\lambda_{xy}\in[0,1]\) over \(d_v-1\) neighbors \(y\). The maximum of

\[
\frac1{d_v-1}\sum_y\lambda_{xy}
\]

over this box is attained when all coordinates equal one, giving exactly
one. Thus no local cross-edge counterexample exists.

Verdict: PASS.

### A11. Hidden assertion of optimality

The gate calls \(w_1\) a feasible packing, not an optimal packing of the
whole graph. The exact formula is for its constructed value only.

Verdict: PASS.

### A12. Residual-capacity sign

On a hot edge \(\kappa_e>1\), the actual residual is zero, not
\(1-\kappa_e<0\). The Gate Record explicitly records

\[
r_e=\max\{1-\kappa_e,0\}.
\]

Any later use of the signed coefficient must justify an exact dual
transformation.

Verdict: PASS WITH FORWARD WARNING.

## Material Objections

None.

## Warnings

- Do not state that every cross edge is saturated; only an upper bound was
  proved.
- Do not state that \(w_1\) is globally optimal.
- Phase II must use nonnegative residual capacities before any dual
  algebra introduces signed coefficients.

## Verdict

`PROVISIONAL_PASS` is supported for the exact gate statement.

The audit is not independent and cannot supply the independent validation
required for a theorem-closing or assembly gate.
