# Audit Record

Audit ID: ERDOZ81-P1-PHASE2-DUAL-01-AUDIT-001  
Gate ID: ERDOZ81-P1-PHASE2-DUAL-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / internal adversarial audit  
Independence level: Same agent, role-separated pass  
Auditor: Researcher — auditor role  
Date: 2026-07-05  
Materials supplied: exact gate statement, dependency Gate Records, candidate proof  
Materials withheld: historical manuscript narrative except for architecture comparison  
Protocol version: 1.0  

## Scope

Attempt to reject the Phase-II primal/dual formulation and every algebraic transformation leading to the signed fixed-polytope identity.

## Checks performed

### 1. Residual-capacity sign check

Verified that actual residual capacities are

\[
r_e=\max\{1-\kappa_e,0\}\ge0.
\]

The signed coefficient \(1-\kappa_e\) is introduced only after dualization and an exact objective-extension argument. The proof does not treat a negative number as a capacity.

Verdict: PASS.

### 2. Primal completeness

Every Phase-II triangle lies entirely in \(K\), because Phase I is fixed and Phase II is defined to add only clique triangles. Each such triangle consumes one unit of its weight on each of its three clique edges.

Verdict: PASS for the stated Phase-II construction. No claim of global optimality is made.

### 3. Dual derivation

The coefficient of each dual variable is the corresponding nonnegative residual capacity, and each primal triangle creates the constraint \(x(T)\ge1\).

Verdict: algebraically PASS; theorem invocation remains UNVERIFIED pending certificate.

### 4. Capping challenge

Potential defect: capping a coordinate above one might destroy a triangle-cover constraint.

Rejection attempt: if a capped coordinate was above one, it becomes exactly one and alone satisfies every incident triangle. If no coordinate exceeds one, the triangle sum is unchanged.

Verdict: PASS.

### 5. Zero-cost hot coordinates

Potential defect: because hot-edge dual variables have zero objective coefficient, unbounded coordinates might invalidate the change of variables.

Resolution: capping produces an equally good feasible solution in \([0,1]^{E(K)}\). Thus \(y=1-x\) is legitimate.

Verdict: PASS.

### 6. Signed-extension challenge

Potential defect: adding negative coefficients on hot edges could change the maximum.

For any feasible \(y\), setting hot coordinates to zero preserves feasibility because all constraints are upper bounds. It weakly increases the signed objective. Hence an optimizer has \(y_H=0\).

Boundary \(\kappa_e=1\): coefficient zero, so either value is immaterial.

Verdict: PASS.

### 7. Polytope mapping

Checked bijection

\[
x\in[0,1],\ x(T)\ge1
\leftrightarrow
y=1-x\in[0,1],\ y(T)\le2
\leftrightarrow
z=1-y=x\in\mathcal P_p.
\]

Observation: numerically \(z=x\). The two substitutions are retained because the \(y\)-maximization explains the signed extension.

Verdict: PASS.

### 8. Degenerate clique sizes

For \(p<3\), there are no triangle constraints.

- The Phase-II primal has no variables and value \(0\).
- The dual minimum is \(0\), attained at \(x=0\).
- \(\mathcal P_p=[0,1]^{E(K)}\).
- Because every independent-set vertex has degree at most \(p<3\), direct checks agree with the formulas.

For \(p=0,1\), \(E(K)=\varnothing\).  
For \(p=2\), the only possible clique edge may have nonzero \(\kappa\), but no clique triangle exists; minimizing the signed functional over \([0,1]\) gives the correct combined identity.

Verdict: PASS.

### 9. Empty light or hot sets

- If \(L=\varnothing\), then \(\nu_2=0\); the signed maximization chooses \(y_H=0\).
- If \(H=\varnothing\), the signed extension is identical to the original objective.

Verdict: PASS.

### 10. Exact accounting

Recomputed independently:

\[
\nu_1+\nu_2
=|E(K)|-\max_y\sum_e(1-\kappa_e)y_e
=\frac{b_{\ge2}}2+M(\kappa).
\]

Then

\[
|E(G)|-2\nu_{\mathrm{con}}
=\binom p2-2M(\kappa)+b_1.
\]

No term \(b_0\) appears because isolated independent vertices contribute neither edges nor triangles.

Verdict: PASS.

## Material objections

1. The finite LP strong-duality dependency lacks a completed external theorem certificate.
2. Upstream gates remain `PROVISIONAL_PASS`; dependency health cannot be `CLEAN`.
3. This is a self-audit, not an independent audit.

## Falsification outcome

No mathematical counterexample or algebraic defect was found within the stated scope.

## Verdict

`PROVISIONAL_PASS`, with dependency health `UNVERIFIED`.

## Required actions

- Complete the LP-duality application certificate before promotion to `PASS`.
- Reassess after upstream gates are admitted.
- Preserve the distinction between residual capacities \(r_e\) and signed coefficients \(1-\kappa_e\).
