# Self-Audit — Farkas strong duality gate

Audit ID: ERDOZ81-P1-LP-DUALITY-01-AUD-001  
Gate ID: ERDOZ81-P1-LP-DUALITY-01  
Statement version: 0.2  
Audit type: SELF_AUDIT  
Independence level: PRODUCER_SELF_AUDIT  
Auditor: Researcher  
Date: 2026-07-05  
Materials supplied: Gate Record v0.2; candidate proof v0.2; Phase-II gate  
Materials withheld: Historical exploratory narrative not required  
Protocol version: 1.0  

## Scope

Attempt to reject the specialized Farkas proof and its application to the
Phase-II triangle-packing LP.

## Checks performed

### A. Farkas alternative

1. **Mutual exclusivity.**  
   Verified:
   \[
   b^\top y=z^\top B^\top y\ge0
   \]
   contradicts \(b^\top y<0\).

2. **Closedness of the finitely generated cone.**  
   The proof does not assume coefficient boundedness for arbitrary
   representations. It first reduces to a linearly independent support, then
   passes to a subsequence with fixed support. This avoids cancellation by
   dependent generators.

3. **Nearest-point existence.**  
   The cone is closed; a minimizing sequence can be restricted to a closed
   bounded ball. Finite dimensionality supplies compactness.

4. **Sign of the separating vector.**  
   With \(y=c_0-b\), the derivative calculation gives
   \[
   \langle y,c-c_0\rangle\ge0.
   \]
   Using \(0,2c_0\in C\) forces \(\langle y,c_0\rangle=0\), hence
   \(\langle y,c\rangle\ge0\).

5. **Strict negativity.**  
   Verified:
   \[
   b^\top y=-\|c_0-b\|^2<0.
   \]

### B. Encoding the level constraint

The equality
\[
\mathbf1^\top w-t=a,\qquad t\ge0
\]
is equivalent to \(\mathbf1^\top w\ge a\), not \(\le a\). The sign is correct.

The block matrix yields:
\[
A^\top x+\mu\mathbf1\ge0,\quad x\ge0,\quad-\mu\ge0.
\]
Setting \(\lambda=-\mu\) gives \(A^\top x\ge\lambda\mathbf1\).

### C. Positivity of the normalizing multiplier

If \(\lambda=0\), Farkas strict separation gives \(r^\top x<0\), impossible
because \(r,x\ge0\). Thus division by \(\lambda\) is legitimate.

### D. Compactness step

A general dual level set need not be compact when some \(r_e=0\). The proof
does not claim otherwise. It uses the triangle-specific cap
\[
x_e\mapsto\min\{x_e,1\},
\]
which preserves every three-edge covering inequality and does not increase the
objective. This places certificates in the compact cube \([0,1]^E\).

### E. Degenerate cases

- \(\mathcal T=\varnothing\): treated separately; both values are \(0\).
- \(E=\varnothing\): included in the preceding case.
- all \(r_e=0\) with \(\mathcal T\neq\varnothing\): primal value \(0\); the
  compactness argument supplies a dual feasible vector of objective \(0\).
- some \(r_e=0\): no division by \(r_e\) occurs.
- duplicated triangle columns: harmless.
- edges in no triangle: dual coordinates may be set to \(0\); capping remains
  valid.

### F. Attempted counterexamples

Tested conceptually:

1. one triangle with capacities \((a,b,c)\): primal optimum
   \(\min\{a,b,c\}\); dual can price one minimum-capacity edge at \(1\);
2. two triangles sharing an edge;
3. all capacities zero;
4. an edge of zero capacity appearing in every triangle;
5. unused edges with zero objective coefficient.

No contradiction with the theorem or proof was found.

## Material objections

None found.

## Warnings

1. The proof is specialized to covering constraints where each column
   corresponds to a nonempty triangle and capping at \(1\) preserves
   feasibility. It must not be silently generalized to arbitrary matrices.
2. The evidence remains `CANDIDATE`; this audit is not independent.
3. A later Lean formalization may use an existing Farkas/separation theorem,
   but that does not change the present mathematical proof.

## Verdict

`PROVISIONAL_PASS / SELF_AUDITED`

## Required actions before PASS

- Admit the proof and audit evidence under the project admission procedure.
- Perform the required T2 interface/dependency review.
- Update the Phase-II gate to replace the external LP-duality certificate by
  this internal logical dependency.
