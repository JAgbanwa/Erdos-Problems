# External Theorem Certificate

Certificate ID: ERDOZ81-P1-ETC-LP-DUALITY-001  
Gate ID: ERDOZ81-P1-PHASE2-DUAL-01  
Source: Not yet selected  
Source version: OPEN  
Theorem number: OPEN  
Certificate status: INCOMPLETE  

## Relevant Source Statement

Finite-dimensional linear-programming strong duality for a feasible bounded primal problem and its dual.

## Source Notation

OPEN.

## Project Notation

Primal variables: \(w_T\), indexed by \(T\in\mathcal T(K)\).  
Primal constraints: \(\sum_{T\ni e}w_T\le r_e\), indexed by \(e\in E(K)\).  
Dual variables: \(x_e\ge0\).  
Dual constraints: \(x(T)\ge1\).

## Hypothesis Mapping

| External hypothesis | Internal verification | Evidence |
|---|---|---|
| Finite-dimensional program | Finite graph gives finitely many edges and triangles | Candidate proof |
| Primal feasible | \(w=0\) | Candidate proof |
| Primal bounded | Each positive-weight triangle consumes capacity on three edges; total objective is finite | Candidate proof |
| Nonnegative capacities | \(r_e=\max\{1-\kappa_e,0\}\) | Phase-I proof |

## Thresholds and Uniformity

None expected.

## Imported Conclusion

Equality of the optimal values in (A) and (B), with attainment.

## Ambiguities

Exact authoritative source and theorem number have not yet been fixed.

## Source Locator

OPEN.

## Reviewer

Unassigned.
