# Falsification Record

Evidence ID: ERDOZ81-P1-BOUND-FALSIFY-01-EV-001  
Gate ID: ERDOZ81-P1-BOUND-FALSIFY-01  
Statement version: 0.1  
Artifact type: Falsification and boundary audit  
Evidence role: CHALLENGING / SUPPORTING  
Admission level: CANDIDATE  
Current status: ACTIVE  
Author or agent: Researcher  
Reviewer: Researcher  
Date: 2026-07-05  
Protocol version: 1.0

## Exact target

Attempt to find admissible parameters violating

\[
M(\kappa)\ge R(p,q)-\frac p2.
\]

## Boundary partition

The parameter universe is partitioned into:

1. \(q=0\);
2. \(q\ge1,s=2\);
3. \(q\ge1,s\ge3\);
4. \(o=0,1,2\);
5. \(o\ge3\);
6. signs \(A<0,A=0,A>0\);
7. transition \(B-2C=0\).

Every branch is covered by an exact argument in the proof records.

## Minimal cases

- \(p=0,1,2\): no clique triangle; direct verification.
- \(p=3,q=0\): \(M(0)=1\), while \(R-p/2=0\).
- \(s=2,o=0\): exact optimum \(D=1-q\), and the corrected comparison
  remains valid.
- \(o=1,2\): no nonexistent \(H\)-constraint or \(H\)-candidate is used.
- \(o=3\): first regime in which \(H\) is admissible.

## Equality and tie surfaces

- \(B-2C=0\) is equivalent to \(s-o+1=0\) when \(o>0\); then
  \(D=H\).
- Equality in the quadratic certificate for \(D\) requires
  \(2p-q=0\) and \(o=0\), subject to integrality and admissibility.
- The \(U\)-bound is strictly stronger than the common \(-p/2\) bound
  except in degenerate comparisons.

## Outcome

No admissible branch produces a counterexample.

A genuine defect was found in the historical expansion of \(U-R\), but
the corrected formula preserves the theorem. The defect has been
quarantined under correction record
`ERDOZ81-P1-CORR-BOUND-001`.

## Verdict

The falsification gate supports `PROVISIONAL_PASS` for the quantitative
bound. It does not replace independent audit.
