# Audit Record

Audit ID: ERDOZ81-P1-PROFILE-01-AUDIT-001  
Gate ID: ERDOZ81-P1-PROFILE-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT  
Independence level: Same agent, separated pass  
Auditor: Researcher  
Date: 2026-07-05  
Protocol version: 1.0

## Scope

Attempt to reject the profile identity, normalization, and dominance inequality.

## Falsification and checks

1. **Single active vertex.** Then \(q=1\), one \(\lambda_S=1\), and equality holds.
2. **Repeated identical neighborhoods.** If all \(q\) vertices have type \(S\), then \(\kappa=qa^S\).
3. **Two distinct types.** Coordinatewise expansion counts each vertex exactly once through its unique neighborhood.
4. **Overlapping neighborhoods.** Overlap causes additive load, exactly as in the definition of \(\kappa\); no collision error.
5. **Minimal type \(|S|=2\).** Denominator is \(1\), valid.
6. **Universal type \(S=K\).** Valid whenever \(p\ge2\).
7. **Impossible types.** Sets of size \(0\) or \(1\) are excluded because their vertices are not in \(I_{\ge2}\).
8. **\(q=0\).** Normalization fails; the gate explicitly excludes it.
9. **Concavity direction.** The desired lower bound is consistent with the minimum-linear functional being concave.
10. **Baseline cancellation.** The identity
   \[
   b-\sum_S\lambda_S\kappa^S=\sum_S\lambda_S(b-\kappa^S)
   \]
   uses \(\sum_S\lambda_S=1\); verified.
11. **Support minimum versus all-type minimum.** The latter may be smaller, so the final inequality direction is correct.
12. **Hidden symmetry.** None is used. A heterogeneous fixed baseline is permitted.
13. **Changing baseline by type.** Would invalidate the objective-vector mixture; excluded.
14. **Changing polytope by type.** Would invalidate concavity application; excluded.

## Findings

No counterexample found for the exact statement.

## Verdict

`SELF_AUDIT_PASS`, with mandatory separate treatment of \(q=0\).
