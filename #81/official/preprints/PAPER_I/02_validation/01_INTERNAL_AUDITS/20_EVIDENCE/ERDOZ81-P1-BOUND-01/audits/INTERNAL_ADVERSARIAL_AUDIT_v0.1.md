# Audit Record

Audit ID: ERDOZ81-P1-BOUND-01-AUD-001  
Gate ID: ERDOZ81-P1-BOUND-01  
Statement version: 0.1  
Audit type: SELF_AUDIT / INTERNAL_ADVERSARIAL_AUDIT  
Independence level: same agent, separate adversarial pass  
Auditor: Researcher  
Date: 2026-07-05  
Protocol version: 1.0

## Scope

Attempt to reject the derivation of \(R(p,q)\) and each comparison
\(U,D,H\ge R-p/2\).

## Material finding: historical algebraic omission

The historical manuscript stated

\[
12(U-R)=q(2p+q)-2p.
\]

That identity is false for general \(s\). The correct expansion is

\[
\boxed{
12(U-R)=q(2p+q-2s)-2p
=q(2o+q)-2p.
}
\]

The omitted term is \(-2qs\).

The defect does not invalidate the desired inequality, because
\(q(2o+q)\ge0\). Therefore \(U-R\ge-p/6\) remains valid.

The historical identity is quarantined and must not be reused.

## Falsification performed

- Checked \(s=p\), where the omitted term is maximal.
- Checked \(s=2\), \(o=0,1,2,3\).
- Checked \(q=0\) separately.
- Checked \(p=0,1,2,3\).
- Checked \(q\gg p\), where \(A\) is strongly negative.
- Checked equality surfaces in the square completion for \(D\).
- Checked \(s=p\) and \(s=2\) in the \(H\)-bound.
- Verified that \(H\) is never invoked for \(o<3\).
- Re-expanded all identities symbolically by hand-equivalent algebra;
  no numerical evidence is used in the proof.

## Findings

1. The corrected \(U-R\) identity is exact.
2. The \(D-R\) square completion is exact.
3. The \(H-R\) identity is exact.
4. The \(q=0\) branch requires a separate proof and is now included.
5. The final constant \(-p/2\) is uniform across all candidates.
6. No external bound is imported.

## Verdict

`PROVISIONAL_PASS`.

The gate is mathematically supported by a complete candidate proof and
self-audit. As a T3 gate it still requires independent audit before
`PASS` or `FINAL_PASS`.
