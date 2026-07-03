# Paper I v1.1 — Final Closure Audit

**Manuscript:** *Affine Profile Reduction for Fractional Triangle Covers in Split Graphs*  
**Date:** July 3, 2026  
**Verdict:** `CLOSED AUTHOR VERSION — MATHEMATICAL AND EDITORIAL PASS`

## Final audit result

The external AI-assisted content audit found no mathematical error introduced by the editorial revision.

- Theorem 6.2 / introductory Theorem 1.2 matched direct optimization of the actual orbit polytope, with no mismatch in the auditor's tests.
- The restriction \(X\in\mathbb R\), \(Y,Z\ge0\) is necessary: dropping the nonnegativity of either unbounded orbit coefficient may make the minimization unbounded below.
- The theorem reordering did not change the proof dependencies.
- The sharpness family \(K_p\vee\overline K_{2p}\) and the value \(n^2/6+n/6\) are consistent across Papers I--III.
- The relationship to Paper II v0.8 and Paper III v1.0.4 is explicit and non-contradictory.
- The obsolete statement that an \(n^2/6+O(n)\) bound remained open has been removed.

## Proof status

Every internal result is proved algebraically in the manuscript. The only external mathematical inputs are finite-dimensional LP duality and Haxell--Rödl/Yuster for the integral asymptotic application. Optional scripts and finite enumerations are regression evidence, not proof premises.

## Remaining external matters

- specialist literature and novelty review of the affine-profile coordinate system;
- independent human referee review.

These are not gaps in the internal proof.
