# Paper II v0.8 — Final Closure Audit

**Manuscript:** *Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs*  
**Date:** July 3, 2026  
**Verdict:** `CLOSED AUTHOR VERSION — ANALYTIC PROOF`

## Final change from v0.7

Proposition 6.1 now contains the complete two-way derivation of the
orbit LP. It first uses invariance under
\(\operatorname{Sym}(p)\times\operatorname{Sym}(q)\) to average an optimal
full-LP solution to a symmetric optimum of the same value. It then computes
the exact load induced on both edge orbits and proves the converse
feasibility statement by uniformly distributing any feasible
\((\alpha,\beta)\). The equality between the full fractional packing LP
and the two-variable program is therefore analytic and self-contained.

## Computational independence

No theorem or lemma depends on a script, LP solver, graph atlas, or finite
enumeration. Section 11 is explicitly supplementary. The regression suite
may be removed without altering any proof.

## Proof spine

1. Balogh et al. fractional clone symmetrization.
2. Chordality preservation under simplicial clone-class symmetrization.
3. Strict decrease of maximal clone classes.
4. Terminal chordal graphs are complete split.
5. Reduction of every admissible fractional parameter to the family
   \(S_{p,n-p}\).
6. Exact orbit LP by analytic edge-load counting.
7. Exact finite optimization for every fixed \(K_r\).
8. Haxell--Rödl/Yuster only for the final integral \(o(n^2)\) consequence.

## Remaining external matters

- forward-citation and novelty tracking;
- bibliographic verification by the author or journal;
- independent human referee review.

These are not gaps in the internal proof.
