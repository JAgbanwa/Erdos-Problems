# Changelog — Paper II v1.1.7 to v1.1.8

**Date:** 2026-08-01  
**Change class:** authorized editorial clarification of domain  
**Mathematical baseline:** Paper II v1.1.7  
**Mathematical effect:** none; the arithmetic statement and Lean declaration were already valid for all integers

## Change

| Location | Change class | Before | After |
|---|---|---|---|
| Corollary 1.2′ | `CLARITY` | \(M(n)\) was described as the extremal value and the inequality was stated for every integer \(n\), leaving the graph-theoretic and arithmetic roles implicit. | \(M(n)\) is defined by the floor formula; for \(n\ge1\) it is the extremal value of Theorem 1.1, while the arithmetic inequality is stated for every \(n\in\mathbb Z\). |
| Corollary 1.2′ formalization note | `CLARITY` | Lean declaration cited without its unrestricted integer domain being stated explicitly. | The manuscript records that `PaperII.phiTau_max_sandwich` is formalized for \(n:\mathbb Z\) with no lower-bound hypothesis. |
| Table 5 | `CLARITY` | The row did not explicitly state the integer domain. | The row now records “for every \(n\in\mathbb Z\).” |

## Semantic lock

No theorem, lemma, proposition, corollary formula, displayed equation, constant, proof step, numerical result, Lean declaration, or axiom footprint was changed.

## Query closure

`CQ-II-1` is closed. The researcher confirmed from the Lean declaration that `phiTau_max_sandwich (n : ℤ)` has no hypothesis \(n\ge1\). The graph-theoretic interpretation remains restricted to \(n\ge1\), while the arithmetic inequality is valid for all integers.
