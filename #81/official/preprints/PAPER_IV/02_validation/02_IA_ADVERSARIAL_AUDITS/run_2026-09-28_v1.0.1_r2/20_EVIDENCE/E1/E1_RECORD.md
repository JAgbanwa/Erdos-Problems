# E1 — claim semantics

**Method.** Full reading of the EN manuscript; decomposition into 36 claim IDs (`CLAIM_MAP_AUDITOR.csv`) mapping
each theorem/corollary/byproduct to literal hypotheses and Lean declarations; the author's `CLAIM_MAP.csv` was
**not** consulted (it is in the internal-audit tree, deferred by §1.2).

**Distinctions verified.** All-orders additive b (Thm A, b = N², tower bound) vs eventual sharp M(n) (Thm B) vs
eventual maximum (1.2, witness optimal against unrestricted partitions); rooted defect s (Thm C: c₄ ≤ Q_s(n)
eventually, maximum vs unrestricted partitions; no stability/classification claimed for s > 0); integral stability
(Thm 6.1: hypothesis on order-≤4 partitions, conclusion on graph edits 16δ); partition stability (Cor 6.1a: root
fixed before an arbitrary, order-unrestricted partition; τ + 48δ noncanonical pieces); extremal rigidity
(Cor 6.2, both cp and c₄); explicit tower threshold (T(h+7), b ≤ T(h+8)), explicitly impractical; triangular-only
annex (8.1a) outside `import PaperIV`. The paper does not claim b = 0, a universal linear mixed gap, a practical
threshold, or classification outside the chordal class (verified in §§6.3, 8.2, A.3 and the abstract).

**Small orders / empty graphs / quantifier order.** n = 0 and n = 1 are covered by Thm A (empty partition; Lean
quantifies over all n : ℕ with `Fin n`); M(n) ≥ n²/6 is used only for n ≥ 6 (fails below — E5 negative control);
Thm B/C, 6.1, 6.1a are eventual with the threshold chosen before G (and before δ, τ, Q); Cor 6.1a's root precedes
every partition (checked in the Lean header). Theorem C's truncated subtraction in `defectTarget` is irrelevant
for n ≥ s+1.

**Result.** No semantic defect in the statements themselves. The attribution of Theorem C (E7-F1) is a
bibliographic, not a semantic, defect. **E1 = PASS.**
