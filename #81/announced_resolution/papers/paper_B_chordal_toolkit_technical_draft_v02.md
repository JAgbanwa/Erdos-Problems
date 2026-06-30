# Local and Structural Reductions for Chordal Clique Partitions

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Technical Draft v0.2.** Paper B in the series on clique partitions in split and chordal graphs. This is a technical working draft, not yet a public preprint.

**Keywords.** Clique partitions; chordal graphs; clique trees; triangle packings; fractional packings; local reductions; finite certificates.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

## Abstract

We develop the local and structural toolkit used in a companion paper to prove a fractional triangle-packing theorem for chordal graphs. The tools are organized around clique-tree representations of chordal graphs. We isolate a heavy-bag principle, correct local leaf inequalities, a \(K_{1,4}/K_{1,5}\) threshold, spectral good-leaf criteria for tree-like tails, ear-budget reductions, promotion lemmas for long-core and overload configurations, a bounded \(L_4\) type certificate, a type blow-up realization lemma, and a Core-Fan Allocation Theorem formulated as a quadratic Hall/Farkas capacity statement. This draft is intended as the technical repository of lemmas cited by the global fractional theorem in Paper C.

---

# 1. Introduction

This paper is the technical toolkit paper in the series. It does not prove the final chordal clique partition theorem. Instead, it proves and packages the local and structural reductions used by the global recursive argument in Paper C.

The target result of the series is

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

Paper A proves the split graph theorem and supplies the extremal construction. Paper C proves the fractional triangle theorem for chordal graphs using the tools developed here. Paper D applies fractional-to-integral triangle-packing rounding to obtain the final clique partition theorem.

## Purpose of this draft

This draft makes the dependencies of Paper C explicit. Some proofs are complete at this stage; others are proof schemes with verification checklists. The most sensitive items are:

\[
L_4\text{ certificate},\qquad
\text{Core-Fan/Farkas allocation},\qquad
\text{promotion completeness}.
\]

---

# 2. Chordal preliminaries

A chordal graph admits a clique-tree representation. Each vertex \(v\in V(G)\) corresponds to a connected subtree

\[
\mathcal T_v\subseteq \mathcal T.
\]

For a clique-tree node \(t\), set

\[
C(t)=\{v:t\in\mathcal T_v\}.
\]

Adjacency is represented by subtree intersection:

\[
uv\in E(G)
\quad\Longleftrightarrow\quad
\mathcal T_u\cap\mathcal T_v\neq\varnothing.
\]

The bag coverage is

\[
M(t)=|C(t)|,
\qquad
M_*=\max_t M(t).
\]

---

# 3. Heavy bags

## Lemma B.1 — Heavy-Bag Lemma

Let \(G\) be chordal with clique-tree representation \(\mathcal T\). Then

\[
|E(G)|\le M_* n.
\]

More generally, for nonnegative vertex weights \(x_v\),

\[
\sum_{\mathcal T_u\cap\mathcal T_v\neq\varnothing}x_u x_v
\le
M_*\sum_v x_v.
\]

**Proof.** Assign every intersecting pair of subtrees to one clique-tree node in their intersection. At each node \(t\), the total assigned pair weight is bounded by \(M_*\) times the assigned mass through \(t\). Summing over nodes gives the weighted inequality. The unweighted edge bound follows by taking all \(x_v=1\).

---

# 4. Leaf reductions and the correct strong-leaf inequality

Consider a leaf clique \(K=A\cup S\), where \(A\) is private simplicial mass and \(S\) is the separator. Let

\[
a=|A|,\qquad s=|S|,
\]

and let \(r\) be the outside mass.

## Lemma B.2 — Strong-Leaf Inequality

A leaf is good when

\[
4s\le a+2r+O(1).
\]

A strong leaf satisfies

\[
4s>a+2r-O(1).
\]

Consequently,

\[
5s>n+r-O(1).
\]

**Important.** The consequence \(s>n/3\) is not valid in general.

---

# 5. The \(K_{1,4}/K_{1,5}\) threshold

The shifted local dual calculation gives, for a star \(K_{1,r}\),

\[
Q(c)=\frac13(c^2+r)-\frac r3c,
\]

with minimum

\[
Q_{\min}=
\frac13\left(r-\frac{r^2}{4}\right).
\]

## Lemma B.3 — \(K_{1,4}/K_{1,5}\) Threshold

The local star threshold is sharp:

\[
r\le4
\quad\text{is safe,}
\]

whereas

\[
r=5
\]

forces promotion.

---

# 6. Spectral good-leaf tails

For tree-like triangle-free tails,

\[
Q(x)=
\frac13x^\top
\left(I-\frac12A_T\right)x.
\]

## Lemma B.4 — Spectral Good-Leaf Lemma

If

\[
\rho(A_T)>2,
\]

then the tail has a good leaf. If all leaves are strong, then the tail reduces to a bounded double-broom family.

**Verification needed.** The final manuscript should include an exact table for the bounded double-broom family \(B(r,k,s)\), with \(r,s\in\{1,2,3\}\).

---

# 7. Ear budgets

A simplicial ear of mass \(a\) attached to separator mass \(\sigma\) requires budget

\[
B(a,\sigma)=\frac12a(\sigma-a)_+.
\]

## Lemma B.5 — Ear Budget Lemma

If a family of ears attaches to separator cores with bounded edge multiplicity, the total ear budget fits within boundary capacity. If a separator edge or subcore is requested with unbounded or linear multiplicity, a common-core promotion is triggered.

---

# 8. Promotion lemmas

## Lemma B.6 — Long-Core/Five-Window Promotion

If a bounded-width clique-tree window carries linear long-span mass across five consecutive positions, then one can promote a five-window core. The promotion separates left and right sides into anchored regions and removes promoted core edges from child-private accounts.

## Lemma B.7 — Overload/Common-Core Promotion

If too many ears or trace groups request capacity from the same separator subcore, then that subcore can be promoted to a retained core. After promotion, all adjacent private groups report boundary debits to the promoted core.

**Verification needed.** Promotion completeness is referee-sensitive. The final version must state the exact threshold at which bounded multiplicity ends and promotion begins.

---

# 9. The \(L_4\) finite certificate

The bounded span-four type system is

\[
\mathcal V_{11}
=
\{J,1,2,3,4,12,23,34,13,24,14\}.
\]

## Theorem B.8 — \(L_4\) Certificate Theorem

Every sealed bounded span-four \(L_4\) residue admits a rational type-level fractional triangle certificate over \(\mathcal V_{11}\). In sealed mode, all used edges are internally owned.

The proof package must specify:

1. the eleven vertex types;
2. the complete list of edge and loop atoms;
3. the complete list of feasible triangle types;
4. rational weights \(\lambda_\tau\);
5. verification that edge atoms respect capacity;
6. verification that the target local deficit is met;
7. ownership mode \(B=\varnothing\).

**Draft status.** The certificate is treated as machine-certified in the internal development record. The public draft must include the exact rational certificate and exact verifier.

---

# 10. Type blow-up realization

## Lemma B.9 — Type Blow-Up Realization

A rational type-level fractional triangle certificate over a fixed type system lifts to an actual fractional triangle packing with loss

\[
O_m(n)=o(n^2),
\]

where \(m\) is the number of types. For \(L_4\), \(m=11\), so the loss is \(O(n)\).

---

# 11. Core-Fan Allocation Theorem

Boundary groups are indexed by \(\alpha\). Each has private mass \(u_\alpha\), subcore \(S_\alpha\), size \(s_\alpha=|S_\alpha|\), and exterior mass \(r_\alpha\). Its debit is

\[
T_\alpha
=
\frac{
u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+
}{12}.
\]

## Theorem B.10 — Core-Fan Allocation Theorem

For every subfamily \(\mathcal A\),

\[
\sum_{\alpha\in\mathcal A}T_\alpha
\le
\operatorname{Cap}
\left(
\bigcup_{\alpha\in\mathcal A}E(S_\alpha)
\right).
\]

Equivalently, the boundary debits satisfy all Hall-type capacity inequalities for allocation over the retained core.

**Draft status.** This is the central symbolic capacity theorem. The proof scheme records the intended chain, but the final version must spell out the capacity normalization and the convexity step.

---

# 12. Local terminal toolkit

## Theorem B.11 — Local Terminal Toolkit

Every bounded local residue arising in the chordal recursion is one of:

1. good-leaf reducible;
2. ear-budget reducible;
3. \(L_4\)-certified in sealed mode;
4. long-core/five-window promoted;
5. overload/common-core promoted;
6. core-fan allocated.

This theorem is what Paper C imports for its terminal classification theorem.

---

# 13. How Paper C uses this toolkit

Paper C imports:

\[
\text{Heavy-Bag Lemma},
\quad
\text{Local Terminal Toolkit},
\quad
\text{Core-Fan Allocation},
\quad
L_4\text{ Certificate},
\quad
\text{Type Blow-Up}.
\]

Paper C does not re-prove \(L_4\) or Core-Fan/Farkas. It realizes allocated debits as fractional triangles and patches local packings with an edge-ownership ledger.

---


# 14. Discussion and verification roadmap

This paper is the most verification-sensitive part of the series. Its purpose is not only to state useful local reductions, but also to separate purely symbolic lemmas from finite or computationally assisted certificate claims.

There are five items that should be completed before this draft is promoted to a public preprint.

1. **The \(L_4\) certificate package.** The final version should include the rational certificate, the exact verifier, the type list, the edge and loop atoms, the triangle-type list, and the ownership mode used by the certificate. The sealed mode \(B=\varnothing\) should be the default public route.

2. **The double-broom verification.** The spectral good-leaf lemma reduces the all-strong-leaf case to a bounded double-broom family. The final version should include an exact table or a short independent verification of that family.

3. **The Core-Fan normalization.** The proof of the Core-Fan Allocation Theorem must spell out the capacity normalization and the convexity step converting the quadratic bound into the Hall/Farkas inequality.

4. **Promotion completeness.** The long-core and overload promotion lemmas must define precise thresholds separating bounded local behavior from promotion events.

5. **Interface with Paper C.** Every lemma imported by Paper C should be stated in exactly the form used there, especially the Core-Fan Allocation Theorem, the \(L_4\) Certificate Theorem, and the Type Blow-Up Realization Lemma.

Once these items are formalized, the role of this paper becomes clean: it supplies a finite local toolkit, while Paper C performs the global recursive decomposition and fractional triangle-packing assembly.

## Further technical directions

Several refinements may be worth investigating after the main chordal theorem is stabilized. First, one can ask whether the \(L_4\) certificate can be simplified or replaced by a smaller human-checkable family of local reductions. Second, the promotion thresholds may admit sharper constants than those needed for the asymptotic theorem. Third, the same local toolkit may be useful for intermediate chordal subclasses, such as interval graphs, strongly chordal graphs, and block graphs.

# 15. Proof-status audit

| Item | Status in this draft | Final requirement |
|---|---|---|
| Heavy-Bag Lemma | complete | minor polishing |
| Strong-Leaf Inequality | proof sketch | line-by-line algebra |
| \(K_{1,4}/K_{1,5}\) | complete | none |
| Spectral Good-Leaf | proof scheme | double-broom table |
| Ear Budget | proof sketch | exact multiplicity thresholds |
| Long-Core Promotion | proof scheme | formal threshold/proof |
| Overload Promotion | proof scheme | formal threshold/proof |
| \(L_4\) Certificate | certificate theorem | rational data/verifier |
| Type Blow-Up | complete | minor polishing |
| Core-Fan/Farkas | proof scheme | capacity normalization |
| Terminal Toolkit | outline | depends on all above |

---

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support during the development of this work.

The author used AI-assisted tools, including Gemini 3.5 Pro and ChatGPT, during the development of this work for exploratory search, testing possible approaches, looking for contradictions, organizing proof strategies, improving exposition, and preparing drafts. All mathematical claims, proofs, citations, and final editorial decisions are the sole responsibility of the author. No AI system is listed as an author.

# References

- G.-T. Chen, P. Erdős, and E. T. Ordman, *Clique partitions of split graphs*, in *Combinatorics, graph theory, algorithms and applications* (Beijing, 1993), 21--30, 1994.
- P. Erdős, E. T. Ordman, and Y. Zalcstein, *Clique partitions of chordal graphs*, Combinatorics, Probability and Computing (1993), 409--415.
- P. Erdős, A. W. Goodman, and L. Pósa, *The representation of a graph by set intersections*, Canadian Journal of Mathematics 18 (1966), 106--112.
- F. Gavril, *The intersection graphs of subtrees in trees are exactly the chordal graphs*, Journal of Combinatorial Theory, Series B 16 (1974), 47--56.
- P. E. Haxell and V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21 (2001), 13--38.
- R. Yuster, *Integer and fractional packing of families of graphs*, Combinatorica 28 (2008), 245--251.
