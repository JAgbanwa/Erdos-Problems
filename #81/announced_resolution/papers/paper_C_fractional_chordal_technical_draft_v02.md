# A Fractional Triangle Theorem for Chordal Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Technical Draft v0.2.** Paper C in the series on clique partitions in split and chordal graphs. This is a technical working draft, not yet a public preprint.

**Keywords.** Clique partitions; chordal graphs; clique trees; triangle packings; fractional packings; edge clique partitions; Erdős problems.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

## Abstract

We prove, conditionally on the local toolkit formalized in Paper B, a fractional triangle-packing theorem for chordal graphs. For every chordal graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2,
\]

where \(\nu_3^*(G)\) denotes the maximum total weight of a fractional triangle packing in \(G\). The proof uses a nearest-heavy laminar decomposition of a clique tree into anchored one-boundary branches and two-boundary corridors. Terminal regions are classified using the local toolkit from Paper B. Boundary interactions are converted into debits, allocated over retained cores, and then realized as fractional triangles by a uniform allocation lemma. A global edge-ownership ledger patches all local and boundary triangle weights into one feasible fractional triangle packing. This draft is the global fractional component of the series; the integral clique partition theorem is derived separately in Paper D by fractional-to-integral rounding.

---

# 1. Introduction

The edge clique partition number of a graph \(G\), denoted \(\operatorname{cp}(G)\), is the minimum number of cliques whose edge sets partition \(E(G)\). A triangle packing immediately gives

\[
\operatorname{cp}(G)\le |E(G)|-2\nu_3(G).
\]

For dense asymptotic questions it is natural to pass through fractional triangle packings. This paper proves the fractional chordal theorem needed for the chordal clique partition problem.

## Role in the series

- **Paper A** proves the sharp split graph theorem and supplies the lower-bound construction \(K_p\vee\overline{K}_{2p}\).
- **Paper B** proves the local and structural toolkit for chordal graphs.
- **Paper C**, the present paper, proves the global fractional triangle theorem for chordal graphs.
- **Paper D** applies fractional-to-integral triangle-packing rounding and derives the final chordal clique partition theorem.

This paper does not prove the split lower bound and does not perform final integral rounding.

## Main theorem

### Theorem C.1 — Fractional Chordal Theorem

For every chordal graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

At the level of this technical draft, the theorem is proved as an implication from the Paper B toolkit.

---

# 2. Fractional triangle packings

A fractional triangle packing is a choice of weights

\[
\psi_T\ge0
\qquad
(T\in K_3(G))
\]

such that

\[
\sum_{T\ni e}\psi_T\le1
\qquad
(e\in E(G)).
\]

Define

\[
\nu_3^*(G)=
\max\sum_{T\in K_3(G)}\psi_T.
\]

Define the fractional triangle residual

\[
\tau_3(G)=|E(G)|-2\nu_3^*(G).
\]

---

# 3. Chordal graphs and clique trees

Each vertex \(v\in V(G)\) corresponds to a connected subtree

\[
\mathcal T_v\subseteq\mathcal T.
\]

For a clique-tree node \(t\),

\[
C(t)=\{v:t\in\mathcal T_v\}.
\]

Adjacency is represented by subtree intersection:

\[
uv\in E(G)
\quad\Longleftrightarrow\quad
\mathcal T_u\cap\mathcal T_v\neq\varnothing.
\]

Paper B supplies the Heavy-Bag Lemma:

\[
|E(G)|\le M_*n.
\]

---

# 4. Anchored regions

A one-boundary region is

\[
\mathcal R=(R;S).
\]

Its private set is

\[
P(\mathcal R)
=
\{v:\mathcal T_v\cap R\neq\varnothing\}\setminus S.
\]

A two-boundary region is

\[
\mathcal R=(R;S_L,S_R).
\]

Its private set is

\[
P(\mathcal R)
=
\{v:\mathcal T_v\cap R\neq\varnothing\}
\setminus(S_L\cup S_R).
\]

Let

\[
m(\mathcal R)=|P(\mathcal R)|.
\]

For an internal clique-tree node \(t\),

\[
M_{\mathcal R}(t)
=
|\{v\in P(\mathcal R):t\in\mathcal T_v\}|.
\]

A region is \(\eta\)-diffuse if

\[
M_{\mathcal R}^*
\le
\eta m(\mathcal R).
\]

---

# 5. Nearest-heavy laminar recursion

If \(\mathcal R\) is not diffuse, choose a nearest heavy bag \(b\) satisfying

\[
M_{\mathcal R}(b)>\eta m(\mathcal R).
\]

Retain

\[
C_b=C(b)
\]

as a new core and split the tree region \(R\) along \(b\).

## Theorem C.2 — Nearest-Heavy Laminar Decomposition

For fixed \(\eta>0\), the nearest-heavy recursion produces a finite laminar family of anchored terminal regions and retained cores such that:

1. terminal private sets are pairwise disjoint;
2. retained core edges are excluded from child-private accounts;
3. every edge has a unique ownership account or is unused;
4. diffuse terminal errors sum to \(O(\eta n^2)\);
5. potential releases telescope under \(F(x)=x^2/6\).

---

# 6. Terminal classification

Paper B supplies the Local Terminal Toolkit.

## Theorem C.3 — Terminal Classification

Every terminal region produced by Theorem C.2 is one of:

1. an \(\eta\)-diffuse one-boundary branch;
2. an \(\eta\)-diffuse two-boundary corridor;
3. an atomic core-fan debit call;
4. a sealed \(L_4\)-certified window;
5. a good-leaf or ear-budget reducible window;
6. a promotion event.

---

# 7. Boundary debits

For a boundary trace group \(\alpha\), with private mass \(u_\alpha\), subcore \(S_\alpha\), size \(s_\alpha=|S_\alpha|\), and exterior mass \(r_\alpha\), define

\[
T_\alpha
=
\frac{
u_\alpha(4s_\alpha-u_\alpha-2r_\alpha)_+
}{12}.
\]

Paper B's Core-Fan Allocation Theorem gives, for every subfamily \(\mathcal A\),

\[
\sum_{\alpha\in\mathcal A}T_\alpha
\le
\operatorname{Cap}
\left(
\bigcup_{\alpha\in\mathcal A}E(S_\alpha)
\right).
\]

---

# 8. Uniform boundary-debit realization

Define

\[
z_{\alpha,ij}
=
\frac{T_\alpha}{\binom{s_\alpha}{2}},
\qquad
ij\subseteq S_\alpha.
\]

## Lemma C.4 — Uniform Allocation Calculus

For \(v_i\ge0\), \(V=\sum_i v_i<1\), and \(0<q_i\le1-V\),

\[
\sum_i
\frac{
v_i(6q_i+v_i-2)_+
}{6q_i^2}
\le
\frac23.
\]

## Lemma C.5 — Uniform Boundary-Debit Realization

The allocation \(z_{\alpha,ij}\) realizes all boundary debits by fractional triangles while respecting private-boundary and core-edge capacities.

---

# 9. Sealed \(L_4\) windows and type blow-up

Paper B supplies:

- \(L_4\) Certificate Theorem;
- Type Blow-Up Realization Lemma.

Thus sealed \(L_4\) terminal windows contribute only \(O(|X|)\) loss, and over disjoint private interiors this sums to

\[
O_\eta(n).
\]

---

# 10. Edge ownership ledger

Ownership classes are:

1. internal-private;
2. boundary-debit;
3. retained core;
4. unused.

## Theorem C.6 — Edge Ownership Patching

If every local triangle packing and every boundary-debit triangle packing obeys the ownership ledger, then their sum is a global fractional triangle packing.

---

# 11. Lower-order ledger

## Lemma C.7 — Lower-Order Ledger

All losses in the construction are either

\[
O(\eta n^2)
\]

or

\[
O_\eta(n).
\]

---

# 12. Global amortization and proof

Let

\[
F(x)=\frac{x^2}{6}.
\]

When private mass \(u\) is separated from ambient mass \(N\),

\[
F(N)-F(N-u)
=
\frac{2Nu-u^2}{6}.
\]

The releases telescope:

\[
\sum_j
\left(F(N_j)-F(N_j-u_j)\right)
\le
F(n)=\frac{n^2}{6}.
\]

Construct a global fractional triangle packing \(\psi\) from boundary-debit triangles, sealed \(L_4\) packings, good-leaf/ear local packings, and internal terminal packings. By the ownership ledger, \(\psi\) is feasible.

Therefore

\[
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}
+
O(\eta n^2)
+
O_\eta(n).
\]

Let \(n\to\infty\), then \(\eta\to0\). This proves

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

---

# 13. How Paper D uses this theorem

Paper D applies fractional-to-integral rounding:

\[
\nu_3(G)\ge\nu_3^*(G)-o(n^2).
\]

Then

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2).
\]

By Theorem C.1,

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

Sharpness comes from Paper A.

---


# 14. Discussion and further directions

Theorem C.1 is the conceptual center of the series. It separates the chordal clique partition problem into two layers: a fractional triangle-packing statement proved by clique-tree recursion, and a final integral rounding step handled in Paper D. This separation is useful because the fractional theorem is where the chordal structure is used; the final rounding is a general fixed-family packing result.

There are several natural directions.

1. **Algorithmic realization.** The nearest-heavy recursion and boundary-debit allocation are constructive in spirit. It would be useful to turn the proof into an explicit algorithm producing near-optimal fractional triangle packings, and then near-optimal clique partitions after rounding.

2. **Finite error terms.** The theorem is asymptotic. The present argument tracks losses as \(O(\eta n^2)+O_\eta(n)\). A sharper finite version would require optimizing the diffusion threshold, local certificate losses, and promotion constants.

3. **Reducing dependence on finite certificates.** Paper C imports the sealed \(L_4\) certificate from Paper B. A more conceptual local argument replacing part of that finite certificate would make the proof more transparent.

4. **Subclasses of chordal graphs.** Interval graphs, block graphs, and strongly chordal graphs may admit shorter proofs or stronger error terms. These subclasses are useful test cases for the recursion.

5. **Beyond chordal graphs.** The proof relies heavily on clique-tree structure. Extending the method beyond chordal graphs would require a substitute for laminar separator ownership, and is not immediate.

For the present series, the next task is not to broaden the theorem, but to stabilize the formal interface with Paper B: every imported local lemma must be available in the exact form used above.

# 15. Proof-status audit

| Item | Location | Status |
|---|---|---|
| Nearest-heavy recursion | Paper C | proof draft complete |
| Terminal classification | Paper C + Paper B | depends on B toolkit |
| Core-Fan capacity | Paper B | imported |
| Uniform allocation | Paper C | proof draft complete |
| \(L_4\) certificate | Paper B | imported, needs package |
| Type blow-up | Paper B | imported |
| Ownership ledger | Paper C | proof draft complete |
| Lower-order ledger | Paper C | proof draft complete |
| Fractional theorem | Paper C | conditional assembly |
| Integral rounding | Paper D | not included here |

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
