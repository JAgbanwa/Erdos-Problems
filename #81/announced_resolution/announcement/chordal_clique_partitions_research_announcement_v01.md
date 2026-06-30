# A Research Announcement on Clique Partitions of Chordal Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Research Announcement Draft v0.1.** Full proofs are being prepared in companion manuscripts.

**Primary arXiv category.** math.CO -- Combinatorics.

**Keywords.** Clique partitions; chordal graphs; split graphs; triangle packings; fractional packings; extremal graph theory; Erdős problems.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

## Abstract

We announce an asymptotically sharp bound for the edge clique partition number of chordal graphs. Let \(\operatorname{cp}(G)\) denote the minimum number of cliques whose edge sets partition \(E(G)\). We announce that, for every chordal graph \(G\) on \(n\) vertices,

\[
\operatorname{cp}(G)\le \left(\frac16+o(1)\right)n^2.
\]

The constant is best possible, as shown by the complete split graph

\[
K_p\vee\overline{K}_{2p},\qquad n=3p.
\]

The proof proceeds through a fractional triangle-packing theorem for chordal graphs,

\[
|E(G)|-2\nu_3^*(G)\le \left(\frac16+o(1)\right)n^2,
\]

followed by standard fractional-to-integral rounding for fixed graph families. The full proof is being prepared in a sequence of companion manuscripts. This announcement records the main statements, the extremal construction, and the high-level structure of the argument.

## 1. Introduction

Let \(G\) be a finite simple graph. The edge clique partition number \(\operatorname{cp}(G)\) is the minimum number of cliques whose edge sets form a partition of \(E(G)\).

A classical theorem of Erdős, Goodman and Pósa gives a general \(n^2/4\)-type bound for decomposing the edges of an \(n\)-vertex graph into cliques. In the chordal setting, Erdős, Ordman and Zalcstein asked whether the sharper asymptotic bound

\[
\operatorname{cp}(G)\le \frac{n^2}{6}+O(n)
\]

holds for every \(n\)-vertex chordal graph.

This announcement records an affirmative asymptotic answer.

## 2. Main announced theorem

**Theorem 1 -- Chordal clique partition theorem.** For chordal graphs,

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

The upper bound is the main part of the result. The lower bound is already witnessed inside the class of split graphs.

## 3. Sharpness

Let

\[
G_p=K_p\vee\overline{K}_{2p}.
\]

Then \(G_p\) is a split graph, hence chordal, and has \(n=3p\) vertices. This construction gives

\[
\operatorname{cp}(G_p)\ge \frac{n^2}{6}-O(n).
\]

Thus the constant \(1/6\) in the announced theorem cannot be improved asymptotically.

The split case is treated separately in a companion manuscript, where the corresponding asymptotic maximum over split graphs is determined.

## 4. Fractional reduction

The proof of the chordal upper bound passes through fractional triangle packings. Let \(\nu_3^*(G)\) denote the maximum total weight of a fractional triangle packing in \(G\). The central fractional statement is the following.

**Theorem 2 -- Fractional chordal theorem.** For every chordal graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

This fractional theorem implies the announced clique partition theorem by applying the standard fractional-to-integral packing theorem for the fixed family \(\{K_3\}\), which gives

\[
\nu_3(G)\ge \nu_3^*(G)-o(n^2).
\]

Indeed, every edge-disjoint triangle packing gives

\[
\operatorname{cp}(G)\le |E(G)|-2\nu_3(G),
\]

because each packed triangle replaces three singleton-edge cliques by one triangle clique.

## 5. High-level structure of the proof

The proof uses the clique-tree representation of chordal graphs. Every vertex of a chordal graph is represented by a connected subtree of a tree, and adjacency corresponds to subtree intersection.

The argument has four main components.

First, a structural decomposition isolates large regions of the clique tree and recursively separates the graph into anchored branches and corridors. The recursion is laminar and is designed so that private vertex sets are disjoint and retained core edges are not counted twice.

Second, local terminal configurations are handled by a finite toolkit of reductions. These include local leaf reductions, bounded-window certificates, promotion mechanisms for high-overlap configurations, and capacity inequalities for boundary groups.

Third, the boundary interactions produced by the recursion are converted into debits assigned to retained cores. These debits are then realized as fractional triangles while respecting edge capacities.

Fourth, an ownership ledger patches all local and boundary packings into a single global fractional triangle packing. The resulting amortization gives

\[
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}+O(\eta n^2)+O_\eta(n),
\]

and the theorem follows by first taking \(n\to\infty\) and then \(\eta\to0\).

## 6. Companion manuscripts

The proof is being prepared in the following sequence.

1. **Clique partitions of split graphs and the \(1/6\) barrier.**  
   This manuscript proves the split graph theorem and gives the extremal construction.

2. **Local and structural reductions for chordal clique partitions.**  
   This manuscript develops the local toolkit used in the chordal proof.

3. **A fractional triangle theorem for chordal graphs.**  
   This manuscript proves the fractional chordal theorem.

4. **Clique partitions of chordal graphs.**  
   This manuscript derives the announced clique partition theorem from the fractional theorem using fractional-to-integral rounding and the split lower bound.

The present announcement is intended only to record the main result and the proof architecture. Full details, including the local reduction toolkit and finite certificates, will appear in the companion manuscripts.

## Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support during the development of this work.

The author used AI-assisted tools, including Gemini 3.5 Pro and ChatGPT, during the development of this work for exploratory search, testing possible approaches, looking for contradictions, organizing proof strategies, improving exposition, and preparing drafts. All mathematical claims, proofs, citations, and final editorial decisions are the sole responsibility of the author. No AI system is listed as an author.

## References

[1] G.-T. Chen, P. Erdős, and E. T. Ordman, *Clique partitions of split graphs*, in *Combinatorics, graph theory, algorithms and applications* (Beijing, 1993), 21--30, 1994.

[2] P. Erdős, E. T. Ordman, and Y. Zalcstein, *Clique partitions of chordal graphs*, Combinatorics, Probability and Computing (1993), 409--415.

[3] P. Erdős, A. W. Goodman, and L. Pósa, *The representation of a graph by set intersections*, Canadian Journal of Mathematics 18 (1966), 106--112.

[4] P. E. Haxell and V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21 (2001), 13--38.

[5] R. Yuster, *Integer and fractional packing of families of graphs*, Combinatorica 28 (2008), 245--251.
