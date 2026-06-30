# Clique Partitions of Chordal Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Technical Draft v0.2.** Paper D in the series on clique partitions in split and chordal graphs. This is a technical working draft, not yet a public preprint.

**Keywords.** Clique partitions; chordal graphs; split graphs; triangle packings; fractional packings; Erdős problems.

**MSC 2020.** 05C70, 05C35, 05C65, 05C69.

## Abstract

We derive the asymptotic clique partition theorem for chordal graphs from the fractional triangle theorem proved in Paper C and the fixed-family fractional-to-integral packing theorem of Haxell--Rödl and Yuster. Specifically, for every chordal graph \(G\) on \(n\) vertices,

\[
\operatorname{cp}(G)\le
\left(\frac16+o(1)\right)n^2.
\]

The constant is sharp: the complete split graph \(K_p\vee\overline{K}_{2p}\), analyzed in Paper A, is chordal and has clique partition number \(n^2/6+O(n)\). Thus

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

This paper contains the short final rounding and sharpness step of the series.

---

# 1. Introduction

The edge clique partition number \(\operatorname{cp}(G)\) is the minimum number of cliques whose edge sets partition \(E(G)\). Erdős, Ordman and Zalcstein asked whether every \(n\)-vertex chordal graph admits an edge clique partition with

\[
\frac{n^2}{6}+O(n)
\]

parts. The complete split graph \(K_p\vee\overline{K}_{2p}\), \(n=3p\), shows that the constant \(1/6\) is the correct asymptotic barrier.

This paper is the final step in the series. Paper A proves the sharp split graph theorem. Paper B develops the local and structural chordal toolkit. Paper C proves the fractional chordal theorem

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

Here we combine that theorem with standard fractional-to-integral packing rounding for fixed graph families.

## Main theorem

### Theorem D.1 — Chordal Clique Partition Theorem

For chordal graphs,

\[
\max\{\operatorname{cp}(G):G\text{ chordal}, |V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\]

---

# 2. Triangle packings and clique partitions

Let \(\nu_3(G)\) denote the maximum number of edge-disjoint triangles in \(G\), and let \(\nu_3^*(G)\) denote the maximum total weight of a fractional triangle packing.

## Lemma D.2 — Triangle packing to clique partition

For every graph \(G\),

\[
\operatorname{cp}(G)\le |E(G)|-2\nu_3(G).
\]

**Proof.** Start with singleton-edge cliques. For each triangle in an edge-disjoint triangle packing, replace its three singleton-edge cliques by one triangle clique. This saves two cliques per triangle.

---

# 3. Imported fractional theorem

From Paper C:

## Theorem C.1 — Fractional Chordal Theorem

For every chordal graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

---

# 4. Fractional-to-integral triangle rounding

By Haxell--Rödl and Yuster, for the fixed family \(\{K_3\}\),

\[
\nu_3(G)\ge \nu_3^*(G)-o(n^2).
\]

---

# 5. Upper bound

Let \(G\) be chordal on \(n\) vertices. Then

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\]

Using rounding,

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3^*(G)+o(n^2).
\]

Using Paper C,

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

---

# 6. Sharpness

From Paper A, the split construction

\[
G_p=K_p\vee\overline{K}_{2p}
\]

has \(n=3p\), is chordal, and satisfies

\[
\operatorname{cp}(G_p)\ge \frac{n^2}{6}-O(n).
\]

Thus the upper bound is sharp.

---

# 7. Proof-status audit

| Item | Source | Status |
|---|---|---|
| Split lower bound | Paper A | preprint-level draft |
| Local chordal toolkit | Paper B | technical draft; needs final verification |
| Fractional chordal theorem | Paper C | technical draft; conditional on Paper B |
| Fractional-to-integral rounding | external theorem | citation needed in final form |
| Chordal clique partition theorem | Paper D | follows from above |

---

# 8. Discussion

Paper D is intentionally short. The difficult parts of the argument are not in this paper: the split extremal construction is treated in Paper A, and the fractional chordal theorem is proved in Papers B and C. The role of this paper is to make explicit that the fractional result is strong enough to imply the integral clique partition theorem asymptotically.

A possible final presentation choice is to merge this paper into the end of Paper C. Keeping it separate has the advantage of cleanly distinguishing the fractional chordal theorem from the final clique partition corollary.

---


# 9. Further directions

The final theorem leaves several natural follow-up questions.

1. **Exact finite bounds.** The result is asymptotic. Determining the best possible \(O(n)\) term, or exact extremal values for finite \(n\), remains open.

2. **Constructive partitions.** The proof route is through fractional triangle packing and asymptotic rounding. It would be useful to extract explicit near-optimal clique partitions for chordal graphs.

3. **Shorter proofs for subclasses.** The split case has a much cleaner proof, and intermediate chordal subclasses may admit simpler arguments.

4. **Presentation choice.** This paper may ultimately remain standalone or be merged into Paper C as the final rounding section.

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support during the development of this work.

The author used AI-assisted tools, including Gemini 3.5 Pro and ChatGPT, during the development of this work for exploratory search, testing possible approaches, looking for contradictions, organizing proof strategies, improving exposition, and preparing drafts. All mathematical claims, proofs, citations, and final editorial decisions are the sole responsibility of the author. No AI system is listed as an author.

# References

- G.-T. Chen, P. Erdős, and E. T. Ordman, *Clique partitions of split graphs*, in *Combinatorics, graph theory, algorithms and applications* (Beijing, 1993), 21--30, 1994.
- P. Erdős, E. T. Ordman, and Y. Zalcstein, *Clique partitions of chordal graphs*, Combinatorics, Probability and Computing (1993), 409--415.
- P. Erdős, A. W. Goodman, and L. Pósa, *The representation of a graph by set intersections*, Canadian Journal of Mathematics 18 (1966), 106--112.
- P. E. Haxell and V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21 (2001), 13--38.
- R. Yuster, *Integer and fractional packing of families of graphs*, Combinatorica 28 (2008), 245--251.
