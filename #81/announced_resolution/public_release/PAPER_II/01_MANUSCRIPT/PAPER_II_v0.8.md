# Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
jtraverso@gmail.com  
ORCID: 0009-0003-6068-4096

**Final author manuscript:** v0.8  
**Date:** July 3, 2026  
**Status:** closed author version; the proof is analytic modulo cited mathematical theorems; extensive multi-model AI-assisted adversarial checking completed; not independently peer-reviewed or journal-refereed; forward-citation and novelty tracking remain pending

---

## Abstract

Balogh, He, Krueger, Nguyen, and Wigal developed a general framework for
fractional clique covers and clique decompositions based on Zykov
symmetrization. We prove a constrained version for chordal graphs. If two
nonadjacent maximal clone classes contain simplicial vertices, symmetrizing
either class to the other preserves chordality; their fractional
symmetrization lemma guarantees a nondecreasing direction, and every step
merges clone classes.

The terminal chordal graphs are precisely the complete split graphs
\[
S_{p,q}:=K_p\vee\overline K_q.
\]
Hence every isomorphism-invariant clone-symmetrization-monotone parameter
attains its maximum over \(n\)-vertex chordal graphs on one of the \(n+1\)
graphs \(S_{p,n-p}\). The same maximum is therefore attained inside the
threshold graphs. In particular, this applies to all fractional
clique-cover and clique-decomposition parameters \(CC_t^*(G,\mathbf c)\)
and \(CD_t^*(G,\mathbf c)\) in the Balogh--He--Krueger--Nguyen--Wigal
framework.

For
\[
\Phi_r^*(G)
=
|E(G)|-\left(\binom r2-1\right)\nu_r^*(G),
\]
the reduction leaves a two-variable orbit linear program on \(S_{p,q}\).
Solving it gives an exact finite formula for every \(r\ge3\): the optimum is
the larger of an explicit \(K_r\)-free candidate and the nearest admissible
integer to the vertex of the saturated quadratic. For triangles this
specializes to
\[
\max_{\substack{|V(G)|=n\\G\text{ chordal}}}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.
\]
For every fixed \(r\), the exact formula implies
\[
\max_{\substack{|V(G)|=n\\G\text{ chordal}}}\Phi_r^*(G)
=
\frac{r-1}{4r}n^2+O_r(n).
\]

As consequences, the maximum number of parts in a \(K_r\)-and-edge
partition of an \(n\)-vertex chordal graph is
\[
\left(\frac{r-1}{4r}+o(1)\right)n^2,
\]
and a complete-split extremizer can be constructed in exact polynomial
time for fixed \(r\). The structural reduction and finite fractional
optimization are exact; the \(o(n^2)\) loss enters only in the final
fractional-to-integral packing theorem.

**Keywords:** chordal graph; complete split graph; threshold graph; clique
cover; clique decomposition; fractional clique packing; Zykov
symmetrization; clone classes; simplicial vertex.



---

# 1. Introduction

A split graph is a graph whose vertex set can be partitioned into a clique
and an independent set. A **complete split graph** is a graph of the form
\[
S_{p,q}:=K_p\vee\overline K_q,
\tag{1.1}
\]
where every clique vertex is adjacent to every independent vertex.

Erdős, Ordman, and Zalcstein asked for the asymptotic maximum of the
edge-clique partition number \(\operatorname{cp}(G)\) over \(n\)-vertex
chordal graphs. The complete split constructions in the split-graph
literature already show that the leading constant is at least \(1/6\).

The starting point of this paper is the fractional clone-symmetrization
framework of Balogh, He, Krueger, Nguyen, and Wigal. Their unrestricted
process produces complete multipartite extremizers. We restrict the
operation to maximal clone classes containing simplicial vertices. This
keeps the graph chordal and leads to a different canonical terminal family:
the complete split graphs.

The paper separates into three layers.

1. **Structure.** Constrained symmetrization reduces every relevant chordal
   extremal problem to \(S_{p,n-p}\).
2. **Analysis.** On \(S_{p,q}\), the fixed-\(K_r\) packing problem becomes a
   two-variable orbit linear program.
3. **Applications.** Solving that program gives the exact finite \(K_r\)
   theorem, its triangle specialization, the integral \(K_r\)-and-edge
   asymptotics, and the constructive fixed-\(r\) reduction.

Once the complete-split reduction has been established, every quantitative
result in the paper follows from the two-orbit program. This is a worst-case
extremal reduction, not a typical-graph statement; it is therefore distinct
from the theorem that almost all labelled chordal graphs are split.

## 1.1 Structural result

Let \(\mathcal C_n\) be the family of chordal graphs on a fixed
\(n\)-vertex set, and let
\[
\mathcal Q_n
=
\{S_{p,n-p}:0\le p\le n\}.
\]

A graph parameter \(F\) is **clone-symmetrization monotone** if, whenever
\(U,V\) are disjoint nonadjacent clone classes,
\[
F(G)
\le
\max\{F(G(U\to V)),F(G(V\to U))\}.
\tag{1.2}
\]

## Theorem 1.1 — Complete-split extremizer principle

Let \(F\) be an isomorphism-invariant clone-symmetrization-monotone graph
parameter. For every chordal graph \(G\), there is a complete split graph
\(S_{p,n-p}\) on the same vertex set such that
\[
F(S_{p,n-p})\ge F(G).
\tag{1.3}
\]

Consequently,
\[
\boxed{
\max_{G\in\mathcal C_n}F(G)
=
\max_{0\le p\le n}F(S_{p,n-p}).
}
\tag{1.4}
\]

## 1.2 Universal fractional consequence

For every integer \(t\ge1\) and every nonnegative clique-cost sequence
\(\mathbf c\), let
\[
CC_t^*(G,\mathbf c)
\quad\text{and}\quad
CD_t^*(G,\mathbf c)
\]
denote the fractional \(t\)-clique cover and fractional \(t\)-clique
decomposition parameters of Balogh et al.

## Corollary 1.2

For every \(t\ge1\), every nonnegative cost sequence \(\mathbf c\), and every
\(n\),
\[
\max_{G\in\mathcal C_n}CC_t^*(G,\mathbf c)
=
\max_{0\le p\le n}CC_t^*(S_{p,n-p},\mathbf c),
\tag{1.5}
\]
and
\[
\max_{G\in\mathcal C_n}CD_t^*(G,\mathbf c)
=
\max_{0\le p\le n}CD_t^*(S_{p,n-p},\mathbf c).
\tag{1.6}
\]

Thus an extremal optimization over all chordal graphs reduces to at most
\(n+1\) complete split graphs.


Since every complete split graph is a threshold graph and every threshold
graph is chordal, Theorem 1.1 also gives a threshold-graph sandwich; see
Corollary 5.1.

## 1.3 Quantitative fixed-motif results

For \(r\ge3\), let \(\nu_r^*(G)\) be the fractional packing number of
edge-capacitated copies of \(K_r\), and define
\[
\Phi_r^*(G)
=
|E(G)|
-
\left(\binom r2-1\right)\nu_r^*(G).
\tag{1.7}
\]

## Corollary 1.3

For every \(r\ge3\) and every \(n\),
\[
\max_{G\in\mathcal C_n}\Phi_r^*(G)
=
\max_{0\le p\le n}\Phi_r^*(S_{p,n-p}).
\tag{1.8}
\]

The right-hand side is evaluated explicitly in Section 6.

## Theorem 1.4 — Exact triangle maximum

For every \(n\ge1\),
\[
\boxed{
\max_{G\in\mathcal C_n}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\left\lfloor
\frac{(2n+1)^2}{24}
\right\rfloor.
}
\tag{1.9}
\]

## Theorem 1.5 — Exact finite \(K_r\) maximum

Fix \(r\ge3\) and \(n\ge1\). Put
\[
\ell=\min\{n,r-2\},
\qquad
L_{r,n}=\frac{\ell(2n-\ell-1)}2.
\tag{1.10}
\]
If \(n\ge r\), define
\[
p_0=\frac{(r-1)n+1}{2r},
\qquad
d_{r,n}=\min_{\substack{p\in\mathbb Z\\p\ge r-1}}|p-p_0|,
\tag{1.11}
\]
and
\[
A_{r,n}^{\#}
=
\frac{((r-1)n+1)^2}{4r(r-1)}
-
\frac r{r-1}d_{r,n}^2.
\tag{1.12}
\]
Then
\[
\boxed{
\max_{G\in\mathcal C_n}\Phi_r^*(G)
=
\begin{cases}
L_{r,n},&n<r,\\[2mm]
\max\{L_{r,n},A_{r,n}^{\#}\},&n\ge r.
\end{cases}
}
\tag{1.13}
\]

In particular, for every fixed \(r\ge3\),
\[
\max_{G\in\mathcal C_n}\Phi_r^*(G)
=
\frac{r-1}{4r}n^2+O_r(n).
\tag{1.14}
\]

## 1.4 Integral application

Let \(\pi_r(G)\) be the minimum number of parts in a partition of \(E(G)\)
into copies of \(K_r\) and single edges. Equivalently,
\[
\pi_r(G)
=
|E(G)|
-
\left(\binom r2-1\right)\nu_r(G).
\tag{1.15}
\]

## Corollary 1.6

For every fixed \(r\ge3\),
\[
\boxed{
\max_{G\in\mathcal C_n}\pi_r(G)
=
\left(\frac{r-1}{4r}+o(1)\right)n^2.
}
\tag{1.16}
\]

For \(r=3\), this gives the upper bound needed for the chordal
clique-partition problem:
\[
\operatorname{cp}(G)
\le
\pi_3(G)
\le
\left(\frac16+o(1)\right)n^2.
\tag{1.17}
\]
The known complete split construction gives the matching lower bound for
\(\operatorname{cp}\).

## 1.5 Constructive consequence

## Corollary 1.7

For every fixed \(r\ge3\), there is an exact polynomial-time algorithm that,
given an \(n\)-vertex chordal graph \(G\), constructs an \(n\)-vertex
complete split graph \(S_{p,n-p}\) satisfying
\[
\Phi_r^*(S_{p,n-p})\ge\Phi_r^*(G).
\tag{1.18}
\]

The degree of the polynomial depends on \(r\). No polynomial-time claim is
made when \(r\) is part of the input or for arbitrary unrestricted cost
sequences in Corollary 1.2.

## 1.6 Organization

Section 2 recalls the fractional symmetrization framework and identifies
\(\Phi_r^*\) as a clique-decomposition cost. Sections 3--5 prove the
constrained chordal reduction and the complete-split terminal
characterization. Section 6 solves the complete-split orbit program.
Sections 7--9 derive the exact triangle, exact finite fixed-\(r\), and
integral consequences. Sections 10--12 record the fractional limitation,
computational audit, attribution, limitations, and future directions.

---

# 2. Fractional framework and prior symmetrization

Fix \(t\ge1\) and a nonnegative cost sequence
\[
\mathbf c=(c_i)_{i\ge t}.
\]

A fractional \(t\)-clique cover assigns a nonnegative weight \(w_Q\) to
every clique \(Q\) of order at least \(t\), so that every copy \(T\) of
\(K_t\) satisfies
\[
\sum_{Q\supseteq T}w_Q\ge1.
\]
Its cost is
\[
\sum_Qc_{|Q|}w_Q.
\]
The minimum cost is \(CC_t^*(G,\mathbf c)\).

A fractional \(t\)-clique decomposition replaces the cover inequalities by
equalities:
\[
\sum_{Q\supseteq T}w_Q=1.
\]
Its minimum cost is \(CD_t^*(G,\mathbf c)\).

Two vertices are **clones** when they have the same open neighborhood. Clone
classes are independent sets.

Let \(U,V\) be disjoint clone classes with no edges between them.
The graph \(G(U\to V)\) is obtained by deleting every edge incident with
\(U\) and then making every vertex of \(U\) a false twin of the vertices of
\(V\).

The following is the symmetrization lemma of Balogh, He, Krueger, Nguyen,
and Wigal.

## Lemma 2.1 — Fractional clone symmetrization

For every \(t\ge1\) and every nonnegative cost sequence \(\mathbf c\),
\[
CC_t^*(G,\mathbf c)
\le
\max\{
CC_t^*(G(U\to V),\mathbf c),
CC_t^*(G(V\to U),\mathbf c)
\},
\tag{2.1}
\]
and
\[
CD_t^*(G,\mathbf c)
\le
\max\{
CD_t^*(G(U\to V),\mathbf c),
CD_t^*(G(V\to U),\mathbf c)
\}.
\tag{2.2}
\]

## 2.1 The \(K_r\)-packing functional as a decomposition cost

Fix \(r\ge3\), set \(t=2\), and take
\[
c_2=c_r=1,
\qquad
c_i=\binom i2
\quad(i\ne2,r).
\tag{2.3}
\]

For \(r=3\), this reads
\[
c_2=c_3=1,
\qquad
c_i=\binom i2\quad(i\ge4),
\]
so the triangle convention is exactly the case \(r=3\) of (2.3).

A clique of order \(i\notin\{2,r\}\) can be replaced by its constituent
edges at the same cost. Thus an optimal decomposition may be taken to use
only edges and copies of \(K_r\).

If the total weight assigned to \(K_r\)'s is \(y\), then their total edge
load is
\[
\binom r2y.
\]
The remaining edge weight has total
\[
|E(G)|-\binom r2y,
\]
and the decomposition cost is
\[
|E(G)|
-
\left(\binom r2-1\right)y.
\]
Maximizing \(y\) gives
\[
CD_2^*(G,\mathbf c)
=
|E(G)|
-
\left(\binom r2-1\right)\nu_r^*(G)
=
\Phi_r^*(G).
\tag{2.4}
\]

## 2.2 Direct triangle specialization

For completeness, the case \(r=3\) also has a short direct proof.

Let \(u,v\) be nonadjacent vertices. Copying the incident weights of an
optimal fractional triangle cover from \(u\) to a new false twin \(v\), and
then performing the reverse copying, gives two feasible covers whose costs
sum to twice the original cost. Together with the corresponding edge-count
identity,
\[
\Phi_3^*(G_{v\to u})
+
\Phi_3^*(G_{u\to v})
\ge
2\Phi_3^*(G).
\tag{2.5}
\]

This is included only to make the triangle application self-contained; the
general argument uses Lemma 2.1.

---

# 3. Structural lemmas for constrained symmetrization

A vertex is simplicial when its open neighborhood is a clique.

## Lemma 3.1

If one vertex of a clone class is simplicial, then every vertex in that
class is simplicial and their common open neighborhood is a clique.

### Proof

All vertices in the class have the same open neighborhood.
\(\square\)

## Lemma 3.2 — Chordality preservation

Let \(G\) be chordal. Let \(U,V\) be nonadjacent clone classes, and suppose
that the vertices of \(V\) are simplicial. Then \(G(U\to V)\) is chordal.

### Proof

Delete \(U\). The resulting graph is chordal. The common neighborhood of
\(V\) is a clique. Add the vertices of \(U\) back one at a time with that
same clique neighborhood. Adding a vertex with clique neighborhood preserves
chordality.
\(\square\)

## Lemma 3.3 — Clone-class progress

Suppose \(U,V\) are distinct maximal clone classes with no edges between
them. In either \(G(U\to V)\) or \(G(V\to U)\), the two classes merge and no
old clone class is split. Hence the number of maximal clone classes strictly
decreases.

### Proof

After symmetrization, every vertex of \(U\cup V\) has the same open
neighborhood.

Let \(W\) be any clone class disjoint from \(U\cup V\). Every two vertices of
\(W\) have the same adjacency to the source class, and the operation changes
their adjacency to the target class in the same way. Thus they remain
clones. Other classes may merge, but none splits.
\(\square\)

---

# 4. Complete-split terminal structure

Call a chordal graph **simplicially homogeneous** if every two nonadjacent
simplicial vertices have the same open neighborhood.

## Theorem 4.1 — Terminal characterization

A chordal graph is simplicially homogeneous if and only if it is complete
split.

### Proof

Every complete split graph is simplicially homogeneous: its only
nonadjacent simplicial vertices lie in the independent set and all have the
same neighborhood.

Conversely, suppose \(G\) is simplicially homogeneous.

If \(G\) is disconnected and one component contains an edge, choose a
simplicial vertex with nonempty neighborhood in that component and a
simplicial vertex in another component. They are nonadjacent and have
different neighborhoods, a contradiction. Hence a disconnected
simplicially homogeneous chordal graph is edgeless and is \(S_{0,n}\).

Assume that \(G\) is connected. If \(G\) is complete, it is \(S_{n,0}\).
Otherwise, let \(\mathcal T\) be a clique tree. It has at least two leaf
maximal cliques.

For a leaf clique \(L\), let \(L'\) be its unique neighboring clique and put
\[
P_L=L\setminus L'.
\]
The set \(P_L\) is nonempty. Every \(x\in P_L\) occurs in no maximal clique
other than \(L\), so \(x\) is simplicial and
\[
N_G(x)=L\setminus\{x\}.
\tag{4.1}
\]

We claim that \(P_L\) is a singleton. Choose a different leaf clique \(M\)
and a vertex \(y\in P_M\). If \(P_L\) contained distinct vertices \(x,x'\),
then both pairs \(x,y\) and \(x',y\) would be nonadjacent. Homogeneity would
give
\[
N_G(x)=N_G(y)=N_G(x').
\tag{4.2}
\]
But \(x,x'\in L\), so \(x'\in N_G(x)\), while
\(x'\notin N_G(x')\), contradicting (4.2).

Write
\[
P_L=\{x_L\}.
\]
Then
\[
N_G(x_L)=L\cap L'.
\tag{4.3}
\]

Private vertices from distinct leaf cliques are nonadjacent. Their
neighborhoods are therefore equal. Hence every leaf separator in (4.3) is
the same clique; call it \(K\).

Every leaf bag contains \(K\). For \(a\in K\), the bags containing \(a\)
form a connected subtree containing every leaf of \(\mathcal T\). A
connected subtree of a finite tree containing every leaf is the whole tree.
Thus \(K\) lies in every maximal clique and is universal in \(G\).

Put
\[
J=G-K.
\]
Every leaf-private vertex is isolated in \(J\). If \(J\) contained an edge,
a nontrivial connected component of the chordal graph \(J\) would contain a
simplicial vertex \(z\) with nonempty neighborhood in \(J\). Since \(K\) is
universal,
\[
N_G(z)=K\dot\cup N_J(z)
\]
is a clique, so \(z\) is simplicial in \(G\).

A leaf-private vertex \(x_L\) is nonadjacent to \(z\), but
\[
N_G(x_L)=K
\ne
K\dot\cup N_J(z)=N_G(z),
\]
contradicting homogeneity. Therefore \(J\) is independent and
\[
G=K\vee\overline J.
\]
Thus \(G\) is complete split.
\(\square\)

---

# 5. Complete-split reduction

## Proof of Theorem 1.1

Start with a chordal graph \(G\).

If \(G\) is complete split, stop. Otherwise, Theorem 4.1 and its
contrapositive give nonadjacent simplicial vertices \(u,v\) with distinct
open neighborhoods.

Let \(U,V\) be their maximal clone classes. They are nonadjacent and
simplicial. Clone-symmetrization monotonicity gives a direction, either
\[
G(U\to V)
\quad\text{or}\quad
G(V\to U),
\]
whose \(F\)-value is at least \(F(G)\).

The selected graph is chordal by Lemma 3.2 and has strictly fewer maximal
clone classes by Lemma 3.3.

Repeat. The number of maximal clone classes decreases at every step, so the
process terminates after at most \(n-1\) steps. The terminal graph is
simplicially homogeneous and hence complete split by Theorem 4.1.
\(\square\)

Corollaries 1.2 and 1.3 follow from Lemma 2.1 and identity (2.4).

## Corollary 5.1 — Threshold sandwich

Let \(\mathcal{Th}_n\) be the family of threshold graphs on the fixed
\(n\)-vertex set. For every isomorphism-invariant
clone-symmetrization-monotone graph parameter \(F\),
\[
\boxed{
\max_{G\in\mathcal C_n}F(G)
=
\max_{G\in\mathcal{Th}_n}F(G)
=
\max_{0\le p\le n}F(S_{p,n-p}).
}
\tag{5.1}
\]

### Proof

A threshold graph can be constructed by repeatedly adding an isolated or a
universal vertex. To construct \(S_{p,q}\), first add \(q\) isolated
vertices and then add \(p\) universal vertices. Hence
\[
\mathcal Q_n\subseteq\mathcal{Th}_n\subseteq\mathcal C_n.
\]
Theorem 1.1 gives
\[
\max_{\mathcal C_n}F=\max_{\mathcal Q_n}F,
\]
and the inclusions force equality throughout.
\(\square\)

This applies in particular to \(CC_t^*\), \(CD_t^*\), and \(\Phi_r^*\).

## Algorithm 5.2 — Fixed-\(r\) construction

Fix \(r\ge3\). Given a chordal graph \(G\), repeat while the current graph is
not complete split:

1. use the contrapositive of Theorem 4.1 to find nonadjacent simplicial
   vertices \(u,v\) with distinct neighborhoods;
2. let \(U,V\) be their maximal clone classes;
3. form \(G(U\to V)\) and \(G(V\to U)\);
4. compute \(\Phi_r^*\) in both graphs and retain a direction of maximum
   value.

## Proof of Corollary 1.7

There are at most \(n-1\) iterations.

For a graph \(J\), \(\nu_r^*(J)\) is the optimum of the explicit packing LP
with one variable for each copy of \(K_r\) and one capacity constraint for
each edge. For fixed \(r\), it has at most
\[
\binom nr=O(n^r)
\]
variables and
\[
\binom n2=O(n^2)
\]
constraints.

The LP has rational \(0\)-\(1\) data and is solvable exactly in polynomial
time. Clone classes, simplicial vertices, the two cloned graphs, and
complete-split recognition are also computable in polynomial time.
Therefore Algorithm 5.2 is polynomial for fixed \(r\).
\(\square\)

The scope restrictions are recorded in Section 12.2.

---

# 6. The complete-split orbit program

The structural part of the paper is now complete. All remaining
quantitative statements reduce to evaluating the chosen parameter on
\[
S_{p,q}=K_p\vee\overline K_q.
\]
For the fixed-motif functional \(\Phi_r^*\), this evaluation is the following
two-orbit linear program.

Fix \(r\ge3\) and write
\[
S_{p,q}=K_p\vee\overline K_q.
\]

Every \(K_r\) in \(S_{p,q}\) has one of two types:

1. it is contained in \(K_p\);
2. it contains one independent vertex and \(r-1\) clique vertices.

Put
\[
m=\binom r2,
\qquad
c=\binom{r-1}{2},
\qquad
P=\binom p2.
\tag{6.1}
\]

After averaging over
\[
\operatorname{Sym}(p)\times\operatorname{Sym}(q),
\]
let \(\alpha\) be the total packing weight on the first type and \(\beta\)
the total packing weight on the second type.

For \(p\ge r\), the exact orbit LP is
\[
\max\ \alpha+\beta
\tag{6.2}
\]
subject to
\[
m\alpha+c\beta\le P,
\tag{6.3}
\]
\[
(r-1)\beta\le pq,
\tag{6.4}
\]
and
\[
\alpha,\beta\ge0.
\tag{6.5}
\]

Constraint (6.3) is the clique-edge capacity, while (6.4) is the
cross-edge capacity. Proposition 6.1 proves directly, by orbit counting,
that these two inequalities are exactly equivalent to all individual edge
constraints after averaging.

The breakpoint has a direct geometric interpretation. A unit of the mixed
variable \(\beta\) uses only
\[
c=\binom{r-1}{2}
\]
units of clique-edge capacity, compared with
\[
m=\binom r2
\]
for a unit of the internal variable \(\alpha\), but it also requires
\(r-1\) cross edges. Thus the LP uses mixed cliques as aggressively as the
cross-edge reservoir permits. The equality
\[
\frac{pq}{r-1}=\frac{P}{c}
\quad\Longleftrightarrow\quad
(r-2)q=p-1
\tag{6.6}
\]
is the exact point at which the available cross-edge capacity is just large
enough for mixed \(K_r\)'s alone to exhaust the clique-edge capacity.

Above this threshold, the clique-edge constraint is saturated with
\(\beta\) and the optimum has \(\alpha=0\). Below it, the cross-edge
constraint binds first; the unused clique-edge capacity must then be filled
by the residual internal variable \(\alpha>0\).

## Proposition 6.1 — Exact fractional packing

For \(p\ge r\),
\[
\boxed{
\nu_r^*(S_{p,q})
=
\frac Pm
+
\left(\frac Pc-\frac Pm\right)
\min\left\{
1,\frac{(r-2)q}{p-1}
\right\}.
}
\tag{6.7}
\]

If \(p=r-1\) and \(q\ge1\), then
\[
\nu_r^*(S_{p,q})=1.
\tag{6.8}
\]
If \(p<r-1\), or if \(p=r-1,q=0\), then
\[
\nu_r^*(S_{p,q})=0.
\tag{6.9}
\]

### Proof

Assume first that \(p\ge r\). The feasible region and objective of the
full fractional packing LP are invariant under
\[
\operatorname{Sym}(p)\times\operatorname{Sym}(q).
\]
Averaging an optimal solution over this group therefore preserves
feasibility and total weight and produces a symmetric optimum. Let
\(\alpha\) be the
total weight on the \(\binom pr\) internal copies of \(K_r\), distributed
uniformly over that orbit, and let \(\beta\) be the total weight on the
\[
q\binom p{r-1}
\]
mixed copies, also distributed uniformly.

Every clique edge lies in \(\binom{p-2}{r-2}\) internal copies. Its load
from the internal orbit is therefore
\[
\frac{\alpha\binom{p-2}{r-2}}{\binom pr}
=
\frac{\binom r2}{\binom p2}\alpha
=
\frac{m\alpha}{P}.
\]
The same clique edge lies in
\[
q\binom{p-2}{r-3}
\]
mixed copies, so its mixed load is
\[
\frac{\beta q\binom{p-2}{r-3}}
     {q\binom p{r-1}}
=
\frac{\binom{r-1}{2}}{\binom p2}\beta
=
\frac{c\beta}{P}.
\]
Thus every clique-edge capacity constraint is exactly
\[
m\alpha+c\beta\le P.
\]

Every cross edge lies in \(\binom{p-1}{r-2}\) mixed copies. Its load is
\[
\frac{\beta\binom{p-1}{r-2}}
     {q\binom p{r-1}}
=
\frac{r-1}{pq}\beta,
\]
so every cross-edge capacity constraint is exactly
\[
(r-1)\beta\le pq.
\]

Conversely, if \(\alpha,\beta\ge0\) satisfy these two inequalities, the
uniform assignments above give a feasible fractional packing. Hence the
full packing LP is exactly equivalent to (6.2)--(6.5).

Since
\[
c=\binom{r-1}{2}<\binom r2=m,
\]
a unit of \(\beta\) uses less clique-edge capacity than a unit of
\(\alpha\). An optimum therefore maximizes \(\beta\) first:
\[
\beta
=
\min\left\{
\frac Pc,\frac{pq}{r-1}
\right\},
\]
and fills the remaining clique-edge capacity with
\[
\alpha=\frac{P-c\beta}{m}.
\]
The resulting objective value is (6.7).

If \(p=r-1\) and \(q\ge1\), every \(K_r\) consists of all clique vertices
and one independent vertex. Any two such copies share every clique edge,
so the fractional packing number is \(1\). If \(p<r-1\), or if
\(p=r-1,q=0\), no copy of \(K_r\) exists.
\(\square\)

## Corollary 6.2 — Exact form of \(\Phi_r^*\)

For \(p\ge r\), there are two regimes.

If
\[
(r-2)q\ge p-1,
\tag{6.10}
\]
then
\[
\boxed{
\Phi_r^*(S_{p,q})
=
pq-\frac{p(p-1)}{r-1}.
}
\tag{6.11}
\]

If
\[
(r-2)q\le p-1,
\tag{6.12}
\]
then
\[
\boxed{
\Phi_r^*(S_{p,q})
=
\frac{\binom p2+pq}{\binom r2}.
}
\tag{6.13}
\]

The two expressions agree on the boundary. Formula (6.11) also remains
valid for \(p=r-1,q\ge1\). For \(p<r-1\), \(\Phi_r^*(S_{p,q})\) is simply
the edge count.

---

# 7. Exact triangle maximum

Put \(r=3\), \(q=n-p\), and
\[
\Phi^*(G)=|E(G)|-2\nu_3^*(G).
\]

In the mixed-saturated regime \(q\ge p-1\),
\[
\Phi^*(S_{p,q})
=
pq-\binom p2.
\tag{7.1}
\]
Completing the square gives
\[
pq-\binom p2
=
\frac{(2n+1)^2-(6p-(2n+1))^2}{24}.
\tag{7.2}
\]

The minimum possible value of
\[
|6p-(2n+1)|
\]
is \(1\) when \(3\nmid 2n+1\), and \(3\) when
\(3\mid 2n+1\). Since an odd square is congruent to \(1\) or \(9\pmod{24}\),
the maximum of (7.2) over integers \(p\) is
\[
\left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.
\tag{7.3}
\]
The maximizing integer lies near \((2n+1)/6\) and satisfies
\(q\ge p-1\).

In the unsaturated regime \(q\le p-1\),
\[
\Phi^*(S_{p,q})
=
\frac{\binom p2+pq}{3}
=
\frac{p(2n-p-1)}6.
\tag{7.4}
\]
For \(n\ge3\), this is at most \(n(n-1)/6\), which is strictly below the
value in (7.3). The cases \(n=1,2\) are immediate.

This proves Theorem 1.4.

In particular,
\[
\max_{G\in\mathcal C_n}\Phi^*(G)
=
\frac{n^2}{6}+\frac n6+O(1).
\tag{7.5}
\]

---

# 8. Exact finite optimization for \(K_r\)

Fix \(r\ge3\), put \(q=n-p\), and abbreviate
\[
\Psi_{r,n}(p)=\Phi_r^*(S_{p,n-p}).
\]
Corollary 6.2 and the exceptional cases of Proposition 6.1 divide the
optimization into three formal regimes. We show that only two can be
globally extremal.

## 8.1 The \(K_r\)-free branch

For \(p\le r-2\), the graph \(S_{p,n-p}\) contains no \(K_r\). Hence
\[
\Psi_{r,n}(p)
=
\binom p2+p(n-p)
=
\frac{p(2n-p-1)}2.
\tag{8.1}
\]
This is increasing on the permitted integer interval. With
\[
\ell=\min\{n,r-2\},
\]
the branch maximum is therefore
\[
\boxed{
L_{r,n}=\frac{\ell(2n-\ell-1)}2.
}
\tag{8.2}
\]
If \(n<r\), this is \(\binom n2\).

## 8.2 The saturated branch

In the saturated regime,
\[
(r-2)(n-p)\ge p-1,
\tag{8.3}
\]
we have
\[
A_{r,n}(p)
=
\Psi_{r,n}(p)
=
pn-\frac r{r-1}p^2+\frac p{r-1}.
\tag{8.4}
\]
Completing the square gives
\[
A_{r,n}(p)
=
\frac{((r-1)n+1)^2}{4r(r-1)}
-
\frac r{r-1}(p-p_0)^2,
\tag{8.5}
\]
where
\[
p_0=\frac{(r-1)n+1}{2r}.
\tag{8.6}
\]
For \(n\ge r\), define
\[
d_{r,n}
=
\min_{\substack{p\in\mathbb Z\\p\ge r-1}}|p-p_0|.
\tag{8.7}
\]
The nearest constrained integer lies in the saturated interval (8.3). To
see this, if \(n<2r\), then \(p_0<r-1\), so the constrained minimizer is
\(p=r-1\), which satisfies (8.3). If \(n\ge2r\), then \(p_0\ge r-1\)
and the saturated upper endpoint is
\[
p_{\mathrm{sat}}=\frac{(r-2)n+1}{r-1}.
\]
Indeed,
\[
p_{\mathrm{sat}}-p_0-1
=
\frac{n(r^2-2r-1)-2r^2+3r+1}{2r(r-1)}
\ge0
\]
for \(n\ge2r\) and \(r\ge3\). Hence both nearest integers to \(p_0\)
are saturated. Therefore the exact saturated maximum is
\[
\boxed{
A_{r,n}^{\#}
=
\frac{((r-1)n+1)^2}{4r(r-1)}
-
\frac r{r-1}d_{r,n}^2.
}
\tag{8.8}
\]
Equivalently, evaluate (8.4) at the one or two integers nearest to
\(\max\{r-1,p_0\}\).

## 8.3 The unsaturated branch is never a third extremizer

In the unsaturated regime,
\[
(r-2)(n-p)\le p-1,
\]
Corollary 6.2 gives
\[
B_{r,n}(p)
=
\frac{p(2n-p-1)}{r(r-1)}.
\tag{8.9}
\]
This is nondecreasing for integers \(p\le n\). Hence every unsaturated value
is at most
\[
U_{r,n}=\frac{n(n-1)}{r(r-1)}.
\tag{8.10}
\]

Suppose first that \(r\le n\le2r-1\). The \(K_r\)-free value at \(p=r-2\)
is
\[
L_{r,n}=\frac{(r-2)(2n-r+1)}2.
\]
After clearing denominators,
\[
2r(r-1)(L_{r,n}-U_{r,n})
=
r(r-1)(r-2)(2n-r+1)-2n(n-1).
\tag{8.11}
\]
The right-hand side is a concave quadratic in \(n\). At \(n=r\) it
equals
\[
r(r-1)(r^2-r-4)>0,
\]
and at \(n=2r-1\) it equals
\[
(r-1)\bigl(r(r-2)(3r-1)-4(2r-1)\bigr)>0.
\]
Thus it is nonnegative throughout the interval, and
\[
U_{r,n}\le L_{r,n}.
\tag{8.12}
\]

Now suppose \(n\ge2r\). Then \(p_0\ge r-1\). Rounding the concave
quadratic (8.5) loses at most \(r/[4(r-1)]\), so
\[
A_{r,n}^{\#}
\ge
\frac{((r-1)n+1)^2}{4r(r-1)}
-
\frac r{4(r-1)}.
\]
Subtracting (8.10) gives
\[
A_{r,n}^{\#}-U_{r,n}
\ge
\frac{(r-3)(r+1)n^2+2(r+1)n+1-r^2}{4r(r-1)}.
\tag{8.13}
\]
For \(r=3\), the numerator is \(8(n-1)>0\); for \(r\ge4\), it is plainly
positive. Hence
\[
U_{r,n}\le A_{r,n}^{\#}.
\tag{8.14}
\]
The unsaturated branch never creates a third global maximum.

Combining Sections 8.1--8.3 proves Theorem 1.5:
\[
\max_{G\in\mathcal C_n}\Phi_r^*(G)
=
\begin{cases}
L_{r,n},&n<r,\\[2mm]
\max\{L_{r,n},A_{r,n}^{\#}\},&n\ge r.
\end{cases}
\tag{8.15}
\]

For fixed \(r\), the \(K_r\)-free candidate is \(O_r(n)\), while
\[
A_{r,n}^{\#}
=
\frac{r-1}{4r}n^2+O_r(n).
\]
Thus
\[
\max_{G\in\mathcal C_n}\Phi_r^*(G)
=
\frac{r-1}{4r}n^2+O_r(n).
\tag{8.16}
\]
For \(r=3\), (8.15) reduces to the closed form in Theorem 1.4.

---

# 9. Integral application

Let
\[
M_r=\binom r2.
\]

Every edge partition into copies of \(K_r\) and single edges corresponds to
an edge-disjoint \(K_r\)-packing, and therefore
\[
\pi_r(G)
=
|E(G)|-(M_r-1)\nu_r(G).
\tag{9.1}
\]

For fixed \(r\), the Haxell--Rödl theorem, or Yuster's family version, gives
uniformly over \(n\)-vertex graphs
\[
\nu_r^*(G)-\nu_r(G)=o(n^2).
\tag{9.2}
\]

Hence
\[
\pi_r(G)
\le
\Phi_r^*(G)+o(n^2).
\]
The asymptotic consequence (8.16) of Theorem 1.5 gives the corresponding upper bound over chordal graphs.

Conversely,
\[
\pi_r(G)\ge\Phi_r^*(G)
\]
for every graph. Applying this to a complete split graph maximizing
\(\Phi_r^*\) gives the matching lower bound. This proves Corollary 1.6.

For \(r=3\), any partition into triangles and edges is a clique partition,
so
\[
\operatorname{cp}(G)\le\pi_3(G).
\]
Together with the classical complete split lower-bound construction, this
settles the Erdős--Ordman--Zalcstein asymptotic constant.

---

# 10. Fractional scope and integral obstruction

The monotonicity relies on convex averaging and has no integral analogue.

Consider two triangles
\[
abc,\qquad cde
\]
sharing only the vertex \(c\). The vertices \(a,d\) are nonadjacent and
simplicial, and
\[
\nu_3(G)=2.
\]
After cloning \(d\) to \(a\), or \(a\) to \(d\), the resulting triangles
share an edge, so both integral packing numbers are \(1\).

Thus the exact reduction must occur at the fractional level. The
\(o(n^2)\) term enters only through (9.2).

---

# 11. Supplementary computational regression tests

Every statement tested in this section is proved analytically in the
manuscript. The supplied scripts are optional regression tests and
reproducibility material; no computation, LP solver, finite graph atlas, or
finite enumeration is a logical premise of any theorem. They provide the
following independent checks:

1. all chordal graph-atlas graphs through seven vertices symmetrize to
   complete split graphs;
2. both clone directions preserve chordality;
3. maximal clone classes strictly decrease;
4. \(\Phi_r^*\) never decreases for \(r=3,4\);
5. chordal and complete-split maxima agree through seven vertices;
6. Proposition 6.1 agrees with the full packing LP for
   \(3\le r\le6\) and \(0\le p,q\le8\);
7. Theorem 1.4 holds for \(1\le n\le500\);
8. the exact finite formula in Theorem 1.5 agrees with direct maximization
   over all \(0\le p\le n\) for \(3\le r\le30\) and \(1\le n\le500\);
9. the fixed-\(r\) leading coefficient agrees numerically for
   \(3\le r\le8\).

The corresponding analytic proofs are Theorem 4.1, Lemmas 2.1 and
3.1--3.3, Proposition 6.1, Sections 7--8, and the standard external
theorems cited in Section 2. The computations are supplementary evidence
only.

---

# 12. Discussion

## 12.1 Contributions

The fractional clone-symmetrization mechanism is due to Balogh et al. The
contribution of this paper is the constrained chordal analysis:

1. simplicial clone-class symmetrization remains inside the chordal class;
2. maximal clone classes give a strictly decreasing finite potential;
3. the terminal chordal graphs are exactly complete split;
4. every fractional parameter in Corollary 1.2 reduces to the \(n+1\)
   graphs \(S_{p,n-p}\), and therefore also to the threshold-graph class;
5. fixed clique motifs admit an explicit two-orbit linear program;
6. that program yields the exact finite \(K_r\) maximum, its triangle
   specialization, the fixed-\(r\) asymptotics, and the fixed-\(r\)
   constructive reduction.

An earlier companion manuscript developed a direct fractional analysis of
split graphs. The complete-split reduction and exact triangle theorem now
make that manuscript unnecessary as a logical dependency of the present
result, although the direct method may retain independent methodological
interest.

## 12.2 Scope and limitations

The claims of the paper are intentionally limited as follows.

- The general fractional symmetrization lemma is attributed to Balogh et al.;
  it is not claimed here as a new method.
- The claimed structural contribution is the constrained chordal process
  and its complete-split terminal family. A targeted search found no earlier
  reduction of this form, but forward-citation tracking and specialist
  review remain necessary.
- The algorithmic statement is polynomial only for fixed \(r\). It is not
  polynomial jointly in \((G,r)\), and no comparable claim is made for
  arbitrary unrestricted cost sequences in Corollary 1.2.
- The algorithm constructs a fractional complete-split extremizer; it does
  not construct the final integral partition supplied asymptotically by
  Haxell--Rödl/Yuster.
- The exact extremizer theorem does not imply stability or characterize all
  near-extremizers.
- Apart from the cited mathematical theorems, the complete proof is
  analytic. No script, solver output, or finite enumeration is used as a
  premise.
- The supplementary computational regressions are independent evidence
  and are not proof dependencies.

## 12.3 Future directions

The one-parameter reduction suggests several separate questions.

1. **Simonovits-type stability.** Determine whether, for every fixed
   \(r\ge3\) and every \(\varepsilon>0\), there is a
   \(\delta=\delta(r,\varepsilon)>0\) such that every \(n\)-vertex chordal
   graph satisfying
   \[
   \Phi_r^*(G)
   \ge
   \max_{H\in\mathcal C_n}\Phi_r^*(H)-\delta n^2
   \]
   is within \(\varepsilon n^2\) edge edits of some maximizing complete
   split graph \(S_{p,n-p}\), or converges to that family in an equivalent
   graphon metric.

   A proof would have to quantify the gain under nonterminal
   symmetrizations and exclude large structural changes with negligible
   objective improvement.

2. Determine exact integer formulas for \(\pi_r\).
3. Develop implementations that avoid repeated general LP solves.
4. Identify other hereditary graph classes whose constrained
   symmetrization has a canonical terminal family.

These questions are independent of the present proof.


---

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children
Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love,
patience, and support.

AI-assisted tools were used during exploratory, computational, adversarial,
and editorial stages. They supported testing of candidate mechanisms, generation and review of
optional regression code, organization of proof gates, bibliographic
searches, and preparation of drafts. Several plausible routes
were rejected or superseded after explicit counterexamples or shorter
arguments were found. All mathematical claims, citations, code, and final
editorial decisions remain the sole responsibility of the author. No AI
system is listed as an author.

---

# References

1. J. Balogh, J. He, R. A. Krueger, T. Nguyen, and M. C. Wigal,
   *Clique covers and decompositions of cliques of graphs*,
   arXiv:2412.05522v2, 2024.

2. E. A. Bender, L. B. Richmond, and N. C. Wormald,
   *Almost all chordal graphs split*,
   Journal of the Australian Mathematical Society (Series A) **38** (1985),
   214--221.
   DOI: [link](https://doi.org/10.1017/S1446788700023077).

3. G.-T. Chen, P. Erdős, and E. T. Ordman,
   *Clique Partitions of Split Graphs*,
   in **Combinatorics, Graph Theory, Algorithms and Applications**
   (Beijing, 1993), World Scientific, 1994, 21--30.

4. V. Chvátal and P. L. Hammer,
   *Aggregation of inequalities in integer programming*,
   in **Studies in Integer Programming**, Annals of Discrete Mathematics
   **1**, North-Holland, 1977, 145--162.

5. G. A. Dirac,
   *On rigid circuit graphs*,
   Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg
   **25** (1961), 71--76.
   DOI: [link](https://doi.org/10.1007/BF02992776).

6. P. Erdős, E. T. Ordman, and Y. Zalcstein,
   *Clique Partitions of Chordal Graphs*,
   Combinatorics, Probability and Computing **2** (1993), 409--415.
   DOI: [link](https://doi.org/10.1017/S0963548300000808).

7. P. E. Haxell and V. Rödl,
   *Integer and Fractional Packings in Dense Graphs*,
   Combinatorica **21** (2001), 13--38.
   DOI: [link](https://doi.org/10.1007/s004930170003).

8. A. Schrijver,
   *Theory of Linear and Integer Programming*,
   Wiley, 1986.

9. R. Yuster,
   *Integer and Fractional Packing of Families of Graphs*,
   Random Structures & Algorithms **26** (2005), 110--118.
   DOI: [link](https://doi.org/10.1002/rsa.20048).

10. A. A. Zykov,
   *On some properties of linear complexes*,
   Matematicheskii Sbornik (N.S.) **24(66)** (1949), 163--188.
