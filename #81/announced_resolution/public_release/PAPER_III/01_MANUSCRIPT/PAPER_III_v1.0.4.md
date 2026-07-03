# Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Frozen author manuscript:** v1.0.4  
**Date:** July 3, 2026  
**Status:** final closed author version; all internal proof steps are analytic, with external theorem dependencies isolated in Section 2.4; supplementary computations are non-logical regression tests; extensive multi-model AI-assisted adversarial checking completed; not yet independently peer-reviewed or journal-refereed

**MSC 2020:** Primary 05C70; Secondary 05C35, 05C72, 05C15.

---

## Abstract

Let \(G=(K\cup I,E)\) be a split graph on \(n\) vertices, with \(K\) a clique and \(I\) an independent set. We prove that there is an absolute constant \(C\) such that

\[
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}+Cn,
\]

where \(\nu_3(G)\) is the maximum number of pairwise edge-disjoint triangles in \(G\). Consequently,

\[
\operatorname{cp}(G)
\le
\frac{n^2}{6}+Cn
\]

for every split graph \(G\), where \(\operatorname{cp}(G)\) is the minimum number of cliques whose edge sets partition \(E(G)\). This strengthens the asymptotic \((1/6+o(1))n^2\) bound to the correct linear-error scale. The leading constant is sharp.

The proof separates three regimes according to \(\alpha=|I|/|K|\). In the bulk regime, an exact four-orbit linear program for a common-neighborhood profile yields a uniform quadratic fractional margin; the Haxell--Rödl theorem then absorbs the subquadratic integrality loss. When \(\alpha\to0\), large edge-disjoint matchings anchored at the independent vertices leave an almost complete, triangle-divisible clique residual, which is decomposed exactly by dense graph decomposition results. When \(\alpha\to2\), averaged factorization closes the short corridor, while a double-factor polarization inequality and a shifted-center gain-completion argument close the remaining mesoscopic corridor.

The proof does not establish the stronger universal estimate \(\nu_3^*(G)-\nu_3(G)=O(n)\). Away from the extremal corridor, a potentially superlinear integrality gap is absorbed by quadratic fractional slack.

**Keywords:** clique partition; split graph; triangle packing; fractional packing; factorization; polarization; list edge coloring; graph decomposition.

---

# 1. Introduction

## 1.1 Clique partitions of split graphs

A **clique partition** of a graph \(G\) is a family of complete subgraphs whose edge sets partition \(E(G)\). Cliques of order two are allowed. The minimum size of such a family is denoted by \(\operatorname{cp}(G)\).

The chordal clique-partition problem of Erdős, Ordman, and Zalcstein asks for the correct extremal order of \(\operatorname{cp}(G)\) on chordal graphs. Their complete-split (indeed threshold) construction shows that the coefficient \(1/6\) is unavoidable. Split graphs form a natural and important subclass of chordal graphs: a graph is split if its vertex set can be partitioned into a clique and an independent set.

A companion manuscript determines the fractional extremal problem exactly. For every \(n\),

\[
\max_{\substack{|V(G)|=n\\G\text{ chordal}}}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\max_{\substack{|V(G)|=n\\G\text{ split}}}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.
\]

It follows, by standard fractional-to-integral rounding, that every chordal graph satisfies

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

The present paper addresses a different and genuinely second-order question: it strengthens the integral bound to \(n^2/6+O(n)\) for arbitrary split graphs.

## 1.2 Triangle packings and the linear-error target

Let \(\nu_3(G)\) be the maximum number of pairwise edge-disjoint triangles in \(G\). Every such packing gives a clique partition: keep every packed triangle and use one \(K_2\) for each uncovered edge. Hence

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\tag{1.1}
\]

The central theorem of this paper is an integral estimate at the correct second-order scale.

### Theorem 1.1 — Linear-error split-graph theorem

There exists an absolute constant \(C\) such that every split graph \(G\) on \(n\) vertices satisfies

\[
\boxed{
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}+Cn.
}
\tag{1.2}
\]

Combining (1.1) and Theorem 1.1 gives the clique-partition statement.

### Corollary 1.2 — Linear-error clique partition bound

There exists an absolute constant \(C\) such that every split graph \(G\) on \(n\) vertices satisfies

\[
\boxed{
\operatorname{cp}(G)
\le
\frac{n^2}{6}+Cn.
}
\tag{1.3}
\]

The Erdős--Ordman--Zalcstein complete-split (indeed threshold) family \(K_p\vee\overline K_{2p}\), with \(n=3p\), shows that the leading constant \(1/6\) is sharp and that a linear term naturally appears.

## 1.3 Localization of hypothetical obstructions

### Proposition 1.3 — Localization of hypothetical obstructions

Suppose, for contradiction, that no absolute linear-error bound holds, and for each positive integer \(k\) choose a minimum-order split graph \(G_k\) satisfying

\[
|E(G_k)|-2\nu_3(G_k)>\frac{|V(G_k)|^2}{6}+k|V(G_k)|.
\]

After passing to a subsequence, writing \(|K_k|=p_k\), \(|I_k|=q_k\), every such hypothetical sequence must satisfy

\[
\frac{q_k}{p_k}\longrightarrow 2.
\]

Moreover, if \(q_k=2p_k-s_k\), then the bulk and short-corridor estimates force

\[
\sqrt{p_k}\ll s_k=o(p_k).
\]

Thus any obstruction to a linear error term would have to concentrate in the mesoscopic near-extremal corridor. The high/low-dispersion dichotomy in Section 9 excludes that corridor.

## 1.4 What the theorem does not prove

Let \(\nu_3^*(G)\) denote the fractional triangle-packing number. The present proof does **not** establish

\[
\nu_3^*(G)-\nu_3(G)=O(n)
\tag{1.4}
\]

uniformly over split graphs.

Indeed, write

\[
\Delta(G)=\nu_3^*(G)-\nu_3(G)
\]

and

\[
S(G)=\frac{n^2}{6}-\bigl(|E(G)|-2\nu_3^*(G)\bigr).
\]

Then

\[
|E(G)|-2\nu_3(G)
=
\frac{n^2}{6}-S(G)+2\Delta(G).
\tag{1.5}
\]

Theorem 1.1 only requires

\[
2\Delta(G)\le S(G)+O(n).
\]

In the bulk regime, \(S(G)\) is quadratic and absorbs the general \(o(n^2)\) integrality loss. Thus the universal linear integrality-gap problem remains open.

## 1.5 Proof architecture

Write

\[
|K|=p,
\qquad
|I|=q,
\qquad
\alpha=\frac qp.
\]

The proof begins by disposing of \(q\ge2p-1\) through a direct averaged factorization. We may therefore assume \(0\le\alpha<2\). A hypothetical sequence of counterexamples has a subsequence in one of three regimes.

1. **Bulk:** \(\alpha\) stays away from both \(0\) and \(2\). An exact common-profile LP and a replication argument produce quadratic fractional slack. Haxell--Rödl converts the fractional packing into an integral one with only \(o(n^2)\) loss.

2. **Sparse independent side:** \(\alpha\to0\). Each independent vertex anchors a large matching inside its neighborhood. The residual clique is almost complete. After deleting \(O(p)\) edges to correct divisibility, it admits an exact triangle decomposition.

3. **Near-extremal corridor:** \(\alpha\to2\). Write \(q=2p-s\). Averaged factorization closes \(s=O(\sqrt p)\). For \(\sqrt p\ll s=o(p)\), high dispersion is paid by a double-factor polarization term, while low dispersion implies closeness to a common center and is handled by shifted-center gain completion.

## 1.6 Supplementary computational audits

The accompanying closure package contains exact-arithmetic and finite-instance regression tests for selected identities and quantitative inequalities used in the proof.

Every audited statement is proved analytically in the manuscript. No computation, script, finite enumeration, or solver output is a logical premise of Theorem 1.1. The supplementary material is provided solely for independent checking, regression testing, and reproducibility.

## 1.7 Organization

Section 2 fixes notation and external inputs. Section 3 solves the common-profile LP. Section 4 proves replication and the global fractional margin. Section 5 develops averaged and double-factor rounding. Section 6 proves polarization. Section 7 proves shifted-center gain completion. Section 8 handles the sparse-independent regime. Section 9 assembles the three regimes. Section 10 records corollaries, Section 11 discusses the proof and its limitations, and Section 12 describes future uses and open directions. The appendices contain algebraic and reproducibility details.

---

# 2. Preliminaries

## 2.1 Split notation

Throughout,

\[
G=(K\sqcup I,E)
\]

is a split graph, where \(K\) is a clique of size \(p\) and \(I=\{v_1,\ldots,v_q\}\) is independent.

For \(v_i\in I\), write

\[
N_i=N(v_i)\cap K,
\qquad
d_i=|N_i|,
\qquad
S_i=K\setminus N_i,
\qquad
m_i=|S_i|.
\]

Set

\[
M=\sum_i m_i,
\qquad
S_2=\sum_i m_i^2.
\]

When \(q\) is close to \(2p\), write

\[
q=2p-s.
\tag{2.1}
\]

## 2.2 Triangle packings

A fractional triangle packing is a nonnegative weight assignment to the triangles of \(G\) such that the total weight through every edge is at most one. Its maximum value is \(\nu_3^*(G)\).

The dual is a fractional triangle cover: a nonnegative weight assignment to edges such that every triangle receives total edge weight at least one. LP duality gives equality between the two optimum values.

## 2.3 Complete graph factorizations

Adopt the boundary conventions

\[
\chi'(K_0)=\chi'(K_1)=0.
\]

For \(t\ge2\), the edge-chromatic number of a complete graph is

\[
\chi'(K_t)
=
\begin{cases}
t-1,&t\text{ even},\\
t,&t\text{ odd}.
\end{cases}
\tag{2.2}
\]

Thus \(E(K_t)\) decomposes into \(\chi'(K_t)\) matchings. The conventions for \(t\le1\) make the same language valid for empty edge sets.

## 2.4 External theorems

We use three external inputs.

### Theorem 2.1 — Haxell--Rödl/Yuster

For every fixed graph \(H\),

\[
\nu_H^*(G)-\nu_H(G)=o(|V(G)|^2)
\]

uniformly over graphs \(G\). We apply this with \(H=K_3\).

### Theorem 2.2 — Borodin--Kostochka--Woodall

Let \(B\) be a bipartite multigraph. If every edge \(xy\) is assigned a list \(L(xy)\) with

\[
|L(xy)|\ge\max\{d_B(x),d_B(y)\},
\]

then \(B\) has a proper edge coloring choosing the color of each edge from its list.

### Theorem 2.3 — Dense triangle decomposition

For every \(\varepsilon>0\), every sufficiently large triangle-divisible graph \(H\) with

\[
\delta(H)\ge(0.9+\varepsilon)|V(H)|
\]

admits a triangle decomposition. This follows from Dross's fractional decomposition theorem together with the iterative-absorption theorem of Barber, Kühn, Lo, and Osthus.

---

# 3. The Common-Profile Linear Program

For integers \(p,q,d\), let \(H(p,q,d)\) be the split graph with clique \(K\), \(|K|=p\), independent set \(I\), \(|I|=q\), and a fixed set \(N\subseteq K\), \(|N|=d\), such that every vertex of \(I\) has neighborhood \(N\). Put \(R=K\setminus N\) and \(r=p-d\).

## 3.1 Symmetric cover variables

Averaging over permutations of \(N\), \(R\), and \(I\), an optimal fractional triangle cover may be assumed constant on the four edge classes

\[
E(N),
\qquad E(N,I),
\qquad E(N,R),
\qquad E(R).
\]

Let their weights be \(a,b,c,e\), respectively. The triangle constraints are

\[
a+2b\ge1,
\qquad
3a\ge1,
\tag{3.1}
\]

\[
a+2c\ge1,
\qquad
2c+e\ge1,
\qquad
3e\ge1.
\tag{3.2}
\]

Constraints corresponding to empty triangle types may be omitted; the formula below remains valid for \(p\ge3\).

The objective is

\[
\binom d2a+qdb+dr\,c+\binom r2e.
\tag{3.3}
\]

## 3.2 Exact solution

### Theorem 3.1 — Common-profile formula

For \(p\ge3\),

\[
\boxed{
\nu_3^*(H(p,q,d))
=
F(p,q,d),
}
\tag{3.4}
\]

where

\[
\boxed{
F(p,q,d)
=
\min\left\{
\frac{\binom p2+qd}{3},
\binom d2+\binom r2,
\binom d2+\frac{dr+\binom r2}{3}
\right\}.
}
\tag{3.5}
\]

### Proof

At an optimum,

\[
b=\frac{1-a}{2},
\qquad
c=\frac{1-\min\{a,e\}}2,
\qquad
\frac13\le a,e\le1.
\]

If \(a\le e\), decreasing \(e\) to \(a\) cannot increase the objective. It therefore suffices to minimize on

\[
\frac13\le e\le a\le1.
\]

The objective is affine on this triangle, so a minimum occurs at

\[
(a,e)=\left(\frac13,\frac13\right),
\qquad
(1,1),
\qquad
\left(1,\frac13\right).
\]

The corresponding values are precisely the three expressions in (3.5). Duality completes the proof. \(\square\)

## 3.3 Interpretation of the three covers

The three candidates correspond to three geometric cover patterns.

- The **uniform cover** assigns weight \(1/3\) to every clique edge and weight \(1/3\) to every independent incidence.
- The **separated cover** assigns full weight to the internal edges of \(N\) and \(R\), with no crossing weight.
- The **hot-neighborhood cover** assigns full weight to \(E(N)\) and uniform weight to the remainder.

This finite trichotomy is the source of the global fractional margin.

---

# 4. Replication and the Exact Fractional Margin

## 4.1 Replication

### Lemma 4.1 — Replication bound

For every split graph with \(q\ge1\),

\[
\boxed{
\nu_3^*(G)
\ge
\frac1q\sum_{i=1}^qF(p,q,d_i).
}
\tag{4.1}
\]

### Proof

Let \(y\) be any fractional triangle cover of \(G\). Put

\[
A=\sum_{e\in E(K)}y_e
\]

and

\[
B_i=\sum_{x\in N_i}y_{v_ix}.
\]

Replace \(v_i\) by \(q\) independent clones, all with neighborhood \(N_i\), and give each clone the incident weights of \(v_i\). Together with the original clique-edge weights, this is a fractional cover of \(H(p,q,d_i)\) of weight \(A+qB_i\). Hence

\[
A+qB_i\ge F(p,q,d_i).
\]

Summing over \(i\) gives

\[
q\left(A+\sum_iB_i\right)
\ge
\sum_iF(p,q,d_i).
\]

Minimizing over covers proves the lemma. \(\square\)

## 4.2 The exact margin

Assume \(0<q\le2p\), set

\[
\alpha=\frac qp,
\]

and define the packing threshold

\[
T(G)=\frac12\left(|E(G)|-\frac{(p+q)^2}{6}\right).
\tag{4.2}
\]

Define

\[
\mu(\alpha)
=
\begin{cases}
\alpha^2/12,&0\le\alpha\le2/3,\\
(2-\alpha)^2/48,&2/3\le\alpha\le2.
\end{cases}
\tag{4.3}
\]

### Theorem 4.2 — Unified fractional margin

\[
\boxed{
\nu_3^*(G)
\ge
T(G)+\mu(\alpha)p^2-\frac p4.
}
\tag{4.4}
\]

### Proof

Let

\[
C_\alpha=\frac{2-2\alpha-\alpha^2}{12}.
\]

For each branch of \(F(p,q,d)\), completion of squares gives

\[
F(p,q,d)
\ge
\frac{qd}{2}+C_\alpha p^2+\mu(\alpha)p^2-\frac p2.
\tag{4.5}
\]

The three normalized residual minima are

\[
\frac{\alpha^2}{12},
\qquad
\frac{(2-\alpha)^2}{48},
\]

and

\[
\begin{cases}
\alpha(8-5\alpha)/48,&\alpha\le4/3,\\
(2-\alpha)^2/12,&\alpha\ge4/3.
\end{cases}
\]

The third is never below the minimum of the first two. Averaging (4.5) through Lemma 4.1 gives

\[
\nu_3^*(G)
\ge
\frac12\sum_i d_i+C_\alpha p^2+\mu(\alpha)p^2-\frac p2.
\]

Since

\[
T(G)=\frac12\sum_i d_i+C_\alpha p^2-\frac p4,
\]

we obtain (4.4). \(\square\)

## 4.3 Bulk consequence

If

\[
\varepsilon\le\alpha\le2-\varepsilon,
\]

then \(\mu(\alpha)\ge c_\varepsilon>0\). Theorem 4.2 and Haxell--Rödl imply

\[
\nu_3(G)\ge T(G)
\]

for all sufficiently large graphs in this regime. Hence

\[
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}.
\tag{4.6}
\]

---

# 5. Factorization Rounding Near \(q=2p\)

Let

\[
r_p=\chi'(K_p).
\]

## 5.1 One-factor averaging

### Lemma 5.1

If \(q\ge r_p\), then

\[
\boxed{
\nu_3(G)
\ge
\frac1q\sum_i\binom{d_i}{2}.
}
\tag{5.1}
\]

### Proof

Factor \(K_p\) into \(r_p\) matchings. Assign the factors injectively and uniformly to vertices of \(I\). In the factor assigned to \(v_i\), retain only edges with both endpoints in \(N_i\). The retained edges form valid edge-disjoint \(KKI\) triangles.

The expected number retained is

\[
\frac1q\sum_i\sum_{j=1}^{r_p}|F_j\cap E(K[N_i])|
=
\frac1q\sum_i\binom{d_i}{2}.
\]

Some assignment attains at least the expectation. \(\square\)

Writing \(q=2p-s\), substitution gives

\[
\Phi(G)
\le
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+
\frac{(s-1)M-S_2}{q}.
\tag{5.2}
\]

Using \(S_2\ge M^2/q\) and maximizing the resulting parabola yields

\[
\boxed{
\Phi(G)
\le
\frac{n^2}{6}+\frac p2+\frac{s^2-6s+3}{12}.
}
\tag{5.3}
\]

Thus \(s=O(\sqrt p)\) is closed with linear error.

## 5.2 Double-factor rounding

For a clique edge \(e=xy\), let

\[
b_e=|\{i:\{x,y\}\not\subseteq N_i\}|.
\]

Put

\[
h=\min\{r_p,q-r_p\},
\qquad
\delta=\frac h{r_p}.
\]

Choose \(h\) factors to receive two distinct independent vertices, and give one independent vertex to every other factor. All positions are assigned injectively.

### Lemma 5.2 — Double-factor inequality

If \(q\ge r_p\), then

\[
\boxed{
\begin{aligned}
\Phi(G)
\le{}&
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+
\frac{(s-1)M-S_2}{q}\\
&-
\frac{2\delta V}{q(q-1)},
\end{aligned}
}
\tag{5.4}
\]

where

\[
V=\sum_{e\in E(K)}b_e(q-b_e).
\tag{5.5}
\]

### Proof

If the factor containing \(e\) receives one vertex, \(e\) is lost with probability \(b_e/q\). If it receives two vertices, it is lost only when both are bad, with probability

\[
\frac{b_e(b_e-1)}{q(q-1)}.
\]

Thus the expected number \(U\) of lost clique edges is

\[
U
=
\frac1q\sum_e b_e
-
\frac{\delta}{q(q-1)}\sum_e b_e(q-b_e).
\]

Because every factor is a matching, each retained edge may be assigned to one of its admitting vertices without creating an edge collision. Substitution gives (5.4). \(\square\)

---

# 6. Quantitative Polarization

For every \(i\), define

\[
\mathcal B_i=\{e\in E(K):e\cap S_i\ne\varnothing\}.
\]

Then

\[
V=\sum_{i,j}|\mathcal B_i\setminus\mathcal B_j|.
\tag{6.1}
\]

Let

\[
m=\max_i|S_i|.
\]

### Lemma 6.1 — Polarization inequality

If \(2p-3m-1\ge0\), then

\[
\boxed{
V
\ge
\frac{2p-3m-1}{4}
\sum_{i,j}|S_i\triangle S_j|.
}
\tag{6.2}
\]

### Proof

Put

\[
a_{ij}=|S_i\setminus S_j|.
\]

The edges in \(\mathcal B_i\setminus\mathcal B_j\) are precisely the edges of \(K_p-S_j\) meeting \(S_i\setminus S_j\). Therefore

\[
|\mathcal B_i\setminus\mathcal B_j|
=
\frac{a_{ij}\bigl(2(p-|S_j|)-a_{ij}-1\bigr)}2.
\]

Since \(|S_j|\le m\) and \(a_{ij}\le m\),

\[
|\mathcal B_i\setminus\mathcal B_j|
\ge
\frac{2p-3m-1}{2}|S_i\setminus S_j|.
\]

Sum over ordered pairs and use

\[
\sum_{i,j}|S_i\setminus S_j|
=
\frac12\sum_{i,j}|S_i\triangle S_j|.
\]

This proves (6.2). \(\square\)

---

# 7. Shifted-Center Gain Completion

Fix \(R\subseteq K\). Put

\[
\rho=|R|,
\qquad
Q=K\setminus R,
\qquad
b=|Q|.
\]

For each \(i\), define

\[
T_i=S_i\setminus R,
\qquad
t_i=|T_i|,
\]

and

\[
G_i=R\setminus S_i,
\qquad
g_i=|G_i|.
\]

Set

\[
A_R=\sum_i t_i,
\qquad
A_{2,R}=\sum_i t_i^2,
\qquad
B_R=\sum_i g_i.
\]

Let

\[
r_b=\chi'(K_b),
\qquad
u=q-r_b.
\]

Assume

\[
b\ge2,
\qquad
q\ge r_b,
\qquad
b\ge\chi'(K_\rho),
\tag{7.1}
\]

and

\[
b-t_i\ge\max\{\rho,u\}
\qquad
\text{for all }i.
\tag{7.2}
\]

Define

\[
\theta_R=\frac{\max\{\rho-1,0\}}{b}
\]

and

\[
\kappa_R
=
1-2(1-\theta_R)\frac{u}{q}.
\tag{7.3}
\]

## 7.1 Packing inside \(Q\)

Reserve a set \(U\subseteq I\) of \(u\) vertices. Assign the remaining \(r_b\) vertices bijectively to a factorization of \(K[Q]\).

For \(v_i\), the number of unavailable edges of \(K[Q]\) is

\[
\beta_i
=
\binom b2-\binom{b-t_i}{2}.
\tag{7.4}
\]

For fixed \(U\), averaging over assignments gives at least

\[
\binom b2-\frac1{r_b}\sum_{i\notin U}\beta_i
\tag{7.5}
\]

edge-disjoint \(QQI\) triangles.

## 7.2 The gain graph

Construct a bipartite graph with parts \(U\) and \(R\), joining \(v_i\) to \(r\) when \(r\in G_i\). Assign the list

\[
L(v_ir)=N_i\cap Q.
\]

By (7.2),

\[
|L(v_ir)|=b-t_i
\ge
\max\{d(v_i),d(r)\}
\]

in the gain graph. Theorem 2.2 gives a proper list edge coloring. If \(v_ir\) receives color \(z\in Q\), take the triangle \(v_irz\). This gives

\[
B_U=\sum_{i\in U}g_i
\]

edge-disjoint \(IRQ\) triangles.

## 7.3 Completion inside \(R\)

For each \(z\in Q\), let \(U_z\subseteq R\) be the vertices \(r\) for which \(rz\) was used by an \(IRQ\) triangle.

If \(\rho\le1\), the graph \(K[R]\) has no edges, so this completion contributes no \(RRQ\) triangles. Suppose therefore that \(\rho\ge2\). Factor \(K[R]\), inject its factors into the colors \(z\in Q\), and delete from the factor assigned to \(z\) every edge incident with \(U_z\). Averaging over the injections loses at most

\[
\frac{\rho-1}{b}\sum_z|U_z|
=
\theta_RB_U
\]

edges. Hence, in all cases, we obtain at least

\[
\binom\rho2-\theta_RB_U
\]

additional \(RRQ\) triangles.

The three families \(QQI\), \(IRQ\), and \(RRQ\) are edge-disjoint. In particular, the forbidden-color deletion prevents an \(IRQ\) triangle and an \(RRQ\) triangle from sharing an edge \(rz\).

## 7.4 The centered inequality

Choose \(U\), \(|U|=u\), maximizing

\[
\sum_{i\in U}
\left(
\frac{2\beta_i}{r_b}+2(1-\theta_R)g_i
\right).
\]

The best \(u\) terms have sum at least \(u/q\) times the total. Using

\[
2\sum_i\beta_i
=(2b-1)A_R-A_{2,R},
\]

we obtain the principal local lemma.

### Lemma 7.1 — Reserved-gain shifted-center inequality

Under (7.1)--(7.2),

\[
\boxed{
\begin{aligned}
\Phi(G)
\le{}&
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+s\rho-2\rho^2\\
&+
\kappa_RB_R
+
\frac{(s-2\rho-1)A_R-A_{2,R}}q.
\end{aligned}
}
\tag{7.6}
\]

---

# 8. The Sparse-Independent Regime

Assume \(q=o(p)\). We prove the required bound directly and integrally.

## 8.1 Minimal-counterexample degree bound

In the global contradiction argument, a minimal counterexample with penalty \(kn\) satisfies, for every \(v\in I\),

\[
d(v)>
\frac{2n-1}{6}+k.
\tag{8.1}
\]

Since \(q=o(p)\), this implies eventually

\[
d(v)\ge2q+2.
\tag{8.2}
\]

## 8.2 Successive matchings

Order \(I=\{v_1,\ldots,v_q\}\). Choose successively edge-disjoint matchings

\[
M_i\subseteq K[N_i]
\]

of size \(\lfloor d_i/2\rfloor\).

Before choosing \(M_i\), each vertex has lost at most \(i-1\) incident edges, so the available graph on \(N_i\) has minimum degree at least

\[
d_i-i\ge d_i/2.
\]

Dirac's theorem supplies a Hamilton cycle and hence a matching of the required size.

Let

\[
F=\bigcup_iM_i.
\]

Then

\[
|F|
\ge
\frac12\sum_i d_i-\frac q2,
\qquad
\Delta(F)\le q.
\tag{8.3}
\]

The edges of \(M_i\) yield \(|M_i|\) edge-disjoint \(KKI\) triangles with apex \(v_i\).

## 8.3 Divisibility correction

The residual clique graph

\[
R_0=K_p-F
\]

satisfies

\[
\delta(R_0)
\ge
p-1-q
=(1-o(1))p.
\tag{8.4}
\]

In particular, for all sufficiently large members of the sequence, \(\delta(R_0)>p/2\). Dirac's theorem therefore gives a Hamilton cycle, and hence a Hamilton path

\[
P=x_1x_2\cdots x_p
\]

contained in \(R_0\). Let \(O\) be the set of odd-degree vertices of \(R_0\). By the handshaking lemma, \(|O|\) is even. Define the path subgraph \(J\subseteq P\) by

\[
x_jx_{j+1}\in E(J)
\quad\Longleftrightarrow\quad
|O\cap\{x_1,\ldots,x_j\}|\text{ is odd}.
\tag{8.5}
\]

For an internal vertex \(x_j\), the parity of its degree in \(J\) is the change in prefix parity between positions \(j-1\) and \(j\), and is therefore \(1\) precisely when \(x_j\in O\). The same conclusion holds at the two endpoints because \(|O|\) is even. Consequently,

\[
\operatorname{Odd}(J)=O,
\qquad
|E(J)|\le p-1,
\qquad
\Delta(J)\le2.
\tag{8.6}
\]

Thus

\[
R_1:=R_0-J
\]

has all degrees even, and

\[
\delta(R_1)\ge p-1-q-2.
\tag{8.7}
\]

Since \(q=o(p)\), eventually \(\delta(R_1)>3p/4\). By Turán's theorem, \(R_1\) contains a copy of \(K_5\). Choose a \(C_4\) and a \(C_5\) inside this fixed \(K_5\). According as

\[
|E(R_1)|\equiv0,1,2\pmod3,
\]

remove respectively nothing, the \(C_4\), or the \(C_5\). Let \(C\) denote the removed cycle, allowing \(C=\varnothing\), and put

\[
H:=R_1-E(C).
\]

Every vertex loses either zero or two incident edges when a cycle is removed, so all degrees of \(H\) remain even. Moreover, \(|E(C)|\equiv |E(R_1)|\pmod3\), and hence

\[
|E(H)|\equiv0\pmod3.
\]

Therefore \(H\) is triangle-divisible. The total loss of degree in passing from \(R_0\) to \(H\) is at most four, so

\[
\delta(H)\ge p-1-q-4.
\tag{8.8}
\]

To apply Theorem 2.3 with a fixed parameter, take for example \(\varepsilon_0=1/100\). Since \(q=o(p)\), eventually \(q\le p/20\), and then, for sufficiently large \(p\),

\[
\delta(H)\ge p-1-q-4\ge0.91p=(0.9+\varepsilon_0)|V(H)|.
\tag{8.9}
\]

Theorem 2.3 now gives an exact triangle decomposition of \(H\). Notice that the decomposition theorem is applied on the original \(p\)-vertex set: no vertices are deleted during the correction. The entire correction removes at most \(p+4\) edges.

## 8.4 Packing size

The combined packing has size

\[
\begin{aligned}
\nu_3(G)
&\ge
|F|+\frac{\binom p2-|F|-O(p)}3\\
&=
\frac13\binom p2+\frac23|F|-O(p)\\
&\ge
\frac13\binom p2+\frac13\sum_i d_i-O(p+q).
\end{aligned}
\tag{8.10}
\]

Consequently,

\[
\begin{aligned}
\Phi(G)
&\le
\frac13\binom p2+\frac13\sum_i d_i+O(p+q)\\
&\le
\frac13\binom p2+\frac{pq}{3}+O(p+q)\\
&=
\frac{(p+q)^2}{6}-\frac{p+q^2}{6}+O(p+q).
\end{aligned}
\tag{8.11}
\]

This is at most \(n^2/6+O(n)\).

---

# 9. Proof of the Main Theorem

We now prove Theorem 1.1 by contradiction.

Suppose no absolute constant works. For every positive integer \(k\), choose a split graph \(G_k\), minimal in its number \(n_k\) of vertices, such that

\[
\Phi(G_k)
>
\frac{n_k^2}{6}+kn_k.
\tag{9.1}
\]

Necessarily \(n_k\to\infty\). For every \(v\in I(G_k)\), minimality gives

\[
\Phi(G_k)
\le
\Phi(G_k-v)+d(v),
\]

and therefore

\[
\boxed{
d(v)>
\frac{2n_k-1}{6}+k.
}
\tag{9.2}
\]

First, if \(q_k\ge2p_k-1\), Lemma 5.1 gives

\[
\Phi(G_k)
\le
\frac{n_k^2}{6}+\frac{p_k}{2},
\]

contradicting (9.1) for large \(k\). We may therefore assume \(q_k<2p_k-1\) and pass to a subsequence according to

\[
\alpha_k=\frac{q_k}{p_k}\in[0,2).
\]

## 9.1 Bulk regime

Suppose that for some \(\varepsilon>0\),

\[
\varepsilon\le\alpha_k\le2-\varepsilon.
\]

Theorem 4.2 gives

\[
\nu_3^*(G_k)
\ge
T(G_k)+c_\varepsilon p_k^2-O(p_k).
\]

Haxell--Rödl gives

\[
\nu_3(G_k)
\ge
\nu_3^*(G_k)-o(n_k^2).
\]

For sufficiently large \(k\), the quadratic margin dominates the integrality loss, so \(\nu_3(G_k)\ge T(G_k)\), contrary to (9.1).

## 9.2 The endpoint \(\alpha_k\to0\)

This is closed by Section 8, which gives an absolute \(C_0\) such that

\[
\Phi(G_k)
\le
\frac{n_k^2}{6}+C_0n_k.
\]

For \(k>C_0\), this contradicts (9.1).

## 9.3 The endpoint \(\alpha_k\to2\)

Write

\[
q=2p-s,
\qquad
s=o(p).
\]

If \(s=O(\sqrt p)\), inequality (5.3) gives the required linear-error bound. Assume henceforth

\[
\sqrt p\ll s=o(p).
\tag{9.3}
\]

For all sufficiently large members of the sequence,

\[
p\ge2304,
\qquad
6\sqrt p\le s\le\frac p8,
\qquad
k\ge1.
\tag{9.4}
\]

By (9.2),

\[
m_i=|S_i|
<
\frac s3+\frac16-k
\le
\frac s3-\frac56.
\]

Since every \(m_i\) is an integer, with \(m=\max_i m_i\),

\[
\boxed{3m\le s-3.}
\tag{9.5}
\]

For \(x\in K\), put

\[
a_x=|\{i:x\in S_i\}|
\]

and

\[
D=\sum_{x\in K}a_x(q-a_x).
\tag{9.6}
\]

Then

\[
\sum_{i,j}|S_i\triangle S_j|=2D.
\tag{9.7}
\]

### High dispersion

Suppose

\[
D\ge\frac{qs^2}{12}.
\tag{9.8}
\]

By (9.5),

\[
2p-3m-1\ge2p-s+2=q+2.
\]

Lemma 6.1 and (9.7) therefore give

\[
V
\ge
\frac{q+2}{2}D
\ge
\frac q2D.
\tag{9.9}
\]

The double-factor coefficient in Lemma 5.2 satisfies

\[
\boxed{\delta\ge\frac78.}
\tag{9.10}
\]

Indeed, if \(p\) is odd then \(r_p=p\) and

\[
\delta=\frac{p-s}{p}\ge\frac78,
\]

while if \(p\) is even then \(r_p=p-1\) and

\[
\delta=\frac{p+1-s}{p-1}\ge\frac78.
\]

Moreover, \(S_2\ge M^2/q\), and (9.5) implies \(M/q\le m\le(s-3)/3\). Since the resulting parabola is increasing on this interval,

\[
\frac{(s-1)M-S_2}{q}
\le
\frac{2s(s-3)}9.
\tag{9.11}
\]

Substituting (9.8)--(9.11) into Lemma 5.2 yields

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac p2-\frac{5s^2}{288}-\frac{2s}{3}.
\tag{9.12}
\]

Since \(s^2\ge36p\),

\[
\Phi(G)-\frac{n^2}{6}
\le
-\frac p8-\frac{2s}{3}<0,
\]

a contradiction.

### Low dispersion

Suppose

\[
D<\frac{qs^2}{12}.
\tag{9.13}
\]

By (9.7), some \(j\) satisfies

\[
\sum_i|S_i\triangle S_j|
<
\frac{s^2}{6}.
\tag{9.14}
\]

Set

\[
R=S_j,
\qquad
\rho=|R|.
\]

Then

\[
A_R+B_R<\frac{s^2}{6},
\qquad
\rho\le m\le\frac{s-3}{3}.
\tag{9.15}
\]

We verify the hypotheses of Lemma 7.1 explicitly. Since \(s\le p/8\),

\[
q=2p-s\ge\frac{15p}{8},
\qquad
b=p-\rho\ge p-\frac s3.
\]

Thus \(b\ge2\), \(q\ge r_b\), and \(b\ge\chi'(K_\rho)\). Also \(r_b\ge b-1\), so

\[
u=q-r_b\le p-s+\rho+1.
\]

For every \(i\),

\[
2\rho+t_i+1
\le
3m+1
\le
s-2.
\]

Consequently,

\[
b-t_i\ge\max\{\rho,u\},
\]

and Lemma 7.1 applies.

If \(\rho=0\), then \(B_R=0\). If \(\rho\ge1\), then

\[
\theta_R
\le
\frac{\rho}{p-\rho}
\le
\frac{8s}{23p}.
\]

Using \(u=q-r_b\), \(r_b\le b\), and \(q\ge15p/8\), we obtain

\[
\kappa_R
=1-2(1-\theta_R)\frac uq
\le
\frac sq+2\theta_R
\le
\frac{5s}{4p}.
\tag{9.16}
\]

Likewise,

\[
\frac{(s-2\rho-1)_+}{q}
\le
\frac{5s}{4p}.
\tag{9.17}
\]

By (9.15), the total positive deviation in (7.6) is therefore at most

\[
\frac{5s}{4p}(A_R+B_R)
<
\frac{5s^3}{24p}
\le
\frac{5s^2}{192}.
\tag{9.18}
\]

Meanwhile,

\[
\frac{s^2}{6}-s\rho+2\rho^2
=
2\left(\rho-\frac s4\right)^2+\frac{s^2}{24}
\ge
\frac{s^2}{24}.
\tag{9.19}
\]

Lemma 7.1 now gives

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac p2-\frac{s^2}{64}.
\tag{9.20}
\]

Since \(s^2\ge36p\), the right-hand side is at most \(-p/16\), again a contradiction.

All possible subsequences are impossible. Theorem 1.1 follows. \(\square\)

---

# 10. Corollaries

## 10.1 Clique partitions

Corollary 1.2 follows immediately from

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\]

## 10.2 Sharpness of the leading term

The family

\[
K_p\vee\overline K_{2p}
\]

has \(n=3p\). A factorization of \(K_p\) assigned to independent vertices packs every clique edge into a \(KKI\) triangle. The resulting triangle-packing expression is

\[
|E|-2\nu_3
=
\frac{n^2}{6}+\frac n6.
\tag{10.1}
\]

The Erdős--Ordman--Zalcstein clique-partition construction on this family shows that the coefficient \(1/6\) cannot be improved.

## 10.3 Localization of difficult sequences

Proposition 1.3 records the localization statement supplied by the proof. It should be understood as a structural description of a hypothetical failure of every linear-error estimate, rather than as an additional extremal theorem after Theorem 1.1. The bulk margin excludes ratios bounded away from \(0\) and \(2\), the sparse construction excludes \(|I|/|K|\to0\), and averaged factorization excludes the short corridor near \(|I|=2|K|\). The only remaining location is the mesoscopic corridor

\[
|I|=2|K|-s,
\qquad
\sqrt{|K|}\ll s=o(|K|),
\]

which is then eliminated by the dispersion dichotomy.

## 10.4 Exact common-profile fractional value

Theorem 3.1 is independently useful: it gives the exact fractional triangle packing for every split graph in which all independent vertices have one common neighborhood, including the regime with too few independent vertices to color all neighborhood edges integrally.

## 10.5 Localized effectivity near \(q=2p\)

### Proposition 10.1 — Explicit corridor bounds

Let \(q=2p-s\) and \(n=p+q\).

1. If
   \[
   p\ge36,
   \qquad
   0\le s\le6\sqrt p,
   \]
   then
   \[
   \boxed{
   \Phi(G)\le\frac{n^2}{6}+2n.
   }
   \tag{10.2}
   \]

2. If
   \[
   p\ge2304,
   \qquad
   6\sqrt p\le s\le\frac p8,
   \]
   and every \(v\in I\) satisfies
   \[
   d(v)>\frac{2n-1}{6}+1,
   \]
   then
   \[
   \boxed{
   \Phi(G)\le\frac{n^2}{6}.
   }
   \tag{10.3}
   \]

Consequently, for every \(C\ge2\), a minimum-order counterexample to

\[
\Phi(G)\le\frac{n^2}{6}+Cn
\]

cannot satisfy

\[
p\ge2304,
\qquad
0\le s\le\frac p8.
\]

### Proof

For the short corridor, inequality (5.3) and \(s^2\le36p\) give

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac{7p}{2}+\frac14
\le
2n,
\]

because \(p\ge36\) implies \(s\le p\) and hence \(n=3p-s\ge2p\).

The mesoscopic assertion is exactly the quantitative high/low-dispersion calculation in Section 9.3. The final consequence follows from the degree inequality obtained by deleting an independent vertex from a minimum-order counterexample. \(\square\)

---

# 11. Discussion

## 11.1 From fractional asymptotics to a linear-error integral theorem

The central difficulty is that the general theorem

\[
\nu_3^*(G)-\nu_3(G)=o(n^2)
\]

has no linear rate. The present proof avoids demanding one uniform rounding mechanism.

- In the bulk, the common-profile LP produces quadratic slack.
- Near \(q=2p\), explicit factorization structures replace general rounding.
- Near \(q=0\), the residual clique becomes dense enough for exact decomposition.

This regime-dependent strategy is weaker than a universal linear integrality-gap theorem but sufficient for the extremal clique-partition problem.

## 11.2 Why residual maximum degree is not the right invariant

Early exploratory work attempted to prove that an optimal packing leaves a clique residual of bounded maximum degree. Numerical behavior depended strongly on the packing algorithm, and no such property is needed in the final proof.

The effective invariants are instead:

- the common-profile fractional margin;
- the variance term \(S_2\);
- the polarization energy \(V\);
- the centered deviations \(A_R,B_R\);
- divisibility of the dense residual.

## 11.3 Localized effectivity and remaining non-effectivity

Proposition 10.1 shows that the entire near-extremal corridor treated by factorization, polarization, and shifted-center completion is quantitatively effective. One may take

\[
C_{\mathrm{corr}}=2,
\qquad
p_0=2304,
\qquad
s_0(p)=6\sqrt p,
\qquad
\eta_0=\frac18.
\]

The global constant \(C\) remains non-effective for two independent reasons.

1. The Haxell--Rödl theorem is used through an asymptotic \(o(n^2)\) statement in the bulk.
2. Dense triangle decomposition theorems are invoked with unspecified sufficiently-large thresholds in the sparse-independent regime.

Thus no hidden non-effectivity remains in Sections 5--7; it comes only from the two external asymptotic inputs above.

## 11.4 Relationship with the fractional extremal theorem

The complete-split extremal theorem determines the global fractional maximum of

\[
|E(G)|-2\nu_3^*(G)
\]

over both split and chordal graphs. The common-profile LP in the present paper serves a different purpose: it is a profile-sensitive local lower bound for the replicated graph, and its quantitative slack absorbs integrality loss away from the extremal corridor.

Thus the global fractional extremal calculation and the local common-profile calculation are compatible but logically distinct. The present proof is self-contained apart from the external theorems stated in Section 2.

## 11.5 Relationship with the chordal linear-error problem

The complete-split reduction settles the asymptotically sharp chordal bound

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

The stronger estimate

\[
\operatorname{cp}(G)
\le
\frac{n^2}{6}+O(n)
\]

remains open for general chordal graphs. The mechanisms developed here suggest possible local ingredients for that problem:

- replication can provide profile-sensitive fractional slack;
- shifted-center completion can model protected separator capacities;
- polarization can quantify incompatibility between descendant trace profiles;
- dense residual decomposition may close clique-tree nodes with a small private side.

A chordal linear-error proof would still have to preserve ownership and separator capacities across the clique tree.

---

# 12. Potential Uses and Future Directions

## 12.1 Universal linear integrality gap

### Problem 12.1

Is there an absolute constant \(C\) such that

\[
\nu_3^*(G)-\nu_3(G)
\le C|V(G)|
\]

for every split graph \(G\)?

The present paper supplies supporting structures near the extremal corridor but does not resolve the bulk regime without quadratic slack.

## 12.2 Effective global constants

### Problem 12.2

Find an explicit global constant \(C\) in Theorem 1.1.

The near-extremal corridor is already effective by Proposition 10.1. A fully quantitative global theorem therefore requires only explicit rates in fractional-to-integral packing, or a structured replacement for Haxell--Rödl in the bulk, together with effective dense-decomposition thresholds in the sparse-independent regime.

## 12.3 Algorithmic packing

The proof contains polynomially implementable pieces:

- complete-graph factorizations;
- weighted selection of reserved vertices;
- bipartite list edge coloring;
- matching extraction;
- dense decomposition algorithms implicit in iterative absorption.

It is natural to seek a polynomial-time algorithm that outputs a clique partition of size

\[
\frac{n^2}{6}+O(n)
\]

with an explicit constant.

## 12.4 Stability and extremal classification

### Problem 12.3

Characterize split graphs satisfying

\[
\operatorname{cp}(G)
\ge
\frac{n^2}{6}-o(n^2).
\]

The proof suggests that near-extremal graphs should have \(|I|=(2+o(1))|K|\) and low-dispersion absence profiles close to a common center.

## 12.5 Higher-clique linear-error packing

The complete-split reduction determines the fractional extremal problem and the first-order integral asymptotics for fixed \(K_r\)-and-edge partitions. The natural higher-clique analogue of the present paper is the following linear-error question.

For fixed \(r\ge3\), does every split graph satisfy

\[
\pi_r(G)
\le
\frac{r-1}{4r}n^2+O_r(n),
\]

where \(\pi_r(G)\) is the minimum number of parts in an edge partition into copies of \(K_r\) and single edges?

The common-profile and replication ideas suggest one possible approach, but the relevant local orbit programs and integral rounding mechanisms become substantially more complicated. Design and decomposition methods such as those developed by Keevash [10] and the regular-slice framework of Allen, Böttcher, Cooley, and Mycroft [11] may be useful tools; they are not ingredients of the present proof.

## 12.6 Chordal and clique-tree applications

Shifted-center completion was designed to separate owned clique edges from protected interface edges. A parametric version may be useful in a future chordal linear-error theorem, where separators are shared between neighboring maximal cliques.

## 12.7 Reusable proof principle

The paper illustrates a broader strategy:

> Use exact symmetric LPs to create slack away from extremality, then reserve explicit combinatorial rounding only for the corridor where the slack vanishes.

This may apply to other structured packing-covering problems in which a general regularity theorem is too weak at second order.

---

# 13. Reproducibility and closure package

The final v1.0.4 closure package is organized as follows.

```text
01_MANUSCRIPT/
    PAPER_III_FINAL_V1_0_4.md
    PAPER_III_FINAL_V1_0_4.tex
    PAPER_III_FINAL_V1_0_4.pdf
02_PROOF_AUDIT/
    PAPER_III_V1_0_4_FINAL_CLOSURE_AUDIT.md
    PAPER_III_V1_0_4_PROOF_DEPENDENCY_LEDGER.md
    PAPER_III_V1_0_4_SUBMISSION_CLAIMS_MATRIX.md
    GATE_PIII_EFF_01_EXPLICIT_CORRIDOR_CONSTANTS.md
    GATE_PIII_EFF_02_ALGEBRAIC_CLOSURE.md
03_SUPPLEMENTARY_REGRESSION/
    verify_piii_eff_01.py
    verify_paper_iii_v1_0_4_output.txt
    README.md
04_INTEGRITY/
    PAPER_III_V1_0_4_PDF_INSPECT.txt
    PAPER_III_V1_0_4_VISUAL_DIFF.txt
    SHA256SUMS_PAPER_III_V1_0_4.txt
```

The proof itself is contained in the manuscript. The common-profile optimization is proved in Theorem 3.1; the fractional margin is proved in Theorem 4.2 and Appendix A; the factorization, polarization, and shifted-center inequalities are proved in Lemmas 5.1--7.1; the divisibility correction is proved in Section 8.3 and Appendix B; and the explicit near-extremal constants are proved algebraically in Sections 9.3 and 10.5.

The included script is a supplementary regression test for the explicit corridor constants. Its output is not used as a hypothesis, reduction, or proof step anywhere in the manuscript. Historical exploratory computations are not part of the logical proof package.
---

# Appendix A. Algebra of the Fractional Margin

Let \(x=d/p\) and \(\alpha=q/p\). Ignoring the exact linear terms temporarily, the three normalized branches of \(F\) are

\[
f_1(x)=\frac16+\frac{\alpha x}{3},
\]

\[
f_2(x)=x^2-x+\frac12,
\]

and

\[
f_3(x)=\frac16+\frac{x^2}{3}.
\]

Subtracting the affine target contribution gives minima

\[
\min_x\left(f_1(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\frac{\alpha^2}{12},
\]

\[
\min_x\left(f_2(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\frac{(2-\alpha)^2}{48},
\]

and

\[
\min_x\left(f_3(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\begin{cases}
\alpha(8-5\alpha)/48,&\alpha\le4/3,\\
(2-\alpha)^2/12,&\alpha\ge4/3.
\end{cases}
\]

The third is dominated by the lower envelope of the first two. Restoring the exact \(-p/2\) contribution in each pointwise estimate and averaging produces the \(-p/4\) term in Theorem 4.2.

---

# Appendix B. Divisibility Correction

Let \(P=x_1\cdots x_p\) be a path and let \(O\subseteq V(P)\) have even cardinality. Define

\[
J=\{x_jx_{j+1}:|O\cap\{x_1,\ldots,x_j\}|\text{ is odd}\}.
\]

Every internal vertex \(x_j\) changes prefix parity precisely when \(x_j\in O\). Therefore

\[
\operatorname{Odd}(J)=O.
\]

Also \(|E(J)|\le p-1\) and \(\Delta(J)\le2\).

After parity correction, the minimum degree has fallen by at most two. In the sparse-independent regime it is still greater than \(3p/4\) for all sufficiently large \(p\), so Turán's theorem supplies a \(K_5\). Deleting a \(C_4\) inside that \(K_5\) changes the edge count by \(1\pmod3\), while deleting a \(C_5\) changes it by \(2\pmod3\). Every affected degree changes by two, so parity is preserved. The total degree loss from the path subgraph and the correcting cycle is at most four. Thus, when \(q=o(p)\), the final graph has minimum degree at least \(p-1-q-4\), which eventually exceeds \((0.9+\varepsilon_0)p\) for any fixed \(0<\varepsilon_0<0.1\).

---

# Appendix C. Computational Audits

## C.1 Exact common-profile LP

`verify_common_profile_lp.py` enumerates the vertices of the symmetrized cover polyhedron using exact rational Gaussian elimination and compares the optimum with (3.5).

## C.2 Exact fractional margin

`verify_fractional_margin.py` checks Theorem 4.2 for

\[
3\le p\le80,
\qquad
1\le q\le2p,
\qquad
0\le d\le p
\]

using exact rational arithmetic.

## C.3 Small ILP audits

`verify_factor_rounding.py` and `verify_shifted_center.py` compute exact integral triangle packings on small instances using a binary edge-capacity ILP. They verify the stated upper bounds on \(\Phi(G)\).

## C.4 Polarization

`verify_polarization.py` performs exhaustive small-profile and randomized exact-integer checks of Lemma 6.1.

## C.5 Divisibility

`verify_divisibility_correction.py` exhaustively verifies the path parity construction through order eighteen, checks the fixed minimum-degree threshold exactly, and follows the full parity and modulo-three correction on randomized dense residuals.

---

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support during the development of this work.

AI-assisted tools were used during the exploratory, computational, adversarial, and editorial stages of this work, including Anthropic Claude Opus, Google Gemini 3.1 and 3.5, and OpenAI systems accessed through ChatGPT, including GPT-5.5 and Codex. These tools supported exploratory search, testing of candidate mechanisms, generation and review of verification code, organization of gate ledgers, bibliographic checks, and preparation of drafts. Several initially plausible claims were rejected after adversarial analysis or explicit counterexamples. All mathematical statements, proofs, citations, code, and final editorial decisions remain the sole responsibility of the author. No AI system is listed as an author.

---

# References

[1] B. Barber, D. Kühn, A. Lo, and D. Osthus, **Edge-Decompositions of Graphs with High Minimum Degree**, *Advances in Mathematics* **288** (2016), 337–385. DOI: `10.1016/j.aim.2015.09.032`.

[2] O. V. Borodin, A. V. Kostochka, and D. R. Woodall, **List Edge and List Total Colourings of Multigraphs**, *Journal of Combinatorial Theory, Series B* **71** (1997), no. 2, 184–204. DOI: `10.1006/jctb.1997.1780`.

[3] G.-T. Chen, P. Erdős, and E. T. Ordman, **Clique Partitions of Split Graphs**, in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, 21–30.

[4] G. A. Dirac, **Some Theorems on Abstract Graphs**, *Proceedings of the London Mathematical Society* (3) **2** (1952), 69–81. DOI: `10.1112/plms/s3-2.1.69`.

[5] F. Dross, **Fractional Triangle Decompositions in Graphs with Large Minimum Degree**, *SIAM Journal on Discrete Mathematics* **30** (2016), no. 1, 36–42. DOI: `10.1137/15M1014310`.

[6] P. Erdős, E. T. Ordman, and Y. Zalcstein, **Clique Partitions of Chordal Graphs**, *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415. DOI: `10.1017/S0963548300000808`.

[7] P. E. Haxell and V. Rödl, **Integer and Fractional Packings in Dense Graphs**, *Combinatorica* **21** (2001), 13–38. DOI: `10.1007/s004930170003`.

[8] J. P. Traverso Gianini, **Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs**, author manuscript, v0.7-pre, July 2026.

[9] R. Yuster, **Integer and Fractional Packing of Families of Graphs**, *Random Structures & Algorithms* **26** (2005), 110–118. DOI: `10.1002/rsa.20048`.

[10] P. Keevash, **The Existence of Designs**, arXiv:`1401.3665`, revised 2018.

[11] P. Allen, J. Böttcher, O. Cooley, and R. Mycroft, **Tight Cycles and Regular Slices in Dense Hypergraphs**, *Journal of Combinatorial Theory, Series A* **149** (2017), 30–100. DOI: `10.1016/j.jcta.2017.01.003`.
