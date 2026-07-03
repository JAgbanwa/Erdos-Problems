# Affine Profile Reduction for Fractional Triangle Covers in Split Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Final author manuscript:** v1.1  
**Date:** July 3, 2026  
**Status:** closed author version; the proof is analytic modulo cited mathematical theorems; multi-model AI-assisted adversarial and editorial audits completed; not independently peer-reviewed or journal-refereed; specialist novelty review remains pending

**MSC 2020:** Primary 05C70; Secondary 05C35, 05C72, 05C69.

---

## Abstract

We develop an affine profile-reduction method for fractional triangle-cover programs on split graphs. The residual optimization is performed over a fixed cover polytope, while its objective vector depends affinely on the masses of independent-set neighborhood types. Concavity of the resulting value function implies that every mixed profile is bounded below by a convex combination of pure profiles, and hence by a single pure profile.

For a pure neighborhood \(S\), symmetry reduces the cover program to three orbit variables. We determine its exact optimum as the minimum of three canonical geometries: the uniform cover \(U\), the separated cover \(D\), and the hot-set cover \(H\). We also solve the weighted three-orbit program. The distinction is explicit: arbitrary fixed heterogeneous baselines preserve pure-profile reduction, while the closed formula \(\min\{U,D,H\}\) additionally requires the baseline to be constant on the three edge orbits \(SS\), \(S\bar S\), and \(\bar S\bar S\).

The reduction remains exact for nonnegative real masses on neighborhood types and yields Dirac extremizers on the finite profile simplex. The value function is Lipschitz under \(\ell_1\)-perturbations of either the baseline or the aggregate profile.

As a first graph-theoretic application of the method, every split graph \(G\) on \(n\) vertices satisfies

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n.
\]

Together with Haxell--Rödl/Yuster, this gives

\[
\operatorname{cp}(G)\le\left(\frac16+o(1)\right)n^2,
\]

with sharp leading constant. Companion papers subsequently determine the exact finite fractional extremum on chordal graphs and establish a linear-error integral theorem for split graphs. The durable contribution of the present paper is the fixed-polytope affine reduction and its weighted, continuous, and robust extensions.

**Keywords:** clique partition; split graph; fractional triangle packing; fractional triangle cover; affine profile reduction; weighted linear programming; robustness; extremal graph theory.

---

# 1. Introduction

## 1.1 Clique partitions and the split benchmark

A **clique partition** of a graph \(G\) is a family of complete subgraphs whose edge sets partition \(E(G)\). Cliques of order two are allowed. The minimum size of such a family is denoted by \(\operatorname{cp}(G)\).

Erdős, Ordman, and Zalcstein studied clique partitions of chordal graphs and exhibited a complete-split construction requiring asymptotically \(n^2/6\) cliques. The construction is in fact threshold. Chen, Erdős, and Ordman developed the split-graph side of the problem and proved the general bound \(3n^2/16+O(n)\).

This paper isolates a different mechanism. Neighborhood multiplicities are encoded as an affine objective vector over one fixed triangle-cover polytope. Concavity then reduces arbitrary mixtures of neighborhood types to pure profiles. Symmetry is used only after that reduction.

The main contribution is therefore methodological:

\[
\boxed{
\text{fixed-polytope concavity}
\Longrightarrow
\text{pure-profile reduction}
\Longrightarrow
\text{three-orbit optimization}.
}
\]

The split-graph extremal bounds below are applications of this mechanism, not the strongest quantitative results now available in the companion papers.

## 1.2 Triangle packings

Let \(\nu_3(G)\) be the maximum number of pairwise edge-disjoint triangles in \(G\), and let \(\nu_3^*(G)\) be the fractional triangle-packing number.

Every integral triangle packing gives a clique partition by taking the packed triangles and one \(K_2\) for every uncovered edge. Hence

\[
\operatorname{cp}(G)\le |E(G)|-2\nu_3(G).
\tag{1.1}
\]

Haxell--Rödl, with Yuster's generalization, gives

\[
\nu_3^*(G)-\nu_3(G)=o(n^2)
\tag{1.2}
\]

uniformly over \(n\)-vertex graphs.

## 1.3 Main methodological results

Let \(K\) be a clique of order \(p\), and let

\[
\mathcal P_p=
\left\{
z\in[0,1]^{E(K)}:
\sum_{e\in E(T)}z_e\ge1
\text{ for every triangle }T\subseteq K
\right\}.
\]

For a fixed baseline \(b\in\mathbb R^{E(K)}\), define

\[
M_b(\kappa)=\min_{z\in\mathcal P_p}\langle b-\kappa,z\rangle.
\]

For each neighborhood type \(S\subseteq K\), \(|S|\ge2\), put

\[
a^S_e=\frac{\mathbf 1_{\{e\subseteq S\}}}{|S|-1}.
\]

### Theorem 1.1 — Weighted affine dominance and robustness

Let \((\mu_S)\) be nonnegative real masses with total mass

\[
q=\sum_S\mu_S>0,
\qquad
\kappa_\mu=\sum_S\mu_Sa^S,
\qquad
\kappa^{S,q}=qa^S.
\]

Then

\[
\boxed{
M_b(\kappa_\mu)
\ge
\sum_S\frac{\mu_S}{q}M_b(\kappa^{S,q})
\ge
\min_SM_b(\kappa^{S,q}).
}
\tag{1.3}
\]

Moreover, for every \(\varepsilon,\eta\in\mathbb R^{E(K)}\),

\[
\boxed{
\left|
M_{b+\varepsilon}(\kappa+\eta)-M_b(\kappa)
\right|
\le
\|\varepsilon\|_1+\|\eta\|_1.
}
\tag{1.4}
\]

Thus pure-profile reduction survives continuous type masses and arbitrary fixed edgewise heterogeneity.

### Theorem 1.2 — Weighted three-orbit formula

Fix a pure profile \(S\subseteq K\) with \(|S|\ge3\) and \(|K\setminus S|\ge3\). Suppose the baseline is constant on the three edge orbits

\[
SS,\qquad S(K\setminus S),\qquad (K\setminus S)(K\setminus S).
\]

Let \(X,Y,Z\) be the aggregate objective coefficients, with \(X\in\mathbb R\) and \(Y,Z\ge0\). Then

\[
\boxed{
\min_{(\alpha,\beta,\gamma)\in\mathcal Q_2}
(X\alpha+Y\beta+Z\gamma)
=
\min\left\{
\frac{X+Y+Z}{3},\,
X+Z,\,
X+\frac{Y+Z}{3}
\right\}.
}
\tag{1.5}
\]

The three values correspond to the uniform, separated, and hot-set covers.

## 1.4 Graph-theoretic applications

### Theorem 1.3 — Fractional split-graph application

For every split graph \(G\) on \(n\) vertices,

\[
\boxed{
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}+n.
}
\tag{1.6}
\]

### Corollary 1.4 — Asymptotic clique-partition application

For every split graph \(G\) on \(n\) vertices,

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2,
\tag{1.7}
\]

and

\[
\max\{\operatorname{cp}(G):G\text{ split},\,|V(G)|=n\}
=
\left(\frac16+o(1)\right)n^2.
\tag{1.8}
\]

The Erdős--Ordman--Zalcstein complete-split family

\[
K_p\vee\overline K_{2p},
\qquad n=3p,
\]

witnesses the sharp leading constant.

## 1.5 Relation to the companion papers

The three manuscripts have distinct roles.

- **Paper I (this paper)** isolates affine profile reduction, continuous masses, heterogeneous baselines, Dirac extremization, Lipschitz stability, and the weighted three-orbit formula.
- **Paper II**, *Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs*, proves that the fractional chordal extremum is attained on a one-parameter complete-split family and gives exact finite formulas for triangles and general \(K_r\).
- **Paper III**, *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing*, proves the stronger integral estimate
  \[
  \operatorname{cp}(G)\le\frac{n^2}{6}+O(n)
  \]
  for split graphs.

Accordingly, (1.6)--(1.8) are retained as the first graph-theoretic applications of the affine-profile method, not as the final quantitative record of the series.

## 1.6 Proof architecture

Write the split graph as \(G=(K\cup I,E)\), with \(K\) a clique.

1. Construct a feasible fractional packing using triangles that meet \(I\).
2. Use the residual clique-edge capacities for triangles contained in \(K\).
3. Apply LP duality to obtain an exact residual cover functional over the fixed polytope \(\mathcal P_p\).
4. Express the objective vector as an affine mixture of pure neighborhood profiles.
5. Use fixed-polytope concavity to reduce to a pure profile.
6. Average over the stabilizer of the pure profile and solve the resulting three-orbit program.
7. Compare its three canonical values with one quadratic benchmark.

---

# 2. Preliminaries

Let \(G=(K\cup I,E)\) be split, with \(p=|K|\). For \(v\in I\), let \(N(v)\subseteq K\) and \(d_v=|N(v)|\). Partition

\[
I_{\ge2}=\{v:d_v\ge2\},
\qquad
I_1=\{v:d_v=1\},
\qquad
I_0=\{v:d_v=0\},
\]

and put

\[
q=|I_{\ge2}|,
\qquad
b_1=|I_1|,
\qquad
b_0=|I_0|.
\]

Then

\[
n=p+q+b_1+b_0.
\tag{2.1}
\]

Let

\[
b_{\ge2}=\sum_{v\in I_{\ge2}}d_v.
\]

Thus

\[
|E(G)|=\binom p2+b_{\ge2}+b_1.
\tag{2.2}
\]

We use finite-dimensional LP duality between capacitated fractional triangle packings and fractional triangle covers.

---

# 3. A Two-Phase Fractional Packing

For each clique edge \(e\in E(K)\), define

\[
\kappa_e
=
\sum_{\substack{v\in I_{\ge2}\\e\subseteq N(v)}}
\frac1{d_v-1}.
\tag{3.1}
\]

### Lemma 3.1 — Load identity

\[
\boxed{
\sum_{e\in E(K)}\kappa_e=\frac{b_{\ge2}}2.
}
\tag{3.2}
\]

Indeed,

\[
\sum_e\kappa_e
=
\sum_{v\in I_{\ge2}}
\frac{\binom{d_v}{2}}{d_v-1}
=
\sum_{v\in I_{\ge2}}\frac{d_v}{2}.
\]

Define

\[
\lambda_e=
\begin{cases}
1,&\kappa_e=0,\\
\min(1,\kappa_e^{-1}),&\kappa_e>0.
\end{cases}
\]

For each triangle \(vxy\) meeting \(I\), put

\[
w_1(vxy)=\frac{\lambda_{xy}}{d_v-1}.
\tag{3.3}
\]

The load on a clique edge \(e\) is \(\lambda_e\kappa_e=\min(\kappa_e,1)\), while the load on a cross edge \(vx\) is at most one. Thus \(w_1\) is feasible.

Let

\[
H=\{e:\kappa_e\ge1\},
\qquad
L=\{e:\kappa_e<1\}.
\]

Its value is

\[
\nu_1=|H|+\sum_{e\in L}\kappa_e.
\tag{3.4}
\]

In Phase II, fractionally pack clique triangles using residual capacity \(1-\kappa_e\) on \(e\in L\). Let the optimum be \(\nu_2\), and define

\[
\nu_{\mathrm{con}}=\nu_1+\nu_2\le\nu_3^*(G).
\tag{3.5}
\]

---

# 4. Exact Dual Reduction

Dualizing Phase II, capping every cover coordinate at one, and substituting \(y_e=1-x_e\) yields a maximization with constraints \(0\le y_e\le1\) and \(y(T)\le2\). Extending by \(y_e=0\) on hot edges is exact because \(1-\kappa_e\le0\) there.

Put \(z_e=1-y_e\). Then \(z\in\mathcal P_p\), and define

\[
M(\kappa)
=
\min_{z\in\mathcal P_p}
\sum_{e\in E(K)}(1-\kappa_e)z_e.
\tag{4.1}
\]

### Theorem 4.1 — Exact dual reduction

\[
\boxed{
|E(G)|-2\nu_{\mathrm{con}}
=
\binom p2-2M(\kappa)+b_1.
}
\tag{4.2}
\]

The identity follows from

\[
\nu_1+\nu_2
=
\binom p2-
\max_y\sum_e(1-\kappa_e)y_e,
\]

the substitution \(z=1-y\), and Lemma 3.1.

---

# 5. Affine Reduction of Neighborhood Profiles

## 5.1 Fixed-polytope concavity

### Lemma 5.1

Let \(P\subseteq\mathbb R^m\) be nonempty and

\[
\Phi(c)=\min_{x\in P}\langle c,x\rangle.
\]

If \(c=\sum_i\lambda_ic^{(i)}\), with \(\lambda_i\ge0\) and \(\sum_i\lambda_i=1\), then

\[
\boxed{
\Phi(c)\ge\sum_i\lambda_i\Phi(c^{(i)})
\ge\min_i\Phi(c^{(i)}).
}
\tag{5.1}
\]

For each \(x\in P\),

\[
\langle c,x\rangle
=
\sum_i\lambda_i\langle c^{(i)},x\rangle
\ge
\sum_i\lambda_i\Phi(c^{(i)}),
\]

and taking the minimum proves the claim.

## 5.2 Discrete profiles

For \(S\subseteq K\), \(|S|\ge2\), define

\[
a^S_e=\frac{\mathbf1_{\{e\subseteq S\}}}{|S|-1}.
\]

If \(n_S\) is the number of active independent vertices with neighborhood \(S\), then

\[
\kappa=\sum_Sn_Sa^S.
\]

For \(q>0\), put \(\lambda_S=n_S/q\) and \(\kappa^S=qa^S\). Then

\[
\kappa=\sum_S\lambda_S\kappa^S.
\tag{5.2}
\]

### Theorem 5.2 — Affine dominance

\[
\boxed{
M(\kappa)
\ge
\sum_S\lambda_SM(\kappa^S)
\ge
\min_SM(\kappa^S).
}
\tag{5.3}
\]

For the uniform baseline, permutation symmetry implies that \(M(\kappa^S)\) depends only on \(s=|S|\). Hence

\[
M(\kappa)\ge\min_{2\le s\le p}M_{\mathrm{id}}(p,q,s).
\tag{5.4}
\]

## 5.3 Continuous masses and heterogeneous baselines

Let \(b\in\mathbb R^{E(K)}\) be arbitrary and define

\[
M_b(\kappa)=\min_{z\in\mathcal P_p}\langle b-\kappa,z\rangle.
\]

For nonnegative real masses \(\mu_S\), define

\[
q=\sum_S\mu_S,
\qquad
\kappa_\mu=\sum_S\mu_Sa^S.
\]

Then Theorem 1.1 follows directly from Lemma 5.1 applied to the objective vectors \(b-\kappa^{S,q}\).

The pure-profile reduction therefore survives arbitrary fixed heterogeneity. Further reduction by orbit symmetry may fail unless \(b\) is invariant under the stabilizer of the profile.

## 5.4 Dirac extremization

Let

\[
\Delta(\mathcal S_p)
=
\left\{
\lambda\in\mathbb R_{\ge0}^{\mathcal S_p}:
\sum_S\lambda_S=1
\right\},
\qquad
\kappa(\lambda)=q\sum_S\lambda_Sa^S.
\]

### Corollary 5.3 — Dirac extremization

\[
\boxed{
\min_{\lambda\in\Delta(\mathcal S_p)}M_b(\kappa(\lambda))
=
\min_{S\in\mathcal S_p}M_b(qa^S).
}
\tag{5.5}
\]

This is a finite-dimensional measure statement and is not, by itself, a graphon-limit theorem.

## 5.5 Lipschitz stability

For \(z\in\mathcal P_p\subseteq[0,1]^{E(K)}\),

\[
|\langle\varepsilon-\eta,z\rangle|
\le
\|\varepsilon\|_1+\|\eta\|_1.
\]

Evaluating an optimizer of either program in the other proves (1.4).

---

# 6. The Pure-Profile Orbit Program

Fix \(S\subseteq K\), \(|S|=s\), and put \(o=p-s\). Suppose every active independent vertex has neighborhood \(S\). Then

\[
\kappa_e=
\begin{cases}
q/(s-1),&e\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\]

Averaging over the stabilizer of \(S\) gives an optimum constant on the three edge orbits. Write the variables as

\[
\alpha,\qquad\beta,\qquad\gamma.
\]

Set

\[
A=\frac{s(s-1-q)}2,
\qquad
B=so,
\qquad
C=\frac{o(o-1)}2.
\tag{6.1}
\]

The objective is \(A\alpha+B\beta+C\gamma\). The triangle constraints are

\[
3\alpha\ge1,\qquad
\alpha+2\beta\ge1,\qquad
2\beta+\gamma\ge1,\qquad
3\gamma\ge1,
\tag{6.2}
\]

with constraints for nonexistent triangle types omitted.

Define

\[
U=\frac{A+B+C}{3},
\qquad
D=A+C,
\qquad
H=A+\frac{B+C}{3}.
\tag{6.3}
\]

### Theorem 6.1 — Three-candidate orbit formula

For every \(p\ge3\), \(q\ge0\), and \(2\le s\le p\),

\[
\boxed{
M_{\mathrm{id}}(p,q,s)=\min\{U,D,H\}.
}
\tag{6.4}
\]

#### Proof

Assume first \(s,o\ge3\).

If \(A<0\), increasing \(\alpha\) decreases the objective, so \(\alpha=1\). The remaining lower boundary joins \((\beta,\gamma)=(0,1)\) and \((1/3,1/3)\), giving \(D\) or \(H\).

If \(A\ge0\), for fixed \(\beta\) the least feasible values are

\[
\alpha=\gamma=\max(1/3,1-2\beta).
\]

On \(0\le\beta\le1/3\) the objective is linear between \(D\) and \(U\). For \(\beta\ge1/3\), it equals

\[
U+B(\beta-1/3)\ge U.
\]

The boundary cases \(s=2\) or \(o\le2\) are checked in Appendix A; every additional endpoint is dominated by \(U,D\), or \(H\).

### Theorem 6.2 — Weighted three-orbit formula

For the fixed feasible polytope determined by (6.2), if the objective is

\[
X\alpha+Y\beta+Z\gamma,
\qquad
X\in\mathbb R,\quad Y,Z\ge0,
\]

then

\[
\boxed{
\min
=
\min\left\{
\frac{X+Y+Z}{3},
X+Z,
X+\frac{Y+Z}{3}
\right\}.
}
\tag{6.5}
\]

The proof repeats the two sign cases above with \(X,Y,Z\) in place of \(A,B,C\).

---

# 7. The Fractional Envelope

Define

\[
R(p,q)=\frac{2p^2-2pq-q^2}{12}.
\tag{7.1}
\]

Direct expansion gives

\[
U-R=\frac{q(2p+q)-2p}{12}\ge-\frac p6.
\tag{7.2}
\]

Also,

\[
12(D-R)
=
12(p-s)^2-6(p-s)(2p-q)+(2p-q)^2-6p.
\]

Since

\[
12u^2-6uv+v^2
=
12\left(u-\frac v4\right)^2+\frac{v^2}{4}\ge0,
\]

we obtain

\[
D-R\ge-\frac p2.
\tag{7.3}
\]

Finally,

\[
12(H-R)
=
(2s-q)^2+2q(p-s)-2p-4s
\ge-6p,
\]

so

\[
H-R\ge-\frac p2.
\tag{7.4}
\]

### Theorem 7.1 — Fractional envelope

For every split-neighborhood profile,

\[
\boxed{
M(\kappa)\ge R(p,q)-\frac p2.
}
\tag{7.5}
\]

---

# 8. Fractional Split-Graph Application

By Theorem 4.1 and Theorem 7.1,

\[
|E(G)|-2\nu_{\mathrm{con}}
\le
\binom p2-2R(p,q)+p+b_1.
\]

The identity

\[
\binom p2-2R(p,q)+p
=
\frac{(p+q)^2}{6}+\frac p2
\]

gives

\[
|E(G)|-2\nu_{\mathrm{con}}
\le
\frac{(p+q)^2}{6}+\frac p2+b_1.
\]

Since \(p+q\le n\) and \(p/2+b_1\le n\),

\[
|E(G)|-2\nu_{\mathrm{con}}
\le
\frac{n^2}{6}+n.
\]

Because \(\nu_{\mathrm{con}}\le\nu_3^*(G)\), Theorem 1.3 follows.

---

# 9. Integral Application and Sharpness

Equation (1.1), Haxell--Rödl/Yuster, and Theorem 1.3 prove the upper bound in Corollary 1.4.

For sharpness, take

\[
G_p=K_p\vee\overline K_{2p}.
\]

Fix \(v\) in the independent side. If the cliques containing \(v\) meet the core in sets of sizes \(r_{v,1},\ldots,r_{v,c_v}\), then

\[
\sum_jr_{v,j}=p
\]

and

\[
\sum_j\binom{r_{v,j}}2
\ge
\sum_j(r_{v,j}-1)=p-c_v.
\]

Summing over the \(2p\) independent vertices and using that each core edge belongs to at most one clique in the partition gives

\[
2p^2-\sum_vc_v\le\binom p2.
\]

Hence

\[
\sum_vc_v
\ge
2p^2-\binom p2
=
\frac{3p^2+p}{2}.
\]

Thus, with \(n=3p\),

\[
\boxed{
\operatorname{cp}(G_p)\ge\frac{n^2}{6}+\frac n6.
}
\tag{9.1}
\]

Adding at most two isolated vertices handles arbitrary \(n\).

---

# 10. Discussion

## 10.1 The reusable principle

The value function

\[
\Phi(c)=\min_{x\in P}\langle c,x\rangle
\]

is concave in \(c\) whenever \(P\) is fixed. The structural content is the affine identity expressing an arbitrary neighborhood profile as a convex combination of pure profiles.

The method does not automatically apply when the feasible polytope changes with the profile, when global restrictions couple the profile masses, or when interactions enter non-affinely.

## 10.2 Affine reduction versus orbit reduction

These are distinct operations.

- Affine dominance survives arbitrary fixed heterogeneous baselines.
- Orbit reduction requires invariance under the stabilizer of the pure profile.
- The explicit three-candidate formula further uses \(Y,Z\ge0\).

This distinction prevents the weighted statement from being overgeneralized.

## 10.3 Continuous profiles and robustness

Nonnegative real masses are admitted without changing the proof. Dirac profiles attain the minimum over the profile simplex. The Lipschitz estimate shows that approximate symmetry has a controlled cost.

No graphon-limit, network-interdiction, or directed-triangle theorem is claimed.

## 10.4 Relation to the companion papers

Paper II supersedes the finite fractional application quantitatively by determining the exact chordal maximum. Paper III supersedes the integral application quantitatively by proving a linear-error split theorem. Neither supersedes the affine-profile mechanism proved here.

## 10.5 Current open problems

Paper III establishes

\[
f_{\mathrm{split}}(n)=\frac{n^2}{6}+O(n).
\]

The remaining second-order problem is therefore:

### Problem 10.1

Determine the optimal linear coefficient, or the correct bounded periodic refinement, in the maximum split-graph clique-partition number.

### Problem 10.2

Characterize split graphs satisfying

\[
\operatorname{cp}(G)\ge\frac{n^2}{6}-o(n^2).
\]

A natural route is to analyze near-equality in affine dominance and determine when the active pure profiles admit nearly common optimal covers.

### Problem 10.3

Develop higher-clique analogues of affine profile reduction. For \(K_r\), the profiles live on \((r-1)\)-subsets and the pure-profile orbit polytope has more orbit types.

---

# Appendix A. Boundary Cases in the Orbit Program

The boundary cases arise when \(s=2\) or \(o=p-s\le2\).

If \(A<0\), every optimum has \(\alpha=1\). For \(o=2\), the extra endpoint \((\beta,\gamma)=(1/2,0)\) has value \(A+B/2\), and

\[
B/2=s\ge1=C,
\]

so it is dominated by \(D=A+C\). For \(o=1\) or \(o=0\), the minimum is directly \(D=A\).

If \(A\ge0\) and \(s=2\), the missing constraint \(3\alpha\ge1\) introduces the endpoint \(\beta=1/2\), whose value differs from \(U\) by

\[
\frac{B-2A}{6}\ge0.
\]

If \(A\ge0\) and \(o=2\), the symmetric argument gives domination by \(U\) or \(D\). The cases \(o=1\) and \(o=0\) reduce to one- or two-variable intervals and add no smaller vertex. Thus Theorem 6.1 holds in every boundary case.

---

# Appendix B. Supplementary Computational Regression Tests

Every statement tested below is proved analytically in the manuscript. The scripts are independent regression tests and reproducibility material; no computation or finite enumeration is a logical premise of any theorem.

The prior v1.0 record reports:

- 1,000 exact rational affine-mixture checks;
- 711,763 exact orbit-formula and envelope instances;
- 2,000 exact rational dual-bridge profiles.

The regression package is useful for detecting transcription or implementation errors, but the proof remains entirely analytic apart from the cited external mathematical theorems. The optional checks may be removed without changing any theorem, lemma, or corollary.

---

# Acknowledgements and use of AI-assisted tools

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support.

AI-assisted tools were used during exploratory, computational, adversarial, and editorial stages, including Anthropic Claude, Google Gemini, and OpenAI systems accessed through ChatGPT and Codex. They supported exploratory search, testing of candidate arguments, exact computational regression, proof organization, and preparation of drafts. All mathematical claims, citations, code, and final editorial decisions remain the sole responsibility of the author. No AI system is listed as an author.

---

# References

[1] M. Bonamy, Ł. Bożyk, A. Grzesik, M. Hatzel, T. Masařík, J. Novotná, and K. Okrasa, **Tuza’s Conjecture for Threshold Graphs**, *Discrete Mathematics & Theoretical Computer Science* **24** (2022), no. 1, Article 24, 1–14.

[2] G.-T. Chen, P. Erdős, and E. T. Ordman, **Clique Partitions of Split Graphs**, in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

[3] P. Erdős, E. T. Ordman, and Y. Zalcstein, **Clique Partitions of Chordal Graphs**, *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[4] P. E. Haxell and V. Rödl, **Integer and Fractional Packings in Dense Graphs**, *Combinatorica* **21** (2001), 13–38.

[5] R. Yuster, **Integer and Fractional Packing of Families of Graphs**, *Random Structures & Algorithms* **26** (2005), 110–118.

[6] J. P. Traverso Gianini, **Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs**, final author manuscript v0.8, July 2026.

[7] J. P. Traverso Gianini, **Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing**, final author manuscript v1.0.4, July 2026.
