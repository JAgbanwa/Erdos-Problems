# Affine Profile Reduction for Fractional Triangle Packings in Split Graphs

**Juan Pablo Traverso Gianini**  
Independent researcher, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Preprint manuscript:** v1.0  
**Date:** July 6, 2026  
**Status:** preprint release; finite fractional theorem internally frozen, AI-adversarially audited, and formally verified in Lean 4 with Mathlib v4.28.0. The statement of Theorem 1.1 is machine-checked, sorry-free, and its axiom report contains only Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with no project-specific axiom; see Section 10 and Appendix C. Not externally peer-reviewed; bibliographic and novelty review incomplete.

**MSC 2020:** Primary 05C70; Secondary 05C35, 05C72.

---

## Abstract

We study fractional triangle packings in split graphs. A split presentation \(V(G)=K\sqcup I\) allows the triangles meeting the independent set to be packed explicitly. The unused capacities on the clique edges lead, by finite linear-programming duality, to a triangle-cover problem over one fixed polytope. The objective vector of that cover problem depends affinely on the neighborhood types appearing in \(I\).

The minimum of a linear objective over a fixed polytope is concave in the objective vector. This simple observation reduces the task of proving a uniform lower bound for an arbitrary mixture of independent-set neighborhoods to the analysis of pure neighborhood profiles. After averaging over the stabilizer of the pure profile, the residual cover problem becomes a three-variable linear program. Solving that program gives a uniform quadratic lower bound for the residual value.

As a consequence, every split graph \(G\) on \(n\) vertices satisfies

\[
\boxed{
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n,
}
\]

where \(\nu_3^*(G)\) is the maximum fractional triangle-packing value. The leading constant \(1/6\) is the one appearing in Erdős Problem #81 on clique partitions of chordal graphs; the present result concerns the finite fractional problem for the subclass of split graphs. The proof is finite and analytic. No asymptotic transfer theorem is used.

**Keywords:** split graph; fractional triangle packing; fractional triangle cover; linear programming; affine reduction; symmetrization.

---

## 1. Introduction

A split graph is a graph whose vertex set can be partitioned into a clique and an independent set. This class is a natural testing ground for clique-partition questions: it retains a rigid complete core while allowing many different neighborhood patterns outside the core. Erdős, Ordman, and Zalcstein [1] exhibited chordal examples requiring asymptotically \(n^2/6\) cliques and proved that \((1-c)n^2/4\) cliques suffice for some absolute constant \(c>0\). For split graphs, Chen, Erdős, and Ordman [2] proved the sharper upper bound \(\frac{3}{16}n^2+O(n)\). The present paper studies instead the fractional triangle-packing deficit \(|E(G)|-2\nu_3^*(G)\), for which the result below has leading constant \(1/6\). For broader background on clique partitions and coverings, see Cavers [5].

The present paper isolates a fractional mechanism related to the split-graph side of Erdős Problem #81. Rather than trying to choose edge-disjoint triangles directly, we first build a fractional packing from triangles that meet the independent set. The capacity not used by this first packing remains on the clique edges, and those residual capacities support a second packing formed entirely by clique triangles. Duality then turns this residual packing problem into a fractional triangle-cover problem on the clique.

The main structural point is that the feasible cover polytope does not depend on the independent-set neighborhood profile. Only the objective vector changes. Since the optimum of a minimization problem over a fixed polytope is concave in its objective vector, a mixed neighborhood profile is bounded below by the corresponding convex combination of pure-profile values, and therefore by the smallest of those values. This does not identify a mixed profile with a pure one; it shows that a uniform lower bound may be proved by considering pure profiles. The pure case then has enough symmetry to reduce to three orbit variables.

**Role within the broader program.** This paper is self-contained apart from the standard finite-dimensional strong linear-programming duality theorem cited and applied in Appendix B. Its main purpose is to isolate the affine profile-reduction mechanism in the split-graph setting and to give a finite fractional application. Within a broader program on Erdős Problem #81, this mechanism serves as a methodological starting point for later fractional and integral developments. None of those later results is used here.

The resulting proof has the following shape:

\[
\begin{aligned}
\text{explicit packing}
&\longrightarrow
\text{fixed residual polytope}\\
&\longrightarrow
\text{affine profile reduction}\\
&\longrightarrow
\text{three-orbit optimization}
\end{aligned}
\]

Our main theorem is finite.

#### Theorem 1.1

For every split graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}+n.
\]

**Formal verification.** Theorem 1.1 is formalized in Lean 4 with Mathlib v4.28.0 as `paperI_main`. In the formal development, the statement is `Phi ≤ n^2/6 + n`, where `Phi = |E| − 2·nu3star` and `nu3star` is the supremum of the feasible fractional triangle-packing values. Thus the Lean statement is the inequality of Theorem 1.1. The proof is sorry-free. Its axiom report lists only Lean's standard foundational axioms, `propext`, `Classical.choice`, and `Quot.sound`, and no project-specific axiom. Proposition B.1 is also formalized: the finite packing-covering duality used there is derived in `FiniteLPDuality.lean` from Mathlib's finite Farkas and closed-cone infrastructure, rather than postulated. The Lean sources, toolchain file, Lake configuration and manifest, build log, and axiom report are included in the public repository [8], in `PAPER_I/05_formalization/lean`.

The notation and every calculation used in the proof are recorded in the accompanying file `CALCULATION_LEDGER_FINITE_FRACTIONAL_preprint_v1.0.md`. The paper itself emphasizes the mathematical ideas and keeps routine algebra visible but compact.

---

## 2. Split-graph notation

Fix a split presentation

\[
V(G)=K\sqcup I,
\]

where \(K\) is a clique and \(I\) is independent. Write

\[
p:=|K|.
\]

For \(v\in I\), let

\[
d_v:=|N(v)|.
\]

Separate the independent vertices into

\[
I_{\ge2}:=\{v\in I:d_v\ge2\},
\qquad
I_1:=\{v\in I:d_v=1\},
\qquad
I_0:=\{v\in I:d_v=0\}.
\]

Put

\[
q:=|I_{\ge2}|,
\qquad
b_1:=|I_1|,
\qquad
b_{\ge2}:=\sum_{v\in I_{\ge2}}d_v.
\]

Because there are no edges inside \(I\),

\[
|E(G)|
=
\binom{p}{2}+b_{\ge2}+b_1.
\tag{2.1}
\]

Also,

\[
n=p+q+b_1+|I_0|.
\tag{2.2}
\]

Let \(\nu_3^*(G)\) denote the maximum value of a fractional triangle packing: a nonnegative weight \(w(T)\) is assigned to each triangle \(T\), subject to the condition that the total weight of triangles containing any fixed edge is at most one.

---

## 3. The aggregate load on the clique

For a clique edge \(e\in E(K)\), define

\[
\kappa_e
:=
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{1}{d_v-1}.
\tag{3.1}
\]

The normalization is chosen so that each active independent vertex contributes half its degree in total.

#### Lemma 3.1

\[
\sum_{e\in E(K)}\kappa_e
=
\frac{b_{\ge2}}2.
\]

#### Proof

Exchange the order of summation:

\[
\begin{aligned}
\sum_{e\in E(K)}\kappa_e
&=
\sum_{v\in I_{\ge2}}
\frac{\binom{d_v}{2}}{d_v-1}\\
&=
\frac12
\sum_{v\in I_{\ge2}}d_v\\
&=
\frac{b_{\ge2}}2.
\end{aligned}
\]

---

## 4. A two-phase fractional packing

### 4.1 Phase I

For each clique edge \(e\), define

\[
\lambda_e
:=
\begin{cases}
1,&\kappa_e=0,\\[1mm]
\min\{1,\kappa_e^{-1}\},&\kappa_e>0.
\end{cases}
\]

For every triangle \(vxy\) with \(v\in I_{\ge2}\) and \(x,y\in N(v)\), assign

\[
w_1(vxy)
:=
\frac{\lambda_{xy}}{d_v-1}.
\tag{4.1}
\]

The load on a clique edge \(e\) is

\[
\lambda_e\kappa_e
=
\min\{\kappa_e,1\}.
\tag{4.2}
\]

A cross edge \(vx\) lies in at most \(d_v-1\) such triangles, each of weight at most \(1/(d_v-1)\). Thus \(w_1\) is feasible.

Define

\[
H:=\{e:\kappa_e\ge1\},
\qquad
L:=\{e:\kappa_e<1\}.
\]

Every positive Phase-I triangle contains exactly one clique edge. Hence

\[
|w_1|
=
|H|+\sum_{e\in L}\kappa_e.
\tag{4.3}
\]

### 4.2 Phase II

The residual capacity on a clique edge is

\[
r_e:=\max\{1-\kappa_e,0\}.
\tag{4.4}
\]

Let \(w_2\) be an optimal fractional packing of clique triangles under these residual capacities. The finite packing-covering duality used here is recorded explicitly in Appendix B.

After capping the dual cover variables at one, substitute

\[
y_e:=1-x_e.
\]

The triangle-cover constraints become

\[
\sum_{e\in E(T)}y_e\le2.
\]

The coefficients \(1-\kappa_e\) are nonpositive on \(H\), so the maximizing vector may be taken to vanish there. A second substitution,

\[
z_e:=1-y_e,
\]

leads to the fixed polytope

\[
\mathcal P_p
:=
\left\{
z\in[0,1]^{E(K)}:
\sum_{e\in E(T)}z_e\ge1
\text{ for every triangle }T\subseteq K
\right\}.
\tag{4.5}
\]

Define

\[
M(\kappa)
:=
\min_{z\in\mathcal P_p}
\sum_{e\in E(K)}(1-\kappa_e)z_e.
\tag{4.6}
\]

Let

\[
w_{\mathrm{com}}:=w_1+w_2,
\qquad
V_{\mathrm{com}}:=|w_{\mathrm{com}}|.
\]

Here \(M(\kappa)\) is the value of a residual cover problem, not the value of an additional packing. Its feasible region depends only on the clique size \(p\), while all information from the independent-set neighborhoods enters through the objective coefficients \(1-\kappa_e\).

The dual calculation and Lemma 3.1 give the exact identity

\[
\boxed{
V_{\mathrm{com}}
=
\frac{b_{\ge2}}2+M(\kappa).
}
\tag{4.7}
\]

The packing is feasible: on a clique edge, the Phase-I and residual loads add to at most

\[
\min\{\kappa_e,1\}
+
\max\{1-\kappa_e,0\}
=
1.
\]

Therefore

\[
V_{\mathrm{com}}\le\nu_3^*(G).
\tag{4.8}
\]

Combining (2.1) and (4.7) yields

\[
\boxed{
|E(G)|-2V_{\mathrm{com}}
=
\binom{p}{2}-2M(\kappa)+b_1.
}
\tag{4.9}
\]

This cancellation is the bridge from the packing construction to the profile problem.

---

## 5. Affine reduction to a pure neighborhood

For every set \(S\subseteq K\) with \(|S|\ge2\), define

\[
a_e^S
:=
\frac{\mathbf1_{\{e\subseteq S\}}}{|S|-1}.
\tag{5.1}
\]

Let \(n_S\) be the number of vertices \(v\in I_{\ge2}\) with \(N(v)=S\). Then

\[
\kappa=\sum_Sn_Sa^S.
\tag{5.2}
\]

Assume first that \(q>0\), and set

\[
\lambda_S:=\frac{n_S}{q},
\qquad
\kappa^S:=qa^S.
\]

Then

\[
\kappa=\sum_S\lambda_S\kappa^S,
\qquad
\lambda_S\ge0,
\qquad
\sum_S\lambda_S=1.
\tag{5.3}
\]

The reduction follows from an elementary concavity fact.

#### Lemma 5.1

Let \(P\) be nonempty and define

\[
\Phi(c):=\min_{x\in P}\langle c,x\rangle.
\]

If \(c=\sum_i\lambda_ic^{(i)}\) is a convex combination, then

\[
\Phi(c)
\ge
\sum_i\lambda_i\Phi(c^{(i)})
\ge
\min_i\Phi(c^{(i)}).
\]

#### Proof

For every \(x\in P\),

\[
\langle c,x\rangle
=
\sum_i\lambda_i\langle c^{(i)},x\rangle
\ge
\sum_i\lambda_i\Phi(c^{(i)}).
\]

Take the minimum over \(x\in P\).

Apply the lemma to the objective vectors \(1-\kappa^S\) over the fixed polytope \(\mathcal P_p\). The conclusion is a lower-bound reduction: a mixed profile need not coincide with any pure profile, but its residual value is at least the corresponding average of the pure-profile values. We obtain

\[
\boxed{
M(\kappa)
\ge
\sum_S\lambda_SM(\kappa^S)
\ge
\min_SM(\kappa^S).
}
\tag{5.4}
\]

It remains to control a pure profile.

---

## 6. The pure-profile orbit program

Fix \(S\subseteq K\), and write

\[
s:=|S|,
\qquad
o:=p-s.
\]

For the pure profile,

\[
\kappa_e^S
=
\begin{cases}
q/(s-1),&e\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\tag{6.1}
\]

Average an optimal cover over the stabilizer of \(S\). Both the cover polytope and the pure-profile objective are invariant under this group. Averaging therefore preserves feasibility and objective value. The averaged cover is constant on the three edge orbits:

\[
SS,\qquad
S(K\setminus S),\qquad
(K\setminus S)(K\setminus S).
\]

Call the corresponding values

\[
\alpha,\qquad\beta,\qquad\gamma.
\]

The objective is

\[
A\alpha+B\beta+C\gamma,
\tag{6.2}
\]

where

\[
A:=\frac{s(s-1-q)}2,
\qquad
B:=so,
\qquad
C:=\frac{o(o-1)}2.
\tag{6.3}
\]

The existing triangle types impose

\[
3\alpha\ge1,
\qquad
\alpha+2\beta\ge1,
\qquad
2\beta+\gamma\ge1,
\qquad
3\gamma\ge1,
\tag{6.4}
\]

with any constraint omitted when its triangle type does not exist.

The feasible region is now a three-dimensional polytope. Its relevant extreme points give the uniform, separated, and hot-set covers; when some triangle types do not exist, the corresponding boundary regimes must be treated separately. Solving this three-variable program gives

\[
M(\kappa^S)
=
\begin{cases}
\min\{U,D\},&o\le2,\\[1mm]
\min\{U,D,H\},&o\ge3,
\end{cases}
\tag{6.5}
\]

where

\[
U:=\frac{A+B+C}{3},
\qquad
D:=A+C,
\qquad
H:=A+\frac{B+C}{3}.
\tag{6.6}
\]

The three values correspond to the uniform cover, the separated cover, and the hot-set cover.

---

## 7. A uniform lower bound for the residual cover

Define

\[
R(p,q)
:=
\frac{2p^2-2pq-q^2}{12}.
\tag{7.1}
\]

We compare each candidate in (6.5) with \(R(p,q)\).

For the uniform candidate, using \(o=p-s\),

\[
12(U-R)
=
q(2o+q)-2p.
\tag{7.2}
\]

Since \(q,o\ge0\),

\[
U-R\ge-\frac p6.
\tag{7.3}
\]

For the separated candidate,

\[
12(D-R)
=
12o^2-6o(2p-q)+(2p-q)^2-6p.
\tag{7.4}
\]

The quadratic part is nonnegative because

\[
12u^2-6uv+v^2
=
12\left(u-\frac v4\right)^2+\frac{v^2}{4}.
\]

Thus

\[
D-R\ge-\frac p2.
\tag{7.5}
\]

For the hot-set candidate,

\[
12(H-R)
=
(2s-q)^2+2q(p-s)-2p-4s.
\tag{7.6}
\]

The first two terms are nonnegative, and \(s\le p\), so

\[
H-R\ge-\frac p2.
\tag{7.7}
\]

Consequently,

\[
M(\kappa^S)
\ge
R(p,q)-\frac p2
\]

for every pure profile. By (5.4),

\[
\boxed{
M(\kappa)
\ge
R(p,q)-\frac p2.
}
\tag{7.8}
\]

When \(q=0\), the same estimate follows directly. If \(p\le2\), then \(M(0)=0\). If \(p\ge3\), the constant cover \(z_e=1/3\) is feasible. To see that it is optimal, sum the cover constraints over all clique triangles: every clique edge occurs in exactly \(p-2\) such triangles, which gives the matching lower bound. Hence

\[
M(0)=\frac{p(p-1)}6.
\]

---

## 8. Proof of the main theorem

Start from (4.9):

\[
|E(G)|-2V_{\mathrm{com}}
=
\binom p2-2M(\kappa)+b_1.
\]

Insert (7.8):

\[
|E(G)|-2V_{\mathrm{com}}
\le
\binom p2-2R(p,q)+p+b_1.
\tag{8.1}
\]

A direct simplification gives

\[
\binom p2-2R(p,q)+p
=
\frac{(p+q)^2}{6}+\frac p2.
\tag{8.2}
\]

Hence

\[
|E(G)|-2V_{\mathrm{com}}
\le
\frac{(p+q)^2}{6}+\frac p2+b_1.
\tag{8.3}
\]

From (2.2), the vertices counted by \(p+q\) form only part of \(V(G)\), so

\[
p+q\le n
\]

and the quadratic term may be enlarged accordingly. Likewise, the clique vertices and the degree-one independent vertices are disjoint, and therefore

\[
\frac p2+b_1
\le
p+b_1
\le
n.
\]

Therefore

\[
|E(G)|-2V_{\mathrm{com}}
\le
\frac{n^2}{6}+n.
\tag{8.4}
\]

Finally, \(V_{\mathrm{com}}\le\nu_3^*(G)\). Thus

\[
|E(G)|-2\nu_3^*(G)
\le
|E(G)|-2V_{\mathrm{com}}
\le
\frac{n^2}{6}+n.
\]

This proves Theorem 1.1.

---

## 9. Discussion

Three elementary ideas drive the proof. We first separate the packing into a part supported on triangles meeting the independent set and a residual part supported entirely on the clique. We then formulate the residual problem over one fixed cover polytope. Symmetry is used only after the lower-bound problem has been reduced to pure profiles.

The fixed-polytope feature is the central structural point. Concavity applies because the feasible region does not change when the neighborhood profile changes; only the objective vector does. If the constraints themselves depended on the profile, the reduction in Section 5 would no longer follow from the same argument. Orbit averaging is a separate step: it uses the symmetry of a pure profile and is not needed for the affine reduction itself.

The intermediate quantities \(p\), \(q\), and \(\kappa\) depend on the chosen split presentation. The final estimate does not. Once the terms are assembled, the conclusion is expressed only in terms of \(n=|V(G)|\).

The additive term \(+n\) in Theorem 1.1 is not optimized. For the complete-split family \(K_p\vee\overline{K}_{2p}\), with \(p\ge2\) and \(n=3p\), every triangle uses at least one clique edge, so \(\nu_3^*(G)\le\binom p2\), while the Phase-I construction attains equality. Consequently, the left-hand side of Theorem 1.1 equals \(n^2/6+n/6\) on this family. Determining the optimal linear term is outside the scope of the present argument.

The paper is intentionally limited to the finite fractional inequality. Any passage to integral triangle packings, clique partitions, asymptotic consequences, or wider graph classes requires additional results and belongs to a separate stage.

The value of the present argument lies primarily in the reduction mechanism, which is intended to be reusable independently of the particular finite bound proved here.

---

## 10. Reproducibility and proof record

The proof is analytic. Computational experiments were used during development to search for counterexamples and detect transcription errors, but no computation is a logical premise of the theorem. For that reason, computational regression material is kept outside the paper rather than included as a second appendix.

The accompanying file `CALCULATION_LEDGER_FINITE_FRACTIONAL_preprint_v1.0.md` records:

- every exact identity;
- every inequality direction;
- the complete loss accounting;
- the branch \(q=0\);
- the orbit regimes;
- the final conversion to \(n\).

The theorem, its quantitative bound, and the complete assembly have each received adversarial internal audit. This statement describes the author's validation record; it is not a claim of external peer review.

### Formal verification in Lean

Theorem 1.1 is formalized and machine-checked in Lean 4 with Mathlib v4.28.0 [6,7]. The corresponding declaration is `paperI_main`. Its formal statement is `Phi ≤ n^2/6 + n`; under the definitions used in the Lean development, `Phi = |E| − 2·nu3star`, and `nu3star` is the supremum of the feasible fractional triangle-packing values. This is the same inequality as Theorem 1.1, stated in the notation of the formalization; Appendix C records the exact Lean declaration.

The development is sorry-free. The recorded axiom report for `paperI_main` contains only Lean's standard foundational axioms, `propext`, `Classical.choice`, and `Quot.sound`. No project-specific axiom is used. These axioms are part of the ordinary logical foundation used throughout Mathlib, not extra mathematical assumptions introduced by this paper.

The finite-dimensional packing-covering duality used in Proposition B.1 is also formalized. In Lean it appears as `residual_duality`, an application of the general theorem `covering_packing_duality`. That general theorem is proved from a finite Farkas lemma and Mathlib's closed-cone infrastructure; the duality is therefore derived inside the formal development, not postulated as an external axiom. The citation to Schrijver [4, Corollary 7.1g] remains the classical reference for the written mathematical proof.

The public formalization artifact is distributed with the preprint through the project repository [8], in `PAPER_I/05_formalization/lean`. The release package contains the Lean sources `FiniteLPDuality.lean` and `PaperI_Statement.lean`, the toolchain file, the Lake configuration and manifest, exact build instructions, a recorded build log, and the recorded axiom report for Theorem 1.1 and Proposition B.1. These files make the formal-verification claims independently rerunnable and auditable.

---


## Appendix A. The three-orbit program and its boundary cases

This appendix supplies the details behind (6.5). It is included because the cases in which one of the four triangle types does not exist are easy to obscure in a compressed orbit calculation.

For a pure profile \(S\subseteq K\), write

\[
s:=|S|,
\qquad
o:=p-s,
\]

and let \(\alpha,\beta,\gamma\) denote the cover values on the edge orbits

\[
SS,\qquad S(K\setminus S),\qquad (K\setminus S)(K\setminus S).
\]

The objective is

\[
A\alpha+B\beta+C\gamma,
\]

where

\[
A=\frac{s(s-1-q)}2,
\qquad
B=so,
\qquad
C=\frac{o(o-1)}2.
\]

Only constraints corresponding to existing triangle types are imposed.

### A.1 The interior case \(s\ge3\) and \(o\ge3\)

All four constraints are present:

\[
3\alpha\ge1,
\qquad
\alpha+2\beta\ge1,
\qquad
2\beta+\gamma\ge1,
\qquad
3\gamma\ge1.
\]

If \(A<0\), decreasing the objective favors the largest feasible value of \(\alpha\), so an optimum has \(\alpha=1\). The remaining lower boundary joins

\[
(\beta,\gamma)=(0,1)
\]

and

\[
(\beta,\gamma)=\left(\frac13,\frac13\right).
\]

Because the objective is linear on that segment, its minimum is attained at an endpoint. These two endpoint values are

\[
D=A+C
\]

and

\[
H=A+\frac{B+C}{3}.
\]

If \(A\ge0\), then for fixed \(\beta\) the least feasible values of \(\alpha\) and \(\gamma\) are

\[
\alpha=\gamma=\max\left\{\frac13,1-2\beta\right\}.
\]

For \(0\le\beta\le1/3\), the objective is linear between the separated point and the uniform point, with values \(D\) and

\[
U=\frac{A+B+C}{3}.
\]

For \(\beta\ge1/3\), the objective is

\[
U+B\left(\beta-\frac13\right)\ge U,
\]

because \(B\ge0\). Hence the minimum is one of \(U,D,H\).

### A.2 The case \(s=2\)

The \(SSS\) triangle type does not exist, so the constraint \(3\alpha\ge1\) is omitted.

If \(A<0\), the same monotonicity argument gives \(\alpha=1\), and the endpoint analysis above remains valid.

If \(A\ge0\), the missing constraint introduces one additional boundary endpoint at \(\beta=1/2\). Its objective value exceeds the uniform value by

\[
\frac{B-2A}{6}.
\]

For \(s=2\),

\[
B-2A
=
2o-2(1-q)
=
2(o+q-1)\ge0
\]

whenever this endpoint is relevant. Therefore it does not improve on \(U\).

### A.3 The cases \(o=0,1,2\)

When \(o=0\), we have \(B=C=0\). If \(s\ge3\), the only triangle constraint is \(3\alpha\ge1\), so

\[
\min_{\alpha\in[1/3,1]}A\alpha
=
\min\left\{\frac A3,A\right\}
=
\min\{U,D\}.
\]

If \(s=2\), then \(p=2\) and there are no clique-triangle constraints. Since the pure-profile case has \(q>0\), we have \(A=1-q\le0\), and the minimum over \(0\le\alpha\le1\) is \(A=D\). Thus the formula \(\min\{U,D\}\) remains valid.

When \(o=1\), there are no \((K\setminus S)^2\) edges and no triangle type entirely in \(K\setminus S\). The reduced feasible region is an interval, and its endpoints give \(U\) or \(D\).

When \(o=2\), the triangle type entirely in \(K\setminus S\) does not exist. A possible extra endpoint has

\[
(\beta,\gamma)=\left(\frac12,0\right)
\]

and objective value

\[
A+\frac B2.
\]

Since \(o=2\),

\[
\frac B2=s
\qquad\text{and}\qquad
C=1,
\]

so

\[
A+\frac B2\ge A+C=D.
\]

Thus this endpoint is dominated by \(D\).

Consequently,

\[
M(\kappa^S)
=
\begin{cases}
\min\{U,D\},&o\le2,\\[1mm]
\min\{U,D,H\},&o\ge3.
\end{cases}
\]

No nonexistent orbit or triangle constraint is used in any boundary regime.

---

## Appendix B. Finite packing-covering duality

For completeness, we record the specialized finite packing-covering dual pair used in Section 4, prove weak duality, verify the hypotheses required for the finite-dimensional strong linear-programming duality theorem cited below, and apply that theorem to the residual program.

#### Proposition B.1

Let \(\mathcal T\) be a finite family of triangles, let \(E\) be the finite set of edges appearing in them, and let \(r=(r_e)_{e\in E}\) be a nonnegative capacity vector. Then

\[
\max\left\{
\sum_{T\in\mathcal T}w_T:
w_T\ge0,\ 
\sum_{T\ni e}w_T\le r_e
\text{ for every }e\in E
\right\}
\]

equals

\[
\min\left\{
\sum_{e\in E}r_ex_e:
x_e\ge0,\ 
\sum_{e\in E(T)}x_e\ge1
\text{ for every }T\in\mathcal T
\right\}.
\]

Both optima are attained.

#### Proof

Let \(A\) be the edge-triangle incidence matrix, so that \(A_{eT}=1\) when \(e\in E(T)\) and \(A_{eT}=0\) otherwise. The two programs are

\[
\max\{\mathbf 1^{\mathsf T}w:Aw\le r,\ w\ge0\}
\]

and

\[
\min\{r^{\mathsf T}x:A^{\mathsf T}x\ge\mathbf 1,\ x\ge0\}.
\]

Weak duality follows directly. Indeed, for every feasible pair \(w,x\),

\[
\mathbf 1^{\mathsf T}w
\le
x^{\mathsf T}Aw
\le
x^{\mathsf T}r.
\]

The primal feasible region is nonempty, since \(w=0\) is feasible. It is also bounded in every coordinate: if \(T\in\mathcal T\), then for each edge \(e\in E(T)\),

\[
0\le w_T\le\sum_{T'\ni e}w_{T'}\le r_e.
\]

Hence the primal optimum is finite and attained. The dual is feasible, for example with \(x_e=1\) for every \(e\). Finite-dimensional strong linear-programming duality [4, Corollary 7.1g] therefore gives equality of the two attained optimum values. Applying the proposition to the clique triangles and the residual capacities \(r_e\) in (4.4) yields the dual program used in Section 4.

**Formalization note.** Proposition B.1 is also machine-checked in Lean as `residual_duality`, an instance of the general finite strong-duality theorem `covering_packing_duality`. The latter is proved from a finite Farkas lemma, using the closedness of a finitely generated convex cone and the hyperplane-separation theorem for closed convex cones. Thus the duality used here is derived inside the formal development, not postulated as a project-specific axiom. Schrijver remains the classical reference for the written argument. The corresponding sources, build log, and axiom report are included in the public artifact [8], in `PAPER_I/05_formalization/lean`.


---

## Appendix C. Formalized statement

The machine-checked statement of Theorem 1.1 is the following Lean 4 declaration:

```lean
theorem paperI_main (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ)
```

Here `Split` packages the data of a split graph used in the proof: a clique of size `p`, an independent vertex type, and the neighborhoods of the independent vertices inside the clique. The field `n` is the total number of vertices. The quantity `Phi` is defined as `|E| − 2·nu3star`, where `nu3star` is the supremum of the feasible fractional triangle-packing values. With these definitions, `paperI_main` is precisely

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n,
\]

the inequality stated in Theorem 1.1.

The verification is sorry-free. The recorded axiom report is:

```text
PaperI.paperI_main depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard foundational axioms of Lean and Mathlib. No project-specific axiom is used.


## Acknowledgements

The author is deeply grateful to his wife María Paz and to his children Lucas, Juan Cristóbal, Francisca, Raimundo, and Benjamín for their love, patience, and support.

---

## Use of AI-assisted tools

AI-assisted tools were used during exploratory, computational, adversarial, and editorial stages, including systems from Anthropic, Google, and OpenAI. They supported the testing of candidate arguments, exact regression checks, proof organization, and drafting. The author reviewed the mathematical content, selected the final arguments, and remains solely responsible for the claims, citations, code, and presentation. No AI system is listed as an author.

---

## References

1. P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

2. G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

3. T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, accessed 2026-07-06.

4. A. Schrijver, *Theory of Linear and Integer Programming*, Wiley-Interscience Series in Discrete Mathematics and Optimization, John Wiley & Sons, Chichester, 1986.

5. M. S. Cavers, *Clique Partitions and Coverings of Graphs*, M.Math. essay, University of Waterloo, 2005.

6. L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language,” in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science **12699**, Springer, 2021, pp. 625–635, https://doi.org/10.1007/978-3-030-79876-5_37.

7. The mathlib Community, “The Lean Mathematical Library,” in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367–381, https://doi.org/10.1145/3372885.3373824.

8. J. P. Traverso Gianini, *Erdős #81 Chordal Clique Partitions: Public Preprints and Formalization Artifacts*, public project repository, 2026, https://github.com/jtraverso/erdos-81-chordal-clique-partitions, accessed July 7, 2026.
