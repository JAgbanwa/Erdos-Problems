# Calculation Ledger for the Finite Fractional Split-Graph Theorem

**Project:** ERDOZ81 — Paper I  
**Ledger version:** preprint v1.0  
**Frozen theorem gate:** `ERDOZ81-P1-FRAC-THM-01`  
**Assembly gate:** `ERDOZ81-P1-ASSEMBLY-01`  
**Status:** `FINAL_PASS / FROZEN / CLEAN`  
**Purpose:** record every proof-relevant calculation, substitution, inequality, and loss in one linear chain.

---

## 0. The statement being calculated

Let \(G\) be a finite split graph on \(n\) vertices. We prove

\[
\boxed{
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n,
}
\]

where \(\nu_3^*(G)\) is the maximum value of a fractional triangle packing.

The only imported proof-critical theorem used in this ledger is finite-dimensional strong linear-programming duality, cited in Appendix B of the manuscript as Schrijver [4, Corollary 7.1g]. Appendix B records the specialized finite packing-covering programs, proves weak duality, verifies the hypotheses required for the cited theorem, and derives the equality used below. `ERDOZ81-P1-LP-DUALITY-01` records this verified application; it is not an internal proof of the general strong-duality theorem.

---

## 1. Split presentation and vertex classes

Fix a split presentation

\[
V(G)=K\sqcup I,
\]

where \(K\) induces a clique and \(I\) is independent.

Set

\[
p:=|K|.
\]

For \(v\in I\), let

\[
d_v:=|N(v)|.
\]

Partition the independent side by degree:

\[
I=I_{\ge2}\sqcup I_1\sqcup I_0,
\]

where

\[
I_{\ge2}:=\{v\in I:d_v\ge2\},
\qquad
I_1:=\{v\in I:d_v=1\},
\qquad
I_0:=\{v\in I:d_v=0\}.
\]

Write

\[
q:=|I_{\ge2}|,
\qquad
b_1:=|I_1|,
\qquad
b_{\ge2}:=\sum_{v\in I_{\ge2}}d_v.
\]

Since \(I\) is independent, every edge of \(G\) is either:

1. an edge of the clique \(K\);
2. an edge from \(K\) to a vertex of \(I_{\ge2}\);
3. the unique edge incident with a vertex of \(I_1\).

Therefore

\[
\boxed{
|E(G)|=\binom{p}{2}+b_{\ge2}+b_1.
}
\tag{L1}
\]

The total number of vertices is

\[
\boxed{
n=p+q+b_1+|I_0|.
}
\tag{L2}
\]

No approximation has occurred.

---

## 2. Aggregate clique-edge load

For every clique edge \(e\in E(K)\), define

\[
\kappa_e
:=
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{1}{d_v-1}.
\tag{L3}
\]

Now sum over all clique edges:

\[
\sum_{e\in E(K)}\kappa_e
=
\sum_{e\in E(K)}
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{1}{d_v-1}.
\]

Exchange the order of summation:

\[
\sum_{e\in E(K)}\kappa_e
=
\sum_{v\in I_{\ge2}}
\sum_{e\in\binom{N(v)}2}
\frac{1}{d_v-1}.
\]

For a fixed \(v\), the inner sum contains \(\binom{d_v}{2}\) terms. Hence

\[
\sum_{e\in E(K)}\kappa_e
=
\sum_{v\in I_{\ge2}}
\frac{\binom{d_v}{2}}{d_v-1}.
\]

Use

\[
\binom{d_v}{2}
=
\frac{d_v(d_v-1)}2.
\]

Therefore

\[
\frac{\binom{d_v}{2}}{d_v-1}
=
\frac{d_v}{2},
\]

and so

\[
\sum_{e\in E(K)}\kappa_e
=
\frac12\sum_{v\in I_{\ge2}}d_v.
\]

By the definition of \(b_{\ge2}\),

\[
\boxed{
\sum_{e\in E(K)}\kappa_e
=
\frac{b_{\ge2}}2.
}
\tag{L4}
\]

This is the aggregate-load identity.

---

## 3. Phase I: triangles meeting the independent set

For each clique edge \(e\), define

\[
\lambda_e
:=
\begin{cases}
1,&\kappa_e=0,\\[2mm]
\min\{1,\kappa_e^{-1}\},&\kappa_e>0.
\end{cases}
\tag{L5}
\]

For every triangle \(vxy\) with

\[
v\in I_{\ge2},
\qquad
x,y\in N(v),
\]

assign

\[
w_1(vxy)
:=
\frac{\lambda_{xy}}{d_v-1}.
\tag{L6}
\]

### 3.1 Load on a clique edge

Fix \(e=xy\in E(K)\). Its total Phase-I load is

\[
\begin{aligned}
\ell_{w_1}(e)
&=
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{\lambda_e}{d_v-1}\\
&=
\lambda_e
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{1}{d_v-1}\\
&=
\lambda_e\kappa_e.
\end{aligned}
\]

From the definition of \(\lambda_e\),

\[
\lambda_e\kappa_e
=
\min\{\kappa_e,1\}.
\]

Thus

\[
\boxed{
\ell_{w_1}(e)=\min\{\kappa_e,1\}\le1.
}
\tag{L7}
\]

### 3.2 Load on a cross edge

Fix a cross edge \(vx\), with \(v\in I_{\ge2}\) and \(x\in N(v)\). It belongs to exactly the triangles

\[
vxy,
\qquad
y\in N(v)\setminus\{x\}.
\]

There are \(d_v-1\) such triangles, and every weight satisfies

\[
w_1(vxy)
=
\frac{\lambda_{xy}}{d_v-1}
\le
\frac{1}{d_v-1}.
\]

Therefore

\[
\ell_{w_1}(vx)
\le
(d_v-1)\frac1{d_v-1}
=
1.
\tag{L8}
\]

Hence \(w_1\) is a feasible fractional triangle packing.

### 3.3 Exact value of Phase I

Define

\[
H:=\{e\in E(K):\kappa_e\ge1\},
\qquad
L:=\{e\in E(K):\kappa_e<1\}.
\tag{L9}
\]

Every positive Phase-I triangle contains exactly one clique edge. Therefore the value of \(w_1\) equals the sum of its clique-edge loads:

\[
\begin{aligned}
\nu_1
:=
|w_1|
&=
\sum_{e\in E(K)}\min\{\kappa_e,1\}\\
&=
\sum_{e\in H}1
+
\sum_{e\in L}\kappa_e.
\end{aligned}
\]

Thus

\[
\boxed{
\nu_1=|H|+\sum_{e\in L}\kappa_e.
}
\tag{L10}
\]

---

## 4. Phase II: residual clique-triangle packing

The residual capacity on a clique edge is

\[
r_e
:=
1-\ell_{w_1}(e)
=
1-\min\{\kappa_e,1\}.
\]

Equivalently,

\[
\boxed{
r_e=\max\{1-\kappa_e,0\}.
}
\tag{L11}
\]

Thus

\[
r_e=
\begin{cases}
1-\kappa_e,&e\in L,\\
0,&e\in H.
\end{cases}
\]

Let \(\nu_2\) be the optimum of the residual clique-triangle packing program:

\[
\begin{aligned}
\nu_2:=\max\quad
&\sum_T w_2(T)\\
\text{subject to}\quad
&w_2(T)\ge0
&&\text{for every clique triangle }T,\\
&\sum_{T\ni e}w_2(T)\le r_e
&&\text{for every }e\in E(K).
\end{aligned}
\tag{L12}
\]

Finite strong duality gives

\[
\begin{aligned}
\nu_2=\min\quad
&\sum_{e\in E(K)}r_ex_e\\
\text{subject to}\quad
&x_e\ge0
&&\text{for every }e\in E(K),\\
&\sum_{e\in E(T)}x_e\ge1
&&\text{for every clique triangle }T.
\end{aligned}
\tag{L13}
\]

Because \(r_e\ge0\), capping \(x_e\) at \(1\) cannot increase the objective and preserves every triangle constraint. Hence one may impose

\[
0\le x_e\le1.
\tag{L14}
\]

Set

\[
y_e:=1-x_e.
\tag{L15}
\]

Then

\[
0\le y_e\le1,
\]

and for every clique triangle \(T\),

\[
\sum_{e\in E(T)}x_e\ge1
\iff
3-\sum_{e\in E(T)}y_e\ge1
\iff
\sum_{e\in E(T)}y_e\le2.
\tag{L16}
\]

The dual objective becomes

\[
\sum_e r_ex_e
=
\sum_e r_e(1-y_e)
=
\sum_e r_e-\sum_e r_ey_e.
\]

Consequently,

\[
\boxed{
\nu_2
=
\sum_{e\in L}(1-\kappa_e)
-
\max_y
\sum_{e\in L}(1-\kappa_e)y_e,
}
\tag{L17}
\]

where the maximum is over \(0\le y_e\le1\) and \(y(T)\le2\).

On a hot edge \(e\in H\),

\[
1-\kappa_e\le0.
\]

If a feasible vector has \(y_e>0\) on a hot edge, replacing that coordinate by \(0\):

- preserves \(0\le y_e\le1\);
- can only decrease each triangle sum;
- cannot decrease the signed objective.

Therefore the maximization may be extended over all clique edges:

\[
\boxed{
\max_y
\sum_{e\in L}(1-\kappa_e)y_e
=
\max_y
\sum_{e\in E(K)}(1-\kappa_e)y_e.
}
\tag{L18}
\]

Now set

\[
z_e:=1-y_e.
\tag{L19}
\]

The conditions \(0\le y_e\le1\) become \(0\le z_e\le1\), and

\[
y(T)\le2
\iff
3-z(T)\le2
\iff
z(T)\ge1.
\]

Thus \(z\) lies in the fixed fractional triangle-cover polytope

\[
\mathcal P_p
:=
\left\{
z\in[0,1]^{E(K)}:
\sum_{e\in E(T)}z_e\ge1
\text{ for every clique triangle }T
\right\}.
\tag{L20}
\]

Define

\[
\boxed{
M(\kappa)
:=
\min_{z\in\mathcal P_p}
\sum_{e\in E(K)}(1-\kappa_e)z_e.
}
\tag{L21}
\]

Using \(y=1-z\),

\[
\begin{aligned}
\max_y
\sum_e(1-\kappa_e)y_e
&=
\max_{z\in\mathcal P_p}
\sum_e(1-\kappa_e)(1-z_e)\\
&=
\sum_e(1-\kappa_e)
-
\min_{z\in\mathcal P_p}
\sum_e(1-\kappa_e)z_e\\
&=
\sum_e(1-\kappa_e)-M(\kappa).
\end{aligned}
\tag{L22}
\]

---

## 5. Exact value of the combined packing

Choose an optimal Phase-II packing \(w_2\) and define

\[
w_{\mathrm{com}}:=w_1+w_2.
\tag{L23}
\]

Its value is

\[
V_{\mathrm{com}}
:=
|w_{\mathrm{com}}|
=
\nu_1+\nu_2.
\tag{L24}
\]

Insert (L10), (L17), (L18), and (L22):

\[
\begin{aligned}
V_{\mathrm{com}}
&=
|H|
+
\sum_{e\in L}\kappa_e
+
\sum_{e\in L}(1-\kappa_e)\\
&\qquad
-
\max_y
\sum_{e\in E(K)}(1-\kappa_e)y_e\\
&=
|H|+|L|
-
\max_y
\sum_{e\in E(K)}(1-\kappa_e)y_e\\
&=
\binom p2
-
\left[
\sum_{e\in E(K)}(1-\kappa_e)-M(\kappa)
\right].
\end{aligned}
\]

Now

\[
\sum_{e\in E(K)}(1-\kappa_e)
=
\binom p2-\sum_{e\in E(K)}\kappa_e.
\]

Use (L4):

\[
\sum_{e\in E(K)}(1-\kappa_e)
=
\binom p2-\frac{b_{\ge2}}2.
\]

Therefore

\[
\begin{aligned}
V_{\mathrm{com}}
&=
\binom p2
-
\left(
\binom p2-\frac{b_{\ge2}}2-M(\kappa)
\right)\\
&=
\boxed{
\frac{b_{\ge2}}2+M(\kappa).
}
\end{aligned}
\tag{L25}
\]

### 5.1 Feasibility of the combined packing

On each clique edge,

\[
\ell_{w_1}(e)=\min\{\kappa_e,1\},
\]

while Phase II uses at most

\[
r_e=\max\{1-\kappa_e,0\}.
\]

Hence

\[
\begin{aligned}
\ell_{w_{\mathrm{com}}}(e)
&\le
\min\{\kappa_e,1\}
+
\max\{1-\kappa_e,0\}\\
&=
1.
\end{aligned}
\tag{L26}
\]

Phase II does not use cross edges, and Phase I already satisfies every cross-edge capacity. Thus \(w_{\mathrm{com}}\) is feasible, so

\[
\boxed{
V_{\mathrm{com}}\le\nu_3^*(G).
}
\tag{L27}
\]

---

## 6. Exact deficit identity

Combine the edge count (L1) with the packing value (L25):

\[
\begin{aligned}
|E(G)|-2V_{\mathrm{com}}
&=
\left(
\binom p2+b_{\ge2}+b_1
\right)
-
2\left(
\frac{b_{\ge2}}2+M(\kappa)
\right)\\
&=
\binom p2+b_{\ge2}+b_1-b_{\ge2}-2M(\kappa)\\
&=
\boxed{
\binom p2-2M(\kappa)+b_1.
}
\end{aligned}
\tag{L28}
\]

The term \(b_{\ge2}\) cancels exactly.

---

## 7. Affine profile reduction

For every set \(S\subseteq K\) with \(|S|\ge2\), define

\[
a_e^S
:=
\frac{\mathbf1_{\{e\subseteq S\}}}{|S|-1}.
\tag{L29}
\]

Let \(n_S\) be the number of vertices \(v\in I_{\ge2}\) with \(N(v)=S\). Then

\[
\kappa=\sum_S n_Sa^S.
\tag{L30}
\]

When \(q>0\), define

\[
\lambda_S:=\frac{n_S}{q},
\qquad
\kappa^S:=qa^S.
\tag{L31}
\]

Since \(\sum_S n_S=q\),

\[
\lambda_S\ge0,
\qquad
\sum_S\lambda_S=1.
\]

Moreover,

\[
\sum_S\lambda_S\kappa^S
=
\sum_S\frac{n_S}{q}\,qa^S
=
\sum_Sn_Sa^S
=
\kappa.
\tag{L32}
\]

For a fixed nonempty polytope \(P\), the function

\[
\Phi(c):=\min_{x\in P}\langle c,x\rangle
\]

is concave in \(c\). Indeed, if \(c=\sum_i\lambda_ic^{(i)}\), then for every \(x\in P\),

\[
\langle c,x\rangle
=
\sum_i\lambda_i\langle c^{(i)},x\rangle
\ge
\sum_i\lambda_i\Phi(c^{(i)}).
\]

Taking the minimum over \(x\in P\) gives

\[
\Phi(c)
\ge
\sum_i\lambda_i\Phi(c^{(i)})
\ge
\min_i\Phi(c^{(i)}).
\tag{L33}
\]

Apply this to the objective vectors \(1-\kappa^S\) over the fixed polytope \(\mathcal P_p\). By (L32),

\[
1-\kappa
=
\sum_S\lambda_S(1-\kappa^S).
\]

Therefore

\[
\boxed{
M(\kappa)
\ge
\sum_S\lambda_SM(\kappa^S)
\ge
\min_SM(\kappa^S).
}
\tag{L34}
\]

Thus it is enough to bound pure profiles.

---

## 8. Pure profile and orbit variables

Fix a pure profile \(S\subseteq K\), with

\[
s:=|S|,
\qquad
o:=p-s.
\tag{L35}
\]

Then

\[
\kappa_e^S
=
\begin{cases}
q/(s-1),&e\subseteq S,\\
0,&\text{otherwise}.
\end{cases}
\tag{L36}
\]

Average an optimum cover over the stabilizer

\[
\operatorname{Sym}(S)\times\operatorname{Sym}(K\setminus S).
\]

The averaged optimum is constant on the three nonempty edge orbits:

- \(SS\), with variable \(\alpha\);
- \(SO\), with variable \(\beta\);
- \(OO\), with variable \(\gamma\).

The aggregate objective coefficients are

\[
\boxed{
A:=\frac{s(s-1-q)}2,
\qquad
B:=so,
\qquad
C:=\frac{o(o-1)}2.
}
\tag{L37}
\]

The objective is

\[
A\alpha+B\beta+C\gamma.
\tag{L38}
\]

The possible triangle types yield:

\[
3\alpha\ge1
\quad\text{if }s\ge3,
\tag{L39}
\]

\[
\alpha+2\beta\ge1
\quad\text{if }o\ge1,
\tag{L40}
\]

\[
2\beta+\gamma\ge1
\quad\text{if }o\ge2,
\tag{L41}
\]

\[
3\gamma\ge1
\quad\text{if }o\ge3.
\tag{L42}
\]

Constraints for nonexistent triangle types are omitted.

The exact orbit solution gives the candidate values

\[
U:=\frac{A+B+C}{3},
\qquad
D:=A+C,
\tag{L43}
\]

and, when \(o\ge3\),

\[
H:=A+\frac{B+C}{3}.
\tag{L44}
\]

The exact optimum is

\[
M(\kappa^S)
=
\begin{cases}
\min\{U,D\},&o\le2,\\[1mm]
\min\{U,D,H\},&o\ge3.
\end{cases}
\tag{L45}
\]

Endpoint domination in the cases \(s=2\) and \(o\le2\) is proved in Appendix A of the paper.

---

## 9. Quantitative benchmark

Define

\[
\boxed{
R(p,q)
:=
\frac{2p^2-2pq-q^2}{12}.
}
\tag{L46}
\]

The goal is to prove

\[
M(\kappa)\ge R(p,q)-\frac p2.
\tag{L47}
\]

### 9.1 Uniform candidate

A direct expansion, using \(o=p-s\), gives

\[
\boxed{
12(U-R)
=
q(2o+q)-2p.
}
\tag{L48}
\]

Since \(q\ge0\) and \(o\ge0\),

\[
q(2o+q)\ge0.
\]

Therefore

\[
12(U-R)\ge-2p,
\]

and hence

\[
\boxed{
U-R\ge-\frac p6\ge-\frac p2.
}
\tag{L49}
\]

### 9.2 Diagonal candidate

A direct expansion gives

\[
12(D-R)
=
12o^2-6o(2p-q)+(2p-q)^2-6p.
\tag{L50}
\]

For real \(u,v\),

\[
\begin{aligned}
12u^2-6uv+v^2
&=
12\left(u-\frac v4\right)^2+\frac{v^2}{4}\\
&\ge0.
\end{aligned}
\tag{L51}
\]

Take

\[
u=o,
\qquad
v=2p-q.
\]

Then the first three terms of (L50) are nonnegative. Hence

\[
12(D-R)\ge-6p,
\]

so

\[
\boxed{
D-R\ge-\frac p2.
}
\tag{L52}
\]

### 9.3 Hot-set candidate

When \(o\ge3\), direct expansion gives

\[
12(H-R)
=
(2s-q)^2+2q(p-s)-2p-4s.
\tag{L53}
\]

The first two terms are nonnegative because

\[
(2s-q)^2\ge0,
\qquad
q(p-s)=qo\ge0.
\]

Thus

\[
12(H-R)\ge-2p-4s.
\]

Since \(s\le p\),

\[
-2p-4s\ge-6p.
\]

Therefore

\[
\boxed{
H-R\ge-\frac p2.
}
\tag{L54}
\]

### 9.4 Pure and mixed profiles

Every candidate that can realize the pure-profile optimum is at least \(R-p/2\). Therefore

\[
M(\kappa^S)\ge R(p,q)-\frac p2
\]

for every pure profile \(S\). By (L34),

\[
\boxed{
M(\kappa)\ge R(p,q)-\frac p2
}
\tag{L55}
\]

whenever \(q>0\).

### 9.5 The branch \(q=0\)

When \(q=0\), one has \(\kappa=0\).

If \(p\le2\), there are no clique triangles and

\[
M(0)=0.
\]

Also,

\[
R(p,0)-\frac p2
=
\frac{p^2-3p}{6}\le0.
\]

If \(p\ge3\), the constant vector \(z_e=1/3\) is feasible. Summing all triangle constraints gives

\[
(p-2)\sum_{e\in E(K)}z_e
\ge
\binom p3.
\]

Thus

\[
M(0)
\ge
\frac1{p-2}\binom p3
=
\frac{p(p-1)}6.
\]

The constant vector attains equality, so

\[
M(0)=\frac{p(p-1)}6.
\]

Finally,

\[
M(0)-R(p,0)
=
-\frac p6
\ge
-\frac p2.
\]

Hence (L55) holds for \(q=0\) as well.

---

## 10. Insert the quantitative bound into the deficit

Start from (L28):

\[
|E(G)|-2V_{\mathrm{com}}
=
\binom p2-2M(\kappa)+b_1.
\]

Use (L55):

\[
M(\kappa)\ge R(p,q)-\frac p2.
\]

Multiplication by \(-2\) reverses the inequality:

\[
-2M(\kappa)
\le
-2R(p,q)+p.
\tag{L56}
\]

Therefore

\[
|E(G)|-2V_{\mathrm{com}}
\le
\binom p2-2R(p,q)+p+b_1.
\tag{L57}
\]

Now expand:

\[
\begin{aligned}
\binom p2-2R(p,q)+p
&=
\frac{p(p-1)}2
-
\frac{2p^2-2pq-q^2}{6}
+p\\
&=
\frac{3p^2-3p-2p^2+2pq+q^2+6p}{6}\\
&=
\frac{p^2+2pq+q^2+3p}{6}\\
&=
\frac{(p+q)^2}{6}+\frac p2.
\end{aligned}
\tag{L58}
\]

Substitute (L58) into (L57):

\[
\boxed{
|E(G)|-2V_{\mathrm{com}}
\le
\frac{(p+q)^2}{6}+\frac p2+b_1.
}
\tag{L59}
\]

---

## 11. Convert to the total vertex count

From (L2),

\[
n=p+q+b_1+|I_0|.
\]

All terms are nonnegative. Hence

\[
p+q\le n,
\]

so

\[
\frac{(p+q)^2}{6}\le\frac{n^2}{6}.
\tag{L60}
\]

Also,

\[
\frac p2+b_1
\le
p+b_1
\le
n.
\tag{L61}
\]

Apply (L60) and (L61) to (L59):

\[
\boxed{
|E(G)|-2V_{\mathrm{com}}
\le
\frac{n^2}{6}+n.
}
\tag{L62}
\]

Finally, by (L27),

\[
V_{\mathrm{com}}\le\nu_3^*(G).
\]

Multiplication by \(-2\) gives

\[
-2\nu_3^*(G)\le-2V_{\mathrm{com}}.
\]

Therefore

\[
\begin{aligned}
|E(G)|-2\nu_3^*(G)
&\le
|E(G)|-2V_{\mathrm{com}}\\
&\le
\frac{n^2}{6}+n.
\end{aligned}
\]

Thus

\[
\boxed{
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}+n.
}
\tag{L63}
\]

---

## 12. Loss ledger

| Step | Exact or lossy? | Quantity introduced | Charged how many times? |
|---|---|---:|---:|
| Edge decomposition (L1) | Exact | none | 0 |
| Aggregate-load identity (L4) | Exact | none | 0 |
| Phase-I value (L10) | Exact | none | 0 |
| Phase-II dual reduction | Exact | none | 0 |
| Combined value (L25) | Exact | none | 0 |
| Deficit identity (L28) | Exact | none | 0 |
| Pure-profile reduction (L34) | Inequality, no additive loss | minimum over pure profiles | once |
| Quantitative envelope (L55) | Additive allowance | \(p/2\) | once |
| Replace \(p+q\) by \(n\) | Monotonic enlargement | quadratic term | once |
| Bound \(p/2+b_1\) by \(n\) | Additive allowance | \(p/2+b_1\) | once |
| Replace \(V_{\mathrm{com}}\) by \(\nu_3^*(G)\) | Optimum comparison | none | once |

There is no asymptotic error, no exceptional-set loss, no parity loss, no divisibility loss, and no numerical tolerance.

---

## 13. Dependency ledger

| Calculation block | Authoritative dependency |
|---|---|
| (L1)–(L4) | `ERDOZ81-P1-DEF-01`, `ERDOZ81-P1-LOAD-01` |
| (L5)–(L10) | `ERDOZ81-P1-PHASE1-01` |
| (L11)–(L22) | Schrijver [4, Corollary 7.1g], hypothesis-checked and applied in Appendix B through `ERDOZ81-P1-LP-DUALITY-01`; `ERDOZ81-P1-PHASE2-DUAL-01` |
| (L23)–(L28) | `ERDOZ81-P1-FRAC-THM-01` |
| (L29)–(L34) | `ERDOZ81-P1-CONCAVE-01`, `ERDOZ81-P1-PROFILE-01` |
| (L35)–(L45) | `ERDOZ81-P1-SYMMETRY-01`, `ERDOZ81-P1-3ORBIT-01`, `ERDOZ81-P1-3ORBIT-SOLVE-01` |
| (L46)–(L55) | `ERDOZ81-P1-Q0-01`, `ERDOZ81-P1-BOUND-01` |
| (L56)–(L63) | `ERDOZ81-P1-FRAC-THM-01`, `ERDOZ81-P1-ASSEMBLY-01` |

---


## 14. Correspondence with the paper

The following table records the principal equation-level correspondences between this ledger and `PAPER_I_preprint_v1.0`.

| Ledger | Paper | Role |
|---|---|---|
| (L1) | (2.1) | Exact edge decomposition |
| (L25) | (4.7) | Exact value of the combined packing |
| (L28) | (4.9) | Exact deficit identity |
| (L34) | (5.4) | Affine reduction to pure profiles |
| (L45) | (6.5) | Exact pure-profile orbit optimum |
| (L46) | (7.1) | Definition of the quadratic benchmark |
| (L55) | (7.8) | Uniform residual-cover lower bound |
| (L58) | (8.2) | Algebraic conversion to \((p+q)^2/6+p/2\) |
| (L62) | (8.4) | Final bound for the constructed packing |

Equation (L63) is the final theorem after replacing \(V_{\mathrm{com}}\) by \(\nu_3^*(G)\).

---

## 15. Scope boundary

This ledger certifies the finite fractional theorem only. Its proof uses one imported proof-critical result: finite-dimensional strong linear-programming duality, cited in Appendix B as Schrijver [4, Corollary 7.1g]. Appendix B verifies its applicability to the finite residual packing-covering pair. It does not establish:

- an integral triangle-packing theorem;
- a clique-partition theorem;
- an asymptotic transfer via an external result;
- a theorem for all chordal graphs;
- a theorem for general graphs;
- novelty or priority.

Those require separate gates and, where applicable, verified external-theorem certificates. No asymptotic transfer theorem or external graph-theoretic theorem is used in the proof certified here.

---

## 16. Release binding and editorial context

This ledger is bound to the official manuscript `PAPER_I_preprint_v1.0`.

| Release artifact | SHA-256 |
|---|---|
| `PAPER_I_preprint_v1.0.md` | `02763e8c1aa7df086e6748f403160989a8efd716ebd9779b78c4ace93f2dab69` |
| `PAPER_I_preprint_v1.0.tex` | `af56b0471e10da95c690e5672851135cd095df7e9ae2a29509d0eaacda1f7c5b` |
| `PAPER_I_preprint_v1.0.pdf` | `661ac1a73b77dc8579d6d136cccf83d57a07a63573ce61161eb890d7b12837a3` |

The manuscript contains two contextual additions and two dependency-clarification edits:

1. a paragraph at the end of the Introduction explaining the paper's methodological role within a broader program on Erdős Problem #81;
2. a closing sentence in the Discussion emphasizing that the reduction mechanism is independent of the particular finite bound proved here;
3. a qualification that the paper is self-contained apart from the standard finite-dimensional strong linear-programming duality theorem cited and applied in Appendix B;
4. a revised opening sentence in Appendix B describing the specialized dual pair, weak-duality argument, hypothesis verification, and application of the cited strong-duality theorem.

The dependency descriptions in §0, §13, and §15 have been reconciled with Appendix B. These wording changes introduce no new theorem, lemma, assumption, formula, numerical constant, asymptotic claim, inequality direction, or proof step. Equations (L1)–(L63), the loss ledger, and the mathematical derivation certified above are unchanged.
