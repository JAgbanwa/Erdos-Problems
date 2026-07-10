# Paper II — Calculation Ledger (definitive), self-contained fractional theorem

**Formalization status (v1.1).** The target theorem below is **formally verified in Lean 4 / Mathlib v4.28.0**, unconditionally on the standard chordal definition, as `PaperII.theorem_1_2` (commit `5f2d448`): `sorry`-free, axiom footprint `[propext, Classical.choice, Quot.sound]`. In the formalization the chordal facts A1–A3 (Part A) are **derived from the definition `IsChordal`** and A4 (clique tree) is **not used** — the terminal characterization L7 is formalized by a clique-tree-free argument. This ledger's paper-level proof still uses A1–A4 as textbook facts (a valid, self-contained mathematical route); the note is recorded so the two developments are mutually consistent. See "Verification status" in Part D.

**Target theorem (Theorem 1.2, the *only* claim of Paper II):**
> For every integer `n ≥ 1`,
> $$\max_{\substack{|V(G)|=n\\ G\ \text{chordal}}}\ \bigl(|E(G)|-2\tau_3^*(G)\bigr)\ =\ \left\lfloor\frac{(2n+1)^2}{24}\right\rfloor .$$

**Scope of this ledger.** This document reconstructs, line by line, the proof of the exact
fractional extremum only. It is **self-contained**: it uses only elementary counting, finite
linear programming of the cover LP, and four textbook facts about chordal graphs. It does **not**
use Haxell–Rödl, LP strong duality, integral packings, or clique partitions `cp(G)`. (Those belong
to the separate asymptotic-`cp` paper.) Every step below is either a *definition* (D), an
*admitted external fact* (A), or a *derived step* (L) with its full calculation.

Reading convention: `n := |V(G)|`, `e(G) := |E(G)|`, `P := C(p,2) = p(p−1)/2`.

---

## Cross-reference to Paper II preprint (v0.5, formalization-aligned) — "Complete-Split Extremizers…"

This ledger is the calculation companion to the preprint. **No formula differs between the two**
(verified line by line). The step labels below map to the preprint's numbered statements:

| Ledger step | Preprint statement |
|---|---|
| Target theorem | **Theorem 1.1** |
| L1 (vertex-copy inequality) | **Lemma 3.1** |
| L2 (convexity lift) | **Lemma 4.1** |
| L3 (no clone class splits) | **Lemma 4.2** |
| L4 (simplicial-target chordality) | **Lemma 4.3** |
| L7 (terminal characterization) | **Lemma 5.1** |
| L5 (both-simplicial pair exists) | **Corollary 5.2** |
| L6 (symmetrization reduction) | **Theorem 5.3** |
| L8 (orbit averaging) | **Lemma 6.1** |
| L9 (terminal cover value `τ₃*`) | **Proposition 6.2** |
| L10 (`Φ_τ` of complete-split) | **Corollary 6.3** |
| L11 (integer maximization) | **Proposition 7.1** |
| L12 (assembly) | **Proof of Theorem 1.1** |

**Ordering note (follow the preprint).** The preprint proves the terminal characterization
(**Lemma 5.1** = ledger L7) **first**, then obtains the both-simplicial pair as its contrapositive
(**Corollary 5.2** = ledger L5), then the symmetrization (**Theorem 5.3** = ledger L6). This removes
the forward reference present in the L5→L7 order below; an editor should present §5 in the order
**5.1 → 5.2 → 5.3**. All calculations are otherwise unchanged.

---

## Part 0 — Definitions

**D1 (triangle).** A triangle is a set of three pairwise-adjacent vertices. `T(G)` is the set of
triangles of `G`.

**D2 (fractional triangle cover).** A function `z : E(G) → ℝ_{≥0}` with, for every triangle
`T ∈ T(G)`,
$$\sum_{e\in E(T)} z_e \ \ge\ 1 .$$
Its cost is `Σ_{e} z_e`. The cover number is
$$\tau_3^*(G) := \min\{\ \textstyle\sum_e z_e \ :\ z\ \text{a fractional triangle cover}\ \}.$$
The minimum is attained (finite LP, feasible since `z≡1` works when triangles exist, bounded below
by `0`). If `T(G)=∅` then, by convention, `τ_3^*(G)=0`.

**D3 (deficit functional).** `Φ_τ(G) := e(G) − 2 τ_3^*(G)`.

**D4 (complete-split graph).** `S_{p,q} := K_p ∨ \overline{K_q}`: a clique side `K` with `|K|=p`, an
independent side `I` with `|I|=q`, and every one of the `pq` edges between `K` and `I` present.

**D5 (clone class).** Vertices `u,v` are open-neighborhood clones if `N_G(u)=N_G(v)` (this forces
`u,v` nonadjacent). A clone class is a maximal set of pairwise clones. `m(G)` denotes the number of
maximal clone classes.

**D6 (simplicial).** A vertex `v` is simplicial if `N_G(v)` induces a clique. A clone class is
simplicial if its vertices are simplicial (equivalently, its common neighborhood is a clique).

**D7 (copy operation).** For nonadjacent `u,v`, the graph `G_{v→u}` is obtained by deleting every
edge incident with `v` and then joining `v` to every vertex of `N_G(u)`. Thus, in `G_{v→u}`,
`N(v)=N(u)` and `u,v` are clones.

---

## Part A — Admitted textbook facts about chordal graphs

*(Formalization note: in the Lean development A1–A3 are **proved** from the standard definition `IsChordal` — A3 via a formalized Dirac theorem that every minimal vertex separator of a chordal graph is a clique — and A4 is **eliminated** (L7 is done clique-tree-free). At the paper level they remain standard textbook facts [2,3], used here for a self-contained exposition.)*

**A1.** Every induced subgraph of a chordal graph is chordal.
**A2.** Adding a new vertex whose neighborhood is a clique preserves chordality.
**A3.** Every nonempty chordal graph has a simplicial vertex; every noncomplete connected chordal
graph has at least two nonadjacent simplicial vertices.
**A4 (clique tree).** Every connected chordal graph has a tree whose nodes are its maximal cliques
such that, for each vertex `x`, the maximal cliques containing `x` induce a connected subtree
(running-intersection property).

We also use two elementary tree facts inside L7:
**A5.** A tree with ≥ 2 nodes has ≥ 2 leaves.
**A6.** In a tree, a connected subtree that contains every leaf is the whole tree (every internal
node lies on a path between two leaves).

---

## Part L — Derived steps

### L1 — Vertex-copy inequality
**Claim.** For nonadjacent `u,v`:
$$\Phi_\tau(G_{v\to u})+\Phi_\tau(G_{u\to v})\ \ge\ 2\,\Phi_\tau(G).$$

**Calculation.**
Let `z` be an optimal cover of `G`, so `Σ_e z_e = τ_3^*(G)`.

*(i) Construct a cover `z'` of `G_{v→u}`.* Set
- `z'_e := z_e` for every edge `e` not incident with `v`;
- `z'_{vx} := z_{ux}` for every `x ∈ N_G(u)` (these are exactly the edges incident with `v` in
  `G_{v→u}`).

*(ii) `z'` is feasible.* Every triangle of `G_{v→u}` is one of two kinds.
- A triangle not containing `v`: its three edges are non-`v` edges, hence edges of `G` with
  unchanged weights, so its cover sum is `≥ 1` because `z` was feasible.
- A triangle `vxy`: then `x,y ∈ N_G(u)` and `xy ∈ E(G)`, so `uxy` is a triangle of `G`, and
  $$z'_{vx}+z'_{vy}+z'_{xy}=z_{ux}+z_{uy}+z_{xy}\ \ge\ 1$$
  (feasibility of `z` on the triangle `uxy`; note `xy` is a non-`v` edge so `z'_{xy}=z_{xy}`).

*(iii) Cost of `z'`.* Splitting `Σ z'` into non-`v` edges and `v`-edges,
$$\operatorname{cost}(z') \;=\; \Bigl(\textstyle\sum_e z_e-\sum_{x\in N_G(v)} z_{vx}\Bigr) \;+\; \sum_{x\in N_G(u)} z_{ux}.$$

*(iv) Symmetric cover `z''` of `G_{u→v}`* (swap the roles of `u,v`):
$$\operatorname{cost}(z'') \;=\; \Bigl(\textstyle\sum_e z_e-\sum_{x\in N_G(u)} z_{ux}\Bigr) \;+\; \sum_{x\in N_G(v)} z_{vx}.$$

*(v) Add (iii) and (iv).* The two correction sums cancel exactly:
$$\operatorname{cost}(z')+\operatorname{cost}(z'') \;=\; 2\textstyle\sum_e z_e \;=\; 2\,\tau_3^*(G).$$
Since `τ_3^*` is a minimum, `τ_3^*(G_{v→u}) ≤ cost(z')` and `τ_3^*(G_{u→v}) ≤ cost(z'')`, hence
$$\tau_3^*(G_{v\to u})+\tau_3^*(G_{u\to v})\ \le\ 2\,\tau_3^*(G). \tag{L1-cover}$$

*(vi) Edge counts (exact identity).* `G_{v→u}` replaces `deg_G(v)` by `deg_G(u)` and changes no
other edge, so `e(G_{v→u}) = e(G) − deg_G(v) + deg_G(u)`. Symmetrically
`e(G_{u→v}) = e(G) − deg_G(u) + deg_G(v)`. Adding,
$$e(G_{v\to u})+e(G_{u\to v})\ =\ 2\,e(G). \tag{L1-edges}$$

*(vii) Combine.* Using `Φ_τ = e − 2τ_3^*` and subtracting `2×`(L1-cover) from (L1-edges):
$$\Phi_\tau(G_{v\to u})+\Phi_\tau(G_{u\to v})
= \underbrace{2e(G)}_{\text{(L1-edges)}} - 2\bigl(\tau_3^*(G_{v\to u})+\tau_3^*(G_{u\to v})\bigr)
\ \ge\ 2e(G)-4\tau_3^*(G)=2\Phi_\tau(G).\ \square$$

**Corollary L1′.** At least one of `Φ_τ(G_{v→u}), Φ_τ(G_{u→v})` is `≥ Φ_τ(G)`.
*(A sum of two numbers is `≥ 2A` ⇒ the larger is `≥ A`.)*

> No bound such as `z_e ≤ 1` is used anywhere in L1.

---

### L2 — Lift to a full clone-class copy (discrete convexity)
**Setup.** Let `U,V` be distinct nonadjacent clone classes, `|U|=a`, `|V|=b`. Outside `U∪V` the
graph is fixed. For `0 ≤ k ≤ a+b`, let `H_k` be the graph in which `k` of the `a+b` vertices carry
neighborhood-type `N(U)` and the other `a+b−k` carry `N(V)` (all `a+b` vertices pairwise
nonadjacent). Up to isomorphism `H_a = G`, `H_0 = G_{U→V}`, `H_{a+b}=G_{V→U}`.

**Claim.** With `f(k):=Φ_τ(H_k)`,
$$f(k-1)+f(k+1)\ \ge\ 2 f(k)\quad(1\le k\le a+b-1),\qquad\text{hence}\qquad f(a)\ \le\ \max\{f(0),f(a+b)\}.$$

**Calculation.**
Fix `k` with `1 ≤ k ≤ a+b−1`, so `H_k` has at least one type-`U` vertex `x` and one type-`V`
vertex `y`; they are nonadjacent. Applying D7 inside `H_k`:
- `(H_k)_{x→y}` turns `x` into a type-`V` vertex, giving a graph isomorphic to `H_{k−1}`;
- `(H_k)_{y→x}` turns `y` into a type-`U` vertex, giving a graph isomorphic to `H_{k+1}`.
By L1 applied to `H_k` with the pair `x,y` (and isomorphism-invariance of `Φ_τ`):
$$f(k-1)+f(k+1)=\Phi_\tau((H_k)_{x\to y})+\Phi_\tau((H_k)_{y\to x})\ \ge\ 2\Phi_\tau(H_k)=2f(k).$$
The inequality says the first differences `d(k):=f(k)−f(k−1)` are nondecreasing. A finite sequence
with nondecreasing differences attains its maximum over `{0,…,a+b}` at an endpoint (the differences
change sign at most once, so `f` decreases then increases). Hence `f(a) ≤ max{f(0),f(a+b)}`. `□`

**Consequence.** One of the two full-class copies `G_{U→V}=H_0`, `G_{V→U}=H_{a+b}` has
`Φ_τ ≥ Φ_τ(G)=f(a)`.

---

### L3 — No clone class splits (progress bookkeeping)
**Setup.** Copy source class `W₁` onto target class `W₂` (`{W₁,W₂}` a nonadjacent clone pair); write
`B := N(W₂)`, so in `G'` every vertex of `W₁` has neighborhood `B`.

**Claim.** (i) Every vertex of `W₁∪W₂` has neighborhood `B` in `G'`; they form one clone class.
(ii) For every clone class `C` of `G` disjoint from `W₁∪W₂` and all `c,c' ∈ C`,
`N_{G'}(c)=N_{G'}(c')`. Hence `m(G') < m(G)`.

**Calculation.**
(i) `W₂` is untouched (keeps `B`); `W₁` is reassigned `B`. Since classes are nonadjacent and
internally independent, `B ∩ (W₁∪W₂)=∅`, so no two of these vertices are adjacent: they are pairwise
clones with neighborhood `B`.

(ii) The copy changes only edges incident with `W₁`. Fix `c ∉ W₁∪W₂`.
- *Coordinates off `W₁`:* for `w ∉ W₁`, the edge `cw` is unchanged, so
  `N_{G'}(c)∖W₁ = N_G(c)∖W₁`; as `N_G(c)=N_G(c')`, these agree for `c,c'`.
- *Coordinates in `W₁`:* every `w ∈ W₁` now has neighborhood `B`, so `c` is adjacent to `w` in `G'`
  iff `c ∈ B`, the same answer for all `w ∈ W₁`. Pick any `v ∈ W₂`: then
  `c ∈ B = N_G(v) ⇔ v ∈ N_G(c) ⇔ v ∈ N_G(c') ⇔ c' ∈ B`. So `N_{G'}(c)∩W₁ = N_{G'}(c')∩W₁`.
Both blocks agree ⇒ `N_{G'}(c)=N_{G'}(c')`. Finally the map (old class → the new class containing it)
is well defined and surjective, and it sends the two distinct classes `W₁,W₂` to a single class, so
`m` strictly drops. `□`

---

### L4 — Copying toward a simplicial target preserves chordality
**Claim.** If `G` is chordal and the *target* class `W₂` is simplicial, then `G' = ` (copy `W₁` onto
`W₂`) is chordal.

**Calculation.** Delete the vertices of `W₁`: the remainder is an induced subgraph of `G`, hence
chordal (A1). Reinsert the vertices of `W₁` one at a time, each with neighborhood `B = N(W₂)`. Since
`W₂` is simplicial, `B` is a clique; and `B ∩ W₁ = ∅` (nonadjacent classes), so previously reinserted
vertices never lie in a later neighborhood. Each insertion adds a vertex whose neighborhood is a
clique, preserving chordality (A2). `□`

---

### L5 — A both-simplicial admissible pair exists at every non-terminal graph
**Claim.** If a chordal `G` is **not** complete-split, there exist clone classes `U,V` that are
distinct, nonadjacent, **both simplicial**, with `N(U) ≠ N(V)`.

**Calculation.** By the terminal characterization L7 (contrapositive): since `G` is not
complete-split, there are two nonadjacent **simplicial** vertices `x,y` with `N(x) ≠ N(y)`. Let
`U,V` be their clone classes.
- `U` is simplicial: `N(x)` is a clique and every `x' ∈ U` has `N(x')=N(x)`. Likewise `V`.
- `U ≠ V` because `N(x) ≠ N(y)`.
- `U,V` nonadjacent: if `u ∈ U` were adjacent to `w ∈ V`, then `w ∈ N(u)=N(x)`, so `x ∈ N(w)=N(y)`,
  i.e. `x,y` adjacent — contradiction. `□`

*(No circularity: L7 is proved from A1–A6 only, with no reference to the copy process.)*

---

### L6 — Symmetrization: every chordal `G` reduces to a complete-split with `Φ_τ` nondecreasing
**Definition (admissible copy).** A copy of one class of a pair `(U,V)` of distinct, nonadjacent,
**both-simplicial** clone classes with `N(U) ≠ N(V)`, performed in the direction supplied by L2 (the
one that does not decrease `Φ_τ`).

**Claim (Theorem 5.2).** For every chordal `G` on `n` vertices there are `p,q ≥ 0`, `p+q=n`, with
$$\Phi_\tau(G)\ \le\ \Phi_\tau(S_{p,q}).$$

**Calculation.** Iterate admissible copies:
1. *A move exists while non-terminal.* If the current chordal graph is not complete-split, L5 gives a
   pair `(U,V)`, distinct, nonadjacent, both simplicial, `N(U)≠N(V)`.
2. *The chosen direction is legal.* L2 designates a `Φ_τ`-nondecreasing direction, say copy `W₁` onto
   `W₂` with `{W₁,W₂}={U,V}`. Because **both** classes are simplicial, the target `W₂` is simplicial
   either way, so L4 makes `G'` chordal. *(This is exactly the point that needs "both simplicial";
   with only one simplicial class the nondecreasing direction of L2 might target the non-simplicial
   one and break chordality.)*
3. *Progress.* By L3 the two classes merge and no other class splits, so `m` drops by at least `1`.
4. *Termination and terminal shape.* `m` is a positive integer strictly decreasing, so the process
   halts after finitely many steps. It halts exactly when no admissible pair exists, i.e. when every
   two nonadjacent simplicial vertices have equal neighborhoods; by L7 the graph is then
   complete-split `S_{p,q}` (with `n` vertices, since a copy never changes the vertex set).
Along the way `Φ_τ` never decreases, so `Φ_τ(G) ≤ Φ_τ(S_{p,q})`. `□`

> **Correction incorporated.** The stopping condition is "**complete-split**" (no admissible pair),
> *not* "complete"; and the legality of the chosen direction rests on the both-simplicial pair L5.

---

### L7 — Terminal characterization
**Claim (Lemma 5.1).** If a finite chordal `H` has the property
> (H): every two nonadjacent simplicial vertices have equal open neighborhoods,

then `H` is complete-split.

**Calculation.**
*Degenerate/disconnected.* If `|V(H)| ≤ 1`, done. If `H` is disconnected with an edge in one
component and another nonempty component, pick a simplicial vertex `z` **with a neighbor** in the
first component and a simplicial vertex `w` in another (A3, applied per component, which is chordal
by A1). Then `z,w` are nonadjacent simplicial, so (H) forces `N(z)=N(w)`; but their neighborhoods lie
in disjoint components, hence both empty — contradicting that `z` has a neighbor. So a disconnected
`H` with (H) is edgeless, i.e. `H=K_0∨\overline{K_n}`. If `H` is complete, `H=K_p∨\overline{K_0}`.

*Connected, noncomplete.* Take a clique tree (A4). It has ≥ 2 nodes, hence ≥ 2 leaves (A5). A leaf
clique `L` has a **private vertex** (one in no other maximal clique); it is simplicial and its
neighborhood is `L` minus itself.
- *Private vertices of distinct leaves are nonadjacent.* If `x` (private to `L₁`) were adjacent to
  `y` (private to `L₂ ≠ L₁`), then `{x,y}` lies in a common maximal clique, which for `x` can only be
  `L₁`; so `y ∈ L₁`, contradicting that `y` is private to `L₂`.
- *A common neighborhood `K`.* By (H), all leaf private vertices `x_i` share one neighborhood
  `K := N(x_i) = L_i∖{x_i}`. Thus `K ⊆ L_i` for every leaf, and each leaf is `K∪{x_i}` (a leaf has
  exactly one private vertex: two would be adjacent and both in `K=N(x_j)`, forcing `x_j` adjacent to
  a private vertex of another leaf — impossible by the previous bullet).
- *`K` is universal.* Fix `v ∈ K`. Then `v` is in every leaf, so the subtree of maximal cliques
  containing `v` (connected, by A4) meets every leaf, hence equals the whole tree (A6). Thus `v` lies
  in every maximal clique and is adjacent to all other vertices. As `v ∈ K` was arbitrary, `K` is a
  clique of universal vertices.
- *The rest is independent.* If `H−K` had an edge, a nontrivial component of `H−K` (chordal, A1) has
  a simplicial vertex `z` with a neighbor inside it. Since `K` is universal, `N_H(z)=N_{H−K}(z)∪K`, a
  union of two cliques with all cross-edges present, hence a clique — so `z` is simplicial in `H` with
  `N_H(z) ⊋ K`. Taking any leaf private vertex `x` (with `N_H(x)=K`, and `z ∉ K` so `z,x`
  nonadjacent), (H) forces `N_H(z)=K`, a contradiction. Hence `H−K` is independent.
Therefore `V(H)=K ⊔ (H−K)` with `K` a universal clique, `H−K` independent, all cross edges present:
`H = K_{|K|} ∨ \overline{K_{|H−K|}}`. `□`

---

### L8 — Orbit averaging on the terminal graph
**Claim (Lemma 6.1).** `S_{p,q}` has an optimal fractional cover that is constant on each of the two
edge orbits of `Aut(S_{p,q}) ≅ 𝔖_p × 𝔖_q`: the `P` clique edges and the `pq` radial edges.

**Calculation.** For a feasible cover `z` and `σ ∈ Aut`, define `z^σ_e := z_{σ^{-1}(e)}`. Each `z^σ`
is feasible (automorphisms permute triangles among themselves) with the same cost. The average
`\bar z := |Aut|^{-1} Σ_σ z^σ` is feasible (feasible region convex), has the same cost, and is
`Aut`-invariant, hence constant on each edge orbit. `□`

Write `x` = common weight on a clique edge, `y` = common weight on a radial edge. Triangle orbits:
- three clique vertices (exists iff `p ≥ 3`): constraint `3x ≥ 1`;
- two clique + one independent (exists iff `p ≥ 2` and `q ≥ 1`): constraint `x + 2y ≥ 1`.
The symmetrized LP is `min{ Px + pq·y : x,y ≥ 0 }` with each constraint present only when its orbit
exists.

---

### L9 — Exact terminal cover value
**Claim (Prop 6.2).**
$$\tau_3^*(S_{p,q})=0\quad(p\le1),\qquad \tau_3^*(S_{2,0})=0,$$
and otherwise
$$\tau_3^*(S_{p,q})=\begin{cases}\dfrac{P+pq}{3}, & p\ge3,\ 0\le q\le p-1,\\[2mm] P, & p\ge2,\ q\ge p-1.\end{cases}$$

**Calculation.**
- *No triangles:* `p ≤ 1` (no clique triangle, no radial-based triangle) and `S_{2,0}=K_2` give
  `T(G)=∅`, hence `τ_3^*=0` by convention (D2).
- *`p ≥ 3, q = 0`:* only `3x ≥ 1`; minimize `Px` ⇒ `x=1/3`, value `P/3 = (P+p·0)/3`. (First branch.)
- *`p ≥ 3, q ≥ 1`:* both constraints. For `1/3 ≤ x ≤ 1` the least feasible `y` is `y=(1−x)/2`, so the
  objective is
  $$Px+pq\cdot\frac{1-x}{2}=\frac{pq}{2}+x\Bigl(P-\frac{pq}{2}\Bigr),\qquad P-\frac{pq}{2}=\frac p2\,(p-1-q).$$
  - If `q ≤ p−1` the coefficient `≥ 0`: minimum at `x=y=1/3`, value `(P+pq)/3`.
  - If `q ≥ p−1` the coefficient `≤ 0`: minimum at `x=1, y=0`, value `P`.
- *`p = 2, q ≥ 1`:* no all-clique triangle, only `x+2y ≥ 1`, and `P=1`. Objective `x+2q·y`; since
  `q ≥ 1`, minimum at `x=1,y=0`, value `1 = P`. (Second branch.)
- At `p ≥ 3, q=p−1` both formulas give `(P+p(p−1))/3 = P` after using `P=p(p−1)/2`: agree. `□`

---

### L10 — `Φ_τ` of the complete-split (from L9)
Using `Φ_τ(S_{p,q}) = P + pq − 2τ_3^*` and `n=p+q`:
- **Saturated branch `q ≥ p−1`:**
  $$\Phi_\tau(S_{p,q})=P+pq-2P=pq-P=\frac{p(2n+1-3p)}{2}=:F_n(p).$$
  *(Check: `pq−P = p(n−p) − p(p−1)/2 = pn − p² − p²/2 + p/2 = p(2n−3p+1)/2`.)*
- **Nonsaturated branch `q ≤ p−1` (`p ≥ 3`):**
  $$\Phi_\tau(S_{p,q})=P+pq-\tfrac23(P+pq)=\frac{P+pq}{3}=\frac{p(2n-p-1)}{6}.$$
  *(Check: `(P+pq)/3 = (p(p−1)/2 + p(n−p))/3 = p(p−1+2n−2p)/6 = p(2n−p−1)/6`.)*
- Degenerate `p ≤ 1` and `(2,0)`: `Φ_τ = e(G)` (since `τ_3^*=0`), read off directly (`≤ 1`).

---

### L11 — Integer maximization over `p`
**Claim (Prop 6.3).** For integers `p,q ≥ 0`, `p+q=n`:
$$\Phi_\tau(S_{p,q})\ \le\ \left\lfloor\frac{(2n+1)^2}{24}\right\rfloor,$$
with equality attained in the saturated branch at an integer `p` nearest `(2n+1)/6`.

**Calculation.**
*Saturated branch — complete the square.*
$$F_n(p)=\frac{p(2n+1-3p)}{2}=\frac{(2n+1)^2}{24}-\frac32\Bigl(p-\frac{2n+1}{6}\Bigr)^2.$$
*(Verification: `(3/2)(p−(2n+1)/6)² = (3/2)p² − p(2n+1)/2 + (2n+1)²/24`; subtract from `(2n+1)²/24`
to get `p(2n+1)/2 − (3/2)p² = p(2n+1−3p)/2 = F_n(p)`.)*
Since `F_n(p)` is an integer for integer `p`, and the maximum of the parabola is `(2n+1)²/24`, we get
`F_n(p) ≤ ⌊(2n+1)²/24⌋`. Achievability: write `2n+1 = 6k+r`, `r ∈ {1,3,5}`.
- `r=1`: take `p=k`; squared distance `(1/6)²`; `F_n(k)=((2n+1)²−1)/24`.
- `r=3`: take `p=k` or `k+1`; squared distance `(1/2)²`; `F_n=((2n+1)²−9)/24`.
- `r=5`: take `p=k+1`; squared distance `(1/6)²`; `F_n=((2n+1)²−1)/24`.
An odd square is `≡ 1 (mod 24)` unless divisible by `3`, in which case `≡ 9 (mod 24)`; so these values
equal `⌊(2n+1)²/24⌋` exactly. The chosen `p` satisfies `p ≤ (n+1)/2`, i.e. `q ≥ p−1`, so it lies in
the saturated branch. This proves both the upper bound (for this branch) and attainment.

*Nonsaturated branch never exceeds it.* Here `p ≥ (n+1)/2` and
`Φ_τ = p(2n−p−1)/6`. The numerator `p(2n−p−1)` is concave in `p` with vertex at `p=n−1/2`; over
integers `p ∈ [⌈(n+1)/2⌉, n]` its maximum is at `p=n−1` or `p=n`, both giving `n(n−1)`. Hence
`Φ_τ ≤ n(n−1)/6`. Finally
$$\frac{(2n+1)^2}{24}-\frac{n(n-1)}{6}=\frac{(2n+1)^2-4n(n-1)}{24}=\frac{4n^2+4n+1-4n^2+4n}{24}=\frac{8n+1}{24}\ >\ 1\quad(n\ge3),$$
so `n(n−1)/6 ≤ ⌊(2n+1)²/24⌋`. Cases `n ≤ 2` (incl. `S_{2,0}`) by inspection. `□`

---

### L12 — Assembly of Theorem 1.2
**Upper bound.** For any chordal `G` on `n` vertices, L6 gives a complete-split `S_{p,q}` (`p+q=n`)
with `Φ_τ(G) ≤ Φ_τ(S_{p,q})`, and L11 gives `Φ_τ(S_{p,q}) ≤ ⌊(2n+1)²/24⌋`. Hence
$$\max_{\text{chordal},\,|V|=n}\Phi_\tau\ \le\ \left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.$$
**Attainment (equality).** Take `p` = integer nearest `(2n+1)/6`, `q=n−p`. By L11 (achievability),
`S_{p,q}` is chordal (it is complete-split, hence chordal) and `Φ_τ(S_{p,q}) = ⌊(2n+1)²/24⌋`.
Therefore the maximum equals `⌊(2n+1)²/24⌋`. This is Theorem 1.2. `∎`

---

## Part D — Dependency summary and status

**What Theorem 1.2 uses (and nothing else):**
1. Elementary counting and the cover LP (D2, L1, L8, L9, L10, L11).
2. Discrete convexity of a real sequence (L2).
3. Chordal facts A1–A4 (and elementary tree facts A5–A6).
*No LP strong duality, no `ν_3^*`, no Haxell–Rödl, no `cp` — this theorem is purely about `τ_3^*`.*

**Verification status (for the editor's record):**
- **Formal (Lean 4 / Mathlib v4.28.0):** the target theorem is machine-checked as `PaperII.theorem_1_2` (commit `5f2d448`), unconditional on `IsChordal`, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`. All of L1–L12 are covered by the formalized reduction; A1–A3 are derived and A4 is not used (clique-tree-free L7).
- L1 (vertex-copy): proof complete; also checked on `3517` random graphs (`n≤6`), `0` violations.
- L2, L3, L4, L8, L10: elementary, complete.
- L5 + L6 (symmetrization with the both-simplicial fix) + L7 (terminal): proof complete; the
  reduction was exhaustively checked on all chordal graphs `n ≤ 5` (`0` violations of chordality,
  monotonicity, or strict decrease).
- L9, L11: proof complete; `τ_3^*(S_{p,q})` reproduced by LP (`p ≤ 6`); the integer maximum
  `= ⌊(2n+1)²/24⌋` reproduced for `n ≤ 3000`; the `(2,0)` degenerate is handled explicitly in L9.

**Open items (do not affect Theorem 1.2):** none. The passage to `cp(G)` and Erdős #81 (which needs
Haxell–Rödl and an open `O(n)` transfer) is **out of scope** here and belongs to a separate paper.

**Honest caveats before submission:** (a) the reduction (L1, L5–L7) is now machine-checked in Le