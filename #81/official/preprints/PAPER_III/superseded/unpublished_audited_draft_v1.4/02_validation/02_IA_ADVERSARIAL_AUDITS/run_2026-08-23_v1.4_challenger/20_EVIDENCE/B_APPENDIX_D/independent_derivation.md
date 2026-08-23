# EXT-V14-M02 — independent derivation of Appendix D

Challenger run 2026-08-23. This document was produced by working through Appendix D from its
own definitions before opening the author-side ledger at
`01_INTERNAL_AUDITS/run_2026-08-22_v1.4_editorial_residual/20_EVIDENCE/M02_APPENDIX_D/`.
The comparison with that ledger is recorded in the final section, after the derivation.

The object of the audit is whether Appendix D **proves** the statement Section 2.4 says it
proves, with no circularity, no unproved external ingredient, and no gap that would leave
Theorem 1.1 depending on Galvin's theorem [10] as a black box.

---

## Check 1 — Lemma D.1: preservation and termination

**Statement.** `D` kernel-perfect, every vertex `v` carrying `|L(v)| >= d+_D(v) + 1`. Then the
underlying graph of `D` has a proper colouring with each colour drawn from its list.

**Independent verification of each obligation.**

*Well-definedness of the round.* A colour `c` is chosen that occurs in some list. Then
`S = {v : c in L(v)}` is nonempty, because the vertex whose list supplied `c` lies in it.
`K` is a kernel of `D[S]`.

*`K` is nonempty.* If `K = ∅` then the domination condition would require every vertex of `S`
to have an out-neighbour in `∅`, impossible for `S ≠ ∅`. The appendix states this explicitly
at the end of D.1's preamble. **Confirmed.**

*Properness of the assignment on `K`.* `K` is independent in `D[S]`. Two vertices of `K` that
were adjacent in the underlying graph of `D` would, being both in `S`, be joined by an arc in
the induced subdigraph `D[S]`, contradicting independence. So no two vertices receiving `c`
are adjacent. **Confirmed.**

*Properness against vertices not in `S`.* A vertex `w ∉ S` does not have `c` in its list and
therefore can never receive `c` at any later round either, since lists only shrink. So the
colour class of `c` is exactly a union of kernels drawn from vertices that had `c`, and no
later assignment can conflict with it. The appendix covers this only implicitly, by saying
vertices outside `S` "keep their lists"; the argument is immediate. **Confirmed.**

*Invariant preservation for `v ∈ S \ K`.* Such a `v` loses exactly one list entry, namely `c`.
By kernel domination `v` has an out-neighbour in `K`, and `K` is deleted, so `d+(v)` drops by
at least one. Hence `|L(v)| >= d+(v) + 1` survives the round. **Confirmed** — and this is the
load-bearing step, because it is the only place where domination is used.

*Invariant preservation for `v ∉ S`.* No list entry is lost; `d+(v)` cannot increase when
vertices are deleted. **Confirmed.**

*Kernel-perfectness is preserved.* The next round needs a kernel in `D[S']` for the reduced
digraph. Since the reduced digraph is itself an induced subdigraph of the original `D`, and
an induced subdigraph of an induced subdigraph is induced in the original, kernel-perfectness
transfers. The appendix does **not** state this step. It is a one-line consequence of the
definition of kernel-perfect ("every induced subdigraph has a kernel"), so this is an
expository omission, not a gap. **Recorded as `EXT-V14C-N03`.**

*Termination and totality.* Every round with `S ≠ ∅` colours the nonempty set `K`, so each
round removes at least one vertex from a finite vertex set. If uncolored vertices remain, each
has a nonempty list — from `|L(v)| >= d+(v) + 1 >= 1` — so some colour occurs in some list and
a further round is always available. Hence the process terminates with every vertex coloured.
**Confirmed.** No stall state exists.

**Verdict: Lemma D.1 is proved. One unstated but immediate step.**

---

## Check 2 — Lemma D.2: both cases of the stability proof

**Stability as defined here.** `M` is stable if every `f ∉ M` has an endpoint `z` covered by
some `e ∈ M` at `z` with `e >_z f`. This is the domination form, and it is the form Step 3
later needs; the two definitions must agree and they do.

*Termination.* Each edge is proposed along at most once, and every iteration issues one
proposal. Finitely many edges, so the process halts. `M` is a matching: each `r ∈ R` holds at
most one edge, and each `u ∈ U` has at most one outstanding accepted proposal. **Confirmed.**

*Case A — `u` did propose along `f = ur`.* Then `r` either rejected `f` on arrival or accepted
and later released it. In either event, at that instant `r` held or received an edge it
strictly prefers to `f`. The edge held at `r` improves monotonically and `r`, once matched,
never becomes unmatched — a release only occurs on accepting something strictly better. So the
final `e ∈ M` at `r` satisfies `e >_r f`. **Confirmed.**

*Case B — `u` never proposed along `f`.* The loop guard is "some `u ∈ U` is unmatched **and**
has not yet proposed along all of its edges". At termination the guard fails for `u`. Since
`f` is an untried edge of `u`, `u` has not proposed along all its edges, so the failing
conjunct must be the first: `u` is matched, to some `e ∈ M`. Proposals are issued in
decreasing preference order and `f` was never reached, so `f` lies strictly below every edge
`u` proposed along, in particular below `e`. Hence `e >_u f`. **Confirmed.** The step that
could fail — concluding `u` is matched — is forced by the loop guard, and the appendix states
exactly that reason.

*Exhaustiveness.* The two cases partition the possibilities for `f ∉ M`. **Confirmed.**

**Verdict: Lemma D.2 is proved, both cases, with the correct stability notion.**

---

## Check 3 — König Step 1: alternating-path parity and recolouring

The inductive claim that the argument actually establishes is: every bipartite graph of
maximum degree **at most** `Delta` has a proper edge colouring from `{1,...,Delta}`. The
appendix writes the palette as fixed at `Delta`, which is the correct formulation for the
induction; deleting an edge can only lower the maximum degree, and a colouring with fewer
colours is still a colouring from the palette. **Consistent.**

*Existence of the missing colours.* After deleting `e = ur`, at most `Delta - 1` edges remain
at `u` and at most `Delta - 1` at `r`, so each misses a colour of the palette: `u` misses
`alpha`, `r` misses `beta`. The branch taken assumes no colour is missed by both, so `u` has
a `beta`-edge and `r` has an `alpha`-edge. **Confirmed** — this is what makes the path start.

*`P` is a well-defined simple path.* In the subgraph of edges coloured `alpha` or `beta`, every
vertex has degree at most 2, so components are paths and even cycles; `u` has degree exactly 1
there, since it misses `alpha`. Therefore `u` is an endpoint of a path component, and `P` is
that component — unique, simple, and starting with a `beta`-edge. The appendix says "the
maximal path `P` starting at `u`" without stating the degree-2 observation. Standard, and
again an expository omission rather than a gap. **Recorded as `EXT-V14C-N03`.**

*The parity argument — the point most susceptible to reversal, checked in both directions.*
Suppose `P` ended at `r`. Its last edge cannot be `beta`-coloured, because `r` misses `beta`.
So the last edge is `alpha`-coloured. `P` begins with `beta` and alternates `beta, alpha,
beta, alpha, ...`; ending on `alpha` forces an **even** number of edges. But `u` and `r` are
adjacent in `B`, hence in opposite parts, so every `u`–`r` path in a bipartite graph has
**odd** length. Contradiction, so `P` does not end at `r`. **Confirmed, and the parity is the
right way round**: the even/odd assignment is not reversible, because "starts with `beta`,
ends with `alpha`" genuinely gives even length, and bipartite adjacency genuinely gives odd.

*The recolouring.* Swapping `alpha` and `beta` along the component `P` preserves properness:
inside `P` the alternation is merely relabelled, and at the two endpoints of `P` maximality
means no further edge of either colour is incident, so no conflict is created outside. `r ∉ P`
so `r` still misses `beta`. At `u`, the unique `beta`-edge became `alpha`, so `u` now misses
`beta`. Assigning `beta` to `e = ur` is therefore proper. **Confirmed.**

**Verdict: Step 1 is proved. König's theorem is genuinely reproved, not merely cited.**

---

## Check 4 — the `Delta - 1` out-degree bound

`e = ur` with `phi(e) = c`. Arcs `e -> f` exist exactly when `f >_z e` at a shared endpoint `z`.

- At `u`, higher `phi`-colour is preferred, so out-neighbours at `u` are the edges at `u` with
  colour `> c`. Because `phi` is proper, the colours at `u` are pairwise distinct and lie in
  `{1,...,Delta}`, with `c` among them; so at most `Delta - c` of them exceed `c`.
- At `r`, lower colour is preferred, so out-neighbours at `r` are the edges at `r` with colour
  `< c`, at most `c - 1` of them.

Sum: `d+_D(e) <= (Delta - c) + (c - 1) = Delta - 1`. **Confirmed, and independent of `c`.**

*Where simplicity is load-bearing.* The two counts are added as if disjoint. They are disjoint
precisely because no `f ≠ e` shares **both** endpoints with `e` — that is, because `B` is
simple. In a multigraph a parallel edge would be counted at both endpoints and the bound could
fail. Theorem D.3 does hypothesise simplicity, so the proof is correct; but this is the exact
reason the appendix proves only the simple case, and it is why the scope question in
`EXT-V14C-N02` below is worth raising. **Confirmed.**

---

## Check 5 — kernels are stable matchings, in every induced edge set

`D` has vertex set `E(B)`; an induced subdigraph is `D[S]` for `S ⊆ E(B)`.

*Independence ⇔ matching.* Two distinct edges of `B` sharing an endpoint `z` are always joined
by an arc, in exactly one direction, because the preference order at `z` is **linear** — and
it is linear here because `phi` is a proper colouring, so the colours at `z` are pairwise
distinct and induce a strict total order. Hence an independent set of `D[S]` is exactly a set
of pairwise non-incident edges, i.e. a matching of `(V(B), S)`. **Confirmed.** The reliance on
properness of `phi` for linearity is real and is satisfied.

*Domination ⇔ stability.* `f ∈ S \ K` has an arc into `K` iff there are `e ∈ K` and a shared
endpoint `z` with `e >_z f`, which is verbatim the stability condition of D.2 applied to
`(V(B), S)` with the inherited preferences. **Confirmed.**

*Applicability of D.2 to every `S`.* `(V(B), S)` is bipartite, being a subgraph of `B`, and
the restriction of a linear order is a linear order. So D.2 supplies a stable matching, hence
a kernel, for **every** `S`. That is exactly kernel-perfectness of `D`. **Confirmed** — the
quantifier "every induced subdigraph" is genuinely discharged, not just the full digraph.

*Step 4.* `|L(e)| >= Delta = (Delta - 1) + 1 >= d+_D(e) + 1`, so Lemma D.1 applies. A proper
list colouring of the underlying graph of `D` — which is the line graph of `B` — is a proper
list edge colouring of `B`. **Confirmed.**

**No circularity.** D.1 uses only kernel-perfectness; D.3 establishes kernel-perfectness from
D.2; D.2 is self-contained; König is reproved in Step 1. The dependency order is acyclic and
every ingredient is proved inside the appendix.

---

## Check 6 — the Section 7.2 application

Verified against the definitions in Section 7 and 2.1 rather than against Remark D.4's summary.
Section 2.1: `N_i = N(v_i) ∩ K`, `S_i = K \ N_i`. Section 7: `rho = |R|`, `Q = K \ R`,
`b = |Q|`, `T_i = S_i \ R` with `t_i = |T_i|`, `G_i = R \ S_i` with `g_i = |G_i|`,
`u = q - r_b`, and `U ⊆ I` with `|U| = u`.

*Simplicity.* The gain graph joins `v_i` to `r` when `r ∈ G_i`. Each pair `(v_i, r)` is joined
at most once, so the graph is simple. **Confirmed** — and this is what licenses Theorem D.3
rather than the multigraph version.

*Bipartiteness.* By construction the parts are `U ⊆ I` and `R ⊆ K`, and every edge runs
between them. `U` and `R` are disjoint because `I` and `K` are. **Confirmed.**

*The list size, recomputed from the definitions.* `G_i = R \ S_i = R \ (K \ N_i) = R ∩ N_i`,
so `g_i` counts the neighbours of `v_i` inside `R`. And
`L(v_i r) = N_i ∩ Q`, with

    |N_i ∩ Q| = |Q| - |(K \ N_i) ∩ Q| = b - |S_i \ R| = b - t_i.

So `|L(v_i r)| = b - t_i` exactly, as Section 7.2 asserts. **Confirmed by independent
recomputation.**

*The degree bound.* `d(v_i) = |G_i| = g_i = |R ∩ N_i| <= |R| = rho`, and `d(r) <= |U| = u`.
Hence `Delta <= max{rho, u}`. Hypothesis (7.2) reads `b - t_i >= max{rho, u}` for all `i`, so
every list satisfies `|L(v_i r)| >= max{rho, u} >= Delta`. **Confirmed.** The chain
`|L(v_i r)| = b - t_i >= max{rho, u} >= Delta` holds with the maximum degree of the actual gain
graph, not a surrogate, so Theorem D.3 applies with no unstated strengthening.

*The triangles are legitimate.* If `v_i r` receives colour `z ∈ Q`, the triangle `v_i r z`
needs `v_i r ∈ E` (holds: `r ∈ G_i ⊆ N_i`), `v_i z ∈ E` (holds: `z ∈ L(v_i r) = N_i ∩ Q`), and
`r z ∈ E` (holds: `r, z ∈ K` and `K` is a clique). **Confirmed.**

*Edge-disjointness across the family.* Properness at `v_i` gives distinct colours to the edges
`v_i r` and `v_i r'`, so the triangles do not share the edge `v_i z`. Properness at `r` gives
distinct colours to `v_i r` and `v_j r`, so they do not share `r z`. And `v_i r` is used by one
triangle only. **Confirmed** — the count `B_U = sum_i g_i` follows.

*Was the BKW local refinement needed?* No. Section 2.4 claims (7.2) already bounds every list
by the maximum degree, and the recomputation above confirms it. Reference [4] is correctly
described as not needed. **Confirmed.**

---

## New observations from this review

**`EXT-V14C-N02` (NOTE) — scope of Theorem 2.2 versus Theorem D.3.** Theorem 2.2 is stated for
"a bipartite graph with maximum degree `Delta(B)`". Theorem D.3 proves the statement for a
**simple** bipartite graph, and the additivity of the out-degree count in Step 2 genuinely
requires simplicity. Section 2.4 asserts that Theorem 2.2 is "proved in Appendix D"; under the
usual convention that "graph" means simple graph the two statements coincide and there is
nothing to repair, but the manuscript never declares that convention, and Remark D.4 itself
distinguishes the multigraph version as a separate result. So on the literal reading Theorem
2.2 is very slightly broader than what Appendix D proves. Nothing in the paper's proof chain
depends on the difference — the sole application is the gain graph, which was verified simple —
so this is expository. Recommended repair: insert "simple" into Theorem 2.2. **Not a defect of
the mathematics; recorded as a NOTE.**

**`EXT-V14C-N03` (NOTE) — three standard steps left unstated.** (i) In Lemma D.1, that the
reduced digraph is still kernel-perfect, needed for the recursion; (ii) in König Step 1, that
the `alpha`/`beta` subgraph has maximum degree 2 and `u` has degree 1 in it, which is what makes
"the maximal path `P`" well defined and simple; (iii) that the induction in Step 1 is over
graphs of maximum degree **at most** `Delta`. Each is a one-line consequence and none affects
validity. **Recorded as a NOTE.**

## Comparison with the author-side ledger, performed after the derivation above

The internal ledger reaches `PASS_INTERNAL` on all six areas. This review agrees with it point
for point, including its identification of the parity step as "the point most susceptible to
reversal" and its recomputation `d(v_i) = g_i <= rho`, `d(r) <= |U| = u`. Two differences of
coverage, both in the direction of this review being stricter:

1. The internal ledger states the claim under review as being about "a **simple** bipartite
   graph", i.e. it already reads Theorem 2.2 as the simple case. It does not observe that
   Theorem 2.2's own wording omits "simple". `EXT-V14C-N02` is new here.
2. The internal ledger asserts kernel-perfectness of the reduced digraph as a premise
   ("because the current digraph is induced in the original kernel-perfect digraph") without
   noting that the appendix text omits it; and it does not raise the maximum-degree-2
   observation behind the well-definedness of `P`. `EXT-V14C-N03` is new here.

Neither difference changes the internal ledger's conclusion, and neither was derived from it.

## Disposition

`EXT-V14-M02` — **CLOSED**. Appendix D is a complete and correct self-contained proof of the
maximum-degree case of Galvin's theorem for simple bipartite graphs, and it discharges exactly
what Section 7.2 uses. The paper's list-edge-colouring dependency is genuinely internal: no
step of Theorem 1.1 rests on [10] as an unproved input. Two expository NOTEs are recorded.
