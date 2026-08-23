# E1 — `EXT-V14C-N02` and `EXT-V14C-N03` reviewed as mathematics

These two notes were raised by this auditor in `run_2026-08-23_v1.4_challenger`. The obligation
here is not to confirm that the text now contains matching words, but to check that each
inserted sentence is **true**, is **placed where the argument needs it**, **discharges** the gap
it was written to close, and **introduces no new claim** beyond that.

---

## `EXT-V14C-N02` — "simple" in Theorem 2.2

**v1.4:** "Let \(B\) be a bipartite graph with maximum degree \(\Delta(B)\)."
**v1.5:** "Let \(B\) be a **simple** bipartite graph with maximum degree \(\Delta(B)\)."

**True and necessary.** Theorem D.3 proves the simple case, and simplicity is load-bearing in
its Step 2: the out-degree bound adds the count of higher-coloured edges at `u` to the count of
lower-coloured edges at `r` as if the two sets were disjoint. They are disjoint exactly because
no edge other than `e` shares both endpoints with `e`. In a multigraph a parallel edge would be
counted at both endpoints and `d+_D(e) <= Delta - 1` could fail. So the hypothesis Theorem 2.2
now states is the hypothesis its proof actually uses.

**Not a weakening of anything the paper relies on.** The only application is the Section 7.2
gain graph, which joins `v_i` to `r` when `r ∈ G_i` and therefore admits at most one edge per
pair: simple by construction. Verified again in this run against the Section 7 definitions;
Section 7.2 is byte-identical to v1.4. The narrowed hypothesis is still satisfied at the point
of use, so nothing downstream changes.

**No overclaim introduced.** Remark D.4 continues to record that the multigraph version of
Galvin's theorem holds and is not needed, so the manuscript does not now silently assert the
broader statement it no longer claims to prove. Section 2.4's assertion that Theorem 2.2 is
"proved in Appendix D" becomes literally true rather than true-under-convention.

**Disposition: `EXT-V14C-N02` CLOSED.** The scope of Theorem 2.2 and the scope of Theorem D.3
now coincide.

---

## `EXT-V14C-N03` — three unstated steps

### (i) The reduced digraph remains kernel-perfect

**Inserted, in Lemma D.1's proof, immediately after the deletion step:** "The remaining digraph
is an induced subdigraph of \(D\), and hence is kernel-perfect."

**True.** Round one deletes the vertex set `K` from `D`, and `D - K` is induced in `D`. Every
later round deletes further vertices from a digraph already induced in `D`, and an induced
subdigraph of an induced subdigraph is induced in the original. Kernel-perfectness is defined as
"every induced subdigraph has a kernel", so it transfers to the remainder at every round.

**Correctly placed.** It sits exactly where the recursion needs it: after `K` is deleted and
before "Repeat." Without it, the appeal to a kernel of `D[S']` in the next round has no stated
warrant. With it, the induction is closed.

**Discharges the gap and nothing more.** It asserts only hereditariness of the hypothesis; it
does not alter the invariant, the termination argument or the colour classes.

### (ii) The induction is over graphs of maximum degree at most `Delta`

**v1.4:** "induct on the number of edges."
**v1.5:** "induct on the number of edges among bipartite graphs of maximum degree at most
\(\Delta\) ... the induction hypothesis applies because the remaining graph still has maximum
degree at most \(\Delta\)."

**True and it is the right induction statement.** The palette must stay fixed at `Delta` while
the graph shrinks. Deleting an edge can only lower the maximum degree, so the class "bipartite,
maximum degree at most `Delta`" is closed under edge deletion and a colouring from
`{1,...,Delta}` is still a colouring from the palette. Quantifying over that class is what makes
the induction hypothesis applicable to `B - e`; quantifying over "maximum degree exactly
`Delta`" would not, since `B - e` may drop below `Delta`.

**No new claim.** The conclusion proved is unchanged: a proper edge colouring with colours from
`{1,...,Delta}`.

### (iii) The two-colour subgraph and the well-definedness of `P`

**v1.5:** "the subgraph formed by the \(\alpha\)- and \(\beta\)-colored edges has maximum degree
at most two, and \(u\) has degree one in it. Hence the alternating component starting at \(u\)
is a well-defined simple path \(P\), whose edges are colored alternately \(\beta,\alpha\)."

**True.** Since `φ` is proper, each vertex carries at most one `α`-edge and at most one
`β`-edge, so the `α ∪ β` subgraph has maximum degree at most two and its components are paths
and even cycles. The vertex `u` misses `α`, so it has no `α`-edge; and because the branch
assumes no colour is missed by both endpoints, `u` does not miss `β` and therefore has a
`β`-edge. Degree exactly one. A degree-one vertex in a graph of maximum degree two lies in a
path component and is one of its ends, so the component containing `u` is a simple path,
uniquely determined, beginning with a `β`-edge.

**This is precisely what v1.4 left unstated.** "The maximal path `P` starting at `u`" presumed
existence, uniqueness and simplicity; all three now follow from a stated fact. The subsequent
parity argument and the colour swap are unchanged and still correct: a path ending at `r` would
end on `α` (as `r` misses `β`), hence have even length, contradicting the odd length of every
`u`–`r` path in a bipartite graph with `u`, `r` adjacent; and the swap preserves properness by
maximality, leaves `r` untouched and frees `β` at `u`.

**Disposition: `EXT-V14C-N03` CLOSED.** All three steps are stated, all three are true, each is
placed where the argument requires it, and none introduces a claim beyond closing its gap.

---

## Regression check on the surrounding argument

The rest of Appendix D is byte-identical: Lemma D.2 and its two cases, Steps 2, 3 and 4 of
Theorem D.3, and Remark D.4 are unchanged. The displayed-formula sequence over the whole
manuscript is identical (205 formulas, same order, both languages), the equation-tag sequence is
identical (66), the in-text citation sequence is identical (42 references over 17 bibliography
entries), and no changed hunk lies in Sections 3–10 or Appendices A, B, C, E. So the
clarifications did not perturb any quantifier, constant, parity or implication elsewhere.

The Spanish renders all four insertions faithfully — "grafo bipartito simple", "subdigrafo
inducido de \(D\) y, por tanto, es kernel-perfect", "grafos bipartitos de grado máximo a lo sumo
\(\Delta\)", "grado máximo a lo sumo dos ... camino simple bien definido" — with the term of art
"kernel-perfect" deliberately left untranslated, consistent with the rest of the Spanish text.

**Both notes close. No new mathematical obligation arises from the v1.5 delta.**
