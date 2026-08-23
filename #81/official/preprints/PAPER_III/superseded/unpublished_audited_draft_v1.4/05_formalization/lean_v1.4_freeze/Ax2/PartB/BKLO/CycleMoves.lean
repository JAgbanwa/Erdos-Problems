/-
  Part B (Phase 2) — the *move calculus* for cycle-form chunks.

  The chunk absorber (`ChunkAbsorber.lean`) has to absorb a chunk `S`: at most three
  edge-disjoint cycles of length `≥ 4` whose total number of edges is divisible by three.  The
  gadgets available so far (hub gadget, friendship hub, necklace, double cone) all absorb a chunk
  *in one shot*: they produce, for the whole chunk at once, a hub assignment and a reserved family
  covering the resulting subdivision and hub edges.

  This file develops the complementary, *incremental* point of view: a chunk is rewritten step by
  step into a simpler chunk, each step paid for by a bounded number of reserved triangles.  The
  basic notion is the **transformer step** `Absorbs.transform`: if the part `S₀` of the config is
  consumed by a triangle family together with an intermediate set `D`, and the reserved triangles
  used cover `D` together with a residue `Z`, then absorbing the *rewritten* config `S₁ ∪ Z` is
  enough to absorb `S₀ ∪ S₁`.

  Three concrete moves are then provided, each proved from the transformer step:

  * `absorbs_mergeCycles` — **merging**: one hub `h` and the two reserved *co-apex* triangles
    `{a, c, h}`, `{b, d, h}` replace an edge `ab` of one cycle and an edge `cd` of another by the
    two edges `ac`, `bd`; two cycles of lengths `L₁, L₂` become a single cycle of length
    `L₁ + L₂`.  This is what reduces a chunk of two or three cycles to a *single* cycle, which is
    what the necklace of `Necklace.lean` consumes;
  * `absorbs_shortenTriple` — **shortening**: a single reserved triangle `{a₁, a₃, a₅}` on three
    config vertices at distance two along the cycle replaces the four cycle edges
    `a₁a₂, a₂a₃, a₃a₄, a₄a₅` by the single edge `a₁a₅`; the cycle gets *three* edges shorter;
  * `absorbs_lengthenEdge` — **lengthening**: two reserved triangles `{a, q, r}`, `{b, q, s}`
    sharing a hub `q` replace the cycle edge `ab` by the path `a — r — q — s — b`; the cycle gets
    three edges longer.

  All three moves preserve the length of the config modulo three — as they must: the total number
  of edges of `coveredEdges P ∪ S` is `3·|P| + |S|`, so an absorbable config has `3 ∣ |S|`
  (`localAbsorbable_card_dvd_three`), and hence no chain of moves can change `|S| mod 3`.

  The interest of the three moves for the reservation kernel is that they have very different
  *costs* in a fixed, load-bounded reserved family `B` (see `CHUNK_ABSORBER_STATUS.md`):
  lengthening only asks for one reserved triangle at each of the two endpoints of a config edge
  with a common hub, which the dense regime supplies in abundance, whereas shortening asks for a
  reserved triangle all three of whose vertices are prescribed by the chunk.
-/
import Ax2.PartB.BKLO.AbsorbCalculus

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Triples of vertices -/

omit [Fintype V] in
/-- A triple of pairwise distinct, pairwise adjacent vertices is a triangle. -/
theorem isNClique_triple {G : SimpleGraph V} [DecidableRel G.Adj] {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (axy : G.Adj x y) (axz : G.Adj x z) (ayz : G.Adj y z) :
    G.IsNClique 3 ({x, y, z} : Finset V) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq hpq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact axy | exact axy.symm | exact axz | exact axz.symm | exact ayz | exact ayz.symm
  · rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]

/-! ### Small families of triangles -/

omit [Fintype V] in
/-- The edges covered by a one-element family. -/
theorem coveredEdges_singleton (t : Finset V) :
    coveredEdges ({t} : Finset (Finset V)) = triEdges t := by
  simp [coveredEdges]

omit [Fintype V] in
/-- The edges covered by a two-element family. -/
theorem coveredEdges_pair (t u : Finset V) :
    coveredEdges ({t, u} : Finset (Finset V)) = triEdges t ∪ triEdges u := by
  simp [coveredEdges]

omit [Fintype V] in
/-- A one-element family is edge-disjoint. -/
theorem edgeDisjoint_singleton (t : Finset V) : EdgeDisjoint ({t} : Finset (Finset V)) := by
  intro x hx y hy hxy
  rw [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

omit [Fintype V] in
/-- A two-element family with disjoint edge sets is edge-disjoint. -/
theorem edgeDisjoint_pair {t u : Finset V} (h : Disjoint (triEdges t) (triEdges u)) :
    EdgeDisjoint ({t, u} : Finset (Finset V)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h
  · exact h.symm
  · exact absurd rfl hxy

/-! ### Reshuffling small unions

The gadgets below produce the covered edges of a two-element triangle family in one grouping and
consume them in another; these purely set-theoretic identities do the regrouping. -/

section Shuffle

variable {α : Type*} [DecidableEq α]

theorem union_shuffle_outer (x y z u v w : α) :
    ({x, y, z} ∪ {u, v, w} : Finset α) = {x, u} ∪ {y, z, v, w} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem union_shuffle_coapex (x y z u v w : α) :
    ({x, y, z} ∪ {u, v, w} : Finset α) = {y, v, z, w} ∪ {x, u} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem union_shuffle_chord (x y z u v w : α) :
    ({x, y, z} ∪ {u, v, w} : Finset α) = {x, z, u, w} ∪ {y, v} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem union_shuffle_spokes (x y z u v w : α) :
    ({x, y, z} ∪ {u, v, w} : Finset α) = {x, u} ∪ {y, z, w, v} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem triple_shuffle (x y z : α) : ({x, y, z} : Finset α) = {x, z} ∪ {y} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

theorem triple_shuffle_head (x y z : α) : ({x, y, z} : Finset α) = {x} ∪ {y, z} := by
  ext e; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

end Shuffle

/-! ### The transformer step -/

omit [Fintype V] in
/-- **The transformer step of the absorbing calculus.**  The config splits as `S₀ ∪ S₁`; the part
`S₀` is *consumed* together with an intermediate edge set `D` (`S₀ ∪ D` decomposable), the
reserved edges used are `D ∪ Z` (a union of reserved triangles), and the *rewritten* config
`S₁ ∪ Z` is absorbed by a further reserved set `F`.  Then `S₀ ∪ S₁` is absorbed by
`(D ∪ Z) ∪ F`.

This is the incremental form of `localAbsorbable_of_transformerFamily`: instead of transforming
every cycle of the chunk at once, one rewriting step is performed and the rest of the work is
left to the absorption of the rewritten config. -/
theorem Absorbs.transform {G : SimpleGraph V} [DecidableRel G.Adj]
    {S₀ S₁ D Z F : Finset (Sym2 V)}
    (hcons : TriDecomposable G (S₀ ∪ D)) (hT : TriDecomposable G (D ∪ Z))
    (habs : Absorbs G F (S₁ ∪ Z))
    (h01 : Disjoint S₀ S₁) (h0D : Disjoint S₀ D) (h0Z : Disjoint S₀ Z) (h0F : Disjoint S₀ F)
    (h1D : Disjoint S₁ D) (h1Z : Disjoint S₁ Z) (hDZ : Disjoint D Z) (hDF : Disjoint D F) :
    Absorbs G ((D ∪ Z) ∪ F) (S₀ ∪ S₁) := by
  have hFS₁ : Disjoint F S₁ := by
    have := habs.disjoint
    rw [Finset.disjoint_union_right] at this
    exact this.1
  have hFZ : Disjoint F Z := by
    have := habs.disjoint
    rw [Finset.disjoint_union_right] at this
    exact this.2
  refine ⟨?_, ?_, ?_⟩
  · have hDZS : Disjoint (D ∪ Z) (S₀ ∪ S₁) := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨h0D.symm, h1D.symm⟩, h0Z.symm, h1Z.symm⟩
    have hFS : Disjoint F (S₀ ∪ S₁) := by
      rw [Finset.disjoint_union_right]
      exact ⟨h0F.symm, hFS₁⟩
    rw [Finset.disjoint_union_left]
    exact ⟨hDZS, hFS⟩
  · refine hT.union habs.reserved ?_
    rw [Finset.disjoint_union_left]
    exact ⟨hDF, hFZ.symm⟩
  · have heq : ((D ∪ Z) ∪ F) ∪ (S₀ ∪ S₁) = (S₀ ∪ D) ∪ (F ∪ (S₁ ∪ Z)) := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [heq]
    refine hcons.union habs.total ?_
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right,
      Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨h0F, h01, h0Z⟩, hDF, h1D.symm, hDZ⟩

omit [Fintype V] in
/-- **The transformer step, in reserved-family form.**  The reserved triangles `Q` used by the
move cover `D ∪ Z`, the reserved family `P` absorbs the rewritten config `S₁ ∪ Z`, and the whole
family `P ∪ Q` absorbs the original config `S₀ ∪ S₁`. -/
theorem localAbsorbable_transform {G : SimpleGraph V} [DecidableRel G.Adj]
    {P Q : Finset (Finset V)} {S₀ S₁ D Z : Finset (Sym2 V)}
    (hPcl : ∀ t ∈ P, G.IsNClique 3 t) (hPd : EdgeDisjoint P)
    (hQcl : ∀ t ∈ Q, G.IsNClique 3 t) (hQd : EdgeDisjoint Q)
    (hQcov : coveredEdges Q = D ∪ Z)
    (hcons : TriDecomposable G (S₀ ∪ D))
    (habs : LocalAbsorbable G P (S₁ ∪ Z))
    (h01 : Disjoint S₀ S₁) (h0D : Disjoint S₀ D) (h0Z : Disjoint S₀ Z)
    (h0P : Disjoint S₀ (coveredEdges P))
    (h1D : Disjoint S₁ D) (h1Z : Disjoint S₁ Z) (hDZ : Disjoint D Z)
    (hDP : Disjoint D (coveredEdges P)) (hZP : Disjoint Z (coveredEdges P))
    (h1P : Disjoint S₁ (coveredEdges P)) :
    LocalAbsorbable G (P ∪ Q) (S₀ ∪ S₁) := by
  have habs' : Absorbs G (coveredEdges P) (S₁ ∪ Z) := by
    refine ⟨?_, TriDecomposable.of_family G hPcl hPd, habs⟩
    rw [Finset.disjoint_union_right]
    exact ⟨h1P.symm, hZP.symm⟩
  have hT : TriDecomposable G (D ∪ Z) := by
    rw [← hQcov]
    exact TriDecomposable.of_family G hQcl hQd
  have hmain := Absorbs.transform hcons hT habs' h01 h0D h0Z h0P h1D h1Z hDZ hDP
  have hcov : coveredEdges (P ∪ Q) = (D ∪ Z) ∪ coveredEdges P := by
    rw [show coveredEdges (P ∪ Q) = coveredEdges P ∪ coveredEdges Q by
        simp [coveredEdges, Finset.union_biUnion], hQcov, Finset.union_comm]
  refine (localAbsorbable_iff_triDecomposable G (P ∪ Q) (S₀ ∪ S₁)).mpr ?_
  rw [hcov]
  exact hmain.total

/-! ### Merging two cycles into one -/

omit [Fintype V] in
/-- **The merging move.**  Let `ab` be an edge of one cycle of the chunk and `cd` an edge of
another, and suppose the reserved family contains the two *co-apex* triangles `{a, c, h}` and
`{b, d, h}` through a common hub `h`.  The two outer triangles `{a, b, h}` and `{c, d, h}` consume
the two config edges together with the four spokes, and the residue is `{ac, bd}`: the two cycles
have been spliced into a single cycle of the combined length.

Hence absorbing the merged config `S₁ ∪ {ac, bd}` is enough to absorb `{ab, cd} ∪ S₁`, at the cost
of two reserved triangles.  Applied twice, this reduces a chunk of three cycles to one cycle. -/
theorem absorbs_mergeCycles {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b c d h : V} {S₁ F : Finset (Sym2 V)}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hah : a ≠ h)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbh : b ≠ h)
    (hcd : c ≠ d) (hch : c ≠ h) (hdh : d ≠ h)
    (hQ1 : G.IsNClique 3 ({a, c, h} : Finset V)) (hQ2 : G.IsNClique 3 ({b, d, h} : Finset V))
    (hGab : G.Adj a b) (hGcd : G.Adj c d)
    (habs : Absorbs G F (S₁ ∪ {s(a, c), s(b, d)}))
    (h01 : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V)) S₁)
    (h0F : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V)) F)
    (h1D : Disjoint S₁ ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)))
    (h1Z : Disjoint S₁ ({s(a, c), s(b, d)} : Finset (Sym2 V)))
    (hDF : Disjoint ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) F) :
    Absorbs G ((({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) ∪ {s(a, c), s(b, d)}) ∪ F)
      (({s(a, b), s(c, d)} : Finset (Sym2 V)) ∪ S₁) := by
  classical
  have h0D : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V))
      {s(a, h), s(b, h), s(c, h), s(d, h)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h0Z : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V)) {s(a, c), s(b, d)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hDZ : Disjoint ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V))
      {s(a, c), s(b, d)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hGah : G.Adj a h := hQ1.1 (by simp) (by simp) hah
  have hGch : G.Adj c h := hQ1.1 (by simp) (by simp) hch
  have hGac : G.Adj a c := hQ1.1 (by simp) (by simp) hac
  have hGbh : G.Adj b h := hQ2.1 (by simp) (by simp) hbh
  have hGdh : G.Adj d h := hQ2.1 (by simp) (by simp) hdh
  have hAcl1 : G.IsNClique 3 ({a, b, h} : Finset V) :=
    isNClique_triple hab hah hbh hGab hGah hGbh
  have hAcl2 : G.IsNClique 3 ({c, d, h} : Finset V) :=
    isNClique_triple hcd hch hdh hGcd hGch hGdh
  have htri1 : triEdges ({a, b, h} : Finset V) = {s(a, b), s(a, h), s(b, h)} :=
    triEdges_triple hab hah hbh
  have htri2 : triEdges ({c, d, h} : Finset V) = {s(c, d), s(c, h), s(d, h)} :=
    triEdges_triple hcd hch hdh
  have htri3 : triEdges ({a, c, h} : Finset V) = {s(a, c), s(a, h), s(c, h)} :=
    triEdges_triple hac hah hch
  have htri4 : triEdges ({b, d, h} : Finset V) = {s(b, d), s(b, h), s(d, h)} :=
    triEdges_triple hbd hbh hdh
  have hcons : TriDecomposable G
      (({s(a, b), s(c, d)} : Finset (Sym2 V)) ∪ {s(a, h), s(b, h), s(c, h), s(d, h)}) := by
    refine ⟨{{a, b, h}, {c, d, h}}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [hAcl1, hAcl2]
    · refine edgeDisjoint_pair ?_
      rw [htri1, htri2]
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · rw [coveredEdges_pair, htri1, htri2, union_shuffle_outer]
  have hT : TriDecomposable G
      (({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) ∪ {s(a, c), s(b, d)}) := by
    refine ⟨{{a, c, h}, {b, d, h}}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [hQ1, hQ2]
    · refine edgeDisjoint_pair ?_
      rw [htri3, htri4]
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · rw [coveredEdges_pair, htri3, htri4, union_shuffle_coapex]
  exact Absorbs.transform hcons hT habs h01 h0D h0Z h0F h1D h1Z hDZ hDF

/-! ### Cycles as vertex lists: splicing two cycles

The merging move rewrites two disjoint cycles into a single cycle.  In the list presentation of
`CycleChunks.lean` this is the concatenation of the two vertex lists: if `p` runs from `a` to `b`
and `q` from `d` to `c`, then `p ++ q` is the cycle obtained from `cycleEdges p ∪ cycleEdges q` by
deleting the two closing edges `ab`, `cd` and inserting `ac` and `bd`. -/

section Splice

variable {V : Type*} [DecidableEq V]

/-- Edges of a walk along a concatenation split at the last vertex of the first part. -/
theorem walkEdges_append : ∀ {t : List V} {a b : V}, (a :: t).getLast? = some b →
    ∀ u : List V, walkEdges a (t ++ u) = walkEdges a t ∪ walkEdges b u := by
  intro t
  induction t with
  | nil =>
      intro a b hb u
      simp only [List.getLast?_singleton, Option.some.injEq] at hb
      subst hb
      simp
  | cons x t ih =>
      intro a b hb u
      rw [List.getLast?_cons_cons] at hb
      have hrec := ih hb u
      simp only [List.cons_append, walkEdges_cons, hrec]
      rw [Finset.insert_union]

/-- Edges of a path along a concatenation. -/
theorem pathEdges_append {p q : List V} {b : V} (hb : p.getLast? = some b) :
    pathEdges (p ++ q) = pathEdges p ∪ walkEdges b q := by
  cases p with
  | nil => simp at hb
  | cons a t => simpa using walkEdges_append hb q

/-- A cycle is its path together with the closing edge. -/
theorem cycleEdges_eq_insert {p : List V} {a b : V} (ha : p.head? = some a)
    (hb : p.getLast? = some b) : cycleEdges p = insert s(b, a) (pathEdges p) := by
  cases p with
  | nil => simp at ha
  | cons x t =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      rcases ha with rfl
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x t), Option.some.injEq] at hb
      simp only [cycleEdges, pathEdges_cons, hb]

/-- A walk into a list starts with the edge to its head. -/
theorem walkEdges_cons_head {b d : V} {q : List V} (hq : q.head? = some d) :
    walkEdges b q = insert s(b, d) (pathEdges q) := by
  cases q with
  | nil => simp at hq
  | cons e q' =>
      simp only [List.head?_cons, Option.some.injEq] at hq
      subst hq
      simp [walkEdges, pathEdges]

/-- **Splicing.**  The cycle along `p ++ q` consists of the two paths together with the two
crossing edges `bd` and `ca`. -/
theorem cycleEdges_append {p q : List V} {a b c d : V}
    (ha : p.head? = some a) (hb : p.getLast? = some b)
    (hd : q.head? = some d) (hc : q.getLast? = some c) :
    cycleEdges (p ++ q) = insert s(c, a) (pathEdges p ∪ insert s(b, d) (pathEdges q)) := by
  have hqne : q ≠ [] := by rintro rfl; simp at hd
  have hpne : p ≠ [] := by rintro rfl; simp at ha
  have hhead : (p ++ q).head? = some a := by
    rw [List.head?_append_of_ne_nil p hpne]; exact ha
  have hlast : (p ++ q).getLast? = some c := by
    rw [List.getLast?_append_of_ne_nil p hqne]; exact hc
  rw [cycleEdges_eq_insert hhead hlast, pathEdges_append hb, walkEdges_cons_head hd]

/-- An edge with an endpoint off the list is not a path edge. -/
theorem notMem_pathEdges_of_notMem {l : List V} {v w : V} (hv : v ∉ l) :
    s(v, w) ∉ pathEdges l := fun hmem => hv (mem_of_mem_pathEdges hmem (by simp))

omit [DecidableEq V] in
/-- The head and the last vertex of a nodup list of length `≥ 2` are distinct. -/
theorem head_ne_getLast {l : List V} {a b : V} (hnd : l.Nodup) (h2 : 2 ≤ l.length)
    (ha : l.head? = some a) (hb : l.getLast? = some b) : a ≠ b := by
  cases l with
  | nil => simp at ha
  | cons x t =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      rcases ha with rfl
      have ht : t ≠ [] := by
        rintro rfl
        simp at h2
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x t), Option.some.injEq] at hb
      have hmem : (x :: t).getLast (List.cons_ne_nil x t) ∈ t := by
        rw [List.getLast_cons ht]
        exact List.getLast_mem ht
      rintro rfl
      exact (List.nodup_cons.mp hnd).1 (hb ▸ hmem)

omit [DecidableEq V] in
/-- The head of a list is a member of it. -/
theorem mem_of_head?_eq {l : List V} {a : V} (ha : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at ha
  | cons x t =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      simp [← ha]

omit [DecidableEq V] in
/-- The last vertex of a list is a member of it. -/
theorem mem_of_getLast?_eq {l : List V} {b : V} (hb : l.getLast? = some b) : b ∈ l := by
  cases l with
  | nil => simp at hb
  | cons x t =>
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x t), Option.some.injEq] at hb
      exact hb ▸ List.getLast_mem (List.cons_ne_nil x t)

end Splice

/-! ### Merging two cycles presented by vertex lists -/

omit [Fintype V] in
/-- **Two cycles of a chunk merge into one.**  Let the two cycles be given by disjoint nodup
vertex lists `p` (from `a` to `b`) and `q` (from `d` to `c`), and let `h` be a hub outside both,
carrying the two reserved *co-apex* triangles `{a, c, h}` and `{b, d, h}`.  Then absorbing the
single spliced cycle `cycleEdges (p ++ q)` (together with the rest `S₁` of the chunk) is enough to
absorb the two cycles, at the cost of the two reserved triangles.

This is the reduction of a chunk of several cycles to a chunk consisting of a *single* cycle — of
the same total length, hence still divisible by three when the chunk is. -/
theorem absorbs_mergeCycleLists {G : SimpleGraph V} [DecidableRel G.Adj]
    {p q : List V} {a b c d h : V} {S₁ F : Finset (Sym2 V)}
    (ha : p.head? = some a) (hb : p.getLast? = some b)
    (hd : q.head? = some d) (hc : q.getLast? = some c)
    (hpnd : p.Nodup) (hqnd : q.Nodup) (hp3 : 3 ≤ p.length) (hq3 : 3 ≤ q.length)
    (hpq : ∀ x ∈ p, x ∉ q) (hhp : h ∉ p) (hhq : h ∉ q)
    (hQ1 : G.IsNClique 3 ({a, c, h} : Finset V)) (hQ2 : G.IsNClique 3 ({b, d, h} : Finset V))
    (hGab : G.Adj a b) (hGcd : G.Adj c d)
    (habs : Absorbs G F (S₁ ∪ cycleEdges (p ++ q)))
    (hS₁ : Disjoint S₁ ((cycleEdges p ∪ cycleEdges q) ∪
      (({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) ∪ {s(a, c), s(b, d)})))
    (hF : Disjoint F ((cycleEdges p ∪ cycleEdges q) ∪
      ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)))) :
    Absorbs G ((({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) ∪ {s(a, c), s(b, d)}) ∪ F)
      ((cycleEdges p ∪ cycleEdges q) ∪ S₁) := by
  classical
  -- the vertices involved
  have hap : a ∈ p := mem_of_head?_eq ha
  have hbp : b ∈ p := mem_of_getLast?_eq hb
  have hdq : d ∈ q := mem_of_head?_eq hd
  have hcq : c ∈ q := mem_of_getLast?_eq hc
  have haq : a ∉ q := hpq a hap
  have hbq : b ∉ q := hpq b hbp
  have hcp : c ∉ p := fun hmem => hpq c hmem hcq
  have hdp : d ∉ p := fun hmem => hpq d hmem hdq
  have hab : a ≠ b := head_ne_getLast hpnd (by omega) ha hb
  have hdc : d ≠ c := head_ne_getLast hqnd (by omega) hd hc
  have hac : a ≠ c := fun hh => hcp (hh ▸ hap)
  have had : a ≠ d := fun hh => hdp (hh ▸ hap)
  have hbc : b ≠ c := fun hh => hcp (hh ▸ hbp)
  have hbd : b ≠ d := fun hh => hdp (hh ▸ hbp)
  have hah : a ≠ h := fun hh => hhp (hh ▸ hap)
  have hbh : b ≠ h := fun hh => hhp (hh ▸ hbp)
  have hch : c ≠ h := fun hh => hhq (hh ▸ hcq)
  have hdh : d ≠ h := fun hh => hhq (hh ▸ hdq)
  -- the two cycles, split into their paths and their closing edges
  have hcyc1 : cycleEdges p = insert s(b, a) (pathEdges p) := cycleEdges_eq_insert ha hb
  have hcyc2 : cycleEdges q = insert s(c, d) (pathEdges q) := cycleEdges_eq_insert hd hc
  set S₁' : Finset (Sym2 V) := (pathEdges p ∪ pathEdges q) ∪ S₁ with hS₁'
  have hconfig : (cycleEdges p ∪ cycleEdges q) ∪ S₁
      = ({s(a, b), s(c, d)} : Finset (Sym2 V)) ∪ S₁' := by
    rw [hcyc1, hcyc2, hS₁', Sym2.eq_swap (a := a) (b := b)]
    ext e
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- the merged cycle
  have hmerge : S₁' ∪ ({s(a, c), s(b, d)} : Finset (Sym2 V)) = S₁ ∪ cycleEdges (p ++ q) := by
    rw [cycleEdges_append ha hb hd hc, hS₁', Sym2.eq_swap (a := a) (b := c)]
    ext e
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- the closing edges are not path edges
  have hclose1 : s(a, b) ∉ pathEdges p := by
    obtain ⟨x, t, rfl⟩ : ∃ x t, p = x :: t := by
      cases p with
      | nil => simp at ha
      | cons x t => exact ⟨x, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at ha
    rcases ha with rfl
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ t), Option.some.injEq] at hb
    have := closing_notMem_pathEdges hpnd hp3
    rw [hb] at this
    rw [pathEdges_cons, Sym2.eq_swap]
    exact this
  have hclose2 : s(c, d) ∉ pathEdges q := by
    obtain ⟨x, t, rfl⟩ : ∃ x t, q = x :: t := by
      cases q with
      | nil => simp at hd
      | cons x t => exact ⟨x, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hd
    rcases hd with rfl
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ t), Option.some.injEq] at hc
    have := closing_notMem_pathEdges hqnd hq3
    rw [hc] at this
    rw [pathEdges_cons]
    exact this
  -- disjointness bookkeeping
  have hsubcyc1 : s(a, b) ∈ cycleEdges p := by
    rw [hcyc1, Sym2.eq_swap (a := a) (b := b)]
    exact Finset.mem_insert_self _ _
  have hsubcyc2 : s(c, d) ∈ cycleEdges q := by
    rw [hcyc2]
    exact Finset.mem_insert_self _ _
  have hS₁cyc : Disjoint S₁ (cycleEdges p ∪ cycleEdges q) :=
    Finset.disjoint_of_subset_right (Finset.subset_union_left.trans Finset.Subset.rfl) hS₁
  have hS₁spokes : Disjoint S₁ ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) := by
    refine Finset.disjoint_of_subset_right ?_ hS₁
    intro e he
    exact Finset.mem_union_right _ (Finset.mem_union_left _ he)
  have hS₁Z : Disjoint S₁ ({s(a, c), s(b, d)} : Finset (Sym2 V)) := by
    refine Finset.disjoint_of_subset_right ?_ hS₁
    intro e he
    exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
  have hFcyc : Disjoint F (cycleEdges p ∪ cycleEdges q) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hF
  have hFspokes : Disjoint F ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) :=
    Finset.disjoint_of_subset_right Finset.subset_union_right hF
  have h01 : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V)) S₁' := by
    rw [Finset.disjoint_left]
    intro e he heS
    rw [hS₁'] at heS
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases Finset.mem_union.mp heS with hpath | hrest
    · rcases Finset.mem_union.mp hpath with hp' | hq'
      · rcases he with rfl | rfl
        · exact hclose1 hp'
        · exact notMem_pathEdges_of_notMem hcp hp'
      · rcases he with rfl | rfl
        · exact notMem_pathEdges_of_notMem haq hq'
        · exact hclose2 hq'
    · rcases he with rfl | rfl
      · exact (Finset.disjoint_left.mp hS₁cyc) hrest (Finset.mem_union_left _ hsubcyc1)
      · exact (Finset.disjoint_left.mp hS₁cyc) hrest (Finset.mem_union_right _ hsubcyc2)
  have h0F : Disjoint ({s(a, b), s(c, d)} : Finset (Sym2 V)) F := by
    rw [Finset.disjoint_left]
    intro e he heF
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact (Finset.disjoint_left.mp hFcyc) heF (Finset.mem_union_left _ hsubcyc1)
    · exact (Finset.disjoint_left.mp hFcyc) heF (Finset.mem_union_right _ hsubcyc2)
  have hspokes_notMem : ∀ e ∈ ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)),
      e ∉ pathEdges p ∪ pathEdges q := by
    have hx : ∀ v : V, s(v, h) ∉ pathEdges p ∪ pathEdges q := by
      intro v hmem
      rcases Finset.mem_union.mp hmem with hp' | hq'
      · exact hhp (mem_of_mem_pathEdges hp' (by simp))
      · exact hhq (mem_of_mem_pathEdges hq' (by simp))
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact hx _
  have h1D : Disjoint S₁' ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) := by
    rw [hS₁', Finset.disjoint_right]
    intro e he heS
    rcases Finset.mem_union.mp heS with hpath | hrest
    · exact hspokes_notMem e he hpath
    · exact (Finset.disjoint_left.mp hS₁spokes) hrest he
  have hZ_notMem : ∀ e ∈ ({s(a, c), s(b, d)} : Finset (Sym2 V)),
      e ∉ pathEdges p ∪ pathEdges q := by
    intro e he hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases Finset.mem_union.mp hmem with hp' | hq'
    · rcases he with rfl | rfl
      · exact hcp (mem_of_mem_pathEdges hp' (by simp))
      · exact hdp (mem_of_mem_pathEdges hp' (by simp))
    · rcases he with rfl | rfl
      · exact haq (mem_of_mem_pathEdges hq' (by simp))
      · exact hbq (mem_of_mem_pathEdges hq' (by simp))
  have h1Z : Disjoint S₁' ({s(a, c), s(b, d)} : Finset (Sym2 V)) := by
    rw [hS₁', Finset.disjoint_right]
    intro e he heS
    rcases Finset.mem_union.mp heS with hpath | hrest
    · exact hZ_notMem e he hpath
    · exact (Finset.disjoint_left.mp hS₁Z) hrest he
  have habs' : Absorbs G F (S₁' ∪ {s(a, c), s(b, d)}) := by rw [hmerge]; exact habs
  rw [hconfig]
  exact absorbs_mergeCycles hab hac had hah hbc hbd hbh (Ne.symm hdc) hch hdh hQ1 hQ2 hGab hGcd
    habs' h01 h0F h1D h1Z hFspokes.symm

/-! ### Shortening a cycle by three -/

omit [Fintype V] in
/-- **The shortening move.**  If the reserved family contains the triangle `{a₁, a₃, a₅}` on three
config vertices at distance two along a cycle, then the two chords `a₁a₃`, `a₃a₅` triangulate the
four cycle edges `a₁a₂, a₂a₃, a₃a₄, a₄a₅` (by the two triangles `{a₁, a₂, a₃}` and `{a₃, a₄, a₅}`)
and the residue is the single edge `a₁a₅`: the cycle has become three edges shorter.

This is the cheapest possible move — one reserved triangle — but also the most demanding one on
the reserved family, since all three of its vertices are prescribed by the chunk. -/
theorem absorbs_shortenTriple {G : SimpleGraph V} [DecidableRel G.Adj]
    {a₁ a₂ a₃ a₄ a₅ : V} {S₁ F : Finset (Sym2 V)}
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄) (h15 : a₁ ≠ a₅)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h25 : a₂ ≠ a₅)
    (h34 : a₃ ≠ a₄) (h35 : a₃ ≠ a₅) (h45 : a₄ ≠ a₅)
    (hQ : G.IsNClique 3 ({a₁, a₃, a₅} : Finset V))
    (hG12 : G.Adj a₁ a₂) (hG23 : G.Adj a₂ a₃) (hG34 : G.Adj a₃ a₄) (hG45 : G.Adj a₄ a₅)
    (habs : Absorbs G F (S₁ ∪ {s(a₁, a₅)}))
    (h01 : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) S₁)
    (h0F : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) F)
    (h1D : Disjoint S₁ ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)))
    (h1Z : Disjoint S₁ ({s(a₁, a₅)} : Finset (Sym2 V)))
    (hDF : Disjoint ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) F) :
    Absorbs G ((({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) ∪ {s(a₁, a₅)}) ∪ F)
      (({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) ∪ S₁) := by
  classical
  have h0D : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V))
      {s(a₁, a₃), s(a₃, a₅)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h0Z : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V))
      {s(a₁, a₅)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hDZ : Disjoint ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) {s(a₁, a₅)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hG13 : G.Adj a₁ a₃ := hQ.1 (by simp) (by simp) h13
  have hG35 : G.Adj a₃ a₅ := hQ.1 (by simp) (by simp) h35
  have hAcl1 : G.IsNClique 3 ({a₁, a₂, a₃} : Finset V) :=
    isNClique_triple h12 h13 h23 hG12 hG13 hG23
  have hAcl2 : G.IsNClique 3 ({a₃, a₄, a₅} : Finset V) :=
    isNClique_triple h34 h35 h45 hG34 hG35 hG45
  have htri1 : triEdges ({a₁, a₂, a₃} : Finset V) = {s(a₁, a₂), s(a₁, a₃), s(a₂, a₃)} :=
    triEdges_triple h12 h13 h23
  have htri2 : triEdges ({a₃, a₄, a₅} : Finset V) = {s(a₃, a₄), s(a₃, a₅), s(a₄, a₅)} :=
    triEdges_triple h34 h35 h45
  have htri3 : triEdges ({a₁, a₃, a₅} : Finset V) = {s(a₁, a₃), s(a₁, a₅), s(a₃, a₅)} :=
    triEdges_triple h13 h15 h35
  have hcons : TriDecomposable G
      (({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) ∪
        {s(a₁, a₃), s(a₃, a₅)}) := by
    refine ⟨{{a₁, a₂, a₃}, {a₃, a₄, a₅}}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [hAcl1, hAcl2]
    · refine edgeDisjoint_pair ?_
      rw [htri1, htri2]
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · rw [coveredEdges_pair, htri1, htri2, union_shuffle_chord]
  have hT : TriDecomposable G
      (({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) ∪ {s(a₁, a₅)}) := by
    refine ⟨{{a₁, a₃, a₅}}, ?_, edgeDisjoint_singleton _, ?_⟩
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hQ
    · rw [coveredEdges_singleton, htri3, triple_shuffle]
  exact Absorbs.transform hcons hT habs h01 h0D h0Z h0F h1D h1Z hDZ hDF

/-! ### Shortening a cycle presented by a vertex list -/

omit [Fintype V] in
/-- **Shortening, in list form.**  If the reserved family contains the triangle `{a₁, a₃, a₅}` on
three vertices at distance two along the cycle `a₁ a₂ a₃ a₄ a₅ …`, then absorbing the shorter cycle
`a₁ a₅ …` (three edges shorter, obtained by deleting `a₂, a₃, a₄`) is enough to absorb the original
one.  Iterating, a cycle whose length is divisible by three would be shortened to a triangle, which
is absorbed by nothing (`localAbsorbable_cycleEdges_triple`); what a fixed reserved family cannot
in general supply is the triangle `{a₁, a₃, a₅}` itself — see `CHUNK_ABSORBER_STATUS.md`. -/
theorem absorbs_shortenCycleList {G : SimpleGraph V} [DecidableRel G.Adj]
    {a₁ a₂ a₃ a₄ a₅ z : V} {rest : List V} {F : Finset (Sym2 V)}
    (hhead : rest.head? = some a₅) (hlast : rest.getLast? = some z)
    (hnd : (a₁ :: a₂ :: a₃ :: a₄ :: rest).Nodup) (hlen : 2 ≤ rest.length)
    (hQ : G.IsNClique 3 ({a₁, a₃, a₅} : Finset V))
    (hG12 : G.Adj a₁ a₂) (hG23 : G.Adj a₂ a₃) (hG34 : G.Adj a₃ a₄) (hG45 : G.Adj a₄ a₅)
    (habs : Absorbs G F (cycleEdges (a₁ :: rest)))
    (hF : Disjoint F (cycleEdges (a₁ :: a₂ :: a₃ :: a₄ :: rest) ∪
      ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)))) :
    Absorbs G ((({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) ∪ {s(a₁, a₅)}) ∪ F)
      (cycleEdges (a₁ :: a₂ :: a₃ :: a₄ :: rest)) := by
  classical
  have hrestne : rest ≠ [] := by rintro rfl; simp at hlen
  have hrestnd : rest.Nodup := by
    have := (List.nodup_cons.mp hnd).2
    have := (List.nodup_cons.mp this).2
    exact (List.nodup_cons.mp (List.nodup_cons.mp this).2).2
  have h5 : a₅ ∈ rest := mem_of_head?_eq hhead
  have hz : z ∈ rest := mem_of_getLast?_eq hlast
  have h5z : a₅ ≠ z := head_ne_getLast hrestnd hlen hhead hlast
  -- the four leading vertices are outside `rest` and pairwise distinct
  have h1r : a₁ ∉ rest := fun hmem => (List.nodup_cons.mp hnd).1 (by simp [hmem])
  have h2r : a₂ ∉ rest := fun hmem =>
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hmem])
  have h3r : a₃ ∉ rest := fun hmem =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1 (by simp [hmem])
  have h4r : a₄ ∉ rest := fun hmem =>
    (List.nodup_cons.mp (List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).2).1 (by simp [hmem])
  have h12 : a₁ ≠ a₂ := fun hh => (List.nodup_cons.mp hnd).1 (by simp [hh])
  have h13 : a₁ ≠ a₃ := fun hh => (List.nodup_cons.mp hnd).1 (by simp [hh])
  have h14 : a₁ ≠ a₄ := fun hh => (List.nodup_cons.mp hnd).1 (by simp [hh])
  have h15 : a₁ ≠ a₅ := fun hh => h1r (hh ▸ h5)
  have h23 : a₂ ≠ a₃ := fun hh =>
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hh])
  have h24 : a₂ ≠ a₄ := fun hh =>
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hh])
  have h25 : a₂ ≠ a₅ := fun hh => h2r (hh ▸ h5)
  have h34 : a₃ ≠ a₄ := fun hh =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1 (by simp [hh])
  have h35 : a₃ ≠ a₅ := fun hh => h3r (hh ▸ h5)
  have h45 : a₄ ≠ a₅ := fun hh => h4r (hh ▸ h5)
  -- the two cycles in terms of the common tail
  set S₁ : Finset (Sym2 V) := insert s(z, a₁) (pathEdges rest) with hS₁def
  have hpath4 : pathEdges (a₁ :: a₂ :: a₃ :: a₄ :: rest)
      = ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) ∪ pathEdges rest := by
    have hw : walkEdges a₄ rest = insert s(a₄, a₅) (pathEdges rest) := walkEdges_cons_head hhead
    simp only [pathEdges_cons, walkEdges_cons, hw]
    ext e
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  have hpath1 : pathEdges (a₁ :: rest) = insert s(a₁, a₅) (pathEdges rest) := by
    simp only [pathEdges_cons]
    exact walkEdges_cons_head hhead
  have hlastcons : ∀ w : V, (w :: rest).getLast? = some z := by
    intro w
    cases rest with
    | nil => exact absurd rfl hrestne
    | cons x t => rw [List.getLast?_cons_cons]; exact hlast
  have hlastbig : (a₁ :: a₂ :: a₃ :: a₄ :: rest).getLast? = some z := by
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons, List.getLast?_cons_cons]
    exact hlastcons a₄
  have hlastsmall : (a₁ :: rest).getLast? = some z := hlastcons a₁
  have hcycbig : cycleEdges (a₁ :: a₂ :: a₃ :: a₄ :: rest)
      = ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) ∪ S₁ := by
    rw [cycleEdges_eq_insert (List.head?_cons) hlastbig, hpath4, hS₁def]
    ext e
    simp only [Finset.mem_insert, Finset.mem_union]
    tauto
  have hcycsmall : cycleEdges (a₁ :: rest) = S₁ ∪ ({s(a₁, a₅)} : Finset (Sym2 V)) := by
    rw [cycleEdges_eq_insert (List.head?_cons) hlastsmall, hpath1, hS₁def]
    ext e
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  -- membership criteria for the tail config
  have hout : ∀ x y : V, x ∉ rest → x ≠ a₁ → s(x, y) ∉ S₁ := by
    intro x y hx hx1 hmem
    rw [hS₁def, Finset.mem_insert] at hmem
    rcases hmem with heq | hmem
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hx hz
      · exact hx1 rfl
    · exact hx (mem_of_mem_pathEdges hmem (by simp))
  have hZout : s(a₁, a₅) ∉ S₁ := by
    rw [hS₁def, Finset.mem_insert]
    rintro (heq | hmem)
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1r (h1 ▸ hz)
      · exact h5z h2
    · exact h1r (mem_of_mem_pathEdges hmem (by simp))
  have h01 : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) S₁ := by
    rw [Finset.disjoint_left]
    intro e he heS
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hout a₂ a₁ h2r (Ne.symm h12) (by rwa [Sym2.eq_swap] at heS)
    · exact hout a₂ a₃ h2r (Ne.symm h12) heS
    · exact hout a₃ a₄ h3r (Ne.symm h13) heS
    · exact hout a₄ a₅ h4r (Ne.symm h14) heS
  have h1D : Disjoint S₁ ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) := by
    rw [Finset.disjoint_right]
    intro e he heS
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hout a₃ a₁ h3r (Ne.symm h13) (by rwa [Sym2.eq_swap] at heS)
    · exact hout a₃ a₅ h3r (Ne.symm h13) heS
  have h1Z : Disjoint S₁ ({s(a₁, a₅)} : Finset (Sym2 V)) := by
    rw [Finset.disjoint_right]
    intro e he heS
    rw [Finset.mem_singleton] at he
    exact hZout (he ▸ heS)
  have h0F : Disjoint ({s(a₁, a₂), s(a₂, a₃), s(a₃, a₄), s(a₄, a₅)} : Finset (Sym2 V)) F := by
    refine Finset.disjoint_of_subset_left ?_ (hF.symm)
    intro e he
    refine Finset.mem_union_left _ ?_
    rw [hcycbig]
    exact Finset.mem_union_left _ he
  have hDF : Disjoint ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) F :=
    (Finset.disjoint_of_subset_right Finset.subset_union_right hF).symm
  have habs' : Absorbs G F (S₁ ∪ {s(a₁, a₅)}) := by rw [← hcycsmall]; exact habs
  rw [hcycbig]
  exact absorbs_shortenTriple h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hQ hG12 hG23 hG34 hG45
    habs' h01 h0F h1D h1Z hDF


/-! ### Lengthening a cycle by three -/

omit [Fintype V] in
/-- **The lengthening move.**  Two reserved triangles `{a, q, r}` and `{b, q, s}` sharing the hub
`q` absorb the config edge `ab`: the outer triangle `{a, b, q}` consumes `ab` together with the
two spokes `aq`, `bq`, and the residue is the path `a — r — q — s — b`, so the cycle gets three
edges longer.

Unlike the shortening move, this one is *cheap for a fixed reserved family*: only the hub `q` is
constrained (it has to carry a reserved triangle at `a` and one at `b`), while the two partners
`r`, `s` are whatever the reserved links of `a` and of `b` provide.  In the dense regime this
leaves `≍ ε²n` admissible hubs at every config edge. -/
theorem absorbs_lengthenEdge {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b q r s : V} {S₁ F : Finset (Sym2 V)}
    (hab : a ≠ b) (haq : a ≠ q) (har : a ≠ r) (has : a ≠ s)
    (hbq : b ≠ q) (hbr : b ≠ r) (hbs : b ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hQ1 : G.IsNClique 3 ({a, q, r} : Finset V)) (hQ2 : G.IsNClique 3 ({b, q, s} : Finset V))
    (hGab : G.Adj a b)
    (habs : Absorbs G F (S₁ ∪ {s(a, r), s(q, r), s(q, s), s(b, s)}))
    (h01 : Disjoint ({s(a, b)} : Finset (Sym2 V)) S₁)
    (h0F : Disjoint ({s(a, b)} : Finset (Sym2 V)) F)
    (h1D : Disjoint S₁ ({s(a, q), s(b, q)} : Finset (Sym2 V)))
    (h1Z : Disjoint S₁ ({s(a, r), s(q, r), s(q, s), s(b, s)} : Finset (Sym2 V)))
    (hDF : Disjoint ({s(a, q), s(b, q)} : Finset (Sym2 V)) F) :
    Absorbs G ((({s(a, q), s(b, q)} : Finset (Sym2 V)) ∪ {s(a, r), s(q, r), s(q, s), s(b, s)}) ∪ F)
      (({s(a, b)} : Finset (Sym2 V)) ∪ S₁) := by
  classical
  have h0D : Disjoint ({s(a, b)} : Finset (Sym2 V)) {s(a, q), s(b, q)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h0Z : Disjoint ({s(a, b)} : Finset (Sym2 V)) {s(a, r), s(q, r), s(q, s), s(b, s)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hDZ : Disjoint ({s(a, q), s(b, q)} : Finset (Sym2 V))
      {s(a, r), s(q, r), s(q, s), s(b, s)} := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hGaq : G.Adj a q := hQ1.1 (by simp) (by simp) haq
  have hGbq : G.Adj b q := hQ2.1 (by simp) (by simp) hbq
  have hAcl : G.IsNClique 3 ({a, b, q} : Finset V) :=
    isNClique_triple hab haq hbq hGab hGaq hGbq
  have htri0 : triEdges ({a, b, q} : Finset V) = {s(a, b), s(a, q), s(b, q)} :=
    triEdges_triple hab haq hbq
  have htri1 : triEdges ({a, q, r} : Finset V) = {s(a, q), s(a, r), s(q, r)} :=
    triEdges_triple haq har hqr
  have htri2 : triEdges ({b, q, s} : Finset V) = {s(b, q), s(b, s), s(q, s)} :=
    triEdges_triple hbq hbs hqs
  have hcons : TriDecomposable G
      (({s(a, b)} : Finset (Sym2 V)) ∪ {s(a, q), s(b, q)}) := by
    refine ⟨{{a, b, q}}, ?_, edgeDisjoint_singleton _, ?_⟩
    · intro t ht
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hAcl
    · rw [coveredEdges_singleton, htri0, triple_shuffle_head]
  have hT : TriDecomposable G
      (({s(a, q), s(b, q)} : Finset (Sym2 V)) ∪ {s(a, r), s(q, r), s(q, s), s(b, s)}) := by
    refine ⟨{{a, q, r}, {b, q, s}}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      exacts [hQ1, hQ2]
    · refine edgeDisjoint_pair ?_
      rw [htri1, htri2]
      simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · rw [coveredEdges_pair, htri1, htri2, union_shuffle_spokes]
  exact Absorbs.transform hcons hT habs h01 h0D h0Z h0F h1D h1Z hDZ hDF

/-! ### Reading the moves back as reserved families

Each move consumes a bounded family of reserved triangles; these lemmas identify the edges that
family covers, so that the `Absorbs`-level moves above can be fed back into
`LocalAbsorbable` — the shape in which `ChunkAbsorbing` consumes a reservation. -/

omit [Fintype V] in
/-- If the extra triangles `Q` cover exactly `T`, an absorption by `T ∪ coveredEdges P` is a local
absorption by the enlarged family `P ∪ Q`. -/
theorem localAbsorbable_of_absorbs_union (G : SimpleGraph V) [DecidableRel G.Adj]
    {P Q : Finset (Finset V)} {T S : Finset (Sym2 V)} (hQcov : coveredEdges Q = T)
    (h : Absorbs G (T ∪ coveredEdges P) S) : LocalAbsorbable G (P ∪ Q) S := by
  refine localAbsorbable_of_absorbs G ?_
  rw [show coveredEdges (P ∪ Q) = coveredEdges P ∪ coveredEdges Q by
      simp [coveredEdges, Finset.union_biUnion], hQcov, Finset.union_comm]
  exact h

omit [Fintype V] in
/-- The two co-apex triangles of the merging move cover the four spokes and the two new edges. -/
theorem coveredEdges_coapexPair {a b c d h : V} (hac : a ≠ c) (hah : a ≠ h) (hch : c ≠ h)
    (hbd : b ≠ d) (hbh : b ≠ h) (hdh : d ≠ h) :
    coveredEdges ({{a, c, h}, {b, d, h}} : Finset (Finset V))
      = ({s(a, h), s(b, h), s(c, h), s(d, h)} : Finset (Sym2 V)) ∪ {s(a, c), s(b, d)} := by
  rw [coveredEdges_pair, triEdges_triple hac hah hch, triEdges_triple hbd hbh hdh,
    union_shuffle_coapex]

omit [Fintype V] in
/-- The triangle of the shortening move covers the two chords and the new edge. -/
theorem coveredEdges_shortenTriangle {a₁ a₃ a₅ : V} (h13 : a₁ ≠ a₃) (h15 : a₁ ≠ a₅)
    (h35 : a₃ ≠ a₅) :
    coveredEdges ({{a₁, a₃, a₅}} : Finset (Finset V))
      = ({s(a₁, a₃), s(a₃, a₅)} : Finset (Sym2 V)) ∪ {s(a₁, a₅)} := by
  rw [coveredEdges_singleton, triEdges_triple h13 h15 h35, triple_shuffle]

omit [Fintype V] in
/-- The two triangles of the lengthening move cover the two spokes and the new path. -/
theorem coveredEdges_lengthenPair {a b q r s : V} (haq : a ≠ q) (har : a ≠ r) (hqr : q ≠ r)
    (hbq : b ≠ q) (hbs : b ≠ s) (hqs : q ≠ s) :
    coveredEdges ({{a, q, r}, {b, q, s}} : Finset (Finset V))
      = ({s(a, q), s(b, q)} : Finset (Sym2 V)) ∪ {s(a, r), s(q, r), s(q, s), s(b, s)} := by
  rw [coveredEdges_pair, triEdges_triple haq har hqr, triEdges_triple hbq hbs hqs,
    union_shuffle_spokes]

end Ax2.BKLO
