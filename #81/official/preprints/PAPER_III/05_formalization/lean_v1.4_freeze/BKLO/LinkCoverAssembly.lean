/-
# Assembling a **simultaneous** link cover from a system of pairings.

`BKLO.isLinkCoverR_of_pairing` covers the link of a *single* outer vertex `u ∈ W \ W'`: given a
fixed-point-free involution `g` pairing up `X u` by `F`-edges avoiding `W''`, the triangles
`{u, a, g a}` form a link cover of the one-vertex system.  The reservoir clause
`BKLO.ReservoirClauseR`, however, asks for **one** edge-disjoint family covering the crossing edges
of *all* outer vertices at once, and the single-vertex covers cannot simply be superposed: two
outer vertices may be handed the same edge inside `W'`, and the damage at a vertex of `W'`
accumulates over all the outer vertices whose link uses it.

This file isolates exactly what has to be true for the superposition to work, as the predicate
`BKLO.IsPairedLinkSystem`: a *system* of pairings `g u`, one for each outer vertex `u`, which is

* pointwise legitimate — `g u` is a fixed-point-free involution of `X u`, its pairs are `F`-edges,
  and no pair lies inside the protected level `W''`;
* **globally edge-disjoint** — the pair `s(a, g u a)` determines the outer vertex `u`;
* **load-bounded** — each `v ∈ W'` lies in at most `γ|W'|` of the links `X u`, and in at most
  `γ|W''|` of them is its partner inside `W''`.

`BKLO.isLinkCoverR_of_pairedLinkSystem` then produces the simultaneous cover: the triangles
`{u, a, g u a}`, for all `u` and all `a ∈ X u` at once, form a family satisfying
`BKLO.IsLinkCoverR` in full, damage bounds included.  It is the multi-vertex form of
`BKLO.isLinkCoverR_of_pairing`, and it reduces the link-covering clause of the reservoir to a
statement about pairings only, with no triangle families in it.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirRepairedSat

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Systems of pairings -/

/-- **A paired link system.**  For each outer vertex `u ∈ D` the map `g u` pairs up the link `X u`
by `F`-edges; the pairs of different outer vertices are different edges; and the loads of the
system at the vertices of `W'` are bounded by `γ|W'|`, resp. `γ|W''|` for the part running into the
protected level. -/
structure IsPairedLinkSystem (F : Finset (Sym2 V)) (W' W'' D : Finset V) (X : V → Finset V)
    (γ : ℝ) (g : V → V → V) : Prop where
  /-- `g u` maps the link of `u` to itself. -/
  mem : ∀ u ∈ D, ∀ a ∈ X u, g u a ∈ X u
  /-- `g u` is an involution on the link of `u`. -/
  invol : ∀ u ∈ D, ∀ a ∈ X u, g u (g u a) = a
  /-- `g u` has no fixed point on the link of `u`. -/
  ne : ∀ u ∈ D, ∀ a ∈ X u, g u a ≠ a
  /-- the pairs are edges of `F`. -/
  edge : ∀ u ∈ D, ∀ a ∈ X u, s(a, g u a) ∈ F
  /-- no pair lies inside the protected level. -/
  avoid : ∀ u ∈ D, ∀ a ∈ X u, a ∉ W'' ∨ g u a ∉ W''
  /-- the pairs of different outer vertices are different edges. -/
  distinct : ∀ u ∈ D, ∀ a ∈ X u, ∀ v ∈ D, ∀ b ∈ X v, s(a, g u a) = s(b, g v b) → u = v
  /-- each vertex of `W'` belongs to at most `γ|W'|` of the links. -/
  load : ∀ v ∈ W', ((D.filter (fun u => v ∈ X u)).card : ℝ) ≤ γ * (W'.card : ℝ)
  /-- each vertex of `W'` is paired into `W''` at most `γ|W''|` times. -/
  loadInner : ∀ v ∈ W', ((D.filter (fun u => v ∈ X u ∧ g u v ∈ W'')).card : ℝ)
    ≤ γ * (W''.card : ℝ)

section Assembly

variable {F : Finset (Sym2 V)} {W' W'' D : Finset V} {X : V → Finset V} {γ : ℝ} {g : V → V → V}

/-- The triangle family attached to a system of pairings: `{u, a, g u a}` for every outer vertex
`u ∈ D` and every `a ∈ X u`. -/
def pairTriangles (D : Finset V) (X : V → Finset V) (g : V → V → V) : Finset (Finset V) :=
  D.biUnion (fun u => (X u).image (fun a => ({u, a, g u a} : Finset V)))

theorem mem_pairTriangles {t : Finset V} :
    t ∈ pairTriangles D X g ↔ ∃ u ∈ D, ∃ a ∈ X u, t = ({u, a, g u a} : Finset V) := by
  simp only [pairTriangles, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
  · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩

/-- The three edges of a triangle of the family. -/
theorem cliqueEdges_pairTriangle (hDW' : ∀ u ∈ D, u ∉ W') (hXW' : ∀ u ∈ D, X u ⊆ W')
    (h : IsPairedLinkSystem F W' W'' D X γ g) {u : V} (hu : u ∈ D) {a : V} (ha : a ∈ X u) :
    cliqueEdges ({u, a, g u a} : Finset V) = {s(u, a), s(u, g u a), s(a, g u a)} := by
  have h1 : u ≠ a := fun hh => hDW' u hu (hh ▸ hXW' u hu ha)
  have h2 : u ≠ g u a := fun hh => hDW' u hu (hh ▸ hXW' u hu (h.mem u hu a ha))
  have h3 : a ≠ g u a := fun hh => h.ne u hu a ha hh.symm
  exact cliqueEdges_tripleV h1 h2 h3

/-- Every edge of a triangle of the family is either a crossing edge of the system at `u`, or the
pair edge inside `W'`. -/
theorem mem_cliqueEdges_pairTriangle (hDW' : ∀ u ∈ D, u ∉ W') (hXW' : ∀ u ∈ D, X u ⊆ W')
    (h : IsPairedLinkSystem F W' W'' D X γ g) {u : V} (hu : u ∈ D) {a : V} (ha : a ∈ X u)
    {e : Sym2 V} (he : e ∈ cliqueEdges ({u, a, g u a} : Finset V)) :
    (∃ x ∈ X u, (x = a ∨ x = g u a) ∧ e = s(u, x)) ∨ e = s(a, g u a) := by
  rw [cliqueEdges_pairTriangle hDW' hXW' h hu ha] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact Or.inl ⟨a, ha, Or.inl rfl, rfl⟩
  · exact Or.inl ⟨g u a, h.mem u hu a ha, Or.inr rfl, rfl⟩
  · exact Or.inr rfl

/-- Two triangles of the family that share an edge are equal. -/
theorem pairTriangle_eq_of_common_edge (hDW' : ∀ u ∈ D, u ∉ W') (hXW' : ∀ u ∈ D, X u ⊆ W')
    (h : IsPairedLinkSystem F W' W'' D X γ g) {u : V} (hu : u ∈ D) {a : V} (ha : a ∈ X u)
    {v : V} (hv : v ∈ D) {b : V} (hb : b ∈ X v) {e : Sym2 V}
    (he : e ∈ cliqueEdges ({u, a, g u a} : Finset V))
    (he' : e ∈ cliqueEdges ({v, b, g v b} : Finset V)) :
    ({u, a, g u a} : Finset V) = ({v, b, g v b} : Finset V) := by
  classical
  -- the pair edges of the two triangles coincide, and then so do the triangles
  have key : u = v ∧ s(a, g u a) = s(b, g v b) := by
    rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha he with ⟨x, hx, hxa, rfl⟩ | hpe
    · rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hv hb he' with ⟨y, hy, hyb, hxy⟩ | hpe'
      · -- two crossing edges: same outer vertex, same partner
        rw [Sym2.eq_iff] at hxy
        have huv : u = v ∧ x = y := by
          rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, h2⟩
          · exact absurd (h1 ▸ hXW' v hv hy) (hDW' u hu)
        obtain ⟨rfl, rfl⟩ := huv
        refine ⟨rfl, ?_⟩
        exact pair_sym2_eq_of_common (X := X u) (g := g u) (h.invol u hu) ha hb hxa hyb
      · -- a crossing edge equal to a pair edge inside `W'`
        exfalso
        have hmem : u ∈ s(b, g v b) := by rw [← hpe']; simp
        rcases Sym2.mem_iff.1 hmem with heq | heq
        · exact hDW' u hu (by rw [heq]; exact hXW' v hv hb)
        · exact hDW' u hu (by rw [heq]; exact hXW' v hv (h.mem v hv b hb))
    · rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hv hb he' with ⟨y, hy, hyb, hxy⟩ | hpe'
      · exfalso
        have hmem : v ∈ s(a, g u a) := by rw [← hpe, hxy]; simp
        rcases Sym2.mem_iff.1 hmem with heq | heq
        · exact hDW' v hv (by rw [heq]; exact hXW' u hu ha)
        · exact hDW' v hv (by rw [heq]; exact hXW' u hu (h.mem u hu a ha))
      · have hpair : s(a, g u a) = s(b, g v b) := by rw [← hpe, hpe']
        exact ⟨h.distinct u hu a ha v hv b hb hpair, hpair⟩
  obtain ⟨rfl, hpair⟩ := key
  rw [Sym2.eq_iff] at hpair
  rcases hpair with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rw [h1]
  · ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [Or.inl rfl, Or.inr (Or.inr h1), Or.inr (Or.inl h2)]
    · rintro (rfl | rfl | rfl)
      exacts [Or.inl rfl, Or.inr (Or.inr h2.symm), Or.inr (Or.inl h1.symm)]

/-- **The simultaneous link cover.**  A system of pairings, edge-disjoint across the outer vertices
and load-bounded at the vertices of `W'`, assembles into a single family of triangles covering the
crossing edges of *all* outer vertices at once, in the strong (repaired) sense
`BKLO.IsLinkCoverR`. -/
theorem isLinkCoverR_of_pairedLinkSystem (hW'' : W'' ⊆ W') (hDW' : ∀ u ∈ D, u ∉ W')
    (hXW' : ∀ u ∈ D, X u ⊆ W') (hXF : ∀ u ∈ D, ∀ a ∈ X u, s(u, a) ∈ F)
    (h : IsPairedLinkSystem F W' W'' D X γ g) :
    ∃ Q : Finset (Finset V), IsLinkCoverR F W' W'' D X γ Q := by
  classical
  refine ⟨pairTriangles D X g, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- every member is a triangle
    intro t ht
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
    have h1 : u ≠ a := fun hh => hDW' u hu (hh ▸ hXW' u hu ha)
    have h2 : u ≠ g u a := fun hh => hDW' u hu (hh ▸ hXW' u hu (h.mem u hu a ha))
    have h3 : a ≠ g u a := fun hh => h.ne u hu a ha hh.symm
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]
  · -- all edges lie in `F`
    intro t ht
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
    intro e he
    rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha he with ⟨x, hx, -, rfl⟩ | rfl
    · exact hXF u hu x hx
    · exact h.edge u hu a ha
  · -- the triangles are pairwise edge-disjoint
    intro t ht t' ht' hne
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
    obtain ⟨v, hv, b, hb, rfl⟩ := mem_pairTriangles.1 ht'
    refine Finset.disjoint_left.2 fun e he he' => hne ?_
    exact pairTriangle_eq_of_common_edge hDW' hXW' h hu ha hv hb he he'
  · -- the prescribed crossing edges are covered
    intro e he
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_crossStars.1 he
    refine Finset.mem_biUnion.2 ⟨{u, a, g u a}, mem_pairTriangles.2 ⟨u, hu, a, ha, rfl⟩, ?_⟩
    rw [cliqueEdges_pairTriangle hDW' hXW' h hu ha]
    simp
  · -- only crossing edges of the system and edges inside `W'` are used
    intro e he
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
    rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha het with ⟨x, hx, -, rfl⟩ | rfl
    · exact Finset.mem_union_left _ (crossStars_mem hu hx)
    · refine Finset.mem_union_right _ (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        exacts [hXW' u hu ha, hXW' u hu (h.mem u hu a ha)]
      · have h3 : a ≠ g u a := fun hh => h.ne u hu a ha hh.symm
        simpa [Sym2.isDiag_iff_proj_eq] using h3
  · -- no edge inside `W''` is used
    refine Finset.disjoint_left.2 fun e he he'' => ?_
    obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
    obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
    have hmem := (mem_cliqueEdgesV.1 he'').1
    rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha het with ⟨x, hx, -, rfl⟩ | rfl
    · exact hDW' u hu (hW'' (hmem u (by simp)))
    · rcases h.avoid u hu a ha with hna | hng
      · exact hna (hmem a (by simp))
      · exact hng (hmem (g u a) (by simp))
  · -- the damage inside `W'`
    intro v hv
    have hsub : (famEdges (pairTriangles D X g) ∩ cliqueEdges W').filter (fun e => v ∈ e)
        ⊆ (D.filter (fun u => v ∈ X u)).image (fun u => s(v, g u v)) := by
      intro e he
      obtain ⟨he1, hve⟩ := Finset.mem_filter.1 he
      obtain ⟨hefam, heW'⟩ := Finset.mem_inter.1 he1
      obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hefam
      obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
      rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha het with ⟨x, hx, -, rfl⟩ | rfl
      · exact absurd ((mem_cliqueEdgesV.1 heW').1 u (by simp)) (hDW' u hu)
      · have hvmem : v ∈ X u ∧ s(a, g u a) = s(v, g u v) := by
          rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact ⟨ha, rfl⟩
          · refine ⟨h.mem u hu a ha, ?_⟩
            rw [h.invol u hu a ha, Sym2.eq_swap]
        exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, hvmem.1⟩, hvmem.2.symm⟩
    calc (edeg (famEdges (pairTriangles D X g) ∩ cliqueEdges W') v : ℝ)
        ≤ (((D.filter (fun u => v ∈ X u)).image (fun u => s(v, g u v))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((D.filter (fun u => v ∈ X u)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ γ * (W'.card : ℝ) := h.load v hv
  · -- the damage at the scale of `W''`
    intro v hv
    have hsub : resLink (famEdges (pairTriangles D X g)) W'' v
        ⊆ (D.filter (fun u => v ∈ X u ∧ g u v ∈ W'')).image (fun u => g u v) := by
      intro c hc
      obtain ⟨hcW'', hce⟩ := mem_resLink.1 hc
      obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hce
      obtain ⟨u, hu, a, ha, rfl⟩ := mem_pairTriangles.1 ht
      rcases mem_cliqueEdges_pairTriangle hDW' hXW' h hu ha het with ⟨x, hx, -, hxe⟩ | hpe
      · exfalso
        have : u ∈ s(v, c) := by rw [hxe]; simp
        rcases Sym2.mem_iff.1 this with rfl | rfl
        · exact hDW' u hu hv
        · exact hDW' u hu (hW'' hcW'')
      · have hvmem : v ∈ X u ∧ s(a, g u a) = s(v, g u v) := by
          have hvin : v ∈ s(a, g u a) := by rw [← hpe]; simp
          rcases Sym2.mem_iff.1 hvin with rfl | rfl
          · exact ⟨ha, rfl⟩
          · exact ⟨h.mem u hu a ha, by rw [h.invol u hu a ha]; exact Sym2.eq_swap⟩
        have hcg : c = g u v := by
          have hs : s(v, c) = s(v, g u v) := by rw [hpe]; exact hvmem.2
          rcases Sym2.eq_iff.1 hs with ⟨-, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · rw [h2]; exact h1
        subst hcg
        exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, hvmem.1, hcW''⟩, rfl⟩
    calc ((resLink (famEdges (pairTriangles D X g)) W'' v).card : ℝ)
        ≤ (((D.filter (fun u => v ∈ X u ∧ g u v ∈ W'')).image (fun u => g u v)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((D.filter (fun u => v ∈ X u ∧ g u v ∈ W'')).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ γ * (W''.card : ℝ) := h.loadInner v hv

end Assembly

end BKLO
