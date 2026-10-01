import PaperIV.Model

/-!
# RD09 Phase-I: the exterior triangle lift

Given a literal matching `E` of non-loop edges of a finite simple graph `G` and a common
exterior host vertex `z` adjacent to every endpoint of every edge of `E`, the family of
literal triangles `{z} ∪ e.toFinset` (`e ∈ E`) is a literal `PaperIV.Model.IsPacking` of
`K3` pieces whose covered edges contain all of `E`, and whose cardinality is `E.card`.

Everything stays inside the literal resource model of `PaperIV.Model`: pieces are honest
`Finset V`, and edges are honest elements of `Sym2 V`.
-/

namespace PaperIV.ExteriorTriangleLift

open Finset PaperIV.Model

variable {V : Type*} [DecidableEq V]

/-- `E` is a *literal matching*: distinct members have disjoint endpoint sets. -/
def IsLiteralMatching (E : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e.toFinset f.toFinset

/-- `z` is an *exterior hub* for the edge family `E` in `G`. -/
structure IsExteriorHub [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (z : V)
    (E : Finset (Sym2 V)) : Prop where
  edges : ∀ e ∈ E, e ∈ graphEdges G
  matching : IsLiteralMatching E
  hubAdj : ∀ e ∈ E, ∀ a ∈ e, G.Adj z a

/-- The literal triangle built from the host `z` and the edge `e`. -/
def triangle (z : V) (e : Sym2 V) : Finset V := {z} ∪ e.toFinset

@[simp] theorem mem_triangle {z x : V} {e : Sym2 V} :
    x ∈ triangle z e ↔ x = z ∨ x ∈ e := by
  simp [triangle, Sym2.mem_toFinset]

/-- The two endpoints of a non-loop edge give a two-element triangle base. -/
theorem card_triangle {z : V} {e : Sym2 V} (hd : ¬ e.IsDiag) (hz : z ∉ e) :
    (triangle z e).card = 3 := by
  have hzf : z ∉ e.toFinset := by simpa [Sym2.mem_toFinset] using hz
  have h2 : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e hd
  rw [triangle, Finset.singleton_union, Finset.card_insert_of_notMem hzf, h2]

section Basic

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem adj_of_mem_edge {e : Sym2 V} (he : e ∈ graphEdges G) {x y : V}
    (hx : x ∈ e) (hy : y ∈ e) (hxy : x ≠ y) : G.Adj x y := by
  rw [mem_graphEdges] at he
  induction e with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    simp only [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp_all [he.symm]

end Basic

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {z : V} {E : Finset (Sym2 V)}

theorem notMem_of_hub (h : IsExteriorHub G z E) {e : Sym2 V} (he : e ∈ E) : z ∉ e := by
  intro hz
  exact (h.hubAdj e he z hz).ne rfl

/-- Each constructed triangle is a literal `K3` piece of `G`. -/
theorem isPiece_triangle (h : IsExteriorHub G z E) {e : Sym2 V} (he : e ∈ E) :
    IsPiece G (triangle z e) := by
  refine ⟨?_, ⟨PieceKind.K3, ?_⟩⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_triangle] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact h.hubAdj e he y hy
    · rcases hy with rfl | hy
      · exact (h.hubAdj e he x hx).symm
      · exact adj_of_mem_edge (h.edges e he) hx hy hxy
  · exact card_triangle (not_isDiag_of_mem_graphEdges G (h.edges e he)) (notMem_of_hub h he)

/-- Two triangles over distinct matched edges meet only in the host `z`. -/
theorem triangle_inter (h : IsExteriorHub G z E) {e f : Sym2 V} (he : e ∈ E) (hf : f ∈ E)
    (hef : e ≠ f) : triangle z e ∩ triangle z f = {z} := by
  have hdisj := h.matching e he f hf hef
  ext x
  simp only [Finset.mem_inter, mem_triangle, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | hx, hy | hy⟩
    · exact hx
    · exact hx
    · exact hy
    · exact absurd (Sym2.mem_toFinset.mpr hy)
        (Finset.disjoint_left.mp hdisj (Sym2.mem_toFinset.mpr hx))
  · rintro rfl
    exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- Distinct base edges give edge-disjoint triangle pieces. -/
theorem pieceEdges_disjoint (h : IsExteriorHub G z E) {e f : Sym2 V} (he : e ∈ E) (hf : f ∈ E)
    (hef : e ≠ f) : Disjoint (pieceEdges (triangle z e)) (pieceEdges (triangle z f)) := by
  rw [Finset.disjoint_left]
  intro g hge hgf
  rw [mem_pieceEdges] at hge hgf
  have hsub : ∀ a ∈ g, a ∈ triangle z e ∩ triangle z f := fun a ha =>
    Finset.mem_inter.mpr ⟨hge.1 a ha, hgf.1 a ha⟩
  rw [triangle_inter h he hf hef] at hsub
  refine hge.2 ?_
  induction g with
  | _ a b =>
    have ha : a = z := Finset.mem_singleton.mp (hsub a (by simp))
    have hb : b = z := Finset.mem_singleton.mp (hsub b (by simp))
    simp [Sym2.isDiag_iff_proj_eq, ha, hb]

/-- The triangle construction is injective on a literal matching. -/
theorem triangle_injOn (h : IsExteriorHub G z E) :
    Set.InjOn (triangle z) (E : Set (Sym2 V)) := by
  intro e he f hf hef
  by_contra hne
  have h1 : triangle z e ∩ triangle z f = {z} :=
    triangle_inter h (by simpa using he) (by simpa using hf) hne
  rw [hef, Finset.inter_self] at h1
  have hcard : (triangle z f).card = 3 :=
    card_triangle (not_isDiag_of_mem_graphEdges G (h.edges f (by simpa using hf)))
      (notMem_of_hub h (by simpa using hf))
  rw [h1] at hcard
  simp at hcard

/-- The lifted family of literal triangles. -/
def liftedPacking (z : V) (E : Finset (Sym2 V)) : Finset (Finset V) := E.image (triangle z)

omit [Fintype V] in
@[simp] theorem mem_liftedPacking {s : Finset V} :
    s ∈ liftedPacking z E ↔ ∃ e ∈ E, triangle z e = s := by
  simp [liftedPacking]

/-- The lifted family is a literal packing of `G`. -/
theorem isPacking_liftedPacking (h : IsExteriorHub G z E) :
    IsPacking G (liftedPacking z E) := by
  constructor
  · intro s hs
    rw [mem_liftedPacking] at hs
    obtain ⟨e, he, rfl⟩ := hs
    exact isPiece_triangle h he
  · intro s hs t ht hst
    rw [mem_liftedPacking] at hs ht
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨f, hf, rfl⟩ := ht
    exact pieceEdges_disjoint h he hf fun hef => hst (by rw [hef])

/-- A base edge is a literal edge of its own triangle piece. -/
theorem base_mem_pieceEdges_triangle (h : IsExteriorHub G z E) {e : Sym2 V} (he : e ∈ E) :
    e ∈ pieceEdges (triangle z e) := by
  rw [mem_pieceEdges]
  exact ⟨fun a ha => mem_triangle.mpr (Or.inr ha),
    not_isDiag_of_mem_graphEdges G (h.edges e he)⟩

/-- Every base edge is covered by the lifted packing. -/
theorem base_mem_coveredEdges (h : IsExteriorHub G z E) {e : Sym2 V} (he : e ∈ E) :
    e ∈ coveredEdges (liftedPacking z E) := by
  rw [mem_coveredEdges]
  exact ⟨triangle z e, mem_liftedPacking.mpr ⟨e, he, rfl⟩, base_mem_pieceEdges_triangle h he⟩

theorem base_subset_coveredEdges (h : IsExteriorHub G z E) :
    E ⊆ coveredEdges (liftedPacking z E) := fun _ he => base_mem_coveredEdges h he

/-- The lifted family has exactly `E.card` pieces. -/
theorem card_liftedPacking (h : IsExteriorHub G z E) :
    (liftedPacking z E).card = E.card :=
  Finset.card_image_of_injOn (triangle_injOn h)

/-- The total gain of the lift is `2 * E.card`: each `K3` piece contributes gain `2`. -/
theorem totalGain_liftedPacking (h : IsExteriorHub G z E) :
    totalGain (liftedPacking z E) = 2 * E.card := by
  have : ∀ s ∈ liftedPacking z E, gainOf s = 2 := by
    intro s hs
    rw [mem_liftedPacking] at hs
    obtain ⟨e, he, rfl⟩ := hs
    exact gainOf_of_card_three
      (card_triangle (not_isDiag_of_mem_graphEdges G (h.edges e he)) (notMem_of_hub h he))
  rw [totalGain, Finset.sum_congr rfl this, Finset.sum_const, card_liftedPacking h,
    smul_eq_mul, Nat.mul_comm]

end PaperIV.ExteriorTriangleLift
