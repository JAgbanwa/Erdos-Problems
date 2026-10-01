import PaperIV.ExteriorTriangleLift
import PaperIV.PackingUnion

/-!
# RD09 Phase-I: the multi-host exterior triangle lift

`PaperIV.ExteriorTriangleLift` lifts one literal matching `E` of base edges over a single
exterior host `z` to a literal packing of `K3` pieces.  This module performs the
*multi-host* extension: a finite family of hosts `z i` with base matchings `E i`.

The core new content is genuine **cross-host resource disjointness**: two triangles built
over *different* hosts never share a physical edge resource (`PaperIV.Model.pieceEdges`),
even when their base matching edges share an exterior endpoint.  This is not a consequence
of any single-host statement, and it is deliberately *not* assumed: it is derived from

* `IsExteriorHub G (z i) (E i)` for each `i`,
* pairwise distinct hosts (`Function.Injective z`),
* core/exterior separation: every endpoint of every base edge avoids *all* hosts,
* pairwise disjoint base families `E i`.

From it we obtain the literal packing property of the full union, coverage of every base
edge, and the exact cardinality/gain ledger
`card = ∑ i, (E i).card` and `totalGain = 2 * ∑ i, (E i).card`.

Everything stays inside the literal resource semantics of `PaperIV.Model`.
-/

namespace PaperIV.MultiHostTriangleLift

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {z : I → V} {E : I → Finset (Sym2 V)}

/-- A finite family of exterior hubs with pairwise distinct hosts, base families that are
pairwise disjoint, and full core/exterior separation: no base endpoint is a host. -/
structure IsMultiExteriorHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : I → V) (E : I → Finset (Sym2 V)) : Prop where
  /-- each host is an exterior hub for its own base matching -/
  hub : ∀ i, IsExteriorHub G (z i) (E i)
  /-- the hosts are pairwise distinct -/
  hostInj : Function.Injective z
  /-- core/exterior separation: every endpoint of every base edge avoids every host -/
  exterior : ∀ i j, ∀ e ∈ E i, ∀ a ∈ e, a ≠ z j
  /-- the base families are pairwise disjoint -/
  baseDisjoint : ∀ i j, i ≠ j → Disjoint (E i) (E j)

namespace IsMultiExteriorHub

variable (h : IsMultiExteriorHub G z E)
include h

omit [Fintype I] [DecidableEq I] in
theorem host_ne_host {i j : I} (hij : i ≠ j) : z i ≠ z j := fun he => hij (h.hostInj he)

omit [Fintype I] [DecidableEq I] in
/-- A base edge of `E i` cannot also be a base edge of `E j` for `j ≠ i`. -/
theorem base_ne {i j : I} (hij : i ≠ j) {e f : Sym2 V} (he : e ∈ E i) (hf : f ∈ E j) :
    e ≠ f := by
  rintro rfl
  exact (Finset.disjoint_left.mp (h.baseDisjoint i j hij) he) hf

end IsMultiExteriorHub

omit [Fintype V] [DecidableEq V] in
/-- A non-loop edge is determined by any two distinct vertices it contains. -/
theorem sym2_eq_of_mem_of_mem {e : Sym2 V} {a b : V} (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) :
    e = s(a, b) := by
  induction e with
  | _ p q =>
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [Sym2.eq_swap]

omit [Fintype I] [DecidableEq I] in
/-- Cross-host vertex separation: a vertex shared by triangles over two distinct hosts is an
exterior vertex lying on *both* base edges.  In particular neither host is involved. -/
theorem mem_base_of_mem_triangle_inter (h : IsMultiExteriorHub G z E) {i j : I} (hij : i ≠ j)
    {e f : Sym2 V} (he : e ∈ E i) (hf : f ∈ E j) {x : V}
    (hxe : x ∈ triangle (z i) e) (hxf : x ∈ triangle (z j) f) : x ∈ e ∧ x ∈ f := by
  rw [mem_triangle] at hxe hxf
  rcases hxe with rfl | hxe
  · rcases hxf with hzz | hxf
    · exact absurd hzz (h.host_ne_host hij)
    · exact absurd rfl (h.exterior j i f hf _ hxf)
  · rcases hxf with rfl | hxf
    · exact absurd rfl (h.exterior i j e he _ hxe)
    · exact ⟨hxe, hxf⟩

omit [Fintype I] [DecidableEq I] in
/-- **Cross-host resource disjointness.**  Triangles built over two distinct hosts never
share a physical edge resource, even when their base edges share an exterior endpoint. -/
theorem pieceEdges_disjoint_cross (h : IsMultiExteriorHub G z E) {i j : I} (hij : i ≠ j)
    {e f : Sym2 V} (he : e ∈ E i) (hf : f ∈ E j) :
    Disjoint (pieceEdges (triangle (z i) e)) (pieceEdges (triangle (z j) f)) := by
  rw [Finset.disjoint_left]
  intro g hge hgf
  rw [mem_pieceEdges] at hge hgf
  induction g with
  | _ a b =>
    have hab : a ≠ b := by
      simpa [Sym2.isDiag_iff_proj_eq] using hge.2
    have ha := mem_base_of_mem_triangle_inter h hij he hf
      (hge.1 a (by simp)) (hgf.1 a (by simp))
    have hb := mem_base_of_mem_triangle_inter h hij he hf
      (hge.1 b (by simp)) (hgf.1 b (by simp))
    have hef : e = f := by
      rw [sym2_eq_of_mem_of_mem ha.1 hb.1 hab, sym2_eq_of_mem_of_mem ha.2 hb.2 hab]
    exact h.base_ne hij he hf hef

/-- The lifted family of literal triangles over the whole host family. -/
def multiLiftedPacking (z : I → V) (E : I → Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.biUnion fun i => liftedPacking (z i) (E i)

omit [Fintype V] [DecidableEq I] in
@[simp] theorem mem_multiLiftedPacking {s : Finset V} :
    s ∈ multiLiftedPacking z E ↔ ∃ i, ∃ e ∈ E i, triangle (z i) e = s := by
  simp [multiLiftedPacking]

omit [Fintype I] [DecidableEq I] in
/-- Cross-host resource disjointness, at the level of the lifted piece families. -/
theorem pieceEdges_disjoint_cross_pieces (h : IsMultiExteriorHub G z E) {i j : I} (hij : i ≠ j)
    {s t : Finset V} (hs : s ∈ liftedPacking (z i) (E i)) (ht : t ∈ liftedPacking (z j) (E j)) :
    Disjoint (pieceEdges s) (pieceEdges t) := by
  rw [mem_liftedPacking] at hs ht
  obtain ⟨e, he, rfl⟩ := hs
  obtain ⟨f, hf, rfl⟩ := ht
  exact pieceEdges_disjoint_cross h hij he hf

omit [Fintype I] [DecidableEq I] in
/-- The lifted families over distinct hosts are literally disjoint families of pieces. -/
theorem liftedPacking_disjoint (h : IsMultiExteriorHub G z E) {i j : I} (hij : i ≠ j) :
    Disjoint (liftedPacking (z i) (E i)) (liftedPacking (z j) (E j)) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  have hdisj := pieceEdges_disjoint_cross_pieces h hij hs hs'
  rw [mem_liftedPacking] at hs
  obtain ⟨e, he, rfl⟩ := hs
  have hmem : e ∈ pieceEdges (triangle (z i) e) :=
    base_mem_pieceEdges_triangle (h.hub i) he
  exact (Finset.disjoint_left.mp hdisj hmem) hmem

/-- **The multi-host lift is a literal packing of `G`.** -/
theorem isPacking_multiLiftedPacking (h : IsMultiExteriorHub G z E) :
    IsPacking G (multiLiftedPacking z E) := by
  constructor
  · intro s hs
    rw [mem_multiLiftedPacking] at hs
    obtain ⟨i, e, he, rfl⟩ := hs
    exact isPiece_triangle (h.hub i) he
  · intro s hs t ht hst
    rw [mem_multiLiftedPacking] at hs ht
    obtain ⟨i, e, he, rfl⟩ := hs
    obtain ⟨j, f, hf, rfl⟩ := ht
    by_cases hij : i = j
    · subst hij
      exact pieceEdges_disjoint (h.hub i) he hf fun hef => hst (by rw [hef])
    · exact pieceEdges_disjoint_cross h hij he hf

omit [Fintype V] [DecidableEq I] in
/-- The covered resource set of the multi-host lift is the union of the single-host ones. -/
theorem coveredEdges_multiLiftedPacking :
    coveredEdges (multiLiftedPacking z E)
      = Finset.univ.biUnion fun i => coveredEdges (liftedPacking (z i) (E i)) := by
  ext g
  simp only [mem_coveredEdges, Finset.mem_biUnion, mem_multiLiftedPacking, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨s, ⟨i, e, he, rfl⟩, hg⟩
    exact ⟨i, triangle (z i) e, mem_liftedPacking.mpr ⟨e, he, rfl⟩, hg⟩
  · rintro ⟨i, s, hs, hg⟩
    rw [mem_liftedPacking] at hs
    obtain ⟨e, he, rfl⟩ := hs
    exact ⟨triangle (z i) e, ⟨i, e, he, rfl⟩, hg⟩

omit [DecidableEq I] in
/-- Every base edge of every host is covered by the multi-host lift. -/
theorem base_mem_coveredEdges_multi (h : IsMultiExteriorHub G z E) {i : I} {e : Sym2 V}
    (he : e ∈ E i) : e ∈ coveredEdges (multiLiftedPacking z E) := by
  rw [mem_coveredEdges]
  exact ⟨triangle (z i) e, mem_multiLiftedPacking.mpr ⟨i, e, he, rfl⟩,
    base_mem_pieceEdges_triangle (h.hub i) he⟩

omit [DecidableEq I] in
theorem base_subset_coveredEdges_multi (h : IsMultiExteriorHub G z E) (i : I) :
    E i ⊆ coveredEdges (multiLiftedPacking z E) := fun _ he => base_mem_coveredEdges_multi h he

omit [DecidableEq I] in
/-- All base edges together are covered. -/
theorem biUnion_base_subset_coveredEdges (h : IsMultiExteriorHub G z E) :
    (Finset.univ.biUnion E) ⊆ coveredEdges (multiLiftedPacking z E) := by
  intro e he
  rw [Finset.mem_biUnion] at he
  obtain ⟨i, -, he⟩ := he
  exact base_mem_coveredEdges_multi h he

omit [DecidableEq I] in
/-- **Cardinality ledger.**  The multi-host lift has exactly `∑ i, (E i).card` pieces. -/
theorem card_multiLiftedPacking (h : IsMultiExteriorHub G z E) :
    (multiLiftedPacking z E).card = ∑ i, (E i).card := by
  rw [multiLiftedPacking, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ => card_liftedPacking (h.hub i)
  · intro i _ j _ hij
    exact liftedPacking_disjoint h hij

omit [DecidableEq I] in
/-- **Gain ledger.**  Every piece is a `K3`, so the total gain is `2 * ∑ i, (E i).card`. -/
theorem totalGain_multiLiftedPacking (h : IsMultiExteriorHub G z E) :
    totalGain (multiLiftedPacking z E) = 2 * ∑ i, (E i).card := by
  have hgain : ∀ s ∈ multiLiftedPacking z E, gainOf s = 2 := by
    intro s hs
    rw [mem_multiLiftedPacking] at hs
    obtain ⟨i, e, he, rfl⟩ := hs
    exact gainOf_of_card_three
      (card_triangle (not_isDiag_of_mem_graphEdges G ((h.hub i).edges e he))
        (notMem_of_hub (h.hub i) he))
  rw [totalGain, Finset.sum_congr rfl hgain, Finset.sum_const, card_multiLiftedPacking h,
    smul_eq_mul, Nat.mul_comm]

omit [DecidableEq I] in
/-- The exact ledger identity available from the hypotheses:
`totalGain = 2 * card`, both pinned to `∑ i, (E i).card`. -/
theorem totalGain_eq_two_mul_card (h : IsMultiExteriorHub G z E) :
    totalGain (multiLiftedPacking z E) = 2 * (multiLiftedPacking z E).card
      ∧ (multiLiftedPacking z E).card = ∑ i, (E i).card
      ∧ totalGain (multiLiftedPacking z E) = 2 * ∑ i, (E i).card := by
  refine ⟨?_, card_multiLiftedPacking h, totalGain_multiLiftedPacking h⟩
  rw [card_multiLiftedPacking h, totalGain_multiLiftedPacking h]

/-- Number of covered resources: three edges per piece, all distinct. -/
theorem card_coveredEdges_multiLiftedPacking (h : IsMultiExteriorHub G z E) :
    (coveredEdges (multiLiftedPacking z E)).card = 3 * ∑ i, (E i).card := by
  have hpack := isPacking_multiLiftedPacking h
  have hcard : (coveredEdges (multiLiftedPacking z E)).card
      = ∑ s ∈ multiLiftedPacking z E, (pieceEdges s).card :=
    Finset.card_biUnion fun s hs t ht hst => hpack.edgeDisjoint s hs t ht hst
  have hsum : ∀ s ∈ multiLiftedPacking z E, (pieceEdges s).card = 3 := by
    intro s hs
    have hpiece := hpack.pieces s hs
    have : gainOf s = 2 := by
      rw [mem_multiLiftedPacking] at hs
      obtain ⟨i, e, he, rfl⟩ := hs
      exact gainOf_of_card_three
        (card_triangle (not_isDiag_of_mem_graphEdges G ((h.hub i).edges e he))
          (notMem_of_hub (h.hub i) he))
    rw [hpiece.card_pieceEdges_eq, this]
  rw [hcard, Finset.sum_congr rfl hsum, Finset.sum_const, card_multiLiftedPacking h,
    smul_eq_mul, Nat.mul_comm]

/-- If the multi-host lift happens to cover all of `G`, it is an exact literal partition;
this is the Phase-II completion hook. -/
theorem isExactPartition_of_covers (h : IsMultiExteriorHub G z E)
    (hcov : coveredEdges (multiLiftedPacking z E) = graphEdges G) :
    IsExactPartition G (multiLiftedPacking z E) :=
  ⟨isPacking_multiLiftedPacking h, hcov⟩

/-! ### Assembling the multi-host Phase-I lift with a further phase

Reuse of `PaperIV.PackingUnion`: the multi-host lift can be glued to any other literal
packing whose resources are disjoint from it. -/

theorem isPacking_union_phase (h : IsMultiExteriorHub G z E) {Q : Finset (Finset V)}
    (hQ : IsPacking G Q)
    (hcross : ∀ s ∈ multiLiftedPacking z E, ∀ t ∈ Q, Disjoint (pieceEdges s) (pieceEdges t)) :
    IsPacking G (multiLiftedPacking z E ∪ Q) :=
  PaperIV.PackingUnion.isPacking_union (isPacking_multiLiftedPacking h) hQ hcross

theorem isExactPartition_union_phase (h : IsMultiExteriorHub G z E) {Q : Finset (Finset V)}
    (hQ : IsPacking G Q)
    (hcross : ∀ s ∈ multiLiftedPacking z E, ∀ t ∈ Q, Disjoint (pieceEdges s) (pieceEdges t))
    (hcov : coveredEdges (multiLiftedPacking z E) ∪ coveredEdges Q = graphEdges G) :
    IsExactPartition G (multiLiftedPacking z E ∪ Q) :=
  PaperIV.PackingUnion.isExactPartition_of_union (isPacking_multiLiftedPacking h) hQ hcross hcov

/-! ### Non-vacuity

A concrete two-host instance in which the two base edges `s(2,3)` and `s(3,4)` *share* the
exterior endpoint `3`.  All hypotheses hold, so the cross-host disjointness theorem above
really does apply in the situation it is designed for. -/

namespace Example

/-- The complete graph on six vertices. -/
def graph : SimpleGraph (Fin 6) := ⊤

instance : DecidableRel graph.Adj := fun a b => by unfold graph; infer_instance

/-- Two distinct hosts. -/
def hosts : Fin 2 → Fin 6 := ![0, 1]

/-- Their base matchings share the exterior endpoint `3`. -/
def bases : Fin 2 → Finset (Sym2 (Fin 6)) := ![{s(2, 3)}, {s(3, 4)}]

theorem isMultiExteriorHub_example : IsMultiExteriorHub graph hosts bases := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      exact ⟨by decide, by unfold IsLiteralMatching; decide, by decide⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [hosts]
  · decide
  · decide

theorem card_example : (multiLiftedPacking hosts bases).card = 2 := by decide

theorem isPacking_example : IsPacking graph (multiLiftedPacking hosts bases) :=
  isPacking_multiLiftedPacking isMultiExteriorHub_example

end Example

end PaperIV.MultiHostTriangleLift


