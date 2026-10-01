import Contrib.SpreadMatchingDirac
import PaperIV.ExteriorTriangleLift

/-!
# Deterministic spread absorption by literal triangles

This module adapts the spread perfect-matching theorem to the physical resource
model of Paper IV.  It selects a low-conflict matching and lifts every selected
edge to a literal triangle through a common exterior host.
-/

namespace PaperIV.SpreadAbsorption

open Finset PaperIV.Model PaperIV.ExteriorTriangleLift

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A literal partner certificate on `N`. -/
structure Certificate (G : SimpleGraph V) (N : Finset V) where
  partner : V → V
  mapsTo : ∀ a ∈ N, partner a ∈ N
  invol : ∀ a ∈ N, partner (partner a) = a
  ne : ∀ a ∈ N, partner a ≠ a
  adj : ∀ a ∈ N, G.Adj a (partner a)

/-- Dirac's hypothesis produces a partner certificate. -/
theorem exists_certificate {N : Finset V} {t : ℕ} (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card) :
    ∃ C : Certificate G N, True := by
  obtain ⟨f, hmap, hinv, hne, hadj⟩ :=
    SimpleGraph.exists_involution_adj (G := G) heven
      (fun v hv => (Nat.le_add_right _ t).trans (hdeg v hv))
  exact ⟨⟨f, hmap, hinv, hne, hadj⟩, trivial⟩

/-- The spread theorem produces a certificate with controlled oriented cost. -/
theorem exists_lowConflict_certificate {N : Finset V} {t : ℕ} (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (bad : V → V → ℝ) (hbad : ∀ y z, 0 ≤ bad y z) :
    ∃ C : Certificate G N,
      ∑ y ∈ N, bad y (C.partner y) ≤
        (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ z ∈ N, bad y z := by
  obtain ⟨f, hmap, hinv, hne, hadj, hcost⟩ :=
    SimpleGraph.exists_spread_involution (G := G) heven hdeg bad hbad
  exact ⟨⟨f, hmap, hinv, hne, hadj⟩, hcost⟩

/-- The unoriented physical edge family selected by a certificate. -/
def matchingEdges {N : Finset V} (C : Certificate G N) : Finset (Sym2 V) :=
  N.image fun y => s(y, C.partner y)

/-- Partner edges form a literal matching. -/
theorem matchingEdges_isLiteralMatching {N : Finset V} (C : Certificate G N) :
    IsLiteralMatching (matchingEdges C) := by
  intro e he f hf hef
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
  rw [Finset.disjoint_left]
  intro x hxa hxb
  simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hxa hxb
  apply hef
  rw [Sym2.eq_iff]
  rcases hxa with hxa | hxa <;> rcases hxb with hxb | hxb
  · have hab : a = b := hxa.symm.trans hxb
    exact Or.inl ⟨hab, by rw [hab]⟩
  · have hab : a = C.partner b := hxa.symm.trans hxb
    have hp : C.partner a = b := by rw [hab, C.invol b hb]
    exact Or.inr ⟨hab, hp⟩
  · have hp : C.partner a = b := hxa.symm.trans hxb
    have hab : a = C.partner b := by rw [← hp, C.invol a ha]
    exact Or.inr ⟨hab, hp⟩
  · have hp : C.partner a = C.partner b := hxa.symm.trans hxb
    have hab : a = b := by rw [← C.invol a ha, ← C.invol b hb, hp]
    exact Or.inl ⟨hab, by rw [hab]⟩

/-- The endpoints of the selected matching are exactly `N`. -/
theorem biUnion_matchingEdges {N : Finset V} (C : Certificate G N) :
    (matchingEdges C).biUnion Sym2.toFinset = N := by
  ext x
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [Sym2.mem_toFinset, Sym2.mem_iff] at h
    rcases h with rfl | rfl
    · exact ha
    · exact C.mapsTo a ha
  · intro hx
    refine ⟨s(x, C.partner x), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · rw [Sym2.mem_toFinset, Sym2.mem_iff]
      exact Or.inl rfl

/-- Every vertex of `N` occurs once in a matching edge, hence `2|E|=|N|`. -/
theorem two_mul_card_matchingEdges {N : Finset V} (C : Certificate G N) :
    2 * (matchingEdges C).card = N.card := by
  have hdisj := matchingEdges_isLiteralMatching C
  have hcard : ∀ e ∈ matchingEdges C, e.toFinset.card = 2 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Sym2.card_toFinset_of_not_isDiag _ (by
      simpa [Sym2.isDiag_iff_proj_eq] using (C.ne a ha).symm)
  have hsum := Finset.card_biUnion hdisj
  rw [biUnion_matchingEdges C] at hsum
  calc
    2 * (matchingEdges C).card = (matchingEdges C).card * 2 := Nat.mul_comm _ _
    _ = ∑ e ∈ matchingEdges C, 2 := by simp
    _ = ∑ e ∈ matchingEdges C, e.toFinset.card := by
      apply Finset.sum_congr rfl
      intro e he
      exact (hcard e he).symm
    _ = N.card := hsum.symm

/-- A common neighbour of `N` is an exterior hub for the selected edges. -/
theorem isExteriorHub_matchingEdges {N : Finset V} (C : Certificate G N) {z : V}
    (hz : ∀ a ∈ N, G.Adj z a) : IsExteriorHub G z (matchingEdges C) where
  edges := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa [mem_graphEdges, SimpleGraph.mem_edgeSet] using C.adj a ha
  matching := matchingEdges_isLiteralMatching C
  hubAdj := by
    intro e he a ha
    obtain ⟨y, hy, hey⟩ := Finset.mem_image.mp he
    rw [← hey] at ha
    simp only [Sym2.mem_iff] at ha
    rcases ha with h | h
    · rw [h]
      exact hz y hy
    · rw [h]
      exact hz _ (C.mapsTo y hy)

/-- The physical absorber selected by `C`. -/
def physicalTriangleAbsorber {N : Finset V} (C : Certificate G N) (z : V) :
    Finset (Finset V) := liftedPacking z (matchingEdges C)

theorem physical_triangle_absorber {N : Finset V} (C : Certificate G N) {z : V}
    (hz : ∀ a ∈ N, G.Adj z a) :
    IsPacking G (physicalTriangleAbsorber C z) :=
  isPacking_liftedPacking (isExteriorHub_matchingEdges C hz)

theorem totalGain_physical_triangle_absorber {N : Finset V} (C : Certificate G N) {z : V}
    (hz : ∀ a ∈ N, G.Adj z a) :
    totalGain (physicalTriangleAbsorber C z) = N.card := by
  rw [physicalTriangleAbsorber,
    totalGain_liftedPacking (isExteriorHub_matchingEdges C hz)]
  exact two_mul_card_matchingEdges C

/-- Selection and literal realization in one interface. -/
theorem exists_lowConflict_physical_triangle_absorber {N : Finset V} {t : ℕ}
    (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (bad : V → V → ℝ) (hbad : ∀ y z, 0 ≤ bad y z) {z : V}
    (hz : ∀ a ∈ N, G.Adj z a) :
    ∃ C : Certificate G N,
      IsPacking G (physicalTriangleAbsorber C z) ∧
      totalGain (physicalTriangleAbsorber C z) = N.card ∧
      ∑ y ∈ N, bad y (C.partner y) ≤
        (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ x ∈ N, bad y x := by
  obtain ⟨C, hcost⟩ := exists_lowConflict_certificate heven hdeg bad hbad
  exact ⟨C, physical_triangle_absorber C hz,
    totalGain_physical_triangle_absorber C hz, hcost⟩

/-- If the total conflict mass fits `(t+1)` budgets, the selected literal
absorber costs at most one budget. -/
theorem exists_budgeted_physical_triangle_absorber {N : Finset V} {t : ℕ}
    (heven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 + t ≤ (N.filter fun z => G.Adj v z).card)
    (bad : V → V → ℝ) (hbad : ∀ y z, 0 ≤ bad y z) (budget : ℝ)
    (hmass : ∑ y ∈ N, ∑ x ∈ N, bad y x ≤ ((t : ℝ) + 1) * budget)
    {z : V} (hz : ∀ a ∈ N, G.Adj z a) :
    ∃ C : Certificate G N,
      IsPacking G (physicalTriangleAbsorber C z) ∧
      totalGain (physicalTriangleAbsorber C z) = N.card ∧
      ∑ y ∈ N, bad y (C.partner y) ≤ budget := by
  obtain ⟨C, hpack, hgain, hcost⟩ :=
    exists_lowConflict_physical_triangle_absorber heven hdeg bad hbad hz
  refine ⟨C, hpack, hgain, hcost.trans ?_⟩
  have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  calc
    (1 / ((t : ℝ) + 1)) * ∑ y ∈ N, ∑ x ∈ N, bad y x
        ≤ (1 / ((t : ℝ) + 1)) * (((t : ℝ) + 1) * budget) := by
          gcongr
    _ = budget := by field_simp

end PaperIV.SpreadAbsorption
