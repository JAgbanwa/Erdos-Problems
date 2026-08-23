/-
# Counting tools for the pairing demand at a grid design.

Elementary facts used to *count* what a system of pairings of the links of a grid design must
spend:

* `BKLO.card_gridRow_sum`, `BKLO.card_gridCol_sum` — the row and the column of a grid of pairwise
  disjoint classes have as many vertices as the sum of their class sizes (the classes of a row,
  resp. of a column, are pairwise distinct indices);
* `BKLO.grid_row_of_idx`, `BKLO.gridRegion_inter_classUnion`, `BKLO.two_mul_card_cliqueEdges_le` —
  the row of a class index, the region of a subfamily of the classes, and the number of edges
  inside a set;
* `BKLO.sum_card_le_two_mul_card_cliqueEdges` — the **capacity bound**: if the pairings of the
  outer vertices of a set `D'` all pair vertices of one set `S` with vertices of `S`, then, since
  the pairs of different outer vertices are different edges (`IsPairedLinkCore.distinct`) and each
  edge accounts for at most two paired vertices, the total number of such paired vertices is at
  most twice the number of edges inside `S`.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingClean
import BKLO.ReservoirPairingRefutation

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The row of a grid of pairwise disjoint classes has as many vertices as the sum of the sizes of
its classes. -/
theorem card_gridRow_sum {h : ℕ} {C : ℕ → Finset V} {p : ℕ} (hp : p < h)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) :
    ((Finset.range h).biUnion (fun j => C (p * h + j))).card
      = ∑ j ∈ Finset.range h, (C (p * h + j)).card := by
  classical
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  exact hdisj _ (grid_idx_lt hp (Finset.mem_range.1 hi)) _
    (grid_idx_lt hp (Finset.mem_range.1 hj)) (by omega)

/-- The column of a grid of pairwise disjoint classes has as many vertices as the sum of the sizes
of its classes. -/
theorem card_gridCol_sum {h : ℕ} {C : ℕ → Finset V} {q : ℕ} (hq : q < h)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) :
    ((Finset.range h).biUnion (fun i => C (i * h + q))).card
      = ∑ i ∈ Finset.range h, (C (i * h + q)).card := by
  classical
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le q) hq
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  refine hdisj _ (grid_idx_lt (Finset.mem_range.1 hi) hq) _
    (grid_idx_lt (Finset.mem_range.1 hj) hq) ?_
  intro heq
  exact hij (Nat.eq_of_mul_eq_mul_right hhpos (by omega))

/-- The row of a class index. -/
theorem grid_row_of_idx {h p q : ℕ} (hq : q < h) : (p * h + q) / h = p := by
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le q) hq
  have hrw : p * h + q = q + h * p := by ring
  rw [hrw, Nat.add_mul_div_left _ _ hhpos, Nat.div_eq_of_lt hq, Nat.zero_add]

/-- Shrinking the classes shrinks the designed regions: the region of a cell for a subfamily is
exactly its region for the whole family, intersected with the union of the subfamily. -/
theorem gridRegion_inter_classUnion {h : ℕ} {C C' : ℕ → Finset V} {p q : ℕ}
    (hp : p < h) (hq : q < h) (hCC : ∀ i, C' i ⊆ C i)
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j)) :
    gridRegion h C p q ∩ ((Finset.range (h * h)).biUnion C') = gridRegion h C' p q := by
  classical
  ext a
  simp only [Finset.mem_inter, gridRegion, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_range]
  constructor
  · rintro ⟨hreg, l, hl, hal⟩
    have key : ∀ k, k < h * h → a ∈ C k → a ∈ C' k := by
      intro k hk hak
      by_cases hlk : l = k
      · exact hlk ▸ hal
      · exact absurd hak (Finset.disjoint_left.1 (hdisj l hl k hk hlk) (hCC l hal))
    rcases hreg with ⟨j, hj, haj⟩ | ⟨i, hi, hai⟩
    · exact Or.inl ⟨j, hj, key _ (grid_idx_lt hp hj) haj⟩
    · exact Or.inr ⟨i, hi, key _ (grid_idx_lt hi hq) hai⟩
  · rintro (⟨j, hj, haj⟩ | ⟨i, hi, hai⟩)
    · exact ⟨Or.inl ⟨j, hj, hCC _ haj⟩, _, grid_idx_lt hp hj, haj⟩
    · exact ⟨Or.inr ⟨i, hi, hCC _ hai⟩, _, grid_idx_lt hi hq, hai⟩

/-- A crude bound on the number of edges inside a set. -/
theorem two_mul_card_cliqueEdges_le (S : Finset V) :
    2 * (cliqueEdges S).card ≤ S.card * S.card := by
  classical
  rw [card_cliqueEdges, Nat.choose_two_right]
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · simp [h0]
  · obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by omega⟩
    rw [hk]
    have hdvd : 2 ∣ (k + 1) * (k + 1 - 1) := by
      have hev : Even (k * (k + 1)) := Nat.even_mul_succ_self k
      have : (2 : ℕ) ∣ k * (k + 1) := hev.two_dvd
      simpa [Nat.add_sub_cancel, Nat.mul_comm] using this
    rw [Nat.mul_div_cancel' hdvd]
    exact Nat.mul_le_mul_left _ (by omega)

/-- **The capacity bound.**  In a globally edge-disjoint system of pairings, the vertices that the
outer vertices of `D'` pair *inside* a set `S` are at most twice as many as the edges inside `S`:
each such vertex contributes the edge to its partner, different outer vertices contribute different
edges, and one outer vertex contributes a given edge at most twice. -/
theorem sum_card_le_two_mul_card_cliqueEdges {F : Finset (Sym2 V)} {W' W'' D : Finset V}
    {X : V → Finset V} {γ : ℝ} {g : V → V → V} (hg : IsPairedLinkCore F W' W'' D X γ g)
    {D' S : Finset V} (hD' : D' ⊆ D) {A : V → Finset V}
    (hAX : ∀ u ∈ D', A u ⊆ X u) (hAS : ∀ u ∈ D', A u ⊆ S)
    (hAg : ∀ u ∈ D', ∀ a ∈ A u, g u a ∈ S) :
    ∑ u ∈ D', (A u).card ≤ 2 * (cliqueEdges S).card := by
  classical
  set T : Finset (V × V) := D'.biUnion (fun u => (A u).image (fun a => (u, a))) with hTdef
  have hmemT : ∀ z : V × V, z ∈ T ↔ z.1 ∈ D' ∧ z.2 ∈ A z.1 := by
    intro z
    simp only [hTdef, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, a, ha, rfl⟩
      exact ⟨hu, ha⟩
    · rintro ⟨h1, h2⟩
      exact ⟨z.1, h1, z.2, h2, rfl⟩
  have hTcard : T.card = ∑ u ∈ D', (A u).card := by
    rw [hTdef, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun u _ => ?_
      exact Finset.card_image_of_injective _ (fun a b hab => by simpa using hab)
    · intro u hu v hv huv
      refine Finset.disjoint_left.2 ?_
      intro z hz hz'
      rw [Finset.mem_image] at hz hz'
      obtain ⟨a, -, rfl⟩ := hz
      obtain ⟨b, -, hb⟩ := hz'
      exact huv (congrArg Prod.fst hb).symm
  set Φ : V × V → Sym2 V := fun z => s(z.2, g z.1 z.2) with hΦdef
  have himg : T.image Φ ⊆ cliqueEdges S := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    obtain ⟨hu, ha⟩ := (hmemT z).1 hz
    have h1 : z.2 ∈ S := hAS z.1 hu ha
    have h2 : g z.1 z.2 ∈ S := hAg z.1 hu z.2 ha
    have h3 : z.2 ≠ g z.1 z.2 := fun hc => hg.ne z.1 (hD' hu) z.2 (hAX z.1 hu ha) hc.symm
    refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩
    · intro w hw
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact h1
      · exact h2
    · simpa [Sym2.isDiag_iff_proj_eq] using h3
  have hfib : ∀ e ∈ T.image Φ, (T.filter (fun z => Φ z = e)).card ≤ 2 := by
    intro e _
    by_cases hne : (T.filter (fun z => Φ z = e)).Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      rw [Finset.mem_filter] at hz₀
      obtain ⟨hz₀T, hz₀e⟩ := hz₀
      obtain ⟨hu₀, ha₀⟩ := (hmemT z₀).1 hz₀T
      have hsub : T.filter (fun z => Φ z = e)
          ⊆ ({(z₀.1, z₀.2), (z₀.1, g z₀.1 z₀.2)} : Finset (V × V)) := by
        intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨hzT, hze⟩ := hz
        obtain ⟨hu, ha⟩ := (hmemT z).1 hzT
        have heq : s(z.2, g z.1 z.2) = s(z₀.2, g z₀.1 z₀.2) := by
          have h0 : Φ z = Φ z₀ := by rw [hze, hz₀e]
          simpa [hΦdef] using h0
        have hvu : z.1 = z₀.1 :=
          hg.distinct z.1 (hD' hu) z.2 (hAX z.1 hu ha) z₀.1 (hD' hu₀) z₀.2 (hAX z₀.1 hu₀ ha₀) heq
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases (Sym2.eq_iff).1 heq with ⟨h1, -⟩ | ⟨h1, -⟩
        · left
          exact Prod.ext hvu h1
        · right
          refine Prod.ext hvu ?_
          simpa using h1
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  calc ∑ u ∈ D', (A u).card = T.card := hTcard.symm
    _ ≤ 2 * (T.image Φ).card := Finset.card_le_mul_card_image _ 2 hfib
    _ ≤ 2 * (cliqueEdges S).card := by
        exact Nat.mul_le_mul_left 2 (Finset.card_le_card himg)

end BKLO
