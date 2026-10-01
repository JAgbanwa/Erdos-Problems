import PaperIV.VertexCopy
import PaperIV.FarRoundingRealLP

/-!
# Item transport across one fine vertex copy (DV157–RD09)

Let `u ≠ v` be nonadjacent in `G` and let `H = VertexCopy.graph G u v` be the
graph obtained by copying `v` onto `u` (so `N_H(u) = N_G(v)`).

This module proves the literal dictionary between the mixed `K₃/K₄` items of
`G` and of `H`:

* items avoiding `u` are the same in `G` and in `H`;
* `copyShift u v L = insert u (L.erase v)` is an explicit bijection from the
  items of `G` that avoid `u` and contain `v` onto the items of `H` that
  contain `u`, and it preserves cardinality (hence gain).

No LP statement occurs here; this is the combinatorial layer used by
`PaperIV.VertexCopyTransport`.
-/

namespace PaperIV.VertexCopyItems

open Finset
open PaperIV.FarRounding

variable {V : Type*} [DecidableEq V]

/-- Replace `v` by `u` in a vertex set. -/
def copyShift (u v : V) (L : Finset V) : Finset V := insert u (L.erase v)

@[simp] theorem mem_copyShift {u v : V} {L : Finset V} {a : V} :
    a ∈ copyShift u v L ↔ a = u ∨ (a ≠ v ∧ a ∈ L) := by
  simp [copyShift, Finset.mem_insert, Finset.mem_erase]

theorem mem_copyShift_self (u v : V) (L : Finset V) : u ∈ copyShift u v L := by simp

theorem not_mem_copyShift_of_ne {u v : V} (hne : u ≠ v) (L : Finset V) :
    v ∉ copyShift u v L := by
  simp [mem_copyShift, Ne.symm hne]

theorem card_copyShift {u v : V} {L : Finset V} (hu : u ∉ L) (hv : v ∈ L) :
    (copyShift u v L).card = L.card := by
  have hu' : u ∉ L.erase v := fun h => hu (Finset.mem_of_mem_erase h)
  rw [copyShift, Finset.card_insert_of_notMem hu', Finset.card_erase_of_mem hv]
  have : 1 ≤ L.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

theorem copyShift_copyShift {u v : V} {L : Finset V} (hu : u ∉ L) (hv : v ∈ L) :
    copyShift v u (copyShift u v L) = L := by
  ext a
  simp only [mem_copyShift]
  constructor
  · rintro (rfl | ⟨hau, rfl | ⟨-, ha⟩⟩)
    · exact hv
    · exact absurd rfl hau
    · exact ha
  · intro ha
    by_cases hav : a = v
    · exact Or.inl hav
    · exact Or.inr ⟨fun h => hu (h ▸ ha), Or.inr ⟨hav, ha⟩⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}

omit [Fintype V] [DecidableRel G.Adj] in
/-- An item avoiding the target vertex is unchanged by the copy. -/
theorem isItem_copy_iff_of_not_mem {K : Finset V} (hu : u ∉ K) :
    IsItem (VertexCopy.graph G u v) K ↔ IsItem G K := by
  have key : ∀ a ∈ K, ∀ b ∈ K, ((VertexCopy.graph G u v).Adj a b ↔ G.Adj a b) := by
    intro a ha b hb
    refine VertexCopy.adj_of_ne_left_of_ne_right G ?_ ?_
    · rintro rfl; exact hu ha
    · rintro rfl; exact hu hb
  constructor
  · rintro ⟨hcl, hc⟩
    exact ⟨fun a ha b hb hab => (key a ha b hb).mp (hcl a ha b hb hab), hc⟩
  · rintro ⟨hcl, hc⟩
    exact ⟨fun a ha b hb hab => (key a ha b hb).mpr (hcl a ha b hb hab), hc⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Forward transport: an item of `G` avoiding `u` and containing `v` becomes,
after replacing `v` by `u`, an item of the copied graph containing `u`. -/
theorem isItem_copyShift (hnadj : ¬ G.Adj u v) {L : Finset V}
    (hu : u ∉ L) (hv : v ∈ L) (h : IsItem G L) :
    IsItem (VertexCopy.graph G u v) (copyShift u v L) := by
  have hub : ∀ b ∈ copyShift u v L, b ≠ u → (VertexCopy.graph G u v).Adj u b := by
    intro b hb hbu
    rw [mem_copyShift] at hb
    rcases hb with rfl | ⟨hbv, hbL⟩
    · exact absurd rfl hbu
    · exact (VertexCopy.adj_copied_iff G hnadj b).mpr (h.1 v hv b hbL (Ne.symm hbv))
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    by_cases hau : a = u
    · subst hau
      exact hub b hb (Ne.symm hab)
    · by_cases hbu : b = u
      · subst hbu
        exact (hub a ha hau).symm
      · have haL : a ∈ L := by
          rcases mem_copyShift.mp ha with rfl | ⟨-, haL⟩
          · exact absurd rfl hau
          · exact haL
        have hbL : b ∈ L := by
          rcases mem_copyShift.mp hb with rfl | ⟨-, hbL⟩
          · exact absurd rfl hbu
          · exact hbL
        exact (VertexCopy.adj_of_ne_left_of_ne_right G hau hbu).mpr (h.1 a haL b hbL hab)
  · rw [card_copyShift hu hv]; exact h.2

omit [Fintype V] [DecidableRel G.Adj] in
/-- Backward transport: an item of the copied graph containing `u` avoids `v`,
and replacing `u` by `v` produces an item of `G`. -/
theorem not_mem_of_isItem_copy {K : Finset V} (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hu : u ∈ K) (h : IsItem (VertexCopy.graph G u v) K) : v ∉ K := by
  intro hv
  exact G.irrefl ((VertexCopy.adj_copied_iff G hnadj v).mp (h.1 u hu v hv hne))

omit [Fintype V] [DecidableRel G.Adj] in
theorem isItem_copyShift_symm (hne : u ≠ v) (hnadj : ¬ G.Adj u v) {K : Finset V}
    (hu : u ∈ K) (h : IsItem (VertexCopy.graph G u v) K) :
    IsItem G (copyShift v u K) := by
  have hv : v ∉ K := not_mem_of_isItem_copy G hne hnadj hu h
  have hvb : ∀ b ∈ copyShift v u K, b ≠ v → G.Adj v b := by
    intro b hb hbv
    rcases mem_copyShift.mp hb with rfl | ⟨hbu, hbK⟩
    · exact absurd rfl hbv
    · exact (VertexCopy.adj_copied_iff G hnadj b).mp (h.1 u hu b hbK (Ne.symm hbu))
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    by_cases hav : a = v
    · subst hav
      exact hvb b hb (Ne.symm hab)
    · by_cases hbv : b = v
      · subst hbv
        exact (hvb a ha hav).symm
      · have ha' : a ≠ u ∧ a ∈ K := by
          rcases mem_copyShift.mp ha with rfl | ⟨hau, haK⟩
          · exact absurd rfl hav
          · exact ⟨hau, haK⟩
        have hb' : b ≠ u ∧ b ∈ K := by
          rcases mem_copyShift.mp hb with rfl | ⟨hbu, hbK⟩
          · exact absurd rfl hbv
          · exact ⟨hbu, hbK⟩
        exact (VertexCopy.adj_of_ne_left_of_ne_right G ha'.1 hb'.1).mp
          (h.1 a ha'.2 b hb'.2 hab)
  · rw [card_copyShift hv hu]; exact h.2

theorem copyShift_mem_items (hnadj : ¬ G.Adj u v) {L : Finset V}
    (hu : u ∉ L) (hv : v ∈ L) (h : L ∈ items G) :
    copyShift u v L ∈ items (VertexCopy.graph G u v) :=
  mem_items.mpr (isItem_copyShift G hnadj hu hv (mem_items.mp h))

end PaperIV.VertexCopyItems
