/-
# Nibble — the spreadness hypothesis of the weighted nibble is necessary

`Nibble.exists_matching_of_spread` proves the weighted nibble for fractional matchings whose weights
are all at most a small constant `δ`.  This file shows that the spreadness hypothesis cannot simply
be dropped: the triangle hypergraph of `K₄` is `3`-uniform, has codegree `≤ 1`, and carries a
*perfect* fractional matching (weight `1/2` on each of its four hyperedges), yet its four hyperedges
pairwise intersect, so its largest matching covers only half of its six vertices.

* `Nibble.K4Tri` — the triangle hypergraph of `K₄`, on the six edges of `K₄`.
* `Nibble.UnspreadWeightedNibble` — the weighted nibble with the spreadness hypothesis removed.
* `Nibble.not_unspreadWeightedNibble` — it is false for every `β < 1/2`.

Consequently the residual `Nibble.FracDecompSpreading` of `Nibble/FracRounding.lean` — smoothing a
fractional triangle decomposition into a spread one — is not an artefact of the proof: some global
input beyond the mere existence of a fractional decomposition is genuinely required.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.SpreadNibble

open Finset Hypergraph

namespace Nibble

/-- The triangle hypergraph of `K₄`, with the six edges of `K₄` encoded as `0, …, 5`:
`0 = 12, 1 = 13, 2 = 14, 3 = 23, 4 = 24, 5 = 34`. -/
def K4Tri : Finset (Finset (Fin 6)) :=
  {{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {3, 4, 5}}

theorem k4Tri_uniform : IsUniform K4Tri 3 := by
  intro e he
  fin_cases he <;> decide

set_option maxRecDepth 4000 in
theorem k4Tri_codegree_le_one : ∀ x y : Fin 6, x ≠ y → codegree K4Tri x y ≤ 1 := by decide

set_option maxRecDepth 4000 in
/-- Any two distinct hyperedges of `K4Tri` meet. -/
theorem k4Tri_not_disjoint : ∀ a ∈ K4Tri, ∀ b ∈ K4Tri, a ≠ b → ¬ Disjoint a b := by
  intro a ha b hb hab
  fin_cases ha <;> fin_cases hb <;> simp_all

/-- Every vertex of `K4Tri` lies in exactly two hyperedges. -/
theorem k4Tri_degree (x : Fin 6) : (K4Tri.filter (fun t => x ∈ t)).card = 2 := by
  fin_cases x <;> decide

/-- The uniform weight `1/2` is a perfect fractional matching of `K4Tri`. -/
theorem k4Tri_fracMatching (x : Fin 6) :
    ∑ t ∈ K4Tri.filter (fun t => x ∈ t), (fun _ : Finset (Fin 6) => (1 / 2 : ℝ)) t = 1 := by
  rw [Finset.sum_const, k4Tri_degree x, nsmul_eq_mul]
  norm_num

/-- Every matching of `K4Tri` has at most one hyperedge. -/
theorem k4Tri_matching_card_le {M : Finset (Finset (Fin 6))} (hM : IsMatching K4Tri M) :
    M.card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
  exact k4Tri_not_disjoint a (hM.subset ha) b (hM.subset hb) hab (hM.disjoint a ha b hb hab)

/-- **The weighted nibble with the spreadness hypothesis removed.** -/
def UnspreadWeightedNibble (β : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (w : Finset V → ℝ),
    IsUniform H 3 → (∀ x y : V, x ≠ y → (codegree H x y : ℝ) ≤ 1) →
    (∀ t ∈ H, 0 ≤ w t) → (∀ x : V, ∑ t ∈ H.filter (fun t => x ∈ t), w t = 1) →
    ∃ M : Finset (Finset V), IsMatching H M ∧
      (1 - β) * ((Fintype.card V : ℝ) / 3) ≤ (M.card : ℝ)

/-- **Spreadness is necessary.**  For every `β < 1/2` the unspread weighted nibble is false: the
triangle hypergraph of `K₄` carries a perfect fractional matching but no matching of more than one
hyperedge, so its best matching covers only `1/2` of its vertices. -/
theorem not_unspreadWeightedNibble {β : ℝ} (hβ : β < 1 / 2) : ¬ UnspreadWeightedNibble β := by
  intro h
  obtain ⟨M, hM, hMcard⟩ :=
    h (Fin 6) K4Tri (fun _ => (1 / 2 : ℝ)) k4Tri_uniform
      (fun x y hxy => by exact_mod_cast k4Tri_codegree_le_one x y hxy)
      (fun _ _ => by norm_num) k4Tri_fracMatching
  have hcard : (M.card : ℝ) ≤ 1 := by exact_mod_cast k4Tri_matching_card_le hM
  have h6 : (Fintype.card (Fin 6) : ℝ) = 6 := by simp
  rw [h6] at hMcard
  linarith only [hβ, hMcard, hcard]

end Nibble
