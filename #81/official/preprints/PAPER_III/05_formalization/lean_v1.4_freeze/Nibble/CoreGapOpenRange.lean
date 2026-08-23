/-
# Nibble — the open range of the AX1 core residual is non-vacuous

`Nibble.AX1.CoreGapAt ε δ` (`Nibble.CoreGapAX1`) is proved unconditionally for `δ ≥ θ(ε)` (the dense
range, `Nibble.AX1.coreGapAt_dense`) and for `ε ≥ 1/3` (`Nibble.AX1.coreGapAt_of_third`).  This file
records, machine-checked, that the *remaining* instances are not vacuous: for every `ε < 1/48` and
every bound `N` there is a graph on more than `N` vertices which

* satisfies the hypothesis of `CoreGapAt ε δ` for every `δ ≤ 2/5` — every vertex is isolated or has
  degree at least `(2/5)|V|`;
* is fractionally rich, `ν₃* > ε|V|²`; and
* has a vertex of positive degree below `|V|/2`, hence lies outside the range covered by the dense
  branch (which needs *all* positive degrees above `θ|V|` with `θ` close to `1`).

The witness is the disjoint union of a clique `K_m` with `m` isolated vertices
(`Nibble.AX1.cliquePlusIsolated`): its positive degrees are all `m − 1 ≈ |V|/2`, and it has
`≥ C(m,3) ≈ |V|³/48` triangles, hence `ν₃* ≥ #triangles/|V| ≈ |V|²/48`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapAX1
import Nibble.LowDegreeQuadraticFrac

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- The complete graph on the first `m` of `m + k` vertices; the last `k` vertices are isolated. -/
def cliquePlusIsolated (m k : ℕ) : SimpleGraph (Fin (m + k)) where
  Adj x y := x ≠ y ∧ (x : ℕ) < m ∧ (y : ℕ) < m
  symm := by rintro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (m k : ℕ) : DecidableRel (cliquePlusIsolated m k).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (x : ℕ) < m ∧ (y : ℕ) < m))

/-- The clique part has `m` vertices. -/
theorem cliquePlusIsolated_prefix_card (m k : ℕ) :
    ((Finset.univ : Finset (Fin (m + k))).filter (fun x : Fin (m + k) => (x : ℕ) < m)).card = m := by
  have h : ((Finset.univ : Finset (Fin (m + k))).filter (fun x : Fin (m + k) => (x : ℕ) < m))
      = Finset.image (Fin.castLE (by omega : m ≤ m + k)) (Finset.univ : Finset (Fin m)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, by ext; simp⟩
    · rintro ⟨y, rfl⟩
      simp
  rw [h, Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_univ,
    Fintype.card_fin]

/-- Vertices of the clique part have degree `m − 1`. -/
theorem cliquePlusIsolated_degree_of_lt (m k : ℕ) (x : Fin (m + k)) (hx : (x : ℕ) < m) :
    (cliquePlusIsolated m k).degree x = m - 1 := by
  classical
  have hnb : (cliquePlusIsolated m k).neighborFinset x
      = ((Finset.univ : Finset (Fin (m + k))).filter (fun y : Fin (m + k) => (y : ℕ) < m)).erase x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, -, hy⟩
      exact ⟨Ne.symm hne, hy⟩
    · rintro ⟨hne, hy⟩
      exact ⟨Ne.symm hne, hx, hy⟩
  have hmem : x ∈ (Finset.univ : Finset (Fin (m + k))).filter (fun y : Fin (m + k) => (y : ℕ) < m) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb, Finset.card_erase_of_mem hmem,
    cliquePlusIsolated_prefix_card]

/-- The last `k` vertices are isolated. -/
theorem cliquePlusIsolated_degree_of_ge (m k : ℕ) (x : Fin (m + k)) (hx : m ≤ (x : ℕ)) :
    (cliquePlusIsolated m k).degree x = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
  rintro ⟨-, h, -⟩
  omega

/-- Every `3`-subset of the clique part is a triangle. -/
theorem cliquePlusIsolated_triangles_ge (m k : ℕ) :
    m.choose 3 ≤ ((cliquePlusIsolated m k).cliqueFinset 3).card := by
  classical
  have hsub :
      ((Finset.univ : Finset (Fin (m + k))).filter
        (fun x : Fin (m + k) => (x : ℕ) < m)).powersetCard 3
        ⊆ (cliquePlusIsolated m k).cliqueFinset 3 := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨?_, ht.2⟩
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp (ht.1 hx)
    have hy' := Finset.mem_filter.mp (ht.1 hy)
    exact ⟨hxy, hx'.2, hy'.2⟩
  calc m.choose 3
      = (((Finset.univ : Finset (Fin (m + k))).filter
          (fun x : Fin (m + k) => (x : ℕ) < m)).powersetCard 3).card := by
        rw [Finset.card_powersetCard, cliquePlusIsolated_prefix_card]
    _ ≤ _ := Finset.card_le_card hsub

/-- **The open range of the residual is non-vacuous.**  For every `ε < 1/48` and every `N` there is
a graph on more than `N` vertices which satisfies the degree hypothesis of `CoreGapAt ε δ` for every
`δ ≤ 2/5`, is fractionally rich, and has a vertex of positive degree below `|V|/2` — so it is not
covered by the proved dense range of `CoreGapAt`. -/
theorem exists_openRange_graph (ε : ℝ) (hε : ε < 1 / 48) (N : ℕ) :
    ∃ (m : ℕ) (G : SimpleGraph (Fin (m + m))) (_ : DecidableRel G.Adj),
      N ≤ Fintype.card (Fin (m + m)) ∧
      (∀ x, G.degree x = 0 ∨
        (2 / 5 : ℝ) * (Fintype.card (Fin (m + m)) : ℝ) ≤ (G.degree x : ℝ)) ∧
      ε * (Fintype.card (Fin (m + m)) : ℝ) ^ 2 < nu3star G ∧
      ∃ x, 0 < G.degree x ∧
        (G.degree x : ℝ) < (1 / 2 : ℝ) * (Fintype.card (Fin (m + m)) : ℝ) := by
  classical
  -- choose the clique size
  set c : ℝ := max (48 * ε) 0 with hc
  have hc0 : 0 ≤ c := le_max_right _ _
  have hc1 : c < 1 := max_lt (by linarith) (by norm_num)
  set m : ℕ := max (max N 30) ⌈6 / (1 - c)⌉₊ with hm
  have hm30 : 30 ≤ m := le_trans (le_max_right N 30) (le_max_left _ _)
  have hmN : N ≤ m := le_trans (le_max_left N 30) (le_max_left _ _)
  have hmceil : (6 : ℝ) / (1 - c) ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right (max N 30) ⌈6 / (1 - c)⌉₊)
  have hmR : (30 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm30
  have hcard : (Fintype.card (Fin (m + m)) : ℝ) = 2 * (m : ℝ) := by
    rw [Fintype.card_fin]; push_cast; ring
  have hcardN : Fintype.card (Fin (m + m)) = m + m := Fintype.card_fin _
  have hpos : 0 < Fintype.card (Fin (m + m)) := by rw [hcardN]; omega
  refine ⟨m, cliquePlusIsolated m m, inferInstance, by omega, ?_, ?_, ?_⟩
  · -- the degree hypothesis
    intro x
    rcases lt_or_ge (x : ℕ) m with hx | hx
    · right
      rw [cliquePlusIsolated_degree_of_lt m m x hx, hcard]
      have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [h1]
      linarith
    · exact Or.inl (cliquePlusIsolated_degree_of_ge m m x hx)
  · -- fractional richness
    have hlow := card_triangles_div_card_le_nu3star (cliquePlusIsolated m m) hpos
    rw [hcard] at hlow
    have htri : ((m.choose 3 : ℕ) : ℝ)
        ≤ (((cliquePlusIsolated m m).cliqueFinset 3).card : ℝ) := by
      exact_mod_cast cliquePlusIsolated_triangles_ge m m
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    have hchooseR : 6 * ((m.choose 3 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
      have h := congrArg (fun k : ℕ => (k : ℝ)) (six_mul_choose_three m)
      push_cast [hm1, hm2] at h
      linarith only [h]
    have hden : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    -- `ε (2m)² < C(m,3)/(2m)`
    have hcm : 48 * ε ≤ c := le_max_left _ _
    have hstep : (6 : ℝ) ≤ (1 - c) * (m : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - c)] at hmceil
      linarith
    have hkey : ε * (2 * (m : ℝ)) ^ 2 < ((m.choose 3 : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      rw [lt_div_iff₀ hden]
      have h48 : 48 * ε * (m : ℝ) ^ 3 ≤ c * (m : ℝ) ^ 3 := by
        have hm3 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
        nlinarith only [hcm, hm3]
      have hcm2 : c * (m : ℝ) ^ 3 < (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
        nlinarith only [mul_le_mul_of_nonneg_right hstep (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2), hmR]
      linarith only [hchooseR, h48, hcm2]
    have hmono : ((m.choose 3 : ℕ) : ℝ) / (2 * (m : ℝ))
        ≤ ((((cliquePlusIsolated m m).cliqueFinset 3).card : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      gcongr
    rw [hcard]
    linarith only [hlow, hkey, hmono]
  · -- a vertex of positive degree below `|V|/2`
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · rw [cliquePlusIsolated_degree_of_lt m m ⟨0, by omega⟩ (by simp; omega)]
      omega
    · rw [cliquePlusIsolated_degree_of_lt m m ⟨0, by omega⟩ (by simp; omega), hcard]
      have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [h1]
      linarith

end Nibble.AX1
