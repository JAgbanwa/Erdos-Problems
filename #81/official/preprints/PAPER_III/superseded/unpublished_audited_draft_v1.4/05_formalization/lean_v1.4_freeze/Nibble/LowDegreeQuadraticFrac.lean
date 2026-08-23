/-
# Nibble — why the low-degree branch of the AX1 packing gap cannot be bounded away trivially

`Nibble.AX1.nibbleGapHyp_of_residual` reduces the unconditional packing gap to
`Nibble.AX1.NibbleGapResidual`: the gap `ν₃* − ν₃ ≤ ε|V|²` for graphs that are simultaneously

* NOT dense — some vertex has degree `< θ|V|`, so the dense discharge `nibbleGap_dense` (and with it
  the near-regularity of the triangle hypergraph) is unavailable, and
* triangle-rich — more than `ε|V|²` triangles, so the trivial bound `ν₃* ≤ #triangles`
  (`nibbleGap_fewTriangles`) is unavailable.

This file records, machine-checked, that this residual class is genuinely non-trivial: a graph can
have an ISOLATED vertex (hence fail the density threshold for every `θ > 0`) and still have
`ν₃*` of order `|V|²`.  So the low-degree branch cannot be discharged by any argument that merely
bounds `ν₃*`; it needs the real packing mathematics.

* `Nibble.AX1.card_triangles_div_card_le_nu3star` — for every graph, `ν₃* ≥ #triangles/|V|`
  (uniform weight `1/|V|` on all triangles is a fractional packing).
* `Nibble.AX1.prefixClique` — the clique on the first `m` of `m+1` vertices.
* `Nibble.AX1.prefixClique_isolated` — its last vertex has degree `0`.
* `Nibble.AX1.prefixClique_nu3star_ge_sq` — for `m ≥ 30` its fractional packing number is at least
  `|V|²/8`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseGapAX1

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- At most `|V|` triangles contain a given edge: such a triangle is `insert v e` for a vertex `v`. -/
theorem card_filter_triangleHypergraphE_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Finset V) :
    ((triangleHypergraphE G).filter (fun T => e ∈ T)).card ≤ Fintype.card V := by
  classical
  have hsub : (triangleHypergraphE G).filter (fun T => e ∈ T) ⊆
      Finset.univ.image (fun v : V => (insert v e).powersetCard 2) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hTH, heT⟩ := hT
    rw [triangleHypergraphE, Finset.mem_image] at hTH
    obtain ⟨t, ht, rfl⟩ := hTH
    rw [Finset.mem_powersetCard] at heT
    obtain ⟨hesub, hecard⟩ := heT
    have htcard : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
    have hadd := Finset.card_sdiff_add_card_eq_card hesub
    have hone : (t \ e).card = 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
    have hteq : t = insert v e := by
      have hu := Finset.sdiff_union_of_subset hesub
      rw [hv] at hu
      rw [← hu]
      ext x
      simp [Finset.mem_insert]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, by rw [hteq]⟩
  calc ((triangleHypergraphE G).filter (fun T => e ∈ T)).card
      ≤ (Finset.univ.image (fun v : V => (insert v e).powersetCard 2)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

/-- The edge-based triangle hypergraph has exactly `#triangles` hyperedges. -/
theorem triangleHypergraphE_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    (triangleHypergraphE G).card = (G.cliqueFinset 3).card := by
  rw [triangleHypergraphE, Finset.card_image_of_injOn]
  intro s hs t ht hst
  simp only [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at hs ht
  exact powersetCard_two_inj (by have := hs.card_eq; omega) (by have := ht.card_eq; omega) hst

/-- **A general lower bound on `ν₃*`.**  Uniform weight `1/|V|` on every triangle is a fractional
packing, since each edge lies in at most `|V|` triangles; hence `ν₃* ≥ #triangles/|V|`. -/
theorem card_triangles_div_card_le_nu3star (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 0 < Fintype.card V) :
    ((G.cliqueFinset 3).card : ℝ) / (Fintype.card V : ℝ) ≤ nu3star G := by
  classical
  have hVR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  set c : ℝ := 1 / (Fintype.card V : ℝ) with hc
  set w : Finset (Finset V) → ℝ := fun T => if T ∈ triangleHypergraphE G then c else 0 with hw
  have hcpos : 0 < c := by positivity
  have hpack : IsFracPacking G w := by
    refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
    · simp only [hw]; split_ifs <;> [exact hcpos.le; exact le_rfl]
    · simp only [hw]; rw [if_neg hT]
    · have hsum : ∑ T ∈ (triangleHypergraphE G).filter (fun T => e ∈ T), w T
          = (((triangleHypergraphE G).filter (fun T => e ∈ T)).card : ℝ) * c := by
        rw [Finset.sum_congr rfl (fun T hT => ?_), Finset.sum_const, nsmul_eq_mul]
        simp only [hw]
        rw [if_pos (Finset.mem_filter.mp hT).1]
      rw [hsum, hc, mul_one_div, div_le_one hVR]
      exact_mod_cast card_filter_triangleHypergraphE_le G e
  have hval : ∑ T ∈ triangleHypergraphE G, w T
      = ((G.cliqueFinset 3).card : ℝ) / (Fintype.card V : ℝ) := by
    have hsum : ∑ T ∈ triangleHypergraphE G, w T = ((triangleHypergraphE G).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun T hT => ?_), Finset.sum_const, nsmul_eq_mul]
      simp only [hw]
      rw [if_pos hT]
    rw [hsum, triangleHypergraphE_card G, hc, mul_one_div]
  exact le_csSup (nu3star_bddAbove G) ⟨w, hpack, hval.symm⟩

/-! ### A triangle-rich graph with an isolated vertex -/

/-- The complete graph on the first `m` of `m+1` vertices; the last vertex is isolated. -/
def prefixClique (m : ℕ) : SimpleGraph (Fin (m + 1)) where
  Adj x y := x ≠ y ∧ (x : ℕ) < m ∧ (y : ℕ) < m
  symm := by rintro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (m : ℕ) : DecidableRel (prefixClique m).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (x : ℕ) < m ∧ (y : ℕ) < m))

/-- The last vertex of `prefixClique m` is isolated. -/
theorem prefixClique_isolated (m : ℕ) : (prefixClique m).degree (Fin.last m) = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
  ext y
  simp [SimpleGraph.mem_neighborFinset, prefixClique]

/-- The clique part has `m` vertices. -/
theorem prefixClique_prefix_card (m : ℕ) :
    ((Finset.univ : Finset (Fin (m + 1))).filter (fun x : Fin (m + 1) => (x : ℕ) < m)).card = m := by
  have h : ((Finset.univ : Finset (Fin (m + 1))).filter (fun x : Fin (m + 1) => (x : ℕ) < m))
      = Finset.image Fin.castSucc (Finset.univ : Finset (Fin m)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      simp
    · rintro ⟨y, rfl⟩
      simp [Fin.castSucc]
  rw [h, Finset.card_image_of_injective _ (Fin.castSucc_injective m), Finset.card_univ,
    Fintype.card_fin]

/-- `prefixClique m` has at least `C(m,3)` triangles: every `3`-subset of the clique part is one. -/
theorem prefixClique_triangles_ge (m : ℕ) :
    m.choose 3 ≤ ((prefixClique m).cliqueFinset 3).card := by
  classical
  set S : Finset (Fin (m + 1)) :=
    (Finset.univ : Finset (Fin (m + 1))).filter (fun x : Fin (m + 1) => (x : ℕ) < m) with hS
  have hsub : S.powersetCard 3 ⊆ (prefixClique m).cliqueFinset 3 := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨?_, ht.2⟩
    intro x hx y hy hxy
    have hx' := ht.1 hx
    have hy' := ht.1 hy
    rw [hS, Finset.mem_filter] at hx' hy'
    exact ⟨hxy, hx'.2, hy'.2⟩
  calc m.choose 3 = (S.powersetCard 3).card := by
        rw [Finset.card_powersetCard, hS, prefixClique_prefix_card]
    _ ≤ _ := Finset.card_le_card hsub

/-- `6·C(m,3) = m(m−1)(m−2)`. -/
theorem six_mul_choose_three (m : ℕ) : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
  have h1 := Nat.descFactorial_eq_factorial_mul_choose m 3
  have h2 : m.descFactorial 3 = m * (m - 1) * (m - 2) := by simp [Nat.descFactorial]; ring
  rw [h2] at h1
  simp [Nat.factorial] at h1
  omega

/-- **A graph with an isolated vertex and quadratic fractional packing number.**  For `m ≥ 30`,
`prefixClique m` has `|V| = m+1` vertices, an isolated vertex, and `ν₃* ≥ |V|²/8`. -/
theorem prefixClique_nu3star_ge_sq (m : ℕ) (hm : 30 ≤ m) :
    (Fintype.card (Fin (m + 1)) : ℝ) ^ 2 / 8 ≤ nu3star (prefixClique m) := by
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) = (m : ℝ) + 1 := by
    rw [Fintype.card_fin]; push_cast; ring
  have hpos : 0 < Fintype.card (Fin (m + 1)) := by rw [Fintype.card_fin]; omega
  have hlow := card_triangles_div_card_le_nu3star (prefixClique m) hpos
  rw [hcard] at hlow
  -- the triangle count in real form
  have hchooseN : 6 * m.choose 3 = m * (m - 1) * (m - 2) := six_mul_choose_three m
  have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hchooseR : 6 * ((m.choose 3 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hchooseN
    push_cast [hm1, hm2] at this
    linarith only [this]
  have htri : ((m.choose 3 : ℕ) : ℝ) ≤ (((prefixClique m).cliqueFinset 3).card : ℝ) := by
    exact_mod_cast prefixClique_triangles_ge m
  have hmR : (30 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by linarith only []
  have hstep : ((m : ℝ) + 1) ^ 2 / 8 ≤ ((m.choose 3 : ℕ) : ℝ) / ((m : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) hden]
    nlinarith only [hchooseR, hmR]
  have hmono : ((m.choose 3 : ℕ) : ℝ) / ((m : ℝ) + 1)
      ≤ (((prefixClique m).cliqueFinset 3).card : ℝ) / ((m : ℝ) + 1) :=
    div_le_div_of_nonneg_right htri hden.le
  rw [hcard]
  linarith only [hlow, hstep, hmono]

end Nibble.AX1
