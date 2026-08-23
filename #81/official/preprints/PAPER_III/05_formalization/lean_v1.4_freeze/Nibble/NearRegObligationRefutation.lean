/-
# Nibble — the old AX1 blocker `NearRegObligation*` is FALSE

`Nibble.AX1.nibbleGap_holds` (in `Nibble.TightNibble`) derives the packing gap from
`hReg : ∀ μ η d₀ K, 0 < μ → 0 < η → 0 < d₀ → 0 < K → NearRegObligationSized μ η d₀ K`,
i.e. from near-`d`-regularity of the triangle hypergraph of an ARBITRARY graph.  This file proves
that hypothesis is unsatisfiable, so `hReg` cannot be discharged and the route through it is a dead
end.

The witness is the simplest possible one: a graph with a single edge and no triangle.  Its triangle
hypergraph has a vertex (that edge) of degree `0`, so near-`d`-regularity with `d > 0` forces the
exceptional set to be everything, contradicting `|Exc| ≤ η·|E(G)|` for `η < 1`.

* `Nibble.AX1.singleEdge` — the one-edge graph on `Fin (n+2)`.
* `Nibble.AX1.nearlyRegularMost_singleEdge_false` — the core refutation.
* `Nibble.AX1.not_nearRegObligation`, `Nibble.AX1.not_nearRegObligationSized`,
  `Nibble.AX1.not_nearRegObligationLinearSized` — the three obligations are false at `μ = η = 1/2`.
* `Nibble.AX1.not_forall_nearRegObligationSized` — hence the hypothesis `hReg` of
  `Nibble.AX1.nibbleGap_holds` is false.

This is why `Nibble.DenseGapAX1` replaces `hReg` by the density case split and the honest residual
`Nibble.AX1.NibbleGapResidual`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseGapAX1

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-- The graph on `Fin (n+2)` with the single edge `{0,1}`. -/
def singleEdge (n : ℕ) : SimpleGraph (Fin (n + 2)) where
  Adj x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
  symm := by rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  loopless := ⟨by rintro x (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp at h⟩

instance (n : ℕ) : DecidableRel (singleEdge n).Adj :=
  fun x y => inferInstanceAs (Decidable ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)))

theorem zero_ne_one_fin (n : ℕ) : (0 : Fin (n + 2)) ≠ 1 := by simp

/-- `{0,1}` is an edge of `singleEdge n`. -/
theorem singleEdge_edge (n : ℕ) :
    ({0, 1} : Finset (Fin (n + 2))) ∈ (singleEdge n).cliqueFinset 2 := by
  rw [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hxy
  · rw [Finset.card_pair (zero_ne_one_fin n)]

/-- `singleEdge n` has no triangle. -/
theorem singleEdge_triangleFree (n : ℕ) : (singleEdge n).cliqueFinset 3 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  have hne := zero_ne_one_fin n
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hac with ⟨-, rfl⟩ | ⟨h1, -⟩
    · exact (singleEdge n).irrefl hbc
    · exact hne h1
  · rcases hac with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact hne h1.symm
    · exact (singleEdge n).irrefl hbc

/-- The triangle hypergraph of `singleEdge n` is empty. -/
theorem singleEdge_sub_empty (n : ℕ) : triangleHypergraphSub (singleEdge n) = ∅ := by
  have h := triangleHypergraphSub_card (singleEdge n)
  rw [singleEdge_triangleFree, Finset.card_empty] at h
  exact Finset.card_eq_zero.mp h

/-- Every edge of `singleEdge n` lies in no triangle. -/
theorem singleEdge_degree_zero (n : ℕ) (E : EdgeV (singleEdge n)) :
    Hypergraph.degree (triangleHypergraphSub (singleEdge n)) E = 0 := by
  rw [Hypergraph.degree, singleEdge_sub_empty]
  simp

/-- `singleEdge n` has at least one edge. -/
theorem singleEdge_edgeV_pos (n : ℕ) : 0 < Fintype.card (EdgeV (singleEdge n)) := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨_, singleEdge_edge n⟩⟩

/-- **The core refutation.**  The triangle hypergraph of the one-edge graph is not nearly
`d`-regular for any `d > 0`, band `μ < 1` and exceptional fraction `η < 1`. -/
theorem nearlyRegularMost_singleEdge_false (n : ℕ) {d μ η : ℝ} (hd : 0 < d) (hμ : μ < 1)
    (hη : η < 1) (hreg : NearlyRegularMost (triangleHypergraphSub (singleEdge n)) d μ η) :
    False := by
  obtain ⟨Exc, hcard, hdeg⟩ := hreg
  have hall : ∀ E : EdgeV (singleEdge n), E ∈ Exc := by
    intro E
    by_contra hE
    have h := (hdeg E hE).1
    rw [singleEdge_degree_zero n E, Nat.cast_zero] at h
    nlinarith
  have hExc : Exc = Finset.univ := Finset.eq_univ_of_forall hall
  rw [hExc, Finset.card_univ] at hcard
  have hpos : (0 : ℝ) < (Fintype.card (EdgeV (singleEdge n)) : ℝ) := by
    exact_mod_cast singleEdge_edgeV_pos n
  nlinarith

/-- **`NearRegObligation` is false.** -/
theorem not_nearRegObligation : ¬ NearRegObligation (1 / 2) (1 / 2) 1 := by
  rintro ⟨n₀, h⟩
  obtain ⟨d, hd, -, hreg, -, -⟩ :=
    h (Fin (n₀ + 2)) (singleEdge n₀) (by rw [Fintype.card_fin]; omega)
  exact nearlyRegularMost_singleEdge_false n₀ hd (by norm_num) (by norm_num) hreg

/-- **`NearRegObligationSized` is false** — this is the hypothesis `hReg` of
`Nibble.AX1.nibbleGap_holds`. -/
theorem not_nearRegObligationSized : ¬ NearRegObligationSized (1 / 2) (1 / 2) 1 1 := by
  rintro ⟨n₀, h⟩
  obtain ⟨d, hd, -, hreg, -, -, -⟩ :=
    h (Fin (n₀ + 2)) (singleEdge n₀) (by rw [Fintype.card_fin]; omega)
  exact nearlyRegularMost_singleEdge_false n₀ hd (by norm_num) (by norm_num) hreg

/-- **`NearRegObligationLinearSized` is false.** -/
theorem not_nearRegObligationLinearSized : ¬ NearRegObligationLinearSized (1 / 2) (1 / 2) 1 1 := by
  rintro ⟨n₀, h⟩
  obtain ⟨d, hd, -, hreg, -, -, -⟩ :=
    h (Fin (n₀ + 2)) (singleEdge n₀) (by rw [Fintype.card_fin]; omega)
  exact nearlyRegularMost_singleEdge_false n₀ hd (by norm_num) (by norm_num) hreg

/-- **The blocker hypothesis of `Nibble.AX1.nibbleGap_holds` is unsatisfiable.** -/
theorem not_forall_nearRegObligationSized :
    ¬ (∀ μ η d₀ K : ℝ, 0 < μ → 0 < η → 0 < d₀ → 0 < K → NearRegObligationSized μ η d₀ K) :=
  fun h => not_nearRegObligationSized
    (h (1 / 2) (1 / 2) 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- **The `NearRegObligation` form of the blocker is unsatisfiable too.** -/
theorem not_forall_nearRegObligation :
    ¬ (∀ μ η d₀ : ℝ, 0 < μ → 0 < η → 0 < d₀ → NearRegObligation μ η d₀) :=
  fun h => not_nearRegObligation (h (1 / 2) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num))

end Nibble.AX1
