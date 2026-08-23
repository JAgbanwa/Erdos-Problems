/-
# Nibble — total magnitude bound for the sharp McDiarmid coefficient

This file double-counts the pairs of an edge `e` and a `v`-edge meeting the
neighbourhood of `e`, and bounds the resulting total using maximum degree and
maximum edge size.
-/
import Nibble.SumEstimate

open Finset Hypergraph

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- Swapping the two finite sums counts the same pairs `(e,f)`: the total sharp
coefficient equals the sum, over `v`-edges, of the number of `e` whose
neighbourhood meets that edge. -/
theorem sum_neighborCoef_swap (H : Finset (Finset V)) (v : V) :
    ∑ e ∈ H, neighborCoef H v e =
      ∑ f ∈ H.filter (fun f => v ∈ f),
        (H.filter (fun e => ¬ Disjoint f
          (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card := by
  unfold neighborCoef
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- For a fixed edge `f`, edges whose neighbourhood meets `f` are bounded by
summing over a witnessing vertex `y ∈ f`.  The first term counts edges directly
containing `y`; the second chooses a conflict edge `g` containing `y`, then a
vertex `z ∈ g` where `e` meets `g`. -/
theorem neighborhood_meeting_edges_le (H : Finset (Finset V)) (f : Finset V) :
    (H.filter (fun e => ¬ Disjoint f
      (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card ≤
      ∑ y ∈ f, (degree H y +
        ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z) := by
  have hsub : H.filter (fun e => ¬ Disjoint f
      (e ∪ support (H.filter (fun g => ¬ Disjoint e g)))) ⊆
      f.biUnion (fun y => H.filter (fun e => y ∈ e) ∪ f.biUnion (fun y => ((H.filter (fun g => y ∈ g)).biUnion
        (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e)))))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heH, hnd⟩ := he
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨y, hyf, hy⟩ := hnd
    simp only [Finset.mem_biUnion, Finset.mem_union]
    by_cases hye : y ∈ e
    · exact ⟨y, hyf, Or.inl (Finset.mem_filter.mpr ⟨heH, hye⟩)⟩
    · simp only [support] at hy
      rw [Finset.mem_union] at hy
      cases hy with
      | inl hye' => exact False.elim (hye hye')
      | inr hysupp =>
        simp only [Finset.mem_biUnion] at hysupp
        obtain ⟨g, hg, hyg⟩ := hysupp
        rw [Finset.mem_filter] at hg
        obtain ⟨hgH, hnjde⟩ := hg
        rw [Finset.not_disjoint_iff] at hnjde
        obtain ⟨z, hze, hzg⟩ := hnjde
        use y, hyf
        refine Or.inr ⟨y, hyf, g, Finset.mem_filter.mpr ⟨hgH, hyg⟩, z, hzg, Finset.mem_filter.mpr ⟨heH, hze⟩⟩
  have hsub' : H.filter (fun e => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g)))) ⊆
      (f.biUnion (fun y => H.filter (fun e => y ∈ e))) ∪
      (f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
          (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))) := by
    have : f.biUnion (fun y => H.filter (fun e => y ∈ e) ∪ f.biUnion (fun y => ((H.filter (fun g => y ∈ g)).biUnion
        (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e)))))) ⊆
        (f.biUnion (fun y => H.filter (fun e => y ∈ e))) ∪
        (f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
          (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))) := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_union] at hx ⊢
      obtain ⟨y, hyf, hxy⟩ := hx
      cases hxy with
      | inl hye => exact Or.inl ⟨y, hyf, hye⟩
      | inr hyc => exact Or.inr hyc
    exact Finset.Subset.trans hsub this
  have h1 : (f.biUnion fun y => H.filter (fun e => y ∈ e)).card ≤ ∑ y ∈ f, degree H y := by
    calc (f.biUnion fun y => H.filter (fun e => y ∈ e)).card
        ≤ ∑ y ∈ f, (H.filter (fun e => y ∈ e)).card := card_biUnion_le
      _ = ∑ y ∈ f, degree H y := by simp [degree]
  have h2 : (f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
        (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))).card ≤
        ∑ y ∈ f, ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z := by
    calc (f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
          (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))).card
        ≤ ∑ y ∈ f, ((H.filter (fun g => y ∈ g)).biUnion
            (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e)))).card := card_biUnion_le
      _ ≤ ∑ y ∈ f, ∑ g ∈ H.filter (fun g => y ∈ g),
            (g.biUnion (fun z => H.filter (fun e => z ∈ e))).card := by
          apply Finset.sum_le_sum
          intro y _
          exact card_biUnion_le
      _ ≤ ∑ y ∈ f, ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, (H.filter (fun e => z ∈ e)).card := by
          apply Finset.sum_le_sum
          intro y _
          apply Finset.sum_le_sum
          intro g _
          exact card_biUnion_le
      _ = ∑ y ∈ f, ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z := by simp [degree]
  calc (H.filter (fun e => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card
      ≤ (f.biUnion (fun y => H.filter (fun e => y ∈ e)) ∪
          f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
              (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))).card := by
        apply card_le_card hsub'
    _ ≤ (f.biUnion (fun y => H.filter (fun e => y ∈ e))).card +
        (f.biUnion (fun y => (H.filter (fun g => y ∈ g)).biUnion
            (fun g => g.biUnion (fun z => H.filter (fun e => z ∈ e))))).card := card_union_le _ _
    _ ≤ ∑ y ∈ f, degree H y + ∑ y ∈ f, ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z := add_le_add h1 h2
    _ = ∑ y ∈ f, (degree H y + ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z) := by
        rw [Finset.sum_add_distrib]

/-- Under maximum degree `Δ` and edge arity at most `r`, at most
`r * (Δ + Δ * (r * Δ))` edges have neighbourhood meeting a fixed edge of `H`. -/
theorem neighborhood_meeting_edges_le_uniform (H : Finset (Finset V))
    (f : Finset V) (Δ r : ℕ) (hf : f ∈ H)
    (hΔ : ∀ x, degree H x ≤ Δ) (huni : ∀ g ∈ H, g.card ≤ r) :
    (H.filter (fun e => ¬ Disjoint f
      (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card ≤
      r * (Δ + Δ * (r * Δ)) := by
  have hf_card : f.card ≤ r := huni f hf
  calc (H.filter (fun e => ¬ Disjoint f (e ∪ support (H.filter (fun g => ¬ Disjoint e g))))).card
      ≤ ∑ y ∈ f, (degree H y + ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, degree H z) :=
        neighborhood_meeting_edges_le H f
    _ ≤ ∑ y ∈ f, (Δ + ∑ g ∈ H.filter (fun g => y ∈ g), ∑ z ∈ g, Δ) := by
        apply Finset.sum_le_sum
        intro y _
        apply Nat.add_le_add
        · exact hΔ y
        · apply Finset.sum_le_sum
          intro g _
          calc ∑ z ∈ g, degree H z ≤ g.card * Δ := by
                have := Finset.sum_le_card_nsmul g (fun z => degree H z) Δ (fun z _ => hΔ z)
                simp only [nsmul_eq_mul] at this
                exact this
            _ = ∑ _ ∈ g, Δ := by simp [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ f, (Δ + ∑ g ∈ H.filter (fun g => y ∈ g), g.card * Δ) := by
        apply Finset.sum_le_sum
        intro y _
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro g _
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ f, (Δ + ∑ g ∈ H.filter (fun g => y ∈ g), r * Δ) := by
        apply Finset.sum_le_sum
        intro y _
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro g hg
        exact Nat.mul_le_mul_right Δ (huni g (Finset.mem_filter.mp hg).1)
    _ ≤ ∑ y ∈ f, (Δ + degree H y * (r * Δ)) := by
        apply Finset.sum_le_sum
        intro y _
        apply Nat.add_le_add_left
        have hdep : (H.filter (fun g => y ∈ g)).card ≤ degree H y := le_refl _
        calc ∑ g ∈ H.filter (fun g => y ∈ g), r * Δ = (H.filter (fun g => y ∈ g)).card * (r * Δ) := by simp
          _ ≤ degree H y * (r * Δ) := Nat.mul_le_mul_right _ hdep
    _ ≤ ∑ y ∈ f, (Δ + Δ * (r * Δ)) := by
        apply Finset.sum_le_sum
        intro y _
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_right _ (hΔ y)
    _ ≤ f.card * (Δ + Δ * (r * Δ)) := by simp
    _ ≤ r * (Δ + Δ * (r * Δ)) := Nat.mul_le_mul_right _ hf_card

/-- **Total magnitude bound.** If every vertex has degree at most `Δ` and every
edge has size at most `r`, then the total sharp McDiarmid coefficient at `v` is
at most `degree H v * r * (Δ + Δ * (r * Δ))`.  In particular, the bound is
independent of `|H|` and of the size of the ambient powerset. -/
theorem sum_neighborCoef_le_degree_mul (H : Finset (Finset V)) (v : V)
    (Δ r : ℕ) (hΔ : ∀ x, degree H x ≤ Δ)
    (huni : ∀ f ∈ H, f.card ≤ r) :
    ∑ e ∈ H, neighborCoef H v e ≤
      degree H v * (r * (Δ + Δ * (r * Δ))) := by
  rw [sum_neighborCoef_swap]
  have hdeg : degree H v = (H.filter (fun f => v ∈ f)).card := by simp [degree]
  rw [hdeg]
  have hconst : ∑ _f ∈ H.filter (fun f => v ∈ f), (r * (Δ + Δ * (r * Δ))) =
      (H.filter (fun f => v ∈ f)).card * (r * (Δ + Δ * (r * Δ))) := by
    simp [Finset.sum_const]
  rw [← hconst]
  apply Finset.sum_le_sum
  intro f hf
  exact neighborhood_meeting_edges_le_uniform H f Δ r (Finset.mem_filter.mp hf).1 hΔ huni


end Hypergraph
