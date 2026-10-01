import PaperIV.TrianglePairingDefs

/-!
# RC01: unfolding a matching of the merged system

A matching of `bigFam H₃ H₄ = H₄ ∪ pairFam H₃` is turned back into a matching of the *mixed*
system `H₃ ∪ H₄` by splitting every selected merged set into its two triples.  This is where
the factor `2` of the construction is realised: one selected merged hyperedge yields **two**
triangles, so the triangle quota of the merged system is worth twice as much downstream.

* `unfoldMatching` — the unfolding;
* `unfold_isMatching` — it is a matching of `H₃ ∪ H₄`;
* `unfold_filter_four` — its `K₄` part is unchanged (ranks `3` and `6` cannot be confused);
* `unfold_card` — its size is `#(M ∩ H₄) + 2 · #(M \ H₄)`.
-/

namespace PaperIV.TrianglePairingSplit

open Finset
open PaperIV.TrianglePairingDefs

variable {W : Type*} [DecidableEq W]

/-- A chosen splitting of a merged set into two resource-disjoint triples. -/
noncomputable def splitPair (H₃ : Finset (Finset W)) (P : Finset W) : Finset W × Finset W :=
  if h : ∃ q ∈ pairDom H₃, q.1 ∪ q.2 = P then h.choose else (∅, ∅)

theorem splitPair_spec {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    splitPair H₃ P ∈ pairDom H₃ ∧ (splitPair H₃ P).1 ∪ (splitPair H₃ P).2 = P := by
  have h : ∃ q ∈ pairDom H₃, q.1 ∪ q.2 = P := mem_pairFam.1 hP
  rw [splitPair, dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

theorem splitPair_fst_mem {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    (splitPair H₃ P).1 ∈ H₃ :=
  (mem_pairDom.1 (splitPair_spec hP).1).1

theorem splitPair_snd_mem {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    (splitPair H₃ P).2 ∈ H₃ :=
  (mem_pairDom.1 (splitPair_spec hP).1).2.1

theorem splitPair_disjoint {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    Disjoint (splitPair H₃ P).1 (splitPair H₃ P).2 :=
  (mem_pairDom.1 (splitPair_spec hP).1).2.2

theorem splitPair_fst_subset {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    (splitPair H₃ P).1 ⊆ P := by
  intro a ha
  rw [← (splitPair_spec hP).2]
  exact Finset.mem_union_left _ ha

theorem splitPair_snd_subset {H₃ : Finset (Finset W)} {P : Finset W} (hP : P ∈ pairFam H₃) :
    (splitPair H₃ P).2 ⊆ P := by
  intro a ha
  rw [← (splitPair_spec hP).2]
  exact Finset.mem_union_right _ ha

/-- **The unfolding.**  Keep the `K₄` hyperedges, and replace every selected merged set by its
two triples. -/
noncomputable def unfoldMatching (H₃ H₄ : Finset (Finset W)) (M : Finset (Finset W)) :
    Finset (Finset W) :=
  M.filter (fun P => P ∈ H₄) ∪
    (M.filter (fun P => P ∉ H₄)).biUnion
      (fun P => {(splitPair H₃ P).1, (splitPair H₃ P).2})

section

variable {H₃ H₄ M : Finset (Finset W)}

/-- A selected hyperedge which is not a `K₄` hyperedge is a merged pair. -/
theorem mem_pairFam_of_mem_filter (hM : NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M)
    {P : Finset W} (hP : P ∈ M.filter (fun P => P ∉ H₄)) : P ∈ pairFam H₃ := by
  rw [Finset.mem_filter] at hP
  rcases Finset.mem_union.1 (hM.subset hP.1) with h | h
  · exact absurd h hP.2
  · exact h

/-- The two triples of a selected merged set are distinct. -/
theorem splitPair_ne (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) {P : Finset W}
    (hP : P ∈ pairFam H₃) : (splitPair H₃ P).1 ≠ (splitPair H₃ P).2 :=
  fst_ne_snd_of_mem_pairDom h3 (splitPair_spec hP).1

/-- Every element of the unfolding is a hyperedge of the mixed system. -/
theorem unfold_subset (hM : NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M) :
    unfoldMatching H₃ H₄ M ⊆ H₃ ∪ H₄ := by
  intro X hX
  rcases Finset.mem_union.1 hX with hX | hX
  · exact Finset.mem_union_right _ (Finset.mem_filter.1 hX).2
  · obtain ⟨P, hP, hXP⟩ := Finset.mem_biUnion.1 hX
    have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
    rcases Finset.mem_insert.1 hXP with rfl | hXP
    · exact Finset.mem_union_left _ (splitPair_fst_mem hPf)
    · rw [Finset.mem_singleton] at hXP
      subst hXP
      exact Finset.mem_union_left _ (splitPair_snd_mem hPf)

/-- Each element of the unfolding coming from a merged set is a nonempty subset of it. -/
theorem unfold_piece_subset (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) {P X : Finset W}
    (hP : P ∈ pairFam H₃) (hX : X ∈ ({(splitPair H₃ P).1, (splitPair H₃ P).2} :
      Finset (Finset W))) : X ⊆ P ∧ X.card = 3 := by
  rcases Finset.mem_insert.1 hX with rfl | hX
  · exact ⟨splitPair_fst_subset hP, h3 _ (splitPair_fst_mem hP)⟩
  · rw [Finset.mem_singleton] at hX
    subst hX
    exact ⟨splitPair_snd_subset hP, h3 _ (splitPair_snd_mem hP)⟩

/-- **The unfolding is a matching of the mixed system.** -/
theorem unfold_isMatching (h3 : NibblePort.Hypergraph.IsUniform H₃ 3)
    (hM : NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M) :
    NibblePort.Hypergraph.IsMatching (H₃ ∪ H₄) (unfoldMatching H₃ H₄ M) := by
  classical
  refine ⟨unfold_subset hM, ?_⟩
  intro X hX Y hY hXY
  -- describe the two kinds of members
  have hdesc : ∀ Z ∈ unfoldMatching H₃ H₄ M,
      (Z ∈ M ∧ Z ∈ H₄) ∨ ∃ P ∈ M.filter (fun P => P ∉ H₄), Z ⊆ P ∧ Z.Nonempty ∧
        Z ∈ ({(splitPair H₃ P).1, (splitPair H₃ P).2} : Finset (Finset W)) := by
    intro Z hZ
    rcases Finset.mem_union.1 hZ with hZ | hZ
    · exact Or.inl ⟨(Finset.mem_filter.1 hZ).1, (Finset.mem_filter.1 hZ).2⟩
    · obtain ⟨P, hP, hZP⟩ := Finset.mem_biUnion.1 hZ
      have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
      obtain ⟨hsub, hcard⟩ := unfold_piece_subset h3 hPf hZP
      refine Or.inr ⟨P, hP, hsub, ?_, hZP⟩
      rw [← Finset.card_pos, hcard]; omega
  rcases hdesc X hX with ⟨hXM, hXH⟩ | ⟨P, hP, hXsub, hXne, hXmem⟩ <;>
    rcases hdesc Y hY with ⟨hYM, hYH⟩ | ⟨Q, hQ, hYsub, hYne, hYmem⟩
  · exact hM.disjoint X hXM Y hYM hXY
  · -- X is a K₄ hyperedge, Y sits inside a merged set
    have hQM : Q ∈ M := (Finset.mem_filter.1 hQ).1
    have hQH : Q ∉ H₄ := (Finset.mem_filter.1 hQ).2
    have hne : X ≠ Q := fun h => hQH (h ▸ hXH)
    exact Finset.disjoint_of_subset_right hYsub (hM.disjoint X hXM Q hQM hne)
  · have hPM : P ∈ M := (Finset.mem_filter.1 hP).1
    have hPH : P ∉ H₄ := (Finset.mem_filter.1 hP).2
    have hne : P ≠ Y := fun h => hPH (h ▸ hYH)
    exact Finset.disjoint_of_subset_left hXsub (hM.disjoint P hPM Y hYM hne)
  · by_cases hPQ : P = Q
    · subst hPQ
      have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
      -- `X` and `Y` are the two distinct halves of `P`
      rcases Finset.mem_insert.1 hXmem with rfl | hX1 <;>
        rcases Finset.mem_insert.1 hYmem with rfl | hY1
      · exact absurd rfl hXY
      · rw [Finset.mem_singleton] at hY1
        subst hY1
        exact splitPair_disjoint hPf
      · rw [Finset.mem_singleton] at hX1
        subst hX1
        exact (splitPair_disjoint hPf).symm
      · rw [Finset.mem_singleton] at hX1 hY1
        subst hX1; subst hY1
        exact absurd rfl hXY
    · have hPM : P ∈ M := (Finset.mem_filter.1 hP).1
      have hQM : Q ∈ M := (Finset.mem_filter.1 hQ).1
      exact Finset.disjoint_of_subset_left hXsub
        (Finset.disjoint_of_subset_right hYsub (hM.disjoint P hPM Q hQM hPQ))

/-- **The `K₄` part is untouched by the unfolding**: a triple cannot be a `K₄` hyperedge. -/
theorem unfold_filter_four (h3 : NibblePort.Hypergraph.IsUniform H₃ 3)
    (h4 : NibblePort.Hypergraph.IsUniform H₄ 6)
    (hM : NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M) :
    (unfoldMatching H₃ H₄ M).filter (fun P => P ∈ H₄) = M.filter (fun P => P ∈ H₄) := by
  classical
  ext X
  simp only [Finset.mem_filter, unfoldMatching, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨hX | ⟨P, hP, hXP⟩, hXH⟩
    · exact ⟨hX.1, hXH⟩
    · exfalso
      have hPf : P ∈ pairFam H₃ :=
        mem_pairFam_of_mem_filter hM (Finset.mem_filter.2 hP)
      obtain ⟨-, hcard⟩ := unfold_piece_subset h3 hPf hXP
      have := h4 X hXH
      omega
  · rintro ⟨hXM, hXH⟩
    exact ⟨Or.inl ⟨hXM, hXH⟩, hXH⟩

/-- **The size of the unfolding**: every merged set contributes two triples. -/
theorem unfold_card (h3 : NibblePort.Hypergraph.IsUniform H₃ 3)
    (h4 : NibblePort.Hypergraph.IsUniform H₄ 6)
    (hM : NibblePort.Hypergraph.IsMatching (bigFam H₃ H₄) M) :
    (unfoldMatching H₃ H₄ M).card
      = (M.filter (fun P => P ∈ H₄)).card + 2 * (M.filter (fun P => P ∉ H₄)).card := by
  classical
  set B := (M.filter (fun P => P ∉ H₄)).biUnion
    (fun P => {(splitPair H₃ P).1, (splitPair H₃ P).2}) with hB
  -- the pieces of distinct merged sets are distinct
  have hpair : ∀ P ∈ M.filter (fun P => P ∉ H₄), ∀ Q ∈ M.filter (fun P => P ∉ H₄), P ≠ Q →
      Disjoint ({(splitPair H₃ P).1, (splitPair H₃ P).2} : Finset (Finset W))
        {(splitPair H₃ Q).1, (splitPair H₃ Q).2} := by
    intro P hP Q hQ hPQ
    have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
    have hQf : Q ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hQ
    have hdPQ : Disjoint P Q :=
      hM.disjoint P (Finset.mem_filter.1 hP).1 Q (Finset.mem_filter.1 hQ).1 hPQ
    rw [Finset.disjoint_left]
    intro X hX hX'
    obtain ⟨hsubP, hcard⟩ := unfold_piece_subset h3 hPf hX
    obtain ⟨hsubQ, -⟩ := unfold_piece_subset h3 hQf hX'
    have hXne : X.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    obtain ⟨v, hv⟩ := hXne
    exact (Finset.disjoint_left.1 hdPQ) (hsubP hv) (hsubQ hv)
  have hcardB : B.card = 2 * (M.filter (fun P => P ∉ H₄)).card := by
    rw [hB, Finset.card_biUnion hpair]
    have hterm : ∀ P ∈ M.filter (fun P => P ∉ H₄),
        ({(splitPair H₃ P).1, (splitPair H₃ P).2} : Finset (Finset W)).card = 2 := by
      intro P hP
      have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact splitPair_ne h3 hPf), Finset.card_singleton]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
  have hdisj : Disjoint (M.filter (fun P => P ∈ H₄)) B := by
    rw [Finset.disjoint_left]
    intro X hX hX'
    obtain ⟨P, hP, hXP⟩ := Finset.mem_biUnion.1 hX'
    have hPf : P ∈ pairFam H₃ := mem_pairFam_of_mem_filter hM hP
    obtain ⟨-, hcard⟩ := unfold_piece_subset h3 hPf hXP
    have := h4 X (Finset.mem_filter.1 hX).2
    omega
  rw [unfoldMatching, ← hB, Finset.card_union_of_disjoint hdisj, hcardB]

end

end PaperIV.TrianglePairingSplit

