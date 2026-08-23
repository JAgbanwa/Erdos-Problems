/-
# BKLO §9 for `r = 2`, `F = K₃`: the whole construction

Combining `BKLO.reps_exist` (one transversal triangle per triple of distinct parts) with
`BKLO.stages_exist` (one chain per ordered pair of distinct parts, realising all column pairs)
and `BKLO.reach_vecOf_of_pairs_reps` (column pairs and transversal representatives generate the
parity vector of every triangle) gives `BKLO.construction_exists`: an edge-disjoint family of
triangles of `G`, of bounded maximum degree, realising the parity vector of every triangle on the
vertex set of the partition.

Everything here is `sorry`-free.
-/
import BKLO.Section9Build
import BKLO.Section9Assembly

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

section Construct

variable {G : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {idx : Finset V → ℕ}
  {γ : ℝ} {D₀ Mtop Ecap kQ kR : ℕ}

/-- **The §9 construction.**  Under the greedy hypotheses (`hnum`) and with enough room in the
degree cap `Mtop` and in the edge budget `Ecap`, there is an edge-disjoint family `𝒯` of triangles
of `G`, with all vertices in `S`, of maximum degree at most `Mtop`, such that every triangle on
`⋃P` has the parity vector of some subfamily of `𝒯`. -/
theorem construction_exists
    (hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X')
    (hsubS : ∀ X ∈ P, X ⊆ S)
    (hne : ∀ X ∈ P, X.Nonempty)
    (hdegG : ∀ x ∈ S, ∀ X ∈ P, (1 / 2 + γ) * (X.card : ℝ) ≤ (degTo G x X : ℝ))
    (hnum : ∀ X ∈ P, ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ))
    (hkQ : P.card * P.card ≤ kQ) (hkR : P.card * P.card * P.card ≤ kR)
    (hMtop : D₀ + 8 + 4 * kQ + 6 ≤ Mtop)
    (hbud : 3 * (kR + 2 * S.card * kQ) ≤ Ecap) :
    ∃ 𝒯 : Finset (Finset V), IsTriFamily 𝒯 ∧ famEdges 𝒯 ⊆ G ∧
      (∀ v : V, edeg (famEdges 𝒯) v ≤ Mtop) ∧
      ∀ T₀ : Finset V, T₀.card = 3 → T₀ ⊆ P.biUnion id → Reach P idx 𝒯 (vecOf T₀) := by
  classical
  -- the list of ordered pairs of distinct parts
  set Q : List (Finset V × Finset V) :=
    ((P ×ˢ P).filter (fun p => p.1 ≠ p.2)).toList with hQdef
  -- the list of ordered triples of pairwise distinct parts
  set R : List (Finset V × Finset V × Finset V) :=
    ((P ×ˢ P ×ˢ P).filter (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)).toList with hRdef
  have hQmem : ∀ q : Finset V × Finset V, q ∈ Q ↔ (q.1 ∈ P ∧ q.2 ∈ P) ∧ q.1 ≠ q.2 := by
    intro q
    rw [hQdef, Finset.mem_toList, Finset.mem_filter, Finset.mem_product]
  have hRmem : ∀ t : Finset V × Finset V × Finset V,
      t ∈ R ↔ (t.1 ∈ P ∧ t.2.1 ∈ P ∧ t.2.2 ∈ P) ∧ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) := by
    intro t
    rw [hRdef, Finset.mem_toList, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  have hQlen : Q.length ≤ kQ := by
    have h1 : Q.length = ((P ×ˢ P).filter (fun p => p.1 ≠ p.2)).card := by
      rw [hQdef, Finset.length_toList]
    have h2 : ((P ×ˢ P).filter (fun p => p.1 ≠ p.2)).card ≤ (P ×ˢ P).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_product] at h2
    omega
  have hRlen : R.length ≤ kR := by
    have h1 : R.length
        = ((P ×ˢ P ×ˢ P).filter (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)).card := by
      rw [hRdef, Finset.length_toList]
    have h2 : ((P ×ˢ P ×ˢ P).filter (fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)).card
        ≤ (P ×ˢ P ×ˢ P).card := Finset.card_filter_le _ _
    rw [Finset.card_product, Finset.card_product] at h2
    have h3 : P.card * (P.card * P.card) = P.card * P.card * P.card := by ring
    omega
  -- Step 1: the transversal representatives
  have hemp : famEdges (∅ : Finset (Finset V)) = (∅ : Finset (Sym2 V)) := by simp [famEdges]
  obtain ⟨𝒯₁, -, hfam₁, hG₁, hS₁, hcard₁, hdeg₁, hrep₁⟩ :=
    reps_exist (idx := idx) hdisj hsubS hne hdegG hnum (D₀ + 2) le_rfl (by omega) R ∅
      (fun t ht => ⟨((hRmem t).1 ht).1.1, ((hRmem t).1 ht).1.2.1, ((hRmem t).1 ht).1.2.2,
        ((hRmem t).1 ht).2.1, ((hRmem t).1 ht).2.2.1, ((hRmem t).1 ht).2.2.2⟩)
      ⟨by simp, by simp⟩ (by rw [hemp]; exact Finset.empty_subset _) (by simp)
      (by simp only [Finset.card_empty, Nat.zero_add]; omega)
      (by intro v; rw [hemp]; simp [edeg])
  rw [Finset.card_empty] at hcard₁
  -- Step 2: the chains
  obtain ⟨𝒯, hsub, hfam, hG, hS, -, hdeg, hpair₂⟩ :=
    stages_exist (idx := idx) (D₀ := D₀) (Mtop := Mtop) (Ecap := Ecap)
      hdisj hsubS hne hdegG hnum Q 𝒯₁ (D₀ + 8)
      (fun q hq => ⟨((hQmem q).1 hq).1.1, ((hQmem q).1 hq).1.2, ((hQmem q).1 hq).2⟩)
      le_rfl (by omega) hfam₁ hG₁ hS₁
      (by
        have h1 : 2 * S.card * Q.length ≤ 2 * S.card * kQ :=
          Nat.mul_le_mul_left _ hQlen
        omega)
      (fun v => le_trans (hdeg₁ v) (by omega))
  refine ⟨𝒯, hfam, hG, ?_, ?_⟩
  · intro v
    have := hdeg v
    have h1 : 4 * Q.length ≤ 4 * kQ := Nat.mul_le_mul_left _ hQlen
    omega
  · intro T₀ hcard hsubT
    refine reach_vecOf_of_pairs_reps hfam hdisj ?_ ?_ T₀ hcard hsubT
    · -- the column pairs
      intro A hA a ha a' ha' B hB
      by_cases hAB : A = B
      · subst hAB
        refine (Reach.zero P idx 𝒯).congr ?_
        intro W hW x hx
        rw [uvec_own_part_eq_zero hdisj hA ha hx, uvec_own_part_eq_zero hdisj hA ha' hx]
        simp
      · exact hpair₂ (A, B) ((hQmem (A, B)).2 ⟨⟨hA, hB⟩, hAB⟩) a ha a' ha'
    · -- the transversal representatives
      intro A hA B hB C hC hAB hAC hBC
      obtain ⟨a, haA, b, hbB, c, hcC, hreach⟩ :=
        hrep₁ (A, B, C) ((hRmem (A, B, C)).2 ⟨⟨hA, hB, hC⟩, hAB, hAC, hBC⟩)
      exact ⟨a, haA, b, hbB, c, hcC, hreach.mono hsub⟩

end Construct

end BKLO
