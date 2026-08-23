/-
# BKLO §9 for `r = 2`, `F = K₃`: assembling the parity family

Two loops on top of `BKLO.chain_exists`:

* `BKLO.reps_exist` — one transversal triangle for each triple of distinct parts;
* `BKLO.stages_exist` — one chain for each ordered pair of distinct parts, realising all column
  pairs;

and their combination `BKLO.construction_exists`, which produces an edge-disjoint triangle family
of `G`, of bounded maximum degree, realising every column pair and one transversal triangle per
triple of distinct parts.

Everything here is `sorry`-free.
-/
import BKLO.Section9Chain

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

private theorem zmod2_pair_pair : ∀ p q s : ZMod 2, (p + q) + (p + s) = q + s := by decide +kernel
private theorem zmod2_self : ∀ p : ZMod 2, p + p = 0 := by decide +kernel

/-- A unit vector in the column of its own part vanishes on all admissible coordinates. -/
theorem uvec_own_part_eq_zero {P : Finset (Finset V)} {idx : Finset V → ℕ}
    (hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X')
    {A : Finset V} (hA : A ∈ P) {a : V} (ha : a ∈ A)
    {W : Finset V} {x : V} (hx : x ∈ beforeParts P idx W) :
    uvec a A x W = 0 := by
  by_cases hxa : x = a
  · subst hxa
    have hlt : idx A < idx W := idx_lt_of_mem_beforeParts hdisj hA ha hx
    have hWA : W ≠ A := by
      intro h
      rw [h] at hlt
      exact lt_irrefl _ hlt
    simp [uvec, hWA]
  · simp [uvec, hxa]

section Build

variable {G : Finset (Sym2 V)} {S : Finset V} {P : Finset (Finset V)} {idx : Finset V → ℕ}
  {γ : ℝ} {D₀ Mtop Ecap : ℕ}

/-! ### The transversal representatives -/

/-- **One transversal triangle for each triple of distinct parts.** -/
theorem reps_exist
    (hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X')
    (hsubS : ∀ X ∈ P, X ⊆ S)
    (hne : ∀ X ∈ P, X.Nonempty)
    (hdegG : ∀ x ∈ S, ∀ X ∈ P, (1 / 2 + γ) * (X.card : ℝ) ≤ (degTo G x X : ℝ))
    (hnum : ∀ X ∈ P, ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ))
    (M : ℕ) (hM : D₀ + 2 ≤ M) (hMtop : M ≤ Mtop) :
    ∀ (R : List (Finset V × Finset V × Finset V)) (𝒯 : Finset (Finset V)),
      (∀ t ∈ R, t.1 ∈ P ∧ t.2.1 ∈ P ∧ t.2.2 ∈ P ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) →
      IsTriFamily 𝒯 → famEdges 𝒯 ⊆ G → (∀ T ∈ 𝒯, T ⊆ S) →
      3 * (𝒯.card + R.length) ≤ Ecap →
      (∀ v, edeg (famEdges 𝒯) v ≤ M) →
      ∃ 𝒯' : Finset (Finset V), 𝒯 ⊆ 𝒯' ∧ IsTriFamily 𝒯' ∧ famEdges 𝒯' ⊆ G ∧
        (∀ T ∈ 𝒯', T ⊆ S) ∧ 𝒯'.card ≤ 𝒯.card + R.length ∧
        (∀ v, edeg (famEdges 𝒯') v ≤ M) ∧
        ∀ t ∈ R, ∃ a ∈ t.1, ∃ b ∈ t.2.1, ∃ c ∈ t.2.2,
          Reach P idx 𝒯' (vecOf ({a, b, c} : Finset V)) := by
  classical
  intro R
  induction R with
  | nil =>
    intro 𝒯 _ hfam hG hS _ hdeg
    exact ⟨𝒯, Finset.Subset.refl _, hfam, hG, hS, by simp, hdeg, by simp⟩
  | cons t R' ih =>
    intro 𝒯 hall hfam hG hS hbudget hdeg
    obtain ⟨hA, hB, hC, hAB, hAC, hBC⟩ := hall t (by simp)
    set A := t.1
    set B := t.2.1
    set C := t.2.2
    have hFcard : (famEdges 𝒯).card ≤ Ecap := by
      have h1 := famEdges_card_le hfam.card_three
      have hlen : 0 < (t :: R').length := by simp
      omega
    have hMtop' : ∀ v : V, edeg (famEdges 𝒯) v ≤ Mtop := fun v => le_trans (hdeg v) hMtop
    obtain ⟨p, hp⟩ := hne A hA
    have hpS : p ∈ S := hsubS A hA hp
    -- pick the vertex in `A`
    obtain ⟨a, haA, -, -, -, -, -, hadeg⟩ :=
      exists_common_nbr hdegG hpS hpS hA (famEdges 𝒯) hMtop' hFcard ({p, p} : Finset V)
        (card_pair_le_six p p) (hnum A hA)
    have haS : a ∈ S := hsubS A hA haA
    -- pick the vertex in `B`
    obtain ⟨b, hbB, -, hab, -, habF, -, hbdeg⟩ :=
      exists_common_nbr hdegG haS haS hB (famEdges 𝒯) hMtop' hFcard ({a, a} : Finset V)
        (card_pair_le_six a a) (hnum B hB)
    have hbS : b ∈ S := hsubS B hB hbB
    -- pick the vertex in `C`
    obtain ⟨c, hcC, -, hac, hbc, hacF, hbcF, hcdeg⟩ :=
      exists_common_nbr hdegG haS hbS hC (famEdges 𝒯) hMtop' hFcard ({a, b} : Finset V)
        (card_pair_le_six a b) (hnum C hC)
    have hcS : c ∈ S := hsubS C hC hcC
    have hab' : a ≠ b := fun h => hAB (part_unique hdisj hA hB haA (h ▸ hbB))
    have hac' : a ≠ c := fun h => hAC (part_unique hdisj hA hC haA (h ▸ hcC))
    have hbc' : b ≠ c := fun h => hBC (part_unique hdisj hB hC hbB (h ▸ hcC))
    set T : Finset V := {a, b, c} with hT
    have hTcard : T.card = 3 := card_triple_eq_three hab' hac' hbc'
    have hTS : T ⊆ S := by
      intro v hv
      simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hTG : cliqueEdges T ⊆ G :=
      cliqueEdges_subset_of_edges hab' hac' hbc' hab hbc hac
    have hTF : Disjoint (cliqueEdges T) (famEdges 𝒯) :=
      cliqueEdges_disjoint_of_notMem hab' hac' hbc' habF hbcF hacF
    set 𝒯₁ : Finset (Finset V) := insert T 𝒯 with h𝒯₁
    have hfam₁ : IsTriFamily 𝒯₁ := isTriFamily_insert hfam hTcard hTF
    have hF₁ : famEdges 𝒯₁ = famEdges 𝒯 ∪ cliqueEdges T := by
      rw [h𝒯₁, famEdges_insert, Finset.union_comm]
    have hdeg₁ : ∀ v : V, edeg (famEdges 𝒯₁) v ≤ M := by
      intro v
      by_cases hva : v = a
      · subst hva
        rw [hF₁]
        have := edeg_union_triangle_le hTcard (famEdges 𝒯) v
        omega
      · by_cases hvb : v = b
        · subst hvb
          rw [hF₁]
          have := edeg_union_triangle_le hTcard (famEdges 𝒯) v
          omega
        · by_cases hvc : v = c
          · subst hvc
            rw [hF₁]
            have := edeg_union_triangle_le hTcard (famEdges 𝒯) v
            omega
          · have hvT : v ∉ T := by simp [hT, hva, hvb, hvc]
            rw [hF₁, edeg_union_triangle_eq hTcard _ hvT]
            exact hdeg v
    have h𝒯₁card : 𝒯₁.card ≤ 𝒯.card + 1 := by rw [h𝒯₁]; exact Finset.card_insert_le _ _
    have hbudget' : 3 * (𝒯₁.card + R'.length) ≤ Ecap := by
      have hlen : (t :: R').length = R'.length + 1 := by simp
      omega
    have hG₁ : famEdges 𝒯₁ ⊆ G := by
      rw [hF₁]; exact Finset.union_subset hG hTG
    have hS₁ : ∀ T' ∈ 𝒯₁, T' ⊆ S := by
      intro T' hT'
      rcases Finset.mem_insert.1 hT' with rfl | hT'
      · exact hTS
      · exact hS T' hT'
    obtain ⟨𝒯', hsub', hfam', hG', hS', hcard', hdeg', hreal'⟩ :=
      ih 𝒯₁ (fun t' ht' => hall t' (by simp [ht'])) hfam₁ hG₁ hS₁ hbudget' hdeg₁
    refine ⟨𝒯', Finset.Subset.trans (Finset.subset_insert T 𝒯) hsub', hfam', hG', hS', ?_,
      hdeg', ?_⟩
    · simp only [List.length_cons]
      omega
    · intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · refine ⟨a, haA, b, hbB, c, hcC, ?_⟩
        have hmem : ({a, b, c} : Finset V) ∈ 𝒯₁ := by
          rw [h𝒯₁, ← hT]; exact Finset.mem_insert_self T 𝒯
        exact Reach.of_mem (idx := idx) (hsub' hmem)
      · exact hreal' t' ht'

/-! ### The chains -/

/-- **One chain for each ordered pair of distinct parts.** -/
theorem stages_exist
    (hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X')
    (hsubS : ∀ X ∈ P, X ⊆ S)
    (hne : ∀ X ∈ P, X.Nonempty)
    (hdegG : ∀ x ∈ S, ∀ X ∈ P, (1 / 2 + γ) * (X.card : ℝ) ≤ (degTo G x X : ℝ))
    (hnum : ∀ X ∈ P, ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ)) :
    ∀ (Q : List (Finset V × Finset V)) (𝒯 : Finset (Finset V)) (M : ℕ),
      (∀ q ∈ Q, q.1 ∈ P ∧ q.2 ∈ P ∧ q.1 ≠ q.2) →
      D₀ + 8 ≤ M → M + 4 * Q.length + 6 ≤ Mtop →
      IsTriFamily 𝒯 → famEdges 𝒯 ⊆ G → (∀ T ∈ 𝒯, T ⊆ S) →
      3 * (𝒯.card + 2 * S.card * Q.length) ≤ Ecap →
      (∀ v, edeg (famEdges 𝒯) v ≤ M) →
      ∃ 𝒯' : Finset (Finset V), 𝒯 ⊆ 𝒯' ∧ IsTriFamily 𝒯' ∧ famEdges 𝒯' ⊆ G ∧
        (∀ T ∈ 𝒯', T ⊆ S) ∧ 𝒯'.card ≤ 𝒯.card + 2 * S.card * Q.length ∧
        (∀ v, edeg (famEdges 𝒯') v ≤ M + 4 * Q.length) ∧
        ∀ q ∈ Q, ∀ a ∈ q.1, ∀ a' ∈ q.1,
          Reach P idx 𝒯' (fun x W' => uvec a q.2 x W' + uvec a' q.2 x W') := by
  classical
  intro Q
  induction Q with
  | nil =>
    intro 𝒯 M _ _ _ hfam hG hS _ hdeg
    exact ⟨𝒯, Finset.Subset.refl _, hfam, hG, hS, by simp, by simpa using hdeg, by simp⟩
  | cons q Q' ih =>
    intro 𝒯 M hall hM hMtop hfam hG hS hbudget hdeg
    obtain ⟨hU, hW, hUW⟩ := hall q (by simp)
    set U := q.1
    set W := q.2
    obtain ⟨r, hr⟩ := hne U hU
    set L : List V := (U.erase r).toList with hL
    have hLU : ∀ v ∈ L, v ∈ U := by
      intro v hv
      rw [hL, Finset.mem_toList] at hv
      exact Finset.mem_of_mem_erase hv
    have hLnodup : L.Nodup := by rw [hL]; exact Finset.nodup_toList _
    have hrL : r ∉ L := by
      rw [hL, Finset.mem_toList]
      exact fun hc => (Finset.ne_of_mem_erase hc) rfl
    have hLlen : L.length ≤ S.card := by
      rw [hL, Finset.length_toList]
      exact Finset.card_le_card (Finset.Subset.trans (Finset.erase_subset _ _) (hsubS U hU))
    have hbudL : 3 * (𝒯.card + 2 * L.length) ≤ Ecap := by
      have hb : 3 * (𝒯.card + 2 * S.card * (Q'.length + 1)) ≤ Ecap := by
        simpa [List.length_cons] using hbudget
      have h4 : 2 * S.card * (Q'.length + 1) = 2 * S.card * Q'.length + 2 * S.card := by ring
      rw [h4] at hb
      have h2 : 2 * L.length ≤ 2 * S.card := by omega
      omega
    have hchain := chain_exists (idx := idx) hdisj hsubS hdegG hnum hU hW hUW M (by omega)
      (by simp only [List.length_cons] at hMtop; omega) L r 𝒯 hr hLU hLnodup hrL hfam hG hS
      hbudL
      (fun v => le_trans (hdeg v) (by omega)) (fun v _ => hdeg v)
      (le_trans (hdeg r) (by omega))
    obtain ⟨𝒯₁, hsub₁, hfam₁, hG₁, hS₁, hcard₁, hdeg₁, hreal₁⟩ := hchain
    have hbudget' : 3 * (𝒯₁.card + 2 * S.card * Q'.length) ≤ Ecap := by
      have hb : 3 * (𝒯.card + 2 * S.card * (Q'.length + 1)) ≤ Ecap := by
        simpa [List.length_cons] using hbudget
      have h4 : 2 * S.card * (Q'.length + 1) = 2 * S.card * Q'.length + 2 * S.card := by ring
      rw [h4] at hb
      have h2 : 2 * L.length ≤ 2 * S.card := by omega
      omega
    obtain ⟨𝒯', hsub', hfam', hG', hS', hcard', hdeg', hreal'⟩ :=
      ih 𝒯₁ (M + 4) (fun q' hq' => hall q' (by simp [hq'])) (by omega)
        (by simp only [List.length_cons] at hMtop; omega) hfam₁ hG₁ hS₁ hbudget' hdeg₁
    refine ⟨𝒯', Finset.Subset.trans hsub₁ hsub', hfam', hG', hS', ?_, ?_, ?_⟩
    · have h2 : 2 * L.length ≤ 2 * S.card := by omega
      have h4 : 2 * S.card * (Q'.length + 1) = 2 * S.card * Q'.length + 2 * S.card := by ring
      simp only [List.length_cons]
      omega
    · intro v
      have := hdeg' v
      simp only [List.length_cons]
      omega
    · intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · -- the pair `q = (U, W)`
        intro a ha a' ha'
        have key : ∀ y ∈ U, Reach P idx 𝒯' (fun x W' => uvec r W x W' + uvec y W x W') := by
          intro y hy
          by_cases hyr : y = r
          · subst hyr
            refine (Reach.zero P idx 𝒯').congr ?_
            intro W'' _ x _
            exact (zmod2_self _).symm
          · have hyL : y ∈ L := by
              rw [hL, Finset.mem_toList]
              exact Finset.mem_erase.2 ⟨hyr, hy⟩
            exact (hreal₁ y hyL).mono hsub'
        refine ((key a ha).add hfam' (key a' ha')).congr ?_
        intro W'' _ x _
        exact zmod2_pair_pair _ _ _
      · exact hreal' q' hq'

end Build

end BKLO
