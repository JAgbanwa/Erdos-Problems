import E32.Deletion

/-!
# E32 — the deletion induction (step 2, iterated)

`stableAt_all`: from edit stability for graphs of minimum degree `≥ (1/3 − ε) n`
(constant `K₁`, deficit window `γ₁ n²`) and Theorem C, edit stability holds for all graphs of
rooted defect `s`, with constant `K = max K₁ (2/ε)`, under the invariant `δ ≤ γ₀ n (n − N)`,
`γ₀ = min γ₁ (ε/4)`. `editStable_of_minDeg` restates it with the window `(γ₀/2) n²`.
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic

/-- The induction claim at order `n`. -/
def StableAt (s : ℕ) (γ₀ K : ℚ) (N n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ₀ * (n : ℚ) * ((n : ℚ) - N) →
      LowerAt G ((defectTarget s n : ℚ) - δ) →
        ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧ (rootEdit G C D H : ℚ) ≤ K * δ

/-- Edit stability restricted to minimum degree `≥ (1/3 − ε) n`. -/
def MinDegEditStable (s : ℕ) (ε γ₁ K₁ : ℚ) (N₁ : ℕ) : Prop :=
  ∀ n, N₁ ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    (∀ v, ((1 : ℚ) / 3 - ε) * n ≤ (G.degree v : ℚ)) →
    ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ₁ * (n : ℚ) ^ 2 → LowerAt G ((defectTarget s n : ℚ) - δ) →
      ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧ (rootEdit G C D H : ℚ) ≤ K₁ * δ

/-- Theorem C at a threshold. -/
def TheoremCAt (s NC : ℕ) : Prop :=
  ∀ n, NC ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n

theorem stableAt_all (s : ℕ) {ε γ₁ K₁ : ℚ} {N₁ NC : ℕ} (hε : 0 < ε) (hγ₁ : 0 < γ₁)
    (hK₁ : 0 ≤ K₁) (hmin : MinDegEditStable s ε γ₁ K₁ N₁) (hC : TheoremCAt s NC)
    (N : ℕ) (hN1 : N₁ ≤ N) (hNC : NC + 1 ≤ N) (hNs : s + 3 ≤ N) (hNε : 1 ≤ ε * N)
    (hNK : max K₁ (2 / ε) + 1 ≤ (N : ℚ)) :
    ∀ n, N ≤ n → StableAt s (min γ₁ (ε / 4)) (max K₁ (2 / ε)) N n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hmN G _ hdef δ hδ0 hδ hlow
    set γ₀ := min γ₁ (ε / 4) with hγ₀def
    set K := max K₁ (2 / ε) with hKdef
    have hγ₀ : 0 < γ₀ := lt_min hγ₁ (by positivity)
    have hγ₀1 : γ₀ ≤ γ₁ := min_le_left _ _
    have hγ₀2 : γ₀ ≤ ε / 4 := min_le_right _ _
    have hK1 : K₁ ≤ K := le_max_left _ _
    have hK2 : 2 / ε ≤ K := le_max_right _ _
    have hK0 : 0 ≤ K := le_trans hK₁ hK1
    have hmQ : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
    have hNQ : (N : ℚ) ≤ (m : ℚ) + 1 := by rw [← hmQ]; exact_mod_cast hmN
    have hN0 : (0 : ℚ) ≤ N := Nat.cast_nonneg N
    have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    rw [hmQ] at hδ
    by_cases hdeg : ∀ v, ((1 : ℚ) / 3 - ε) * ((m + 1 : ℕ) : ℚ) ≤ (G.degree v : ℚ)
    · have hδ' : δ ≤ γ₁ * ((m + 1 : ℕ) : ℚ) ^ 2 := by
        rw [hmQ]
        calc δ ≤ γ₀ * ((m : ℚ) + 1) * ((m : ℚ) + 1 - N) := hδ
          _ ≤ γ₀ * ((m : ℚ) + 1) * ((m : ℚ) + 1) := by
              apply mul_le_mul_of_nonneg_left (by linarith); positivity
          _ ≤ γ₁ * ((m : ℚ) + 1) ^ 2 := by
              rw [mul_assoc, ← sq]
              exact mul_le_mul_of_nonneg_right hγ₀1 (by positivity)
      obtain ⟨C, D, H, hR, hE⟩ := hmin (m + 1) (by omega) G hdef hdeg δ hδ0 hδ' hlow
      exact ⟨C, D, H, hR, le_trans hE (mul_le_mul_of_nonneg_right hK1 hδ0)⟩
    · push_neg at hdeg
      obtain ⟨v, hv⟩ := hdeg
      rw [hmQ] at hv
      set G' := deleteV G v with hG'
      set t : ℕ := (m + s + 2) / 3 with ht
      set δ' : ℚ := δ + (G.degree v : ℚ) - t with hδ'def
      have hsucc := A4S1.MinDegreeAll.defectTarget_succ s m (by omega)
      have hlow' : LowerAt G' ((defectTarget s m : ℚ) - δ') := by
        intro Q' hQ'4
        obtain ⟨Q, hQ4, hQ⟩ := lift_partition G v Q' hQ'4
        have h1 := hlow Q hQ4
        have h2 : (Q.size : ℚ) ≤ Q'.size + G.degree v := by exact_mod_cast hQ
        have h3 : (defectTarget s (m + 1) : ℚ) = defectTarget s m + t := by
          rw [hsucc]; push_cast; ring
        rw [hδ'def]; linarith
      have hδ'0 : 0 ≤ δ' := by
        obtain ⟨Q', hQ'4, hQ'⟩ := hC m (by omega) G' (rootedDefectAt_deleteV G v hdef)
        have h1 := hlow' Q' hQ'4
        have h2 : (Q'.size : ℚ) ≤ defectTarget s m := by exact_mod_cast hQ'
        linarith
      have htQ : (m : ℚ) / 3 ≤ t := by
        have h1 : m ≤ 3 * t := by omega
        have h2 : (m : ℚ) ≤ 3 * (t : ℚ) := by exact_mod_cast h1
        linarith
      have hδ'le : δ' ≤ δ - ε * ((m : ℚ) + 1) + 1 / 3 := by
        rw [hδ'def]; linarith
      have hεm : 1 ≤ ε * ((m : ℚ) + 1) :=
        le_trans hNε (mul_le_mul_of_nonneg_left hNQ hε.le)
      by_cases hmN' : N ≤ m
      · have hmNQ : (N : ℚ) ≤ m := by exact_mod_cast hmN'
        have hδ'b : δ' ≤ γ₀ * (m : ℚ) * ((m : ℚ) - N) := by
          have e1 : γ₀ * ((m : ℚ) + 1) * ((m : ℚ) + 1 - N) =
              γ₀ * m * (m - N) + γ₀ * (2 * m + 1 - N) := by ring
          have h0 : 0 ≤ 2 * (m : ℚ) + 1 - N := by linarith
          have e2 : γ₀ * (2 * (m : ℚ) + 1 - N) ≤ ε * ((m : ℚ) + 1) / 2 := by
            calc γ₀ * (2 * (m : ℚ) + 1 - N) ≤ (ε / 4) * (2 * (m : ℚ) + 1 - N) :=
                  mul_le_mul_of_nonneg_right hγ₀2 h0
              _ ≤ (ε / 4) * (2 * ((m : ℚ) + 1)) :=
                  mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = ε * ((m : ℚ) + 1) / 2 := by ring
          linarith
        obtain ⟨C, D, H, hR, hE⟩ :=
          ih hmN' G' (rootedDefectAt_deleteV G v hdef) δ' hδ'0 hδ'b hlow'
        obtain ⟨hR', hE'⟩ := root_lift G v hR
        refine ⟨_, _, _, hR', ?_⟩
        have hE'Q : (rootEdit G (C.map (skip v)) (D.map (skip v)) (insert v (H.map (skip v))) : ℚ)
            ≤ rootEdit G' C D H + m := by exact_mod_cast hE'
        have hKε : 2 ≤ K * ε := by
          have := (div_le_iff₀ hε).1 hK2; linarith
        have hKm : K ≤ m := by linarith
        have h1 : K * δ' ≤ K * (δ - ε * ((m : ℚ) + 1) + 1 / 3) :=
          mul_le_mul_of_nonneg_left hδ'le hK0
        have h2 : 2 * ((m : ℚ) + 1) ≤ K * ε * ((m : ℚ) + 1) :=
          mul_le_mul_of_nonneg_right hKε (by positivity)
        have h3 : K * (δ - ε * ((m : ℚ) + 1) + 1 / 3) =
            K * δ - K * ε * ((m : ℚ) + 1) + K / 3 := by ring
        linarith
      · have hmeq : m + 1 = N := by omega
        have hz : (m : ℚ) + 1 - N = 0 := by rw [← hmeq]; push_cast; ring
        rw [hz, mul_zero] at hδ
        linarith

/-- **Edit stability for all graphs of rooted defect `s`**, from the minimum-degree case. -/
theorem editStable_of_minDeg (s : ℕ) {ε γ₁ K₁ : ℚ} {N₁ NC : ℕ} (hε : 0 < ε) (hγ₁ : 0 < γ₁)
    (hK₁ : 0 ≤ K₁) (hmin : MinDegEditStable s ε γ₁ K₁ N₁) (hC : TheoremCAt s NC) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      RootedDefectAt G s → ∀ δ : ℚ, 0 ≤ δ → δ ≤ min γ₁ (ε / 4) / 2 * (n : ℚ) ^ 2 →
        LowerAt G ((defectTarget s n : ℚ) - δ) →
          ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧
            (rootEdit G C D H : ℚ) ≤ max K₁ (2 / ε) * δ := by
  set N₀ : ℕ := N₁ + NC + s + 3 + ⌈1 / ε⌉₊ + ⌈max K₁ (2 / ε)⌉₊ + 1 with hN₀
  have hNε : 1 ≤ ε * N₀ := by
    have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : (⌈1 / ε⌉₊ : ℚ) ≤ N₀ := by rw [hN₀]; push_cast; linarith [Nat.cast_nonneg (α := ℚ) ⌈max K₁ (2 / ε)⌉₊, Nat.cast_nonneg (α := ℚ) N₁, Nat.cast_nonneg (α := ℚ) NC, Nat.cast_nonneg (α := ℚ) s]
    have h3 : 1 / ε ≤ N₀ := le_trans h1 h2
    have := (div_le_iff₀ hε).1 h3
    linarith
  have hNK : max K₁ (2 / ε) + 1 ≤ (N₀ : ℚ) := by
    have h1 : max K₁ (2 / ε) ≤ (⌈max K₁ (2 / ε)⌉₊ : ℚ) := Nat.le_ceil _
    rw [hN₀]; push_cast
    linarith [Nat.cast_nonneg (α := ℚ) ⌈1 / ε⌉₊, Nat.cast_nonneg (α := ℚ) N₁,
      Nat.cast_nonneg (α := ℚ) NC, Nat.cast_nonneg (α := ℚ) s]
  have hall := stableAt_all s hε hγ₁ hK₁ hmin hC N₀ (by omega) (by omega) (by omega) hNε hNK
  refine ⟨2 * N₀, ?_⟩
  intro n hn G _ hdef δ hδ0 hδ hlow
  apply hall n (by omega) G hdef δ hδ0 _ hlow
  have hγ₀ : 0 ≤ min γ₁ (ε / 4) := le_min hγ₁.le (by positivity)
  have hnN : 2 * (N₀ : ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  calc δ ≤ min γ₁ (ε / 4) / 2 * (n : ℚ) ^ 2 := hδ
    _ = min γ₁ (ε / 4) * (n : ℚ) * ((n : ℚ) / 2) := by ring
    _ ≤ min γ₁ (ε / 4) * (n : ℚ) * ((n : ℚ) - N₀) := by
        apply mul_le_mul_of_nonneg_left (by linarith); positivity

end E32
