/-
# BKLO §9 for `r = 2`, `F = K₃`: Lemma 9.3

This file fixes the constants of the §9 construction and proves

* `BKLO.parityFamilyExists_holds : BKLO.ParityFamilyExists` — the combinatorial core, and
* `BKLO.lemma93K3S_holds : BKLO.Lemma93K3S` — BKLO Lemma 9.3 (repaired statement) for `r = 2`,
  `F = K₃`.

The constants are
```
D₀   = ⌈96 k³ / γ⌉ + 1     (degree cap for the vertices used as apexes)
Mtop = D₀ + 8 + 4 k² + 6   (global degree cap of the parity graph)
Ecap = 3 (k³ + 2 n k²)     (edge budget: at most one triangle per representative and
                            two triangles per chain link)
```
and `n₀` is chosen so that both `Mtop ≤ γ n` and the greedy inequality
`6 + 2 Mtop + 2 Ecap/(D₀+1) < 2 γ |X|` hold for every part `X`.

Everything here is `sorry`-free.
-/
import BKLO.Section9Construct
import BKLO.Section9ParityK3
import Mathlib.Data.Nat.Cast.Order.Field

open Finset

namespace BKLO

set_option maxHeartbeats 400000 in
/-- **The combinatorial core of BKLO §9 for `r = 2`, `F = K₃` holds.** -/
theorem parityFamilyExists_holds : ParityFamilyExists := by
  classical
  intro k γ hk hγ
  set K : ℝ := (k : ℝ) with hKdef
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hk
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨D₀, hD₀def⟩ : ∃ m : ℕ, m = ⌈96 * K ^ 3 / γ⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨Mtop, hMtopdef⟩ : ∃ m : ℕ, m = D₀ + 8 + 4 * (k * k) + 6 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 6 + 2 * (Mtop : ℝ) + γ / 16 := ⟨_, rfl⟩
  refine ⟨⌈K * (C + 2 * γ) / γ⌉₊ + ⌈(Mtop : ℝ) / γ⌉₊ + 1, ?_⟩
  intro V _ G S P idx d hcard _hloop _hGS hd hpart
  set N : ℝ := (S.card : ℝ) with hNdef
  -- the two size conditions on `n`
  have hcardR : ((⌈K * (C + 2 * γ) / γ⌉₊ + ⌈(Mtop : ℝ) / γ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by
    rw [hNdef]; exact_mod_cast hcard
  have hceil₁ : K * (C + 2 * γ) / γ ≤ (⌈K * (C + 2 * γ) / γ⌉₊ : ℝ) := Nat.le_ceil _
  have hceil₂ : (Mtop : ℝ) / γ ≤ (⌈(Mtop : ℝ) / γ⌉₊ : ℝ) := Nat.le_ceil _
  have hceil₁' : (0 : ℝ) ≤ (⌈K * (C + 2 * γ) / γ⌉₊ : ℝ) := Nat.cast_nonneg _
  have hceil₂' : (0 : ℝ) ≤ (⌈(Mtop : ℝ) / γ⌉₊ : ℝ) := Nat.cast_nonneg _
  have hcast : ((⌈K * (C + 2 * γ) / γ⌉₊ + ⌈(Mtop : ℝ) / γ⌉₊ + 1 : ℕ) : ℝ)
      = (⌈K * (C + 2 * γ) / γ⌉₊ : ℝ) + (⌈(Mtop : ℝ) / γ⌉₊ : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hcardR
  have hNbig : K * (C + 2 * γ) / γ < N := by linarith only [hcardR, hceil₁]
  have hNMtop : (Mtop : ℝ) ≤ γ * N := by
    have h : (Mtop : ℝ) / γ ≤ N := by linarith only [hcardR, hceil₂]
    rw [div_le_iff₀ hγ] at h
    linarith only [h]
  -- the edge budget
  obtain ⟨Ecap, hEcapdef⟩ : ∃ m : ℕ, m = 3 * (k * k * k + 2 * S.card * (k * k)) := ⟨_, rfl⟩
  -- structural facts about the partition
  have hdisj : ∀ X ∈ P, ∀ X' ∈ P, X ≠ X' → Disjoint X X' := hpart.1.pairwise_disjoint
  have hsubS : ∀ X ∈ P, X ⊆ S := fun X hX => hpart.1.subset_of_mem hX
  have hdegG : ∀ x ∈ S, ∀ X ∈ P, (1 / 2 + γ) * (X.card : ℝ) ≤ (degTo G x X : ℝ) := by
    intro x hx X hX
    refine le_trans ?_ (hpart.2 x hx X hX)
    exact mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
  -- the greedy inequality
  have hnum : ∀ X ∈ P, ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) < 2 * γ * (X.card : ℝ) := by
    intro X hX
    set Xc : ℝ := (X.card : ℝ) with hXcdef
    -- the parts are almost equal
    have hlow : S.card / k ≤ X.card := hpart.1.size_lower X hX
    have hnat : S.card < k * X.card + k := by
      have h1 := Nat.div_add_mod S.card k
      have h2 := Nat.mod_lt S.card hk
      have h3 : k * (S.card / k) ≤ k * X.card := Nat.mul_le_mul_left _ hlow
      omega
    have hNK : N < K * Xc + K := by
      rw [hNdef, hXcdef, hKdef]; exact_mod_cast hnat
    have hXlow : N / K - 1 < Xc := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hKpos]
      linarith only [hNK]
    -- bounding the nat division
    have hDge : 96 * K ^ 3 / γ ≤ (D₀ : ℝ) + 1 := by
      have h : 96 * K ^ 3 / γ ≤ (⌈96 * K ^ 3 / γ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((D₀ : ℕ) : ℝ) = (⌈96 * K ^ 3 / γ⌉₊ : ℝ) + 1 := by
        rw [hD₀def]; push_cast; ring
      rw [h2]; linarith only [h]
    have hDpos : (0 : ℝ) < (D₀ : ℝ) + 1 := by positivity
    have hNnn : (0 : ℝ) ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
    have hfac : (0 : ℝ) ≤ γ * N / (8 * K) + γ / 16 := by positivity
    have hEcapR : 2 * (Ecap : ℝ) = 6 * K ^ 3 + 12 * N * K ^ 2 := by
      rw [hEcapdef, hNdef, hKdef]; push_cast; ring
    have hid : (γ * N / (8 * K) + γ / 16) * (96 * K ^ 3 / γ) = 6 * K ^ 3 + 12 * N * K ^ 2 := by
      field_simp
      ring
    have hmul : (γ * N / (8 * K) + γ / 16) * (96 * K ^ 3 / γ)
        ≤ (γ * N / (8 * K) + γ / 16) * ((D₀ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hDge hfac
    have hdiv₀ : 2 * (Ecap : ℝ) / ((D₀ : ℝ) + 1) ≤ γ * N / (8 * K) + γ / 16 := by
      rw [div_le_iff₀ hDpos]
      rw [hEcapR]
      rw [hid] at hmul
      linarith only [hmul]
    have hdivnat : ((2 * Ecap / (D₀ + 1) : ℕ) : ℝ) ≤ 2 * (Ecap : ℝ) / ((D₀ : ℝ) + 1) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 2 * Ecap) (n := D₀ + 1)
      push_cast at h
      exact h
    have hdiv : ((2 * Ecap / (D₀ + 1) : ℕ) : ℝ) ≤ γ * N / (8 * K) + γ / 16 :=
      le_trans hdivnat hdiv₀
    -- putting the pieces together
    have hlhs : ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ)
        = 6 + 2 * (Mtop : ℝ) + ((2 * Ecap / (D₀ + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hlhs]
    have hTdef : γ * N / (8 * K) = γ * N / K / 8 := by ring
    have hTnn : (0 : ℝ) ≤ γ * N / K := by positivity
    have hbig : C + 2 * γ < γ * N / K := by
      rw [lt_div_iff₀ hKpos]
      rw [div_lt_iff₀ hγ] at hNbig
      linarith only [hNbig]
    have hXstep : 2 * γ * (N / K - 1) < 2 * γ * Xc :=
      mul_lt_mul_of_pos_left hXlow (by positivity)
    have hNK' : 2 * γ * (N / K - 1) = 2 * (γ * N / K) - 2 * γ := by
      field_simp
    rw [hTdef] at hdiv
    rw [hCdef] at hbig
    linarith only [hdiv, hbig, hXstep, hNK']
  -- the parts are nonempty (from the greedy inequality)
  have hne : ∀ X ∈ P, X.Nonempty := by
    intro X hX
    rw [← Finset.card_pos]
    by_contra hcon
    have h0 : X.card = 0 := by omega
    have := hnum X hX
    rw [h0] at this
    simp only [Nat.cast_zero, mul_zero] at this
    have hge : (0 : ℝ) ≤ ((6 + 2 * Mtop + 2 * Ecap / (D₀ + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [this]
  -- the construction
  obtain ⟨𝒯, hfam, hGsub, hdeg, hreach⟩ :=
    construction_exists (idx := idx) (kQ := k * k) (kR := k * k * k)
      hdisj hsubS hne hdegG hnum
      (by rw [hpart.1.card_parts]) (by rw [hpart.1.card_parts])
      (by omega) (by omega)
  refine ⟨𝒯, hfam, hGsub, ?_, ?_⟩
  · intro v
    have h1 : ((edeg (famEdges 𝒯) v : ℕ) : ℝ) ≤ (Mtop : ℝ) := by exact_mod_cast hdeg v
    linarith only [hNMtop, h1]
  · intro T₀ hT₀card hT₀sub
    have hcover : P.biUnion id = S := hpart.1.cover
    obtain ⟨𝒮, hsub, hval⟩ := hreach T₀ hT₀card (by rw [hcover]; exact hT₀sub)
    exact ⟨𝒮, hsub, hval⟩

/-- **BKLO Lemma 9.3 for `r = 2`, `F = K₃`** (repaired statement `BKLO.Lemma93K3S`). -/
theorem lemma93K3S_holds : Lemma93K3S :=
  lemma93K3S_of_parityFamily parityFamilyExists_holds

end BKLO
