/-
# A self-contained finite Bernoulli probability space, with a Chernoff–Hoeffding bound.

The proof of BKLO Lemma 7.2 is probabilistic: one keeps every edge of `G` independently with
probability `ρ` and shows that the resulting subgraph has the required degree, codegree and
neighbourhood statistics with high probability.

This file develops, from scratch and by purely finitary means, exactly the amount of probability
theory that this argument needs.  The sample space is the powerset of a finite index set `I`, a
sample `A ⊆ I` carrying the weight

`wt ρ I A = ρ ^ |A| * (1 - ρ) ^ |I \ A|`,

which is the law of the `ρ`-random subset of `I`.  The main results are

* `BKLO.Bern.sum_wt` — the weights sum to `1`;
* `BKLO.Bern.expect_prod_blocks` — independence: the expectation of a product of functions of
  pairwise disjoint blocks of coordinates factorises;
* `BKLO.Bern.tail_upper`, `BKLO.Bern.tail_lower` — Chernoff–Hoeffding bounds
  `ℙ[ |Y - 𝔼Y| ≥ t ] ≤ exp (-t² / (4m))` for `Y A = #{z ∈ K : B z ⊆ A}`, the number of *blocks*
  entirely contained in the sample (`|B z| = 1` gives a degree, `|B z| = 2` a codegree), where
  `m ≥ |K|`;
* `BKLO.Bern.exists_of_sum_lt_one` — the probabilistic method: an event of weight `< 1` misses
  some sample.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity

open Finset

namespace BKLO.Bern

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-! ### The weight of a sample -/

/-- The weight of the sample `A` for the `ρ`-random subset of `I`. -/
noncomputable def wt (ρ : ℝ) (I A : Finset α) : ℝ := ρ ^ A.card * (1 - ρ) ^ (I \ A).card

/-- The expectation of `F` under the `ρ`-random subset of `I`. -/
noncomputable def expect (ρ : ℝ) (I : Finset α) (F : Finset α → ℝ) : ℝ :=
  ∑ A ∈ I.powerset, wt ρ I A * F A

theorem wt_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (I A : Finset α) : 0 ≤ wt ρ I A :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

theorem sum_wt (ρ : ℝ) (I : Finset α) : ∑ A ∈ I.powerset, wt ρ I A = 1 := by
  have h := Finset.prod_add (fun _ : α => ρ) (fun _ => 1 - ρ) I
  simp only [Finset.prod_const, add_sub_cancel, one_pow] at h
  simpa [wt] using h.symm

theorem wt_split (ρ : ℝ) {I B A : Finset α} (hB : B ⊆ I) :
    wt ρ I A = wt ρ B (A ∩ B) * wt ρ (I \ B) (A \ B) := by
  have h1 : A.card = (A ∩ B).card + (A \ B).card :=
    (Finset.card_inter_add_card_sdiff A B).symm
  have e1 : B \ (A ∩ B) = B \ A := by ext x; simp
  have e2 : (I \ B) \ (A \ B) = (I \ A) \ B := by
    ext x; simp only [Finset.mem_sdiff]; tauto
  have h2 : (I \ A).card = (B \ A).card + ((I \ A) \ B).card := by
    have h3 : ((I \ A) ∩ B).card + ((I \ A) \ B).card = (I \ A).card :=
      Finset.card_inter_add_card_sdiff _ _
    have e3 : (I \ A) ∩ B = B \ A := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, h⟩, hx⟩; exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨⟨hB hx, h⟩, hx⟩
    rw [e3] at h3; omega
  unfold wt
  rw [h1, h2, e1, e2, pow_add, pow_add]
  ring

/-! ### Independence -/

/-- Splitting a sum over the powerset of `I` along a subset `B ⊆ I`. -/
theorem sum_powerset_split {I B : Finset α} (hB : B ⊆ I) (f g : Finset α → ℝ) :
    ∑ A ∈ I.powerset, f (A ∩ B) * g (A \ B)
      = (∑ C ∈ B.powerset, f C) * (∑ D ∈ (I \ B).powerset, g D) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun A => (A ∩ B, A \ B)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_powerset] at hA
    exact Finset.mem_product.2 ⟨Finset.mem_powerset.2 Finset.inter_subset_right,
      Finset.mem_powerset.2 (Finset.sdiff_subset_sdiff hA (Finset.Subset.refl B))⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    simp only [Finset.mem_powerset]
    exact Finset.union_subset (hp.1.trans hB) (hp.2.trans Finset.sdiff_subset)
  · intro A hA
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨h1, h2⟩ := hp
    have hd : ∀ x ∈ p.2, x ∉ B := fun x hx => (Finset.mem_sdiff.1 (h2 hx)).2
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hxB⟩
        · exact h
        · exact absurd hxB (hd x h)
      · intro hx; exact ⟨Or.inl hx, h1 hx⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hxB⟩
        · exact absurd (h1 h) hxB
        · exact h
      · intro hx; exact ⟨Or.inr hx, hd x hx⟩
  · intro A hA; rfl

theorem expect_split {I B : Finset α} (ρ : ℝ) (hB : B ⊆ I) (f g : Finset α → ℝ) :
    expect ρ I (fun A => f (A ∩ B) * g (A \ B)) = expect ρ B f * expect ρ (I \ B) g := by
  unfold expect
  rw [← sum_powerset_split hB (fun C => wt ρ B C * f C) (fun D => wt ρ (I \ B) D * g D)]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [wt_split ρ (A := A) hB]
  ring

/-- **Independence.**  The expectation of a product of functions of pairwise disjoint blocks of
coordinates factorises. -/
theorem expect_prod_blocks (ρ : ℝ) (K : Finset β) (B : β → Finset α) (g : β → Finset α → ℝ) :
    ∀ I : Finset α, (∀ z ∈ K, B z ⊆ I) →
      (∀ z ∈ K, ∀ z' ∈ K, z ≠ z' → Disjoint (B z) (B z')) →
      expect ρ I (fun A => ∏ z ∈ K, g z (A ∩ B z)) = ∏ z ∈ K, expect ρ (B z) (g z) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    intro I _ _
    simp only [Finset.prod_empty, expect, mul_one]
    exact sum_wt ρ I
  | insert z₀ K hz₀ ih =>
    intro I hBI hdisj
    have hz₀I : B z₀ ⊆ I := hBI z₀ (Finset.mem_insert_self _ _)
    have key : (fun A : Finset α => ∏ z ∈ insert z₀ K, g z (A ∩ B z))
        = (fun A : Finset α => g z₀ (A ∩ B z₀) * ∏ z ∈ K, g z ((A \ B z₀) ∩ B z)) := by
      funext A
      rw [Finset.prod_insert hz₀]
      congr 1
      refine Finset.prod_congr rfl fun z hz => ?_
      congr 1
      have hne : z ≠ z₀ := fun h => hz₀ (h ▸ hz)
      have hdz : Disjoint (B z) (B z₀) :=
        hdisj z (Finset.mem_insert_of_mem hz) z₀ (Finset.mem_insert_self _ _) hne
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hx, hxz⟩
        exact ⟨⟨hx, fun hc => (Finset.disjoint_left.1 hdz hxz hc)⟩, hxz⟩
      · rintro ⟨⟨hx, _⟩, hxz⟩
        exact ⟨hx, hxz⟩
    rw [key, expect_split ρ hz₀I (g z₀) (fun D => ∏ z ∈ K, g z (D ∩ B z)),
      ih (I \ B z₀) ?_ ?_, Finset.prod_insert hz₀]
    · intro z hz
      have hne : z ≠ z₀ := fun h => hz₀ (h ▸ hz)
      have hdz : Disjoint (B z) (B z₀) :=
        hdisj z (Finset.mem_insert_of_mem hz) z₀ (Finset.mem_insert_self _ _) hne
      intro x hx
      exact Finset.mem_sdiff.2 ⟨hBI z (Finset.mem_insert_of_mem hz) hx,
        fun hc => Finset.disjoint_left.1 hdz hx hc⟩
    · intro z hz z' hz' hne
      exact hdisj z (Finset.mem_insert_of_mem hz) z' (Finset.mem_insert_of_mem hz') hne

/-! ### The moment generating function -/

theorem expect_block (ρ : ℝ) (B : Finset α) (lam : ℝ) :
    expect ρ B (fun C => Real.exp (lam * ((if B ⊆ C then (1:ℝ) else 0) - ρ ^ B.card)))
      = ρ ^ B.card * Real.exp (lam * (1 - ρ ^ B.card))
        + (1 - ρ ^ B.card) * Real.exp (lam * (0 - ρ ^ B.card)) := by
  classical
  have hBmem : B ∈ B.powerset := Finset.mem_powerset.2 (Finset.Subset.refl _)
  have hwtB : wt ρ B B = ρ ^ B.card := by simp [wt]
  unfold expect
  rw [← Finset.add_sum_erase _ _ hBmem]
  have h2 : ∀ C ∈ B.powerset.erase B,
      wt ρ B C * Real.exp (lam * ((if B ⊆ C then (1:ℝ) else 0) - ρ ^ B.card))
        = wt ρ B C * Real.exp (lam * (0 - ρ ^ B.card)) := by
    intro C hC
    have hCne : C ≠ B := (Finset.mem_erase.1 hC).1
    have hCsub : C ⊆ B := Finset.mem_powerset.1 (Finset.mem_erase.1 hC).2
    have : ¬ B ⊆ C := fun h => hCne (Finset.Subset.antisymm hCsub h)
    simp [this]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, hwtB]
  have h3 : ∑ C ∈ B.powerset.erase B, wt ρ B C = 1 - ρ ^ B.card := by
    have := sum_wt ρ B
    rw [← Finset.add_sum_erase _ _ hBmem, hwtB] at this
    linarith only [this]
  rw [h3]
  simp

/-- Hoeffding's lemma for one bounded Bernoulli block. -/
theorem block_mgf_le {p lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hlam : |lam| ≤ 1) :
    p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (lam * (0 - p))
      ≤ Real.exp (3 / 4 * lam ^ 2) := by
  have hkey : |Real.exp lam - (1 + lam)| ≤ 3 / 4 * lam ^ 2 := by
    have h := Real.exp_bound hlam (n := 2) (by norm_num)
    simp [Finset.sum_range_succ] at h
    nlinarith only [h, abs_nonneg lam, sq_abs lam]
  have h1 : Real.exp lam - 1 - lam ≤ 3 / 4 * lam ^ 2 := by
    have := abs_le.1 hkey
    linarith only [this.2]
  have h2 : 0 ≤ Real.exp lam - 1 - lam := by
    have := Real.add_one_le_exp lam
    linarith only [this]
  have hstep : p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (lam * (0 - p))
      = Real.exp (-(lam * p)) * (1 + p * (Real.exp lam - 1)) := by
    rw [show lam * (1 - p) = lam + -(lam * p) by ring, show lam * (0 - p) = -(lam * p) by ring,
      Real.exp_add]
    ring
  rw [hstep]
  have hpe : 1 + p * (Real.exp lam - 1) ≤ Real.exp (p * (Real.exp lam - 1)) := by
    have := Real.add_one_le_exp (p * (Real.exp lam - 1))
    linarith only [this]
  have hnn : 0 < Real.exp (-(lam * p)) := Real.exp_pos _
  calc Real.exp (-(lam * p)) * (1 + p * (Real.exp lam - 1))
      ≤ Real.exp (-(lam * p)) * Real.exp (p * (Real.exp lam - 1)) :=
        mul_le_mul_of_nonneg_left hpe hnn.le
    _ = Real.exp (p * (Real.exp lam - 1 - lam)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (3 / 4 * lam ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith only [hp1, h1, h2]

/-- The number of blocks of `K` entirely contained in the sample `A`. -/
noncomputable def blockCount (K : Finset β) (B : β → Finset α) (A : Finset α) : ℕ :=
  (K.filter (fun z => B z ⊆ A)).card

/-- The mean of `blockCount`. -/
noncomputable def blockMean (ρ : ℝ) (K : Finset β) (B : β → Finset α) : ℝ :=
  ∑ z ∈ K, ρ ^ (B z).card

theorem mgf_le (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {I : Finset α} {K : Finset β} {B : β → Finset α}
    (hBI : ∀ z ∈ K, B z ⊆ I) (hdisj : ∀ z ∈ K, ∀ z' ∈ K, z ≠ z' → Disjoint (B z) (B z'))
    {lam : ℝ} (hlam : |lam| ≤ 1) :
    expect ρ I (fun A => Real.exp (lam * ((blockCount K B A : ℝ) - blockMean ρ K B)))
      ≤ Real.exp (3 / 4 * lam ^ 2 * K.card) := by
  classical
  set g : β → Finset α → ℝ := fun z C =>
    Real.exp (lam * ((if B z ⊆ C then (1:ℝ) else 0) - ρ ^ (B z).card)) with hg
  have hrewrite : (fun A : Finset α =>
      Real.exp (lam * ((blockCount K B A : ℝ) - blockMean ρ K B)))
      = fun A => ∏ z ∈ K, g z (A ∩ B z) := by
    funext A
    rw [hg]
    simp only
    rw [← Real.exp_sum]
    congr 1
    have hcard : ((blockCount K B A : ℕ) : ℝ) = ∑ z ∈ K, (if B z ⊆ A then (1:ℝ) else 0) := by
      simp [blockCount]
    have hint : ∀ x ∈ K, lam * ((if B x ⊆ A ∩ B x then (1:ℝ) else 0) - ρ ^ (B x).card)
        = lam * ((if B x ⊆ A then (1:ℝ) else 0) - ρ ^ (B x).card) := by
      intro x _
      have hiff : (B x ⊆ A ∩ B x) ↔ (B x ⊆ A) := by
        constructor
        · intro h; exact h.trans Finset.inter_subset_left
        · intro h y hy; exact Finset.mem_inter.2 ⟨h hy, hy⟩
      simp only [hiff]
    rw [blockMean, hcard, Finset.sum_congr rfl hint, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hrewrite, expect_prod_blocks ρ K B g I hBI hdisj]
  have hb : ∀ z ∈ K, expect ρ (B z) (g z) ≤ Real.exp (3 / 4 * lam ^ 2) := by
    intro z _
    rw [hg, expect_block ρ (B z) lam]
    exact block_mgf_le (pow_nonneg h0 _) (pow_le_one₀ h0 h1) hlam
  have hbn : ∀ z ∈ K, 0 ≤ expect ρ (B z) (g z) := by
    intro z _
    rw [hg, expect_block ρ (B z) lam]
    have hp0 : (0:ℝ) ≤ ρ ^ (B z).card := pow_nonneg h0 _
    have hp1 : ρ ^ (B z).card ≤ 1 := pow_le_one₀ h0 h1
    have := Real.exp_pos (lam * (1 - ρ ^ (B z).card))
    have := Real.exp_pos (lam * (0 - ρ ^ (B z).card))
    nlinarith
  calc ∏ z ∈ K, expect ρ (B z) (g z) ≤ ∏ z ∈ K, Real.exp (3 / 4 * lam ^ 2) :=
        Finset.prod_le_prod hbn hb
    _ = Real.exp (3 / 4 * lam ^ 2 * K.card) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
        ring_nf


/-! ### Markov's inequality and the Chernoff–Hoeffding tail bounds -/

theorem expect_const_mul (ρ : ℝ) (I : Finset α) (c : ℝ) (F : Finset α → ℝ) :
    expect ρ I (fun A => c * F A) = c * expect ρ I F := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ => by ring

theorem markov {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {I : Finset α} (F : Finset α → ℝ)
    (hF : ∀ A, 0 ≤ F A) {Bad : Finset (Finset α)} (hsub : Bad ⊆ I.powerset)
    (hBad : ∀ A ∈ Bad, 1 ≤ F A) :
    ∑ A ∈ Bad, wt ρ I A ≤ expect ρ I F := by
  calc ∑ A ∈ Bad, wt ρ I A ≤ ∑ A ∈ Bad, wt ρ I A * F A := by
        refine Finset.sum_le_sum fun A hA => ?_
        have := wt_nonneg h0 h1 I A
        nlinarith [hBad A hA]
    _ ≤ ∑ A ∈ I.powerset, wt ρ I A * F A :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun A _ _ =>
          mul_nonneg (wt_nonneg h0 h1 I A) (hF A)
    _ = expect ρ I F := rfl

/-- The exponential Markov bound for the block count. -/
theorem tail_general (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {I : Finset α} {K : Finset β}
    {B : β → Finset α} (hBI : ∀ z ∈ K, B z ⊆ I)
    (hdisj : ∀ z ∈ K, ∀ z' ∈ K, z ≠ z' → Disjoint (B z) (B z'))
    {lam t : ℝ} (hlam : |lam| ≤ 1) {Bad : Finset (Finset α)} (hsub : Bad ⊆ I.powerset)
    (hbad : ∀ A ∈ Bad, t ≤ lam * ((blockCount K B A : ℝ) - blockMean ρ K B)) :
    ∑ A ∈ Bad, wt ρ I A ≤ Real.exp (-t + 3 / 4 * lam ^ 2 * K.card) := by
  have hM := markov h0 h1
    (F := fun A => Real.exp (-t) * Real.exp (lam * ((blockCount K B A : ℝ) - blockMean ρ K B)))
    (fun A => by positivity) hsub ?_
  · refine hM.trans ?_
    rw [expect_const_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (mgf_le ρ h0 h1 hBI hdisj hlam) (Real.exp_pos _).le
  · intro A hA
    simp only [← Real.exp_add]
    have h := hbad A hA
    have h2 : (0:ℝ) ≤ -t + lam * ((blockCount K B A : ℝ) - blockMean ρ K B) := by linarith only [h]
    calc (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ _ := Real.exp_le_exp.2 h2

omit [DecidableEq α] [DecidableEq β] in
theorem blockMean_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (K : Finset β) (B : β → Finset α) :
    0 ≤ blockMean ρ K B :=
  Finset.sum_nonneg fun _ _ => pow_nonneg h0 _

omit [DecidableEq α] [DecidableEq β] in
theorem blockMean_le_card {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (K : Finset β) (B : β → Finset α) :
    blockMean ρ K B ≤ (K.card : ℝ) := by
  rw [blockMean]
  calc ∑ z ∈ K, ρ ^ (B z).card ≤ ∑ _z ∈ K, (1:ℝ) :=
        Finset.sum_le_sum fun _ _ => pow_le_one₀ h0 h1
    _ = (K.card : ℝ) := by simp

omit [DecidableEq β] in
theorem blockCount_le (K : Finset β) (B : β → Finset α) (A : Finset α) :
    (blockCount K B A : ℝ) ≤ (K.card : ℝ) := by
  exact_mod_cast Finset.card_filter_le _ _

private theorem chernoff_arith {t m kc : ℝ} (hm0 : 0 < m) (ht : 0 < t) (hmK : kc ≤ m) :
    -(t ^ 2 / (2 * m)) + 3 / 4 * (t ^ 2 / (4 * m ^ 2)) * kc ≤ -(t ^ 2 / (4 * m)) := by
  have h4' : (0:ℝ) < t ^ 2 := by positivity
  have h1' : 3 / 4 * (t ^ 2 / (4 * m ^ 2)) * kc ≤ 3 / 4 * (t ^ 2 / (4 * m ^ 2)) * m :=
    mul_le_mul_of_nonneg_left hmK (by positivity)
  have h3' : 3 / 4 * (t ^ 2 / (4 * m ^ 2)) * m = 3 / 4 * (t ^ 2 / (4 * m)) := by field_simp
  have heq : t ^ 2 / (2 * m) = 2 * (t ^ 2 / (4 * m)) := by field_simp; norm_num
  have h5 : (0:ℝ) < t ^ 2 / (4 * m) := by positivity
  linarith only [h1', h3', heq, h5]

/-- **Chernoff–Hoeffding, upper tail.**  The `ρ`-random subset of `I` contains more than
`𝔼 + t` of the pairwise disjoint blocks `B z`, `z ∈ K`, with probability at most
`exp (-t²/(4m))`, for any `m ≥ |K|`. -/
theorem tail_upper (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {I : Finset α} {K : Finset β}
    {B : β → Finset α} (hBI : ∀ z ∈ K, B z ⊆ I)
    (hdisj : ∀ z ∈ K, ∀ z' ∈ K, z ≠ z' → Disjoint (B z) (B z'))
    {t m : ℝ} (hm0 : 0 < m) (hmK : (K.card : ℝ) ≤ m) (ht : 0 < t)
    {Bad : Finset (Finset α)} (hsub : Bad ⊆ I.powerset)
    (hbad : ∀ A ∈ Bad, blockMean ρ K B + t ≤ (blockCount K B A : ℝ)) :
    ∑ A ∈ Bad, wt ρ I A ≤ Real.exp (-(t ^ 2 / (4 * m))) := by
  rcases le_or_gt t (2 * m) with hcase | hcase
  · set lam : ℝ := t / (2 * m) with hlamdef
    have hlam0 : 0 < lam := div_pos ht (by linarith)
    have hlam1 : lam ≤ 1 := by rw [hlamdef, div_le_one (by linarith)]; exact hcase
    have habs : |lam| ≤ 1 := by rw [abs_of_pos hlam0]; exact hlam1
    have h := tail_general ρ h0 h1 hBI hdisj (lam := lam) (t := lam * t) habs hsub ?_
    · refine h.trans (Real.exp_le_exp.2 ?_)
      have hlamsq : lam ^ 2 = t ^ 2 / (4 * m ^ 2) := by rw [hlamdef]; field_simp; ring
      have h2' : -(lam * t) = -(t ^ 2 / (2 * m)) := by rw [hlamdef]; field_simp
      rw [hlamsq, h2']
      exact chernoff_arith hm0 ht hmK
    · intro A hA
      have := hbad A hA
      nlinarith [hlam0]
  · have hempty : Bad = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      have hb := hbad A hA
      have h1' := blockMean_nonneg h0 K B (ρ := ρ)
      have h2' := blockCount_le K B A
      linarith only [hmK, hcase, hb, h1', h2']
    rw [hempty, Finset.sum_empty]
    exact (Real.exp_pos _).le

/-- **Chernoff–Hoeffding, lower tail.** -/
theorem tail_lower (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {I : Finset α} {K : Finset β}
    {B : β → Finset α} (hBI : ∀ z ∈ K, B z ⊆ I)
    (hdisj : ∀ z ∈ K, ∀ z' ∈ K, z ≠ z' → Disjoint (B z) (B z'))
    {t m : ℝ} (hm0 : 0 < m) (hmK : (K.card : ℝ) ≤ m) (ht : 0 < t)
    {Bad : Finset (Finset α)} (hsub : Bad ⊆ I.powerset)
    (hbad : ∀ A ∈ Bad, (blockCount K B A : ℝ) ≤ blockMean ρ K B - t) :
    ∑ A ∈ Bad, wt ρ I A ≤ Real.exp (-(t ^ 2 / (4 * m))) := by
  rcases le_or_gt t (2 * m) with hcase | hcase
  · set lam : ℝ := -(t / (2 * m)) with hlamdef
    have hlam0 : lam < 0 := by rw [hlamdef, neg_lt_zero]; positivity
    have hlam1 : -1 ≤ lam := by
      rw [hlamdef, neg_le_neg_iff, div_le_one (by linarith)]; exact hcase
    have habs : |lam| ≤ 1 := by rw [abs_of_neg hlam0]; linarith only [hlam1]
    have h := tail_general ρ h0 h1 hBI hdisj (lam := lam) (t := -lam * t) habs hsub ?_
    · refine h.trans (Real.exp_le_exp.2 ?_)
      have hlamsq : lam ^ 2 = t ^ 2 / (4 * m ^ 2) := by rw [hlamdef]; field_simp; ring
      have h2' : -(-lam * t) = -(t ^ 2 / (2 * m)) := by rw [hlamdef]; field_simp
      rw [hlamsq, h2']
      exact chernoff_arith hm0 ht hmK
    · intro A hA
      have hb := hbad A hA
      nlinarith [hlam0]
  · have hempty : Bad = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun A hA => ?_
      have hb := hbad A hA
      have h2' : (0:ℝ) ≤ (blockCount K B A : ℝ) := Nat.cast_nonneg _
      have h3' := blockMean_le_card h0 h1 K B (ρ := ρ)
      linarith only [hmK, hcase, hb, h3']
    rw [hempty, Finset.sum_empty]
    exact (Real.exp_pos _).le

/-! ### The probabilistic method -/

/-- If an event has weight `< 1` then some sample avoids it. -/
theorem exists_of_sum_lt_one {ρ : ℝ} (I : Finset α) {Bad : Finset (Finset α)}
    (hsub : Bad ⊆ I.powerset) (h : ∑ A ∈ Bad, wt ρ I A < 1) : ∃ A, A ⊆ I ∧ A ∉ Bad := by
  by_contra hcon
  push_neg at hcon
  have hall : I.powerset ⊆ Bad := fun A hA => hcon A (Finset.mem_powerset.1 hA)
  have : Bad = I.powerset := Finset.Subset.antisymm hsub hall
  rw [this, sum_wt] at h
  exact lt_irrefl _ h

end BKLO.Bern
