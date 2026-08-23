/-
# Balanced samples, from the moment bound of `BKLO/Sampling.lean`

`BKLO.card_deviant_le_pow` (`BKLO/Sampling.lean`) bounds the number of `t`-subsets of `A` meeting a
fixed set `T ⊆ A` in `y` or more points.  A union bound over the members of a family turns it
into a statement about a single sample.  For the equitable partitions of BKLO §10 one has to bound,
for one and the same sample, both the intersection with a set and the intersection with its
complement, so the index set has to be allowed to be arbitrary; that is
`BKLO.exists_powersetCard_avoiding_index` below.

The main result of the file is `BKLO.exists_balanced_sample`: for every family `T i ⊆ A`
(`i` ranging over an index set `I`) there is a `t`-subset `X` of `A` with

`|T i ∩ X| ≤ |T i|·t/|A| + θ·t`   for every `i ∈ I`,

as soon as `|I| < (θ²t/32)²` — the sample meets every member of the family in at most its
expected share, up to `θt`.  Applying it to a family together with the complements of its members
gives the two-sided form `BKLO.exists_balanced_sample_two_sided`.

Everything here is `sorry`-free.
-/
import BKLO.Sampling

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Union bound over an arbitrary index set.**  As `BKLO.exists_powersetCard_avoiding`, but the
family of sets to be avoided is indexed by an arbitrary finite index set rather than by a set of
vertices. -/
theorem exists_powersetCard_avoiding_index {ι : Type*} {A : Finset V} {I : Finset ι}
    {T : ι → Finset V} {y : ι → ℕ} {t k : ℕ} {ρ : ℝ}
    (hTA : ∀ i ∈ I, T i ⊆ A) (hkt : k ≤ t) (hky : ∀ i ∈ I, k ≤ y i)
    (hkA : k ≤ A.card) (htA : t ≤ A.card)
    (hratio : ∀ i ∈ I, ((T i).card : ℝ) * (t : ℝ)
        ≤ ρ * (((y i + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ)))
    (hsmall : (I.card : ℝ) * ρ ^ k < 1) :
    ∃ X ∈ A.powersetCard t, ∀ i ∈ I, (T i ∩ X).card < y i := by
  classical
  by_contra hcon
  push_neg at hcon
  have hCpos : (0 : ℝ) < (A.card.choose t : ℝ) := by
    have h := Nat.choose_pos htA
    exact_mod_cast h
  have hsub : A.powersetCard t ⊆
      I.biUnion (fun i => (A.powersetCard t).filter (fun X => y i ≤ (T i ∩ X).card)) := by
    intro X hX
    obtain ⟨i, hi, hiy⟩ := hcon X hX
    exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨hX, hiy⟩⟩
  have hcard : (A.powersetCard t).card
      ≤ ∑ i ∈ I, ((A.powersetCard t).filter (fun X => y i ≤ (T i ∩ X).card)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardR : (A.card.choose t : ℝ) ≤ ∑ i ∈ I, (((A.powersetCard t).filter
      (fun X => y i ≤ (T i ∩ X).card)).card : ℝ) := by
    rw [Finset.card_powersetCard] at hcard
    calc (A.card.choose t : ℝ)
        ≤ ((∑ i ∈ I, ((A.powersetCard t).filter
              (fun X => y i ≤ (T i ∩ X).card)).card : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = _ := by push_cast; ring
  have hterm : ∀ i ∈ I, (((A.powersetCard t).filter (fun X => y i ≤ (T i ∩ X).card)).card : ℝ)
      ≤ ρ ^ k * (A.card.choose t : ℝ) :=
    fun i hi => card_deviant_le_pow (hTA i hi) hkt (hky i hi) hkA (hratio i hi)
  have hsum : ∑ i ∈ I, (((A.powersetCard t).filter (fun X => y i ≤ (T i ∩ X).card)).card : ℝ)
      ≤ (I.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) := by
    calc ∑ i ∈ I, (((A.powersetCard t).filter (fun X => y i ≤ (T i ∩ X).card)).card : ℝ)
        ≤ ∑ _i ∈ I, (ρ ^ k * (A.card.choose t : ℝ)) := Finset.sum_le_sum hterm
      _ = (I.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlt : (A.card.choose t : ℝ) < (A.card.choose t : ℝ) :=
    calc (A.card.choose t : ℝ) ≤ (I.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) :=
          le_trans hcardR hsum
      _ = ((I.card : ℝ) * ρ ^ k) * (A.card.choose t : ℝ) := by ring
      _ < 1 * (A.card.choose t : ℝ) := mul_lt_mul_of_pos_right hsmall hCpos
      _ = (A.card.choose t : ℝ) := one_mul _
  exact lt_irrefl _ hlt

/-- The arithmetic behind the ratio condition of `BKLO.exists_balanced_sample`: with a threshold
of `|T|t/n + θt` and a moment order of at most `θt/2`, the ratio the tail bound asks for is at most
`1/(1 + θ/8)`. -/
private theorem sample_ratio_arith {Ti tR nR θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht : 0 < tR)
    (hn : 2 * tR ≤ nR) (hTi0 : 0 ≤ Ti) (hTin : Ti ≤ nR) :
    Ti * tR * (1 + θ / 8) ≤ (Ti * tR / nR + θ * tR / 2) * (nR * (1 - θ / 4)) := by
  have hn0 : 0 < nR := by linarith only [ht, hn]
  have hexp : (Ti * tR / nR + θ * tR / 2) * (nR * (1 - θ / 4))
      = (Ti * tR + θ * tR * nR / 2) * (1 - θ / 4) := by
    field_simp
  rw [hexp]
  have hcore : 3 / 8 * Ti ≤ nR / 2 - θ * nR / 8 := by
    have hθn : θ * nR ≤ 1 * nR := mul_le_mul_of_nonneg_right hθ1 hn0.le
    linarith only [hTin, hθn]
  have h1 : θ * tR * (3 / 8 * Ti) ≤ θ * tR * (nR / 2 - θ * nR / 8) :=
    mul_le_mul_of_nonneg_left hcore (by positivity)
  linarith only [h1]

set_option maxHeartbeats 400000 in
/-- **A balanced sample exists.**  If `|I| < (θ²t/32)²` then some `t`-subset `X` of `A` meets every
member `T i` of the family in at most `|T i|·t/|A| + θt` points: no member is over-represented in
`X` by more than `θt`. -/
theorem exists_balanced_sample {ι : Type*} {A : Finset V} {I : Finset ι} (T : ι → Finset V)
    (hTA : ∀ i ∈ I, T i ⊆ A) {t : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht0 : 0 < t)
    (ht : 2 * t ≤ A.card) (hI : (I.card : ℝ) < (θ ^ 2 * (t : ℝ) / 32) ^ 2) :
    ∃ X ∈ A.powersetCard t, ∀ i ∈ I,
      ((T i ∩ X).card : ℝ) ≤ ((T i).card : ℝ) * (t : ℝ) / (A.card : ℝ) + θ * (t : ℝ) := by
  classical
  set n : ℕ := A.card with hndef
  have htR0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
  have htn : t ≤ n := by omega
  have hnR : (2 : ℝ) * (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith only [htR0, hnR]
  -- the thresholds
  set z : ι → ℝ := fun i => ((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) with hzdef
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    have : (0 : ℝ) ≤ ((T i).card : ℝ) * (t : ℝ) / (n : ℝ) := by positivity
    have : (0 : ℝ) < θ * (t : ℝ) := by positivity
    simp only [hzdef]
    positivity
  set y : ι → ℕ := fun i => ⌈z i⌉₊ with hydef
  set s : ℕ := ⌊θ * (t : ℝ) / 4⌋₊ with hsdef
  set κ : ℕ := 2 * s with hκdef
  set ρ : ℝ := 1 / (1 + θ / 8) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hsR : (s : ℝ) ≤ θ * (t : ℝ) / 4 := Nat.floor_le (by positivity)
  have hsR2 : θ * (t : ℝ) / 4 - 1 ≤ (s : ℝ) := by
    have h := Nat.lt_floor_add_one (θ * (t : ℝ) / 4)
    rw [← hsdef] at h; linarith only [h]
  have hκR : (κ : ℝ) = 2 * (s : ℝ) := by rw [hκdef]; push_cast; ring
  have hκθ : (κ : ℝ) ≤ θ * (t : ℝ) / 2 := by rw [hκR]; linarith only [hsR]
  have hθt : θ * (t : ℝ) ≤ 1 * (t : ℝ) := mul_le_mul_of_nonneg_right hθ1 htR0.le
  have hκt : κ ≤ t := by
    have : (κ : ℝ) ≤ (t : ℝ) := by linarith only [hκθ, hθt]
    exact_mod_cast this
  have hκn : κ ≤ n := le_trans hκt htn
  have hκy : ∀ i ∈ I, κ ≤ y i := by
    intro i _
    have h1 : (κ : ℝ) ≤ z i := by
      have : θ * (t : ℝ) ≤ z i := by
        simp only [hzdef]
        have : (0 : ℝ) ≤ ((T i).card : ℝ) * (t : ℝ) / (n : ℝ) := by positivity
        linarith only [this]
      linarith only [hκθ, this, mul_pos hθ0 htR0]
    have h2 : (κ : ℝ) ≤ (y i : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h2
  -- the ratio condition
  have hratio : ∀ i ∈ I, ((T i).card : ℝ) * (t : ℝ)
      ≤ ρ * (((y i + 1 - κ : ℕ) : ℝ) * ((n + 1 - κ : ℕ) : ℝ)) := by
    intro i hi
    have hTi : ((T i).card : ℝ) ≤ (n : ℝ) := by
      have := Finset.card_le_card (hTA i hi)
      exact_mod_cast this
    have hTi0 : (0 : ℝ) ≤ ((T i).card : ℝ) := Nat.cast_nonneg _
    have hcast1 : ((y i + 1 - κ : ℕ) : ℝ) = (y i : ℝ) + 1 - (κ : ℝ) := by
      have hle : κ ≤ y i + 1 := le_trans (hκy i hi) (Nat.le_succ _)
      rw [Nat.cast_sub hle]; push_cast; ring
    have hcast2 : ((n + 1 - κ : ℕ) : ℝ) = (n : ℝ) + 1 - (κ : ℝ) := by
      have hle : κ ≤ n + 1 := le_trans hκn (Nat.le_succ _)
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hcast1, hcast2]
    have hy : z i ≤ (y i : ℝ) := Nat.le_ceil _
    -- lower bounds for the two factors
    have hf1 : ((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) / 2
        ≤ (y i : ℝ) + 1 - (κ : ℝ) := by
      simp only [hzdef] at hy
      linarith only [hκθ, hy]
    have hf2 : (n : ℝ) * (1 - θ / 4) ≤ (n : ℝ) + 1 - (κ : ℝ) := by
      have hgap : (0 : ℝ) ≤ θ * ((n : ℝ) - 2 * (t : ℝ)) :=
        mul_nonneg hθ0.le (by linarith only [hnR])
      have : (κ : ℝ) ≤ θ * (n : ℝ) / 4 := by linarith only [hκθ, hgap]
      linarith only [this]
    have hf1' : (0 : ℝ) ≤ ((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) / 2 := by positivity
    have hf2' : (0 : ℝ) ≤ (n : ℝ) * (1 - θ / 4) :=
      mul_nonneg hn0.le (by linarith only [hθ1])
    have hprod : (((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) / 2) * ((n : ℝ) * (1 - θ / 4))
        ≤ ((y i : ℝ) + 1 - (κ : ℝ)) * ((n : ℝ) + 1 - (κ : ℝ)) :=
      mul_le_mul hf1 hf2 hf2' (by linarith)
    -- the key inequality
    have hkey : ((T i).card : ℝ) * (t : ℝ) * (1 + θ / 8)
        ≤ (((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) / 2) * ((n : ℝ) * (1 - θ / 4)) :=
      sample_ratio_arith hθ0 hθ1 htR0 hnR hTi0 hTi
    have hρmul : ρ * (1 + θ / 8) = 1 := by
      rw [hρdef]; field_simp
    have hfin : ((T i).card : ℝ) * (t : ℝ)
        ≤ ρ * ((((T i).card : ℝ) * (t : ℝ) / (n : ℝ) + θ * (t : ℝ) / 2)
            * ((n : ℝ) * (1 - θ / 4))) := by
      have := mul_le_mul_of_nonneg_left hkey hρ0.le
      calc ((T i).card : ℝ) * (t : ℝ) = ρ * (((T i).card : ℝ) * (t : ℝ) * (1 + θ / 8)) := by
            rw [show ρ * (((T i).card : ℝ) * (t : ℝ) * (1 + θ / 8))
              = (ρ * (1 + θ / 8)) * (((T i).card : ℝ) * (t : ℝ)) by ring, hρmul, one_mul]
        _ ≤ _ := this
    exact le_trans hfin (mul_le_mul_of_nonneg_left hprod hρ0.le)
  -- the union bound
  have hsmall : (I.card : ℝ) * ρ ^ κ < 1 := by
    have hQ : (0 : ℝ) < (1 + θ / 8) ^ κ := by positivity
    have hbern : 1 + (s : ℝ) * (θ / 8) ≤ (1 + θ / 8) ^ s :=
      one_add_mul_le_pow (by linarith) s
    have hκ2 : (1 + θ / 8) ^ κ = ((1 + θ / 8) ^ s) ^ 2 := by rw [hκdef, mul_comm 2 s, pow_mul]
    have hlow : θ ^ 2 * (t : ℝ) / 32 ≤ 1 + (s : ℝ) * (θ / 8) := by
      have h := mul_le_mul_of_nonneg_right hsR2 (by positivity : (0:ℝ) ≤ θ / 8)
      linarith only [h, hθ1]
    have hlow0 : (0 : ℝ) ≤ θ ^ 2 * (t : ℝ) / 32 := by positivity
    have hsq : (θ ^ 2 * (t : ℝ) / 32) ^ 2 ≤ ((1 + θ / 8) ^ s) ^ 2 :=
      pow_le_pow_left₀ hlow0 (le_trans hlow hbern) 2
    have hpow : (I.card : ℝ) < (1 + θ / 8) ^ κ := by rw [hκ2]; linarith only [hI, hsq]
    rw [hρdef, div_pow, one_pow, mul_one_div, div_lt_one hQ]
    exact hpow
  obtain ⟨X, hX, hXgood⟩ :=
    exists_powersetCard_avoiding_index (A := A) (I := I) (T := T) (y := y) (t := t) (k := κ)
      (ρ := ρ) hTA hκt hκy hκn htn hratio hsmall
  refine ⟨X, hX, fun i hi => ?_⟩
  have h1 : (T i ∩ X).card + 1 ≤ y i := hXgood i hi
  have h2 : ((T i ∩ X).card : ℝ) + 1 ≤ (y i : ℝ) := by exact_mod_cast h1
  have h3 : (y i : ℝ) < z i + 1 := Nat.ceil_lt_add_one (hz0 i)
  simp only [hzdef] at h3
  linarith only [h2, h3]

/-- **A two-sided balanced sample.**  Some `t`-subset `X` of `A` meets every member of the family
in its expected share up to `θt`, from both sides. -/
theorem exists_balanced_sample_two_sided {ι : Type*} [DecidableEq ι] {A : Finset V} {I : Finset ι}
    (T : ι → Finset V) (hTA : ∀ i ∈ I, T i ⊆ A) {t : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (ht0 : 0 < t) (ht : 2 * t ≤ A.card)
    (hI : 2 * (I.card : ℝ) < (θ ^ 2 * (t : ℝ) / 32) ^ 2) :
    ∃ X ∈ A.powersetCard t, ∀ i ∈ I,
      ((T i ∩ X).card : ℝ) ≤ ((T i).card : ℝ) * (t : ℝ) / (A.card : ℝ) + θ * (t : ℝ) ∧
      ((T i).card : ℝ) * (t : ℝ) / (A.card : ℝ) - θ * (t : ℝ) ≤ ((T i ∩ X).card : ℝ) := by
  classical
  -- the doubled family: each `T i` together with its complement in `A`
  set J : Finset (ι × Bool) := I ×ˢ (Finset.univ : Finset Bool) with hJdef
  set T' : ι × Bool → Finset V := fun p => if p.2 then T p.1 else A \ T p.1 with hT'def
  have hT'A : ∀ p ∈ J, T' p ⊆ A := by
    intro p hp
    have hp1 : p.1 ∈ I := (Finset.mem_product.1 hp).1
    simp only [hT'def]
    split
    · exact hTA p.1 hp1
    · exact Finset.sdiff_subset
  have hJcard : (J.card : ℝ) = 2 * (I.card : ℝ) := by
    rw [hJdef, Finset.card_product]
    simp
    ring
  obtain ⟨X, hX, hgood⟩ :=
    exists_balanced_sample (A := A) (I := J) T' hT'A hθ0 hθ1 ht0 ht (by rw [hJcard]; exact hI)
  obtain ⟨hXA, hXcard⟩ := Finset.mem_powersetCard.1 hX
  refine ⟨X, hX, fun i hi => ⟨?_, ?_⟩⟩
  · have h := hgood (i, true) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    simpa [hT'def] using h
  · have h := hgood (i, false) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [hT'def, Bool.false_eq_true, if_false] at h
    -- `|T i ∩ X| = t - |(A \ T i) ∩ X|`
    have hsplit : ((A \ T i) ∩ X).card + (T i ∩ X).card = t := by
      have h1 : ((A \ T i) ∩ X) ∪ (T i ∩ X) = X := by
        ext a
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro (⟨⟨-, -⟩, ha⟩ | ⟨-, ha⟩) <;> exact ha
        · intro ha
          by_cases haT : a ∈ T i
          · exact Or.inr ⟨haT, ha⟩
          · exact Or.inl ⟨⟨hXA ha, haT⟩, ha⟩
      have h2 : Disjoint ((A \ T i) ∩ X) (T i ∩ X) := by
        refine Finset.disjoint_left.2 fun a ha ha' => ?_
        exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 ha).1).2 (Finset.mem_inter.1 ha').1
      have h3 := Finset.card_union_of_disjoint h2
      rw [h1, hXcard] at h3
      omega
    have hcardsdiff : ((A \ T i).card : ℝ) = (A.card : ℝ) - ((T i).card : ℝ) := by
      rw [Finset.card_sdiff_of_subset (hTA i hi)]
      have : (T i).card ≤ A.card := Finset.card_le_card (hTA i hi)
      push_cast [Nat.cast_sub this]
      ring
    have hsplitR : (((A \ T i) ∩ X).card : ℝ) + ((T i ∩ X).card : ℝ) = (t : ℝ) := by
      exact_mod_cast hsplit
    rw [hcardsdiff] at h
    have hA0 : (0 : ℝ) < (A.card : ℝ) := by
      have : 0 < A.card := lt_of_lt_of_le (by omega) (le_trans (by omega) ht)
      exact_mod_cast this
    have hexp : ((A.card : ℝ) - ((T i).card : ℝ)) * (t : ℝ) / (A.card : ℝ)
        = (t : ℝ) - ((T i).card : ℝ) * (t : ℝ) / (A.card : ℝ) := by
      field_simp
    rw [hexp] at h
    linarith only [h, hsplitR]

end BKLO
