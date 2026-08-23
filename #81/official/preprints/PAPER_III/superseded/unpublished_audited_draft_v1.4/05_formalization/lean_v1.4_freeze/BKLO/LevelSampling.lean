/-
# Vortex levels: the random level, with its exact loss.

This file proves the *existence of a vortex level*: given a set `W` whose vertices all have few
non-neighbours inside `W`, a prescribed bottom set `U ⊆ W`, a prescribed avoidance set `D`, and a
prescribed size `m`, there is a level `U ⊆ W' ⊆ W` of size exactly `m`, disjoint from `D`, in which
every vertex of `W` still has few non-neighbours.

The level is a uniformly random `(m - |U|)`-subset of the pool `W \ (U ∪ D)`, together with the
forced part `U`; the moment bound `BKLO.card_deviant_le_pow` of `BKLO/Sampling.lean`, applied once
per vertex of `W` and combined with a union bound (`BKLO.exists_powersetCard_avoiding`), controls
the number of non-neighbours the sample contributes.

The point of the statement is the **exact** form of the loss.  Writing `β|W|` for the bound on the
number of non-neighbours inside `W`, the level `W'` produced here satisfies

`|nonNbrs W'| ≤ β·m + (|nonNbrs U| - β|U|) + β|D| + θ·m`,

for an arbitrary `θ > 0` at the cost of `m ≥ 10⁶K/θ⁴`.  So:

* the forced part `U` costs *nothing* beyond its own deficiency `|nonNbrs U| - β|U|` — in
  particular a bottom set that is as dense as `W` is free, however large it is.  This is sharper
  than the naive "delete `U` from the pool" estimate, and it is what makes an unbounded vortex
  recursion conceivable at all;
* the avoidance set `D` costs `β|D|`, and *that* loss is real: it is not an artefact of the random
  choice (a complete multipartite `W` with `|D|` apexes forces it), and it is not proportional to
  anything that shrinks along a vortex.

Everything here is `sorry`-free.
-/
import BKLO.BottomClause

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### A union bound over the moment tail estimate -/

/-- **Union bound.**  If, for every `v` of an index set `W`, the set `T v ⊆ A` is under-represented
in all but a `ρ^k` fraction of the `t`-subsets of `A`, and `|W|ρ^k < 1`, then some `t`-subset is
good for every `v` simultaneously. -/
theorem exists_powersetCard_avoiding {A W : Finset V} {T : V → Finset V} {y : V → ℕ}
    {t k : ℕ} {ρ : ℝ}
    (hTA : ∀ v ∈ W, T v ⊆ A) (hkt : k ≤ t) (hky : ∀ v ∈ W, k ≤ y v)
    (hkA : k ≤ A.card) (htA : t ≤ A.card)
    (hratio : ∀ v ∈ W, ((T v).card : ℝ) * (t : ℝ)
        ≤ ρ * (((y v + 1 - k : ℕ) : ℝ) * ((A.card + 1 - k : ℕ) : ℝ)))
    (hsmall : (W.card : ℝ) * ρ ^ k < 1) :
    ∃ S ∈ A.powersetCard t, ∀ v ∈ W, (T v ∩ S).card < y v := by
  classical
  by_contra hcon
  push_neg at hcon
  have hCpos : (0 : ℝ) < (A.card.choose t : ℝ) := by
    have h := Nat.choose_pos htA
    exact_mod_cast h
  have hsub : A.powersetCard t ⊆
      W.biUnion (fun v => (A.powersetCard t).filter (fun S => y v ≤ (T v ∩ S).card)) := by
    intro S hS
    obtain ⟨v, hv, hvy⟩ := hcon S hS
    exact Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_filter.2 ⟨hS, hvy⟩⟩
  have hcard : (A.powersetCard t).card
      ≤ ∑ v ∈ W, ((A.powersetCard t).filter (fun S => y v ≤ (T v ∩ S).card)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardR : (A.card.choose t : ℝ) ≤ ∑ v ∈ W, (((A.powersetCard t).filter
      (fun S => y v ≤ (T v ∩ S).card)).card : ℝ) := by
    rw [Finset.card_powersetCard] at hcard
    calc (A.card.choose t : ℝ)
        ≤ ((∑ v ∈ W, ((A.powersetCard t).filter
              (fun S => y v ≤ (T v ∩ S).card)).card : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = _ := by push_cast; ring
  have hterm : ∀ v ∈ W, (((A.powersetCard t).filter (fun S => y v ≤ (T v ∩ S).card)).card : ℝ)
      ≤ ρ ^ k * (A.card.choose t : ℝ) :=
    fun v hv => card_deviant_le_pow (hTA v hv) hkt (hky v hv) hkA (hratio v hv)
  have hsum : ∑ v ∈ W, (((A.powersetCard t).filter (fun S => y v ≤ (T v ∩ S).card)).card : ℝ)
      ≤ (W.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) := by
    calc ∑ v ∈ W, (((A.powersetCard t).filter (fun S => y v ≤ (T v ∩ S).card)).card : ℝ)
        ≤ ∑ _v ∈ W, (ρ ^ k * (A.card.choose t : ℝ)) := Finset.sum_le_sum hterm
      _ = (W.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlt : (A.card.choose t : ℝ) < (A.card.choose t : ℝ) :=
    calc (A.card.choose t : ℝ) ≤ (W.card : ℝ) * (ρ ^ k * (A.card.choose t : ℝ)) :=
          le_trans hcardR hsum
      _ = ((W.card : ℝ) * ρ ^ k) * (A.card.choose t : ℝ) := by ring
      _ < 1 * (A.card.choose t : ℝ) := mul_lt_mul_of_pos_right hsmall hCpos
      _ = (A.card.choose t : ℝ) := one_mul _
  exact lt_irrefl _ hlt

/-! ### Non-neighbours inside a subset -/

/-- The non-neighbours of `v` inside a subset are those of the ambient set that lie in it. -/
theorem nonNbrs_inter_of_subset {E : Finset (Sym2 V)} {W X : Finset V} (hXW : X ⊆ W) (v : V) :
    nonNbrs E X v = X ∩ nonNbrs E W v := by
  simp only [nonNbrs]
  ext a
  constructor
  · intro ha
    obtain ⟨haX, ha'⟩ := Finset.mem_sdiff.1 ha
    refine Finset.mem_inter.2 ⟨haX, Finset.mem_sdiff.2 ⟨hXW haX, fun h => ha' ?_⟩⟩
    exact mem_resLink.2 ⟨haX, (mem_resLink.1 h).2⟩
  · intro ha
    obtain ⟨haX, ha'⟩ := Finset.mem_inter.1 ha
    refine Finset.mem_sdiff.2 ⟨haX, fun h => (Finset.mem_sdiff.1 ha').2 ?_⟩
    exact mem_resLink.2 ⟨hXW haX, (mem_resLink.1 h).2⟩


/-! ### The arithmetic of the loss -/

set_option maxHeartbeats 1000000 in
/-- The real-number bookkeeping behind `BKLO.exists_level_of_nonNbrs`: with `A = |P| + 1 - k` the
effective size of the pool, the number `N + X + k` of non-neighbours the level can have is within
`θm` of `βm` plus the deficiency `N_U - β|U|` of the forced part and the cost `β|D|` of the
avoidance set. -/
private theorem level_arith
    {β θ nR uR dR mR tR kR A Nv NUv X : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hu : 0 ≤ uR) (hd : 0 ≤ dR) (hu2 : 2 * uR ≤ mR) (hm0 : 0 < mR)
    (hn : 2 * mR + dR ≤ nR)
    (hA : A = nR - uR - dR + 1 - kR) (ht : tR = mR - uR)
    (hk0 : 0 ≤ kR) (hk : kR ≤ θ * mR / 16)
    (hNv : Nv ≤ NUv) (hNU : β * uR ≤ NUv)
    (hX : X * A = (1 + θ / 8) * (β * nR - Nv) * tR) :
    Nv + X + kR ≤ β * mR + (NUv - β * uR) + β * dR + θ * mR := by
  have hkm : kR ≤ mR / 16 := by nlinarith only [hθ0, hθ1, hk0, hk]
  have hA75 : 7 / 5 * mR ≤ A := by rw [hA]; linarith only [hu2, hm0, hn, hkm]
  have hApos : 0 < A := by linarith only [hm0, hA75]
  have htR0 : 0 ≤ tR := by linarith only [hu2, hm0, ht]
  have htRm : tR ≤ mR := by linarith only [hu, ht]
  have hmA : mR ≤ 5 / 7 * A := by linarith only [hA75]
  have hdk : (0:ℝ) ≤ dR + kR := by linarith only [hd, hk0]
  have h1 : (1 + θ / 8) * tR ≤ A := by nlinarith only [hθ1, htR0, htRm, hmA]
  have hstep1 : Nv * (A - (1 + θ / 8) * tR) ≤ NUv * (A - (1 + θ / 8) * tR) :=
    mul_le_mul_of_nonneg_right hNv (by linarith)
  have hstep2 : (1 + θ / 8) * tR * (β * uR) ≤ (1 + θ / 8) * tR * NUv :=
    mul_le_mul_of_nonneg_left hNU (by nlinarith)
  have hbt : β * tR ≤ mR := by nlinarith only [hβ1, hu, hu2, ht]
  have hbt0 : 0 ≤ β * tR := mul_nonneg hβ0 htR0
  have hstepA : (1 + θ / 8) * (β * tR) * A ≤ β * tR * A + θ / 8 * mR * A := by
    have h : θ / 8 * (β * tR) * A ≤ θ / 8 * mR * A := by
      have h2 : θ / 8 * (β * tR) ≤ θ / 8 * mR := mul_le_mul_of_nonneg_left hbt (by linarith)
      exact mul_le_mul_of_nonneg_right h2 hApos.le
    nlinarith only [h]
  have hstepB : (1 + θ / 8) * (β * tR) * (dR + kR) ≤ β * dR * A + kR * A := by
    have hc1 : β * tR ≤ β * mR := mul_le_mul_of_nonneg_left htRm hβ0
    have hc2 : (1 + θ / 8) * (β * tR) ≤ 9 / 8 * (β * mR) :=
      mul_le_mul (by linarith) hc1 hbt0 (by positivity)
    have hc3 : (1 + θ / 8) * (β * tR) * (dR + kR) ≤ 9 / 8 * (β * mR) * (dR + kR) :=
      mul_le_mul_of_nonneg_right hc2 hdk
    have hc4 : 9 / 8 * (β * mR) ≤ 9 / 8 * (β * (5 / 7 * A)) := by
      have : β * mR ≤ β * (5 / 7 * A) := mul_le_mul_of_nonneg_left hmA hβ0
      linarith only [this]
    have hc5 : 9 / 8 * (β * mR) * (dR + kR) ≤ 9 / 8 * (β * (5 / 7 * A)) * (dR + kR) :=
      mul_le_mul_of_nonneg_right hc4 hdk
    have hc6 : 9 / 8 * (β * (5 / 7 * A)) * (dR + kR)
        = 45 / 56 * (β * dR * A) + 45 / 56 * (β * kR * A) := by ring
    have hb4 : β * kR * A ≤ kR * A := by
      have h : β * (kR * A) ≤ 1 * (kR * A) :=
        mul_le_mul_of_nonneg_right hβ1 (mul_nonneg hk0 hApos.le)
      nlinarith only [h]
    have hb5 : (0:ℝ) ≤ β * dR * A := by positivity
    have hb6 : (0:ℝ) ≤ β * kR * A := by positivity
    linarith [hc3, hc5, hc6.le, hc6.ge]
  have hstepD : kR * A ≤ θ / 16 * mR * A := by
    have h := mul_le_mul_of_nonneg_right hk hApos.le
    linarith only [h]
  refine le_of_mul_le_mul_right ?_ hApos
  have hexp : (Nv + X + kR) * A = Nv * A + (1 + θ / 8) * (β * nR - Nv) * tR + kR * A := by
    rw [← hX]; ring
  rw [hexp]
  have hnu : nR - uR = A - 1 + kR + dR := by rw [hA]; ring
  have hkey : (1 + θ / 8) * β * (nR - uR) * tR + kR * A
      ≤ (β * tR + β * dR + θ * mR) * A := by
    rw [hnu]
    have hexp2 : (1 + θ / 8) * β * (A - 1 + kR + dR) * tR
        = (1 + θ / 8) * (β * tR) * A + (1 + θ / 8) * (β * tR) * (dR + kR)
          - (1 + θ / 8) * (β * tR) := by ring
    rw [hexp2]
    have hpos : (0:ℝ) ≤ (1 + θ / 8) * (β * tR) := by positivity
    have hmA2 : θ / 8 * mR * A + θ / 16 * mR * A ≤ θ * mR * A := by nlinarith only [hu2, hn, hA, hk0, hk, hkm]
    linarith [hstepA, hstepB, hstepD]
  have hbt2 : β * tR = β * mR - β * uR := by rw [ht]; ring
  nlinarith [hstep1, hstep2, hkey]

/-- The numerical side conditions of `BKLO.exists_level_of_nonNbrs`: with `m ≥ 10⁶K/θ⁴` the
sample size `t`, the moment order `k = 2⌊θm/32⌋` and the pool `P` are in the range the tail bound
needs, and `(1 + θ/8)^k` already exceeds `|W|`. -/
private theorem level_numerics {θ Kr mR uR dR nR aR tR sR kR : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hKr : 1 ≤ Kr) (hm0 : 0 < mR)
    (hm : 10 ^ 6 * Kr ≤ θ ^ 4 * mR)
    (hu2 : 2 * uR ≤ mR) (hn : 2 * mR + dR ≤ nR) (hnK : nR ≤ Kr * mR)
    (ha : aR = nR - uR - dR) (ht : tR = mR - uR)
    (hs1 : sR ≤ θ * mR / 32) (hs2 : θ * mR / 32 - 1 ≤ sR) (hk : kR = 2 * sR) :
    0 ≤ kR ∧ kR ≤ θ * mR / 16 ∧ kR ≤ tR ∧ kR ≤ aR ∧ tR ≤ aR ∧ 0 < aR + 1 - kR
      ∧ nR < (θ ^ 2 * mR / 512) ^ 2 ∧ θ ^ 2 * mR / 512 ≤ 1 + sR * (θ / 8) := by
  have hθ4θ : θ ^ 4 ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by norm_num)
  have hθmbig : (10:ℝ) ^ 6 ≤ θ * mR := by
    have h1 : θ ^ 4 * mR ≤ θ * mR := mul_le_mul_of_nonneg_right hθ4θ hm0.le
    linarith only [hKr, hm, h1]
  have hθm : θ * mR ≤ mR := by
    have h := mul_le_mul_of_nonneg_right hθ1 hm0.le
    linarith only [h]
  have hbig : (1000000:ℝ) ≤ θ * mR := by norm_num at hθmbig; linarith only [hθmbig]
  have hs64 : θ * mR / 64 ≤ sR := by linarith only [hs2, hθmbig]
  have hs0 : 0 ≤ sR := by linarith only [hbig, hs64]
  have hk0 : 0 ≤ kR := by linarith only [hs1, hk, hs64]
  have hk16 : kR ≤ θ * mR / 16 := by linarith only [hs1, hk]
  have hkm : kR ≤ mR / 16 := by linarith only [hs1, hk, hθm]
  refine ⟨hk0, hk16, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · have hex : (θ ^ 2 * mR / 512) ^ 2 = θ ^ 4 * mR * mR / 262144 := by ring
    rw [hex]
    have h1 : 262144 * Kr < θ ^ 4 * mR := by norm_num at hm; linarith only [hKr, hm]
    have h2 : 262144 * Kr * mR < θ ^ 4 * mR * mR := by
      have h := mul_lt_mul_of_pos_right h1 hm0
      linarith only [h]
    have h3 : Kr * mR < θ ^ 4 * mR * mR / 262144 := by
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 262144)]; linarith only [h2]
    linarith only [hnK, h3]
  · have h := mul_le_mul_of_nonneg_right hs64 (by positivity : (0:ℝ) ≤ θ / 8)
    calc θ ^ 2 * mR / 512 = θ * mR / 64 * (θ / 8) := by ring
      _ ≤ sR * (θ / 8) := h
      _ ≤ 1 + sR * (θ / 8) := by linarith only []

/-! ### The level -/

set_option maxHeartbeats 1000000 in
/-- **A vortex level exists, with an explicit loss.**

Let every vertex of `W` have at most `β|W|` non-neighbours inside `W`, let `U ⊆ W` be a prescribed
bottom set with `2|U| ≤ m`, let `D ⊆ W` be a prescribed avoidance set, and let `m` be a prescribed
size with `2m + |D| ≤ |W| ≤ K·m`.  Then, provided `θ⁴m ≥ 10⁶K`, there is a level `U ⊆ W' ⊆ W` of
size exactly `m`, disjoint from `D`, in which every vertex `v` of `W` has at most

`β·m + (N_U(v) - β|U|) + β|D| + θ·m`

non-neighbours; here `N_U(v)` is any bound, at least `β|U|`, for the number of non-neighbours of
`v` inside the forced part `U`.

So the bottom set costs only its own deficiency — a bottom set as dense as `W` is free, however
large — while the avoidance set costs `β|D|`.  The level is `U` together with a uniformly random
`(m - |U|)`-subset of the pool `W \ (U ∪ D)`. -/
theorem exists_level_of_nonNbrs {W U D : Finset V} {E : Finset (Sym2 V)} {m : ℕ}
    {β θ Kr : ℝ} {NU : V → ℝ}
    (hUW : U ⊆ W) (hDW : D ⊆ W) (hUD : Disjoint U D)
    (hUm : 2 * U.card ≤ m) (hpool : 2 * m + D.card ≤ W.card) (hWK : (W.card : ℝ) ≤ Kr * (m : ℝ))
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hKr : 1 ≤ Kr)
    (hm : 10 ^ 6 * Kr ≤ θ ^ 4 * (m : ℝ))
    (hdens : ∀ v ∈ W, ((nonNbrs E W v).card : ℝ) ≤ β * (W.card : ℝ))
    (hNUle : ∀ v ∈ W, ((nonNbrs E U v).card : ℝ) ≤ NU v)
    (hNUβ : ∀ v ∈ W, β * (U.card : ℝ) ≤ NU v) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ Disjoint W' D ∧ W'.card = m ∧
      ∀ v ∈ W, ((nonNbrs E W' v).card : ℝ)
        ≤ β * (m : ℝ) + (NU v - β * (U.card : ℝ)) + β * (D.card : ℝ) + θ * (m : ℝ) := by
  classical
  -- ### The pool
  have hUDW : U ∪ D ⊆ W := Finset.union_subset hUW hDW
  have hud : U.card + D.card ≤ W.card := by
    rw [← Finset.card_union_of_disjoint hUD]; exact Finset.card_le_card hUDW
  set P : Finset V := W \ (U ∪ D) with hPdef
  have hPW : P ⊆ W := Finset.sdiff_subset
  have hPU : Disjoint P U :=
    Finset.disjoint_left.2 fun a ha haU => (Finset.mem_sdiff.1 ha).2 (Finset.mem_union_left _ haU)
  have hPD : Disjoint P D :=
    Finset.disjoint_left.2 fun a ha haD => (Finset.mem_sdiff.1 ha).2 (Finset.mem_union_right _ haD)
  have hPcard : P.card = W.card - (U.card + D.card) := by
    rw [hPdef, Finset.card_sdiff_of_subset hUDW, Finset.card_union_of_disjoint hUD]
  set t : ℕ := m - U.card with htdef
  set s : ℕ := ⌊θ * (m : ℝ) / 32⌋₊ with hsdef
  set k : ℕ := s * 2 with hkdef
  -- ### Real bookkeeping
  have hm0 : (0:ℝ) < (m : ℝ) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hm; norm_num at hm; linarith only [hKr, hm]
    · exact_mod_cast h
  have huR : 2 * (U.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hUm
  have hnR : 2 * (m : ℝ) + (D.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hpool
  have haR : (P.card : ℝ) = (W.card : ℝ) - (U.card : ℝ) - (D.card : ℝ) := by
    rw [hPcard, Nat.cast_sub hud]; push_cast; ring
  have hUmle : U.card ≤ m := by omega
  have htR : (t : ℝ) = (m : ℝ) - (U.card : ℝ) := by rw [htdef, Nat.cast_sub hUmle]
  have hsR1 : (s : ℝ) ≤ θ * (m : ℝ) / 32 := Nat.floor_le (by positivity)
  have hsR2 : θ * (m : ℝ) / 32 - 1 ≤ (s : ℝ) := by
    have h := Nat.lt_floor_add_one (θ * (m : ℝ) / 32)
    rw [← hsdef] at h; linarith only [h]
  have hkR : (k : ℝ) = 2 * (s : ℝ) := by rw [hkdef]; push_cast; ring
  have hdR0 : (0:ℝ) ≤ (D.card : ℝ) := Nat.cast_nonneg _
  have huR0 : (0:ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨hk0, hk16, hktR, hkaR, htaR, hApos, hnlt, hlow⟩ :=
    level_numerics (θ := θ) (Kr := Kr) (mR := (m : ℝ)) (uR := (U.card : ℝ))
      (dR := (D.card : ℝ)) (nR := (W.card : ℝ)) (aR := (P.card : ℝ)) (tR := (t : ℝ))
      (sR := (s : ℝ)) (kR := (k : ℝ)) hθ0 hθ1 hKr hm0 hm huR hnR hWK haR htR hsR1 hsR2 hkR
  have hkt : k ≤ t := by exact_mod_cast hktR
  have hkA : k ≤ P.card := by exact_mod_cast hkaR
  have htA : t ≤ P.card := by exact_mod_cast htaR
  -- ### The thresholds
  set X : V → ℝ := fun v =>
    (1 + θ / 8) * (β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ)) * (t : ℝ)
      / ((P.card : ℝ) + 1 - (k : ℝ)) with hXdef
  have hTle : ∀ v ∈ W, ((nonNbrs E P v).card : ℝ)
      ≤ β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ) := by
    intro v hv
    have h1 : nonNbrs E P v = P ∩ nonNbrs E W v := nonNbrs_inter_of_subset hPW v
    have h2 : nonNbrs E U v = U ∩ nonNbrs E W v := nonNbrs_inter_of_subset hUW v
    have hdisj : Disjoint (P ∩ nonNbrs E W v) (U ∩ nonNbrs E W v) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hPU)
    have hsum : (P ∩ nonNbrs E W v).card + (U ∩ nonNbrs E W v).card ≤ (nonNbrs E W v).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card
        (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    have hsumR : ((nonNbrs E P v).card : ℝ) + ((nonNbrs E U v).card : ℝ)
        ≤ ((nonNbrs E W v).card : ℝ) := by
      rw [h1, h2]; exact_mod_cast hsum
    linarith [hdens v hv]
  have hXmul : ∀ v, X v * ((P.card : ℝ) + 1 - (k : ℝ))
      = (1 + θ / 8) * (β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ)) * (t : ℝ) := by
    intro v
    rw [hXdef]
    exact div_mul_cancel₀ _ (ne_of_gt hApos)
  have hX0 : ∀ v ∈ W, 0 ≤ X v := by
    intro v hv
    have h1 : (0:ℝ) ≤ β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ) := by
      have h2 : (0:ℝ) ≤ ((nonNbrs E P v).card : ℝ) := Nat.cast_nonneg _
      linarith only [hTle v hv]
    have htnn : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
    rw [hXdef]
    positivity
  -- ### The tail estimate, vertex by vertex
  have hratio : ∀ v ∈ W, ((nonNbrs E P v).card : ℝ) * (t : ℝ)
      ≤ (1 / (1 + θ / 8)) * ((((⌈X v⌉₊ + k) + 1 - k : ℕ) : ℝ) * ((P.card + 1 - k : ℕ) : ℝ)) := by
    intro v hv
    have hcast1 : (((⌈X v⌉₊ + k) + 1 - k : ℕ) : ℝ) = (⌈X v⌉₊ : ℝ) + 1 := by
      have h : (⌈X v⌉₊ + k) + 1 - k = ⌈X v⌉₊ + 1 := by omega
      rw [h]; push_cast; ring
    have hcast2 : ((P.card + 1 - k : ℕ) : ℝ) = (P.card : ℝ) + 1 - (k : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ P.card + 1)]; push_cast; ring
    rw [hcast1, hcast2]
    have hρ0 : (0:ℝ) < 1 / (1 + θ / 8) := by positivity
    have e1 : (1 / (1 + θ / 8)) * (X v * ((P.card : ℝ) + 1 - (k : ℝ)))
        = (β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ)) * (t : ℝ) := by
      rw [hXmul v]; field_simp
    have e2 : X v * ((P.card : ℝ) + 1 - (k : ℝ))
        ≤ ((⌈X v⌉₊ : ℝ) + 1) * ((P.card : ℝ) + 1 - (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [Nat.le_ceil (X v)]) hApos.le
    calc ((nonNbrs E P v).card : ℝ) * (t : ℝ)
        ≤ (β * (W.card : ℝ) - ((nonNbrs E U v).card : ℝ)) * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (hTle v hv) (Nat.cast_nonneg _)
      _ = (1 / (1 + θ / 8)) * (X v * ((P.card : ℝ) + 1 - (k : ℝ))) := e1.symm
      _ ≤ (1 / (1 + θ / 8)) * (((⌈X v⌉₊ : ℝ) + 1) * ((P.card : ℝ) + 1 - (k : ℝ))) :=
          mul_le_mul_of_nonneg_left e2 hρ0.le
  -- ### The union bound
  have hsmall : ((W.card : ℝ)) * (1 / (1 + θ / 8)) ^ k < 1 := by
    have hQ : (0:ℝ) < (1 + θ / 8) ^ k := by positivity
    have hbern : 1 + (s : ℝ) * (θ / 8) ≤ (1 + θ / 8) ^ s :=
      one_add_mul_le_pow (by linarith) s
    have hk2 : (1 + θ / 8) ^ k = ((1 + θ / 8) ^ s) ^ 2 := by rw [hkdef, pow_mul]
    have hlow0 : (0:ℝ) ≤ θ ^ 2 * (m : ℝ) / 512 := by positivity
    have hsq : (θ ^ 2 * (m : ℝ) / 512) ^ 2 ≤ ((1 + θ / 8) ^ s) ^ 2 :=
      pow_le_pow_left₀ hlow0 (le_trans hlow hbern) 2
    have hpow : (W.card : ℝ) < (1 + θ / 8) ^ k := by rw [hk2]; linarith only [hnlt, hsq]
    rw [div_pow, one_pow, mul_one_div, div_lt_one hQ]
    exact hpow
  obtain ⟨S, hS, hSgood⟩ :=
    exists_powersetCard_avoiding (A := P) (W := W) (T := fun v => nonNbrs E P v) (y := fun v => ⌈X v⌉₊ + k)
      (t := t) (k := k) (ρ := 1 / (1 + θ / 8))
      (fun v _ => nonNbrs_subset) hkt (fun v _ => Nat.le_add_left k _) hkA htA hratio hsmall
  obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.1 hS
  -- ### The level
  refine ⟨U ∪ S, Finset.subset_union_left, Finset.union_subset hUW (hSP.trans hPW), ?_, ?_, ?_⟩
  · exact Finset.disjoint_union_left.2 ⟨hUD, Finset.disjoint_of_subset_left hSP hPD⟩
  · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hSP hPU.symm), hScard,
      htdef]
    omega
  · intro v hv
    have hW'W : U ∪ S ⊆ W := Finset.union_subset hUW (hSP.trans hPW)
    have hsplit : nonNbrs E (U ∪ S) v = (U ∩ nonNbrs E W v) ∪ (S ∩ nonNbrs E W v) := by
      rw [nonNbrs_inter_of_subset hW'W v, Finset.union_inter_distrib_right]
    have hdisj : Disjoint (U ∩ nonNbrs E W v) (S ∩ nonNbrs E W v) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right (Finset.inter_subset_left.trans hSP) hPU.symm)
    have hSZ : S ∩ nonNbrs E W v = nonNbrs E P v ∩ S := by
      rw [nonNbrs_inter_of_subset hPW v]
      ext a
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨haS, haZ⟩; exact ⟨⟨hSP haS, haZ⟩, haS⟩
      · rintro ⟨⟨-, haZ⟩, haS⟩; exact ⟨haS, haZ⟩
    have hcardsplit : (nonNbrs E (U ∪ S) v).card
        = (nonNbrs E U v).card + (nonNbrs E P v ∩ S).card := by
      rw [hsplit, Finset.card_union_of_disjoint hdisj, ← hSZ, ← nonNbrs_inter_of_subset hUW v]
    have hbad : ((nonNbrs E P v ∩ S).card : ℝ) ≤ X v + (k : ℝ) := by
      have h1 : (nonNbrs E P v ∩ S).card < ⌈X v⌉₊ + k := hSgood v hv
      have h2 : (nonNbrs E P v ∩ S).card + 1 ≤ ⌈X v⌉₊ + k := h1
      have h3 : ((nonNbrs E P v ∩ S).card : ℝ) + 1 ≤ (⌈X v⌉₊ : ℝ) + (k : ℝ) := by
        exact_mod_cast h2
      have h5 : (⌈X v⌉₊ : ℝ) < X v + 1 := Nat.ceil_lt_add_one (hX0 v hv)
      linarith
    have hgoal := level_arith (β := β) (θ := θ) (nR := (W.card : ℝ)) (uR := (U.card : ℝ))
      (dR := (D.card : ℝ)) (mR := (m : ℝ)) (tR := (t : ℝ)) (kR := (k : ℝ))
      (A := (P.card : ℝ) + 1 - (k : ℝ)) (Nv := ((nonNbrs E U v).card : ℝ)) (NUv := NU v)
      (X := X v) hβ0 hβ1 hθ0 hθ1 huR0 hdR0 huR hm0 hnR (by rw [haR]) htR hk0 hk16
      (hNUle v hv) (hNUβ v hv) (hXmul v)
    calc ((nonNbrs E (U ∪ S) v).card : ℝ)
        = ((nonNbrs E U v).card : ℝ) + ((nonNbrs E P v ∩ S).card : ℝ) := by
          rw [hcardsplit]; push_cast; ring
      _ ≤ ((nonNbrs E U v).card : ℝ) + (X v + (k : ℝ)) := by linarith
      _ ≤ β * (m : ℝ) + (NU v - β * (U.card : ℝ)) + β * (D.card : ℝ) + θ * (m : ℝ) := by
          linarith only [hgoal]

end BKLO
