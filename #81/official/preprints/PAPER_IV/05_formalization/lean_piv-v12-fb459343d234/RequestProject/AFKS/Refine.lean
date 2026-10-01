module

public import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Regularity.Increment

/-!
# A refining version of Szemerédi's regularity lemma

Mathlib proves Szemerédi's regularity lemma (`szemeredi_regularity`) starting from an arbitrary
dummy equipartition. For the strong regularity lemma of Alon–Fischer–Krivelevich–Szegedy we need a
version that *refines a given equipartition*: for every `k` and `ε > 0` there are `T` and `N`
such that every equipartition `A` into `k` parts of a graph on `n ≥ N` vertices has an `ε`-uniform
equipartition `B` refining `A` with at most `T` parts.

We obtain it by first splitting every part of `A` into `t` near-equal pieces (which gives an
equipartition refining `A` with many parts), and then running Mathlib's energy increment
(`SzemerediRegularity.increment`), which always refines the partition it starts from.
-/

@[expose] public section

open Finset Fintype SzemerediRegularity

universe u

namespace AFKS

variable {α : Type*} [DecidableEq α]

/-- In an equipartition of `s` into `t` parts, `t * (#x - 1) < #s` for every part. -/
theorem IsEquipartition.mul_card_sub_one_lt {s : Finset α} {P : Finpartition s}
    (hP : P.IsEquipartition) {x : Finset α} (hx : x ∈ P.parts) :
    #P.parts * (#x - 1) < #s := by
  have hpos : 0 < #P.parts := Finset.card_pos.2 ⟨x, hx⟩
  have hxne : x.Nonempty := Finset.nonempty_iff_ne_empty.2 (P.ne_bot hx)
  have hx1 : 1 ≤ #x := Finset.card_pos.2 hxne
  rcases hP.card_parts_eq_average hx with h | h
  · have h1 := Nat.div_mul_le_self #s #P.parts
    have : #P.parts * (#x - 1) < #P.parts * #x :=
      Nat.mul_lt_mul_of_pos_left (by omega) hpos
    rw [h] at this ⊢
    nlinarith [Nat.mul_comm (#s / #P.parts) #P.parts]
  · have hmod : 0 < #s % #P.parts := by
      rw [← hP.card_large_parts_eq_mod]
      exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, h⟩⟩
    have := Nat.div_add_mod #s #P.parts
    rw [h, Nat.add_sub_cancel]
    omega

/-- In an equipartition of `s` into `t` parts, `#s < t * (#y + 1)` for every part. -/
theorem IsEquipartition.lt_mul_card_add_one {s : Finset α} {P : Finpartition s}
    (hP : P.IsEquipartition) {y : Finset α} (hy : y ∈ P.parts) :
    #s < #P.parts * (#y + 1) := by
  have hpos : 0 < #P.parts := Finset.card_pos.2 ⟨y, hy⟩
  have h := hP.average_le_card_part hy
  have := Nat.lt_div_mul_add (a := #s) hpos
  nlinarith [Nat.mul_comm (#s / #P.parts) #P.parts]

/-- Splitting every part of an equipartition into `t` near-equal pieces gives an equipartition
refining it, with `t` times as many parts. -/
theorem exists_subdivision {s : Finset α} (A : Finpartition s) (hA : A.IsEquipartition)
    {t : ℕ} (ht : 0 < t) (hsize : ∀ U ∈ A.parts, t ≤ #U) :
    ∃ P : Finpartition s, P ≤ A ∧ P.IsEquipartition ∧ #P.parts = #A.parts * t := by
  have hQ : ∀ U ∈ A.parts, ∃ Q : Finpartition U, Q.IsEquipartition ∧ #Q.parts = t :=
    fun U hU => Finpartition.exists_equipartition_card_eq U ht.ne' (hsize U hU)
  choose Q hQeq hQcard using hQ
  refine ⟨A.bind Q, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨U, hU, hbU⟩ := Finpartition.mem_bind.1 hb
    exact ⟨U, hU, (Q U hU).le hbU⟩
  · intro x y hx hy
    obtain ⟨U, hU, hxU⟩ := Finpartition.mem_bind.1 hx
    obtain ⟨W, hW, hyW⟩ := Finpartition.mem_bind.1 hy
    have h1 := IsEquipartition.mul_card_sub_one_lt (hQeq U hU) hxU
    have h2 := IsEquipartition.lt_mul_card_add_one (hQeq W hW) hyW
    rw [hQcard] at h1 h2
    have h3 : #U ≤ #W + 1 := hA hU hW
    have h4 : t * (#x - 1) < t * (#y + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left h4
    omega
  · rw [Finpartition.card_bind]
    simp [hQcard]

variable [Fintype α]

/-- Mathlib's increment partition refines the partition it starts from. -/
theorem increment_le {P : Finpartition (univ : Finset α)} (hP : P.IsEquipartition)
    (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) : increment hP G ε ≤ P := by
  intro b hb
  obtain ⟨U, hU, hbU⟩ := Finpartition.mem_bind.1 hb
  exact ⟨U, hU, Finpartition.le _ hbU⟩

/-- **Refining regularity lemma.** For every `k ≥ 1` and `ε > 0` there are `T` and `N` such that
for every graph on `n ≥ N` vertices, every equipartition `A` into `k` parts has an `ε`-uniform
equipartition refining it, with at most `T` parts. -/
theorem exists_refining_uniform (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ T N : ℕ, ∀ {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], N ≤ card α → ∀ A : Finpartition (univ : Finset α),
        A.IsEquipartition → #A.parts = k →
          ∃ B : Finpartition (univ : Finset α), B ≤ A ∧ B.IsEquipartition ∧ #B.parts ≤ T ∧
            B.IsUniform G ε := by
  set ε' := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (100 / ε' ^ 5) (by norm_num : (1 : ℝ) < 4)
  set t0 := n0 + 7 with ht0
  set p0 := k * t0 with hp0
  have ht0p0 : t0 ≤ p0 := Nat.le_mul_of_pos_left t0 hk
  set i0 := ⌊4 / ε' ^ 5⌋₊ with hi0
  set T0 := stepBound^[i0] p0 with hT0
  refine ⟨stepBound^[i0 + 1] p0, max (T0 * 16 ^ T0) (k * t0), ?_⟩
  intro α _ _ G _ hN A hA hAk
  have hp0T0 : p0 ≤ T0 := Function.id_le_iterate_of_id_le le_stepBound i0 p0
  have hT0N : T0 ≤ T0 * 16 ^ T0 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp0le : p0 ≤ card α := hp0T0.trans (hT0N.trans ((le_max_left _ _).trans hN))
  have : Nonempty α := by
    rw [← Fintype.card_pos_iff]; omega
  have hsize : ∀ U ∈ A.parts, t0 ≤ #U := fun U hU => by
    have h := hA.average_le_card_part hU
    rw [card_univ, hAk] at h
    exact le_trans ((Nat.le_div_iff_mul_le hk).2 (by rw [mul_comm]; exact hp0le)) h
  obtain ⟨P0, hP0A, hP0eq, hP0card⟩ := exists_subdivision A hA (by omega : 0 < t0) hsize
  rw [hAk] at hP0card
  have h100 : (100 : ℝ) ≤ 4 ^ p0 * ε' ^ 5 := by
    have h1 : (4 : ℝ) ^ n0 ≤ 4 ^ p0 := pow_right_mono₀ (by norm_num) (by omega)
    have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε' ^ 5)).1 hn0
    nlinarith [pow_pos hε'0 5]
  suffices h : ∀ i : ℕ, ∃ P : Finpartition (univ : Finset α), P ≤ A ∧ P.IsEquipartition ∧
      p0 ≤ #P.parts ∧ #P.parts ≤ stepBound^[i] p0 ∧
        (P.IsUniform G ε' ∨ ε' ^ 5 / 4 * i ≤ P.energy G) by
    obtain ⟨P, h1, h2, h3, h4, h5⟩ := h (i0 + 1)
    refine ⟨P, h1, h2, h4, (h5.resolve_right fun hPenergy => lt_irrefl (1 : ℝ) ?_).mono
      (min_le_left _ _)⟩
    calc
      (1 : ℝ) = ε' ^ 5 / 4 * (4 / ε' ^ 5) := by field_simp
      _ < ε' ^ 5 / 4 * (i0 + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ ≤ (P.energy G : ℝ) := by rwa [← Nat.cast_add_one]
      _ ≤ 1 := mod_cast P.energy_le_one G
  intro i
  induction i with
  | zero =>
    refine ⟨P0, hP0A, hP0eq, hP0card.ge, hP0card.le, Or.inr ?_⟩
    rw [Nat.cast_zero, mul_zero]
    exact mod_cast P0.energy_nonneg G
  | succ i ih =>
    obtain ⟨P, hPA, hP₁, hP₂, hP₃, hP₄⟩ := ih
    by_cases huniform : P.IsUniform G ε'
    · refine ⟨P, hPA, hP₁, hP₂, ?_, Or.inl huniform⟩
      rw [Function.iterate_succ_apply']
      exact hP₃.trans (le_stepBound _)
    replace hP₄ := hP₄.resolve_left huniform
    have hεl' : (100 : ℝ) ≤ 4 ^ #P.parts * ε' ^ 5 :=
      h100.trans (mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hP₂) (by positivity))
    have hi : (i : ℝ) ≤ 4 / ε' ^ 5 := by
      have hi : ε' ^ 5 / 4 * ↑i ≤ 1 := hP₄.trans (mod_cast P.energy_le_one G)
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hsz : #P.parts ≤ T0 :=
      hP₃.trans (Function.monotone_iterate_of_id_le le_stepBound (Nat.le_floor hi) _)
    have hPα : #P.parts * 16 ^ #P.parts ≤ card α :=
      (Nat.mul_le_mul hsz (Nat.pow_le_pow_right (by norm_num) hsz)).trans
        ((le_max_left _ _).trans hN)
    have h7 : 7 ≤ #P.parts := le_trans (by omega) hP₂
    refine ⟨increment hP₁ G ε', (increment_le hP₁ G ε').trans hPA,
      increment_isEquipartition hP₁ G ε', ?_, ?_, Or.inr <| le_trans ?_ <|
        energy_increment hP₁ h7 hεl' hPα huniform hε'0.le hε'1⟩
    · rw [card_increment hPα huniform]
      exact hP₂.trans (le_stepBound _)
    · rw [card_increment hPα huniform, Function.iterate_succ_apply']
      exact stepBound_mono hP₃
    · rw [Nat.cast_succ, mul_add, mul_one]
      gcongr

end AFKS
