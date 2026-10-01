module

public import RequestProject.AFKS.Refine
public import RequestProject.AFKS.MeanSquare

/-!
# The strong regularity lemma (AFKS, Lemma 4.1)

For every `m`, every function `f : ℕ → (0, ∞)` and every `θ > 0` there is `S` such that every
graph on `n ≥ S` vertices has an equipartition `A` into `k ≥ m` parts and an equipartition `B`
refining `A`, with `|B| ≤ S`, such that `B` is `f(k)`-uniform and `q(B) ≤ q(A) + θ`.

The regularity parameter of `B` depends on the number of parts `k` of `A`. This is the point
of the lemma. Closeness of `B` to `A` is expressed through the mean square density `q`, as in
Conlon–Fox, Corollary 1.1. Through the variance inequality `sum_sq_sub_le_msd_sub` this implies
the "`ε`-closeness" of the original formulation.

The proof iterates the refining regularity lemma `exists_refining_uniform`:
`A₀, A₁ = R(A₀), A₂ = R(A₁), …`, where `R(P)` is an `f(|P|)`-uniform refinement of `P`. Since
`0 ≤ q ≤ 1`, after at most `⌈1/θ⌉` steps some step increases `q` by at most `θ`.
-/

@[expose] public section

open Finset Fintype

universe u

namespace AFKS

/-- The refining regularity lemma, for every `k` including `k = 0`. -/
theorem exists_refining_uniform' (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T N : ℕ, ∀ {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
      [DecidableRel G.Adj], N ≤ card α → ∀ A : Finpartition (univ : Finset α),
        A.IsEquipartition → #A.parts = k →
          ∃ B : Finpartition (univ : Finset α), B ≤ A ∧ B.IsEquipartition ∧ #B.parts ≤ T ∧
            B.IsUniform G ε := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, 1, fun {α} _ _ G _ hN A _ hA0 => ?_⟩
    exfalso
    have hne : (univ : Finset α).Nonempty := Finset.univ_nonempty_iff.2 (by
      rw [← Fintype.card_pos_iff]; omega)
    obtain ⟨x, -⟩ := hne
    have := A.part_mem.2 (Finset.mem_univ x)
    rw [Finset.card_eq_zero] at hA0
    simp [hA0] at this
  · exact exists_refining_uniform.{u} k hk hε

/-- **Strong regularity lemma (AFKS, Lemma 4.1)**, mean-square-density form. -/
theorem strong_regularity (m : ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0 < f k) {θ : ℝ} (hθ : 0 < θ) :
    ∃ S : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], S ≤ card V →
        ∃ A B : Finpartition (univ : Finset V), A.IsEquipartition ∧ B.IsEquipartition ∧
          B ≤ A ∧ m ≤ #A.parts ∧ #B.parts ≤ S ∧ B.IsUniform G (f #A.parts) ∧
            msd G B ≤ msd G A + θ := by
  have hR := fun k => exists_refining_uniform'.{u} k (hf k)
  choose T N hTN using hR
  set k0 := max m 1 with hk0def
  set t := ⌈1 / θ⌉₊ + 1 with htdef
  let W : ℕ → ℕ := fun j => Nat.rec k0 (fun _ w => max w ((range (w + 1)).sup T)) j
  have hWsucc : ∀ j, W (j + 1) = max (W j) ((range (W j + 1)).sup T) := fun j => rfl
  have hW0 : W 0 = k0 := rfl
  have hWmono : Monotone W :=
    monotone_nat_of_le_succ fun j => by rw [hWsucc]; exact le_max_left _ _
  set Nb := (range (t + 1)).sup fun j => (range (W j + 1)).sup N with hNbdef
  refine ⟨max (W t) (max Nb k0), ?_⟩
  intro V _ _ G _ hS
  have hk0 : k0 ≤ card V := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hS)
  have hNb : Nb ≤ card V := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hS)
  obtain ⟨A0, hA0eq, hA0card⟩ := Finpartition.exists_equipartition_card_eq (univ : Finset V)
    (by omega : k0 ≠ 0) (by rwa [card_univ])
  by_contra hgoal
  have claim : ∀ j, j ≤ t → ∃ P : Finpartition (univ : Finset V), P.IsEquipartition ∧
      k0 ≤ #P.parts ∧ #P.parts ≤ W j ∧ (j : ℝ) * θ ≤ msd G P := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨A0, hA0eq, hA0card.ge, hA0card.le, by simpa using msd_nonneg G A0⟩
    | succ j ih =>
      intro hj
      obtain ⟨P, hPeq, hPk, hPW, hPq⟩ := ih (by omega)
      have hNP : N #P.parts ≤ card V := by
        refine le_trans ?_ hNb
        refine le_trans (Finset.le_sup (f := N) (Finset.mem_range.2 (by omega : #P.parts < W j + 1)))
          ?_
        exact Finset.le_sup (f := fun j => (range (W j + 1)).sup N)
          (Finset.mem_range.2 (by omega : j < t + 1))
      obtain ⟨B, hBP, hBeq, hBT, hBu⟩ := hTN #P.parts G hNP P hPeq rfl
      have hBW : #B.parts ≤ W (j + 1) := by
        refine hBT.trans ((Finset.le_sup (f := T)
          (Finset.mem_range.2 (by omega : #P.parts < W j + 1))).trans ?_)
        rw [hWsucc]; exact le_max_right _ _
      by_cases hq : msd G B ≤ msd G P + θ
      · exact absurd ⟨P, B, hPeq, hBeq, hBP, le_trans (le_max_left _ _) hPk,
          hBW.trans ((hWmono hj).trans (le_max_left _ _)), hBu, hq⟩ hgoal
      · refine ⟨B, hBeq, hPk.trans (Finpartition.card_mono hBP), hBW, ?_⟩
        push_cast
        push_neg at hq
        linarith
  obtain ⟨P, -, -, -, hq⟩ := claim t le_rfl
  have h1 := msd_le_one G P
  have h2 : 1 / θ ≤ (⌈1 / θ⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : (t : ℝ) = ⌈1 / θ⌉₊ + 1 := by rw [htdef]; push_cast; ring
  rw [div_le_iff₀ hθ] at h2
  nlinarith

end AFKS
