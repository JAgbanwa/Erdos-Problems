/-
# The bottom-set clause of the §10 interface is **proved**, not assumed.

`BKLO.VortexBottomClauseR2` asks, of a large dense edge set, for a bottom set `U` of bounded size
into which all but a `1/(4K²)` fraction of the vertices are dense.  This file proves it, for any
schedule `f` that stays at the bottom of its window (`f s ≤ 9/10 + ε/2`) — which is where the
interface allows it to be, since it only asks `9/10 + ε/2 ≤ f s`.

The bottom set is a uniformly random `t`-subset, with the vertices that are *themselves* badly
joined to it removed; the moment bound `BKLO.card_deviant_le_pow` controls both the number of bad
vertices of the ground set and the number of bad vertices inside the sample, the second through a
conditional form of the same bound (`BKLO.card_deviant_mem_le_pow`).

Everything here is `sorry`-free.
-/
import BKLO.Sampling
import BKLO.ReservoirRepaired2

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Non-neighbours -/

/-- The non-neighbours of `v` inside `S`: the vertices of `S` not joined to `v` by an edge of `E`.
For `v ∈ S` this contains `v` itself. -/
def nonNbrs (E : Finset (Sym2 V)) (S : Finset V) (v : V) : Finset V := S \ resLink E S v

theorem nonNbrs_subset {E : Finset (Sym2 V)} {S : Finset V} {v : V} : nonNbrs E S v ⊆ S :=
  Finset.sdiff_subset

theorem mem_nonNbrs_self {E : Finset (Sym2 V)} {S : Finset V} {v : V} (hv : v ∈ S)
    (hnd : ∀ e ∈ E, ¬ e.IsDiag) : v ∈ nonNbrs E S v := by
  refine Finset.mem_sdiff.2 ⟨hv, fun h => ?_⟩
  exact hnd _ (mem_resLink.1 h).2 (by simp)

/-- Inside a smaller set `U`, the link of `v` is what is left of `U` after the non-neighbours. -/
theorem resLink_eq_sdiff_nonNbrs {E : Finset (Sym2 V)} {S U : Finset V} (hUS : U ⊆ S) (v : V) :
    resLink E U v = U \ nonNbrs E S v := by
  ext a
  constructor
  · intro ha
    obtain ⟨haU, haE⟩ := mem_resLink.1 ha
    refine Finset.mem_sdiff.2 ⟨haU, fun hb => ?_⟩
    exact (Finset.mem_sdiff.1 hb).2 (mem_resLink.2 ⟨hUS haU, haE⟩)
  · intro ha
    obtain ⟨haU, hb⟩ := Finset.mem_sdiff.1 ha
    refine mem_resLink.2 ⟨haU, ?_⟩
    by_contra hE
    exact hb (Finset.mem_sdiff.2 ⟨hUS haU, fun h => hE (mem_resLink.1 h).2⟩)

theorem card_nonNbrs {E : Finset (Sym2 V)} {S : Finset V} {v : V} (hv : v ∈ S)
    (hES : E ⊆ cliqueEdges S) (hnd : ∀ e ∈ E, ¬ e.IsDiag) :
    (nonNbrs E S v).card = S.card - edeg E v := by
  have hres : (resLink E S v).card = edeg E v := by
    rw [← edeg_inter_cliqueEdges_eq_card_resLink hv hnd, Finset.inter_eq_left.2 hES]
  have hsub : resLink E S v ⊆ S := Finset.filter_subset _ _
  rw [nonNbrs, Finset.card_sdiff_of_subset hsub, hres]

/-! ### The conditional form of the moment bound -/

/-- The `t`-subsets of `A` that contain `v` and meet `T` in at least `y` points correspond to the
`(t-1)`-subsets of `A \ {v}` meeting `T \ {v}` in at least `y - 1` points. -/
theorem card_filter_mem_deviant {A T : Finset V} {v : V} (hvA : v ∈ A) (hvT : v ∈ T) {t y : ℕ}
    (ht : 1 ≤ t) :
    ((A.powersetCard t).filter (fun U => v ∈ U ∧ y ≤ (T ∩ U).card)).card
      = (((A.erase v).powersetCard (t - 1)).filter
          (fun U' => y - 1 ≤ ((T.erase v) ∩ U').card)).card := by
  classical
  refine Finset.card_bij' (fun U _ => U.erase v) (fun U' _ => insert v U') ?_ ?_ ?_ ?_
  · intro U hU
    obtain ⟨hmem, hvU, hbad⟩ : U ∈ A.powersetCard t ∧ v ∈ U ∧ y ≤ (T ∩ U).card := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hU; exact ⟨h1, h2.1, h2.2⟩
    obtain ⟨hUA, hUt⟩ := Finset.mem_powersetCard.1 hmem
    have hsplit : T ∩ U = insert v ((T.erase v) ∩ (U.erase v)) := by
      ext a
      by_cases hav : a = v
      · subst hav; simp [hvT, hvU]
      · simp [hav, Finset.mem_erase]
    have hnotmem : v ∉ (T.erase v) ∩ (U.erase v) := by simp
    have hcard : (T ∩ U).card = ((T.erase v) ∩ (U.erase v)).card + 1 := by
      rw [hsplit, Finset.card_insert_of_notMem hnotmem]
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, ?_⟩
    · exact Finset.erase_subset_erase v hUA
    · rw [Finset.card_erase_of_mem hvU, hUt]
    · show y - 1 ≤ ((T.erase v) ∩ (U.erase v)).card
      omega
  · intro U' hU'
    obtain ⟨hmem, hbad⟩ := Finset.mem_filter.1 hU'
    obtain ⟨hU'A, hU't⟩ := Finset.mem_powersetCard.1 hmem
    have hvU' : v ∉ U' := fun h => (Finset.mem_erase.1 (hU'A h)).1 rfl
    have hsplit : T ∩ insert v U' = insert v ((T.erase v) ∩ U') := by
      ext a
      by_cases hav : a = v
      · subst hav; simp [hvT]
      · simp [hav, Finset.mem_erase]
    have hnotmem : v ∉ (T.erase v) ∩ U' := by simp
    have hcard : (T ∩ insert v U').card = ((T.erase v) ∩ U').card + 1 := by
      rw [hsplit, Finset.card_insert_of_notMem hnotmem]
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.insert_subset hvA (hU'A.trans (Finset.erase_subset _ _))
    · rw [Finset.card_insert_of_notMem hvU', hU't]; omega
    · exact Finset.mem_insert_self v U'
    · show y ≤ (T ∩ insert v U').card
      omega
  · intro U hU
    have hvU : v ∈ U := (Finset.mem_filter.1 hU).2.1
    exact Finset.insert_erase hvU
  · intro U' hU'
    have hU'A := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hU').1).1
    have hvU' : v ∉ U' := fun h => (Finset.mem_erase.1 (hU'A h)).1 rfl
    exact Finset.erase_insert hvU'

/-- **The conditional tail bound.**  Among the `t`-subsets *containing* `v`, the fraction meeting
`T` in at least `y` points is at most `ρ^k` as well. -/
theorem card_deviant_mem_le_pow {A T : Finset V} {v : V} (hTA : T ⊆ A) (hvA : v ∈ A) (hvT : v ∈ T)
    {t k y : ℕ} {ρ : ℝ} (ht : 1 ≤ t) (hy : 1 ≤ y) (hkt : k ≤ t - 1) (hky : k ≤ y - 1)
    (hkA : k ≤ A.card - 1)
    (hratio : ((T.card : ℝ) - 1) * ((t : ℝ) - 1) ≤ ρ * (((y - k : ℕ) : ℝ) * ((A.card - k : ℕ) : ℝ))) :
    ((((A.powersetCard t).filter (fun U => v ∈ U ∧ y ≤ (T ∩ U).card)).card : ℝ))
      ≤ ρ ^ k * ((A.card - 1).choose (t - 1) : ℝ) := by
  classical
  have hcard : (A.erase v).card = A.card - 1 := Finset.card_erase_of_mem hvA
  have hTcard : (T.erase v).card = T.card - 1 := Finset.card_erase_of_mem hvT
  have hsub : T.erase v ⊆ A.erase v := Finset.erase_subset_erase v hTA
  have hApos : 1 ≤ A.card := Finset.card_pos.2 ⟨v, hvA⟩
  have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨v, hvT⟩
  have hmain := card_deviant_le_pow (A := A.erase v) (T := T.erase v) (t := t - 1) (k := k)
    (y := y - 1) (ρ := ρ) hsub hkt (by omega) (by omega) ?_
  · rw [card_filter_mem_deviant hvA hvT ht]
    rw [hcard] at hmain
    exact hmain
  · rw [hTcard, hcard]
    have h1 : ((T.card - 1 : ℕ) : ℝ) = (T.card : ℝ) - 1 := by
      rw [Nat.cast_sub hTpos]; norm_num
    have h2 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      rw [Nat.cast_sub ht]; norm_num
    have h3 : (y - 1 + 1 - k : ℕ) = (y - k : ℕ) := by omega
    have h4 : (A.card - 1 + 1 - k : ℕ) = (A.card - k : ℕ) := by omega
    rw [h1, h2, h3, h4]
    exact hratio

/-! ### Averaging: a sample that is good for almost every vertex, and inside itself -/

omit [DecidableEq V] in
/-- Swapping the order of summation: summing the number of vertices that a sample fails over all
samples is summing the number of samples that fail a vertex over all vertices. -/
theorem sum_card_filter_swap {S : Finset V} {P : Finset (Finset V)} (p : V → Finset V → Prop)
    [∀ v U, Decidable (p v U)] :
    ∑ U ∈ P, (S.filter (fun v => p v U)).card = ∑ v ∈ S, (P.filter (fun U => p v U)).card := by
  classical
  calc ∑ U ∈ P, (S.filter (fun v => p v U)).card
      = ∑ U ∈ P, ∑ v ∈ S, if p v U then 1 else 0 := by
        exact Finset.sum_congr rfl fun U _ => Finset.card_filter _ _
    _ = ∑ v ∈ S, ∑ U ∈ P, if p v U then 1 else 0 := Finset.sum_comm
    _ = ∑ v ∈ S, (P.filter (fun U => p v U)).card := by
        exact Finset.sum_congr rfl fun v _ => (Finset.card_filter _ _).symm

theorem card_choose_mul {n t : ℕ} (h1 : 1 ≤ n) (h2 : 1 ≤ t) :
    n * (n - 1).choose (t - 1) = n.choose t * t := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
  simpa using Nat.add_one_mul_choose_eq a b

/-- **A good sample exists**: some `t`-subset fails only few vertices of `S`, and only few of its
own vertices. -/
theorem exists_good_sample {S : Finset V} {t y : ℕ} {σ : ℝ} (T : V → Finset V)
    (hσ : 0 < σ) (ht : 1 ≤ t) (htS : t ≤ S.card)
    (hdev : ∀ v ∈ S, ((((S.powersetCard t).filter
        (fun U => y ≤ ((T v) ∩ U).card)).card : ℝ)) ≤ σ * (S.card.choose t : ℝ))
    (hdevmem : ∀ v ∈ S, ((((S.powersetCard t).filter
        (fun U => v ∈ U ∧ y ≤ ((T v) ∩ U).card)).card : ℝ))
          ≤ σ * ((S.card - 1).choose (t - 1) : ℝ)) :
    ∃ U₀ ∈ S.powersetCard t,
      ((S.filter (fun v => y ≤ ((T v) ∩ U₀).card)).card : ℝ) ≤ 4 * σ * (S.card : ℝ) ∧
        (((S.filter (fun v => y ≤ ((T v) ∩ U₀).card)) ∩ U₀).card : ℝ) ≤ 4 * σ * (t : ℝ) := by
  classical
  set n := S.card with hn
  set P := S.powersetCard t with hP
  set Bad : Finset V → Finset V := fun U => S.filter (fun v => y ≤ ((T v) ∩ U).card) with hBad
  have hnpos : 0 < n := lt_of_lt_of_le ht htS
  have hPcard : P.card = n.choose t := Finset.card_powersetCard _ _
  have hPpos : 0 < P.card := by
    rw [hPcard]
    exact Nat.choose_pos htS
  have hPposR : (0 : ℝ) < (P.card : ℝ) := by exact_mod_cast hPpos
  -- first moment of the number of failed vertices
  have hsum1 : ∑ U ∈ P, (Bad U).card = ∑ v ∈ S, (P.filter (fun U => y ≤ ((T v) ∩ U).card)).card :=
    sum_card_filter_swap (S := S) (P := P) (fun v U => y ≤ ((T v) ∩ U).card)
  have hsum1R : ((∑ U ∈ P, (Bad U).card : ℕ) : ℝ) ≤ σ * (n : ℝ) * (P.card : ℝ) := by
    rw [hsum1]
    push_cast
    calc ∑ v ∈ S, ((P.filter (fun U => y ≤ ((T v) ∩ U).card)).card : ℝ)
        ≤ ∑ _v ∈ S, σ * (n.choose t : ℝ) := Finset.sum_le_sum hdev
      _ = (n : ℝ) * (σ * (n.choose t : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hn]
      _ = σ * (n : ℝ) * (P.card : ℝ) := by rw [hPcard]; ring
  -- first moment of the number of failed vertices inside the sample
  have hinter : ∀ U, (Bad U) ∩ U = S.filter (fun v => v ∈ U ∧ y ≤ ((T v) ∩ U).card) := by
    intro U
    ext v
    simp only [hBad, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hsum2 : ∑ U ∈ P, ((Bad U) ∩ U).card
      = ∑ v ∈ S, (P.filter (fun U => v ∈ U ∧ y ≤ ((T v) ∩ U).card)).card := by
    rw [Finset.sum_congr rfl (fun U _ => by rw [hinter U])]
    exact sum_card_filter_swap (S := S) (P := P) (fun v U => v ∈ U ∧ y ≤ ((T v) ∩ U).card)
  have hchoose : (n : ℝ) * ((n - 1).choose (t - 1) : ℝ) = (P.card : ℝ) * (t : ℝ) := by
    have := card_choose_mul (n := n) (t := t) hnpos ht
    rw [hPcard]
    exact_mod_cast this
  have hsum2R : ((∑ U ∈ P, ((Bad U) ∩ U).card : ℕ) : ℝ) ≤ σ * (t : ℝ) * (P.card : ℝ) := by
    rw [hsum2]
    push_cast
    calc ∑ v ∈ S, ((P.filter (fun U => v ∈ U ∧ y ≤ ((T v) ∩ U).card)).card : ℝ)
        ≤ ∑ _v ∈ S, σ * (((n - 1).choose (t - 1) : ℕ) : ℝ) := Finset.sum_le_sum hdevmem
      _ = (n : ℝ) * (σ * (((n - 1).choose (t - 1) : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hn]
      _ = σ * ((n : ℝ) * (((n - 1).choose (t - 1) : ℕ) : ℝ)) := by ring
      _ = σ * (t : ℝ) * (P.card : ℝ) := by rw [hchoose]; ring
  -- Markov
  set P1 := P.filter (fun U => ¬ (((Bad U).card : ℝ) ≤ 4 * σ * (n : ℝ))) with hP1
  set P2 := P.filter (fun U => ¬ ((((Bad U) ∩ U).card : ℝ) ≤ 4 * σ * (t : ℝ))) with hP2
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hmarkov1 : (P1.card : ℝ) * (4 * σ * (n : ℝ)) ≤ σ * (n : ℝ) * (P.card : ℝ) := by
    refine le_trans ?_ hsum1R
    push_cast
    calc (P1.card : ℝ) * (4 * σ * (n : ℝ))
        = ∑ _U ∈ P1, (4 * σ * (n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ U ∈ P1, ((Bad U).card : ℝ) := by
          refine Finset.sum_le_sum fun U hU => ?_
          have := (Finset.mem_filter.1 hU).2
          push_neg at this
          exact le_of_lt this
      _ ≤ ∑ U ∈ P, ((Bad U).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun U _ _ => Nat.cast_nonneg _)
  have hmarkov2 : (P2.card : ℝ) * (4 * σ * (t : ℝ)) ≤ σ * (t : ℝ) * (P.card : ℝ) := by
    refine le_trans ?_ hsum2R
    push_cast
    calc (P2.card : ℝ) * (4 * σ * (t : ℝ))
        = ∑ _U ∈ P2, (4 * σ * (t : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ U ∈ P2, (((Bad U) ∩ U).card : ℝ) := by
          refine Finset.sum_le_sum fun U hU => ?_
          have := (Finset.mem_filter.1 hU).2
          push_neg at this
          exact le_of_lt this
      _ ≤ ∑ U ∈ P, (((Bad U) ∩ U).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun U _ _ => Nat.cast_nonneg _)
  have h1 : (P1.card : ℝ) ≤ (P.card : ℝ) / 4 := by
    have hpos : (0 : ℝ) < 4 * σ * (n : ℝ) := by positivity
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hmarkov1]
  have h2 : (P2.card : ℝ) ≤ (P.card : ℝ) / 4 := by
    have hpos : (0 : ℝ) < 4 * σ * (t : ℝ) := by positivity
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [hmarkov2]
  -- there is a sample outside both bad sets
  have hunion : ((P1 ∪ P2).card : ℝ) < (P.card : ℝ) := by
    have := Finset.card_union_le P1 P2
    have hcast : ((P1 ∪ P2).card : ℝ) ≤ (P1.card : ℝ) + (P2.card : ℝ) := by exact_mod_cast this
    linarith only [hPposR, h1, h2, hcast]
  have hne : ∃ U₀ ∈ P, U₀ ∉ P1 ∪ P2 := by
    by_contra hcon
    push_neg at hcon
    have hsub : P ⊆ P1 ∪ P2 := fun U hU => hcon U hU
    have := Finset.card_le_card hsub
    have : (P.card : ℝ) ≤ ((P1 ∪ P2).card : ℝ) := by exact_mod_cast this
    linarith
  obtain ⟨U₀, hU₀P, hU₀⟩ := hne
  refine ⟨U₀, hU₀P, ?_, ?_⟩
  · by_contra hcon
    exact hU₀ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hU₀P, hcon⟩))
  · by_contra hcon
    exact hU₀ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hU₀P, hcon⟩))

/-! ### Elementary real arithmetic used by the bottom clause

These are stated with explicit real variables so that the nonlinear arithmetic is done in tiny
contexts. -/

private lemma bc_top {ε fs S d : ℝ} (hε : 0 < ε) (hf : fs ≤ 9 / 10 + ε / 2) (hS : 0 ≤ S)
    (hd : (9 / 10 + ε) * S ≤ d) : fs * S ≤ d := by nlinarith only [hε, hf, hS, hd]

private lemma bc_eps_le {ε N : ℝ} (hε' : ε ≤ 1 / 100) (hN : 0 ≤ N) : ε * N ≤ N := by nlinarith only [hε', hN]

private lemma bc_big {ε T c : ℝ} (hε' : ε ≤ 1 / 100) (hT : 0 ≤ T) (h : 2000 * c ≤ ε * T) :
    200000 * c ≤ T := by
  nlinarith [mul_nonneg (sub_nonneg.2 hε') hT]

private lemma bc_thr_nonneg {ε T : ℝ} (hε' : ε ≤ 1 / 100) (hT : 0 ≤ T) :
    (0 : ℝ) ≤ (1 / 10 - 3 * ε / 4) * T := by
  have h : (0 : ℝ) ≤ 1 / 10 - 3 * ε / 4 := by linarith only [hε']
  exact mul_nonneg h hT

private lemma bc_thr_mono {ε T : ℝ} (hε' : ε ≤ 1 / 100) (hT : 0 ≤ T) :
    (1 / 10 - 3 / 400) * T ≤ (1 / 10 - 3 * ε / 4) * T := by
  have h : (1 / 10 - 3 / 400 : ℝ) ≤ 1 / 10 - 3 * ε / 4 := by linarith only [hε']
  exact mul_le_mul_of_nonneg_right h hT

private lemma bc_master {ε N T Y c : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hcT : 2000 * c ≤ ε * T) (hcN : 2000 * c ≤ ε * N)
    (hY : (1 / 10 - 3 * ε / 4) * T ≤ Y) :
    (1 / 10 - ε) * N * T ≤ (1 - ε) * ((Y - c) * (N - c)) := by
  have h1 : (1 / 10 - 1501 / 2000 * ε) * T ≤ Y - c := by linarith only [hcT, hY]
  have h2 : (1 - ε / 2000) * N ≤ N - c := by linarith only [hcN]
  have h1nn : (0 : ℝ) ≤ (1 / 10 - 1501 / 2000 * ε) * T := by
    have h : (0 : ℝ) ≤ 1 / 10 - 1501 / 2000 * ε := by linarith only [hε']
    exact mul_nonneg h hT
  have h2nn : (0 : ℝ) ≤ (1 - ε / 2000) * N := by
    have h : (0 : ℝ) ≤ 1 - ε / 2000 := by linarith only [hε']
    exact mul_nonneg h hN
  have hsq : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
  have hcube : ε ^ 3 ≤ ε ^ 2 * (1 / 100) := by nlinarith only [hε']
  have hcoef : (1 / 10 - ε) ≤ (1 - ε) * (1 / 10 - 1501 / 2000 * ε) * (1 - ε / 2000) := by
    nlinarith only [hsq, hcube, hε]
  calc (1 / 10 - ε) * N * T = (1 / 10 - ε) * (N * T) := by ring
    _ ≤ ((1 - ε) * (1 / 10 - 1501 / 2000 * ε) * (1 - ε / 2000)) * (N * T) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hN hT)
    _ = (1 - ε) * (((1 / 10 - 1501 / 2000 * ε) * T) * ((1 - ε / 2000) * N)) := by ring
    _ ≤ (1 - ε) * ((Y - c) * (N - c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 h2nn (le_trans h1nn h1)) (by linarith)

private lemma bc_incr {Y N c : ℝ} (hY : 0 ≤ Y - c) (hN : 0 ≤ N - c) :
    (Y - c) * (N - c) ≤ (Y + 1 - c) * (N + 1 - c) := by linarith only [hY, hN]

private lemma bc_sub_one {T t : ℝ} (hT : 0 ≤ T) (ht : 1 ≤ t) : (T - 1) * (t - 1) ≤ T * t := by
  linarith only [hT, ht]

private lemma bc_Ulb {ε σ T I : ℝ} (hT : 0 ≤ T) (hσ : σ ≤ ε / 64) (h : I ≤ 4 * σ * T) :
    (1 - ε / 16) * T ≤ T - I := by
  nlinarith [mul_nonneg (sub_nonneg.2 hσ) hT]

private lemma bc_half {ε m u : ℝ} (hε' : ε ≤ 1 / 100) (hm : 0 ≤ m)
    (h : (1 - ε / 16) * (2 * m) ≤ u) : m ≤ u := by nlinarith only [hε', hm, h]

private lemma bc_dens {ε T Y u : ℝ} (hεnn : 0 ≤ ε) (hε' : ε ≤ 1 / 100) (hT : 0 ≤ T)
    (hY : Y - 1 ≤ (1 / 10 - 3 * ε / 4) * T) (hu : (1 - ε / 16) * T ≤ u) :
    Y - 1 ≤ (1 / 10 - ε / 2) * u := by
  have hmul : (1 / 10 - ε / 2) * ((1 - ε / 16) * T) ≤ (1 / 10 - ε / 2) * u :=
    mul_le_mul_of_nonneg_left hu (by linarith)
  nlinarith [mul_nonneg hεnn hT, mul_nonneg (mul_nonneg hεnn hεnn) hT]

private lemma bc_final {ε fu u Y c : ℝ} (hf : fu ≤ 9 / 10 + ε / 2) (hu : 0 ≤ u)
    (hY : Y - 1 ≤ (1 / 10 - ε / 2) * u) (hc : u - (Y - 1) ≤ c) : fu * u ≤ c := by nlinarith only [hf, hu, hY, hc]

/-! ### The bottom-set clause of the twice-repaired interface -/

set_option maxHeartbeats 1000000 in
/-- **The twice-repaired bottom-set clause is a theorem.**

For any schedule `f` that sits at the bottom of its window (`f s ≤ 9/10 + ε/2`, which is where
`BKLO.VortexReservoirEngineR2` allows it to be), any window `C ≥ 2n₂` and any `n₂` large enough
that `1000 k ≤ ε n₂` for some `k` with `(1-ε)^k ≤ ε/(16K²)`, the clause holds.

The bottom set is a uniformly random `2n₂`-subset `U₀` of `S`, with the vertices badly joined to
it deleted; the exceptional set `B` is the set of vertices of `S` badly joined to `U₀`. -/
theorem vortexBottomClauseR2_of_schedule_window {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    {f : ℕ → ℝ} {n₂ C K k : ℕ} (hK : 2 ≤ K) (hk1 : 1 ≤ k)
    (hf : ∀ s : ℕ, n₂ ≤ s → s ≤ C → f s ≤ 9 / 10 + ε / 2)
    (hkσ : (1 - ε) ^ k ≤ ε / (16 * (K : ℝ) * (K : ℝ)))
    (hkn₂ : (1000 : ℝ) * k ≤ ε * n₂) (hC : 2 * n₂ ≤ C) :
    VortexBottomClauseR2 ε f n₂ C K := by
  classical
  intro V _ S E hSn hES hdeg
  have hnd : ∀ e ∈ E, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hES he)).2
  have hreslink : ∀ v ∈ S, (resLink E S v).card = edeg E v := fun v hv => by
    rw [← edeg_inter_cliqueEdges_eq_card_resLink hv hnd, Finset.inter_eq_left.2 hES]
  by_cases hcase : S.card ≤ C
  · -- `S` is already small enough: take it as the bottom set, with no exceptional vertices.
    refine ⟨S, ∅, Finset.Subset.refl _, Finset.empty_subset _, Finset.disjoint_empty_right _,
      hSn, hcase, by simp, fun v hv => ?_⟩
    have hvS : v ∈ S := (Finset.mem_sdiff.1 hv).1
    rw [hreslink v hvS]
    exact bc_top hε (hf S.card hSn hcase) (Nat.cast_nonneg _) (hdeg v hvS)
  push_neg at hcase
  set n := S.card with hn
  set t := 2 * n₂ with htdef
  -- ### Numerical preliminaries
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have htn : t ≤ n := le_of_lt (lt_of_le_of_lt hC hcase)
  have htR : (t : ℝ) = 2 * (n₂ : ℝ) := by rw [htdef]; push_cast; ring
  have htnR : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
  have htnn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkt2 : (2000 : ℝ) * k ≤ ε * t := by rw [htR]; linarith only [hkn₂]
  have hkn2 : (2000 : ℝ) * k ≤ ε * n :=
    le_trans hkt2 (mul_le_mul_of_nonneg_left htnR hε.le)
  have hktsmall : 200000 * (k : ℝ) ≤ (t : ℝ) := bc_big hε' htnn hkt2
  have hknsmall : 200000 * (k : ℝ) ≤ (n : ℝ) := bc_big hε' hnnn hkn2
  have htbig : (200000 : ℝ) ≤ (t : ℝ) := by linarith only [hkR, hktsmall]
  have hnbig : (200000 : ℝ) ≤ (n : ℝ) := by linarith only [htnR, htbig]
  have htpos : 1 ≤ t := by
    have h : (1 : ℝ) ≤ (t : ℝ) := by linarith only [htbig]
    exact_mod_cast h
  -- the deviation threshold
  set y : ℕ := ⌊(1 / 10 - 3 * ε / 4) * (t : ℝ)⌋₊ + 1 with hydef
  have hy_lb : (1 / 10 - 3 * ε / 4) * (t : ℝ) ≤ (y : ℝ) := by
    rw [hydef]; push_cast; exact le_of_lt (Nat.lt_floor_add_one _)
  have hy_ub : (y : ℝ) - 1 ≤ (1 / 10 - 3 * ε / 4) * (t : ℝ) := by
    have := Nat.floor_le (bc_thr_nonneg hε' htnn)
    rw [hydef]; push_cast; linarith only [this]
  have hy_lb' : (1 / 10 - 3 / 400) * (t : ℝ) ≤ (y : ℝ) :=
    le_trans (bc_thr_mono hε' htnn) hy_lb
  have hkylt : (k : ℝ) + 1 ≤ (y : ℝ) := by linarith only [hktsmall, htbig, hy_lb']
  have hktlt : (k : ℝ) + 1 ≤ (t : ℝ) := by linarith only [hktsmall, htbig]
  have hknlt : (k : ℝ) + 1 ≤ (n : ℝ) := by linarith only [hknsmall, hnbig]
  have hkyN : k + 1 ≤ y := by exact_mod_cast hkylt
  have hktN : k + 1 ≤ t := by exact_mod_cast hktlt
  have hknN : k + 1 ≤ n := by exact_mod_cast hknlt
  -- the failure fraction
  have hεlt : ε < 1 := by linarith only [hε']
  have hσpos : (0 : ℝ) < (1 - ε) ^ k := pow_pos (by linarith) k
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h64 : (64 : ℝ) ≤ 16 * (K : ℝ) * (K : ℝ) := by nlinarith only [hKR]
  have hKpos : (0 : ℝ) < 16 * (K : ℝ) * (K : ℝ) := by linarith only [h64]
  have hσK : (16 * (K : ℝ) * (K : ℝ)) * ((1 - ε) ^ k) ≤ ε := by
    calc (16 * (K : ℝ) * (K : ℝ)) * ((1 - ε) ^ k)
        ≤ (16 * (K : ℝ) * (K : ℝ)) * (ε / (16 * (K : ℝ) * (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hkσ hKpos.le
      _ = ε := by field_simp
  have hσle : (1 - ε) ^ k ≤ ε / 64 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    calc (1 - ε) ^ k * 64 ≤ (1 - ε) ^ k * (16 * (K : ℝ) * (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h64 hσpos.le
      _ = (16 * (K : ℝ) * (K : ℝ)) * ((1 - ε) ^ k) := by ring
      _ ≤ ε := hσK
  -- ### The non-neighbourhoods are small
  have hTcard : ∀ v ∈ S, ((nonNbrs E S v).card : ℝ) ≤ (1 / 10 - ε) * (n : ℝ) := by
    intro v hv
    have hcn := card_nonNbrs hv hES hnd
    have hle : edeg E v ≤ n := by
      rw [← hreslink v hv]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hcast : ((nonNbrs E S v).card : ℝ) = (n : ℝ) - (edeg E v : ℝ) := by
      rw [hcn, Nat.cast_sub hle]
    have hd := hdeg v hv
    rw [hcast]
    linarith only [hd]
  -- ### The master ratio inequality
  have hyk : (0 : ℝ) ≤ (y : ℝ) - k := by linarith only [hkylt]
  have hnk : (0 : ℝ) ≤ (n : ℝ) - k := by linarith only [hknlt]
  have hmaster : (1 / 10 - ε) * (n : ℝ) * (t : ℝ) ≤ (1 - ε) * (((y : ℝ) - k) * ((n : ℝ) - k)) :=
    bc_master hε hε' htnn hnnn hkt2 hkn2 hy_lb
  -- ### The two tail bounds
  have hcasty : ((y + 1 - k : ℕ) : ℝ) = (y : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ y + 1)]; push_cast; ring
  have hcastn : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]; push_cast; ring
  have hcasty' : ((y - k : ℕ) : ℝ) = (y : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ y)]
  have hcastn' : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ n)]
  have hdev : ∀ v ∈ S, (((S.powersetCard t).filter
      (fun U => y ≤ ((nonNbrs E S v) ∩ U).card)).card : ℝ)
        ≤ (1 - ε) ^ k * (n.choose t : ℝ) := by
    intro v hv
    refine card_deviant_le_pow (A := S) (T := nonNbrs E S v) nonNbrs_subset
      (by omega) (by omega) (by omega) ?_
    rw [hcasty, hcastn]
    calc ((nonNbrs E S v).card : ℝ) * (t : ℝ) ≤ ((1 / 10 - ε) * (n : ℝ)) * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (hTcard v hv) htnn
      _ = (1 / 10 - ε) * (n : ℝ) * (t : ℝ) := by ring
      _ ≤ (1 - ε) * (((y : ℝ) - k) * ((n : ℝ) - k)) := hmaster
      _ ≤ (1 - ε) * (((y : ℝ) + 1 - k) * ((n : ℝ) + 1 - k)) :=
          mul_le_mul_of_nonneg_left (bc_incr hyk hnk) (by linarith)
  have hdevmem : ∀ v ∈ S, (((S.powersetCard t).filter
      (fun U => v ∈ U ∧ y ≤ ((nonNbrs E S v) ∩ U).card)).card : ℝ)
        ≤ (1 - ε) ^ k * ((n - 1).choose (t - 1) : ℝ) := by
    intro v hv
    refine card_deviant_mem_le_pow (A := S) (T := nonNbrs E S v) nonNbrs_subset hv
      (mem_nonNbrs_self hv hnd) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
    rw [hcasty', hcastn']
    have h1R : (1 : ℝ) ≤ (t : ℝ) := by linarith only [hktlt]
    calc (((nonNbrs E S v).card : ℝ) - 1) * ((t : ℝ) - 1)
        ≤ ((nonNbrs E S v).card : ℝ) * (t : ℝ) := bc_sub_one (Nat.cast_nonneg _) h1R
      _ ≤ ((1 / 10 - ε) * (n : ℝ)) * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (hTcard v hv) htnn
      _ = (1 / 10 - ε) * (n : ℝ) * (t : ℝ) := by ring
      _ ≤ (1 - ε) * (((y : ℝ) - k) * ((n : ℝ) - k)) := hmaster
  -- ### The good sample
  obtain ⟨U₀, hU₀P, hbad1, hbad2⟩ :=
    exists_good_sample (S := S) (t := t) (y := y) (σ := (1 - ε) ^ k) (nonNbrs E S)
      hσpos htpos htn hdev hdevmem
  obtain ⟨hU₀S, hU₀t⟩ := Finset.mem_powersetCard.1 hU₀P
  set Bad := S.filter (fun v => y ≤ ((nonNbrs E S v) ∩ U₀).card) with hBaddef
  have hUcard : (U₀ \ Bad).card + (U₀ ∩ Bad).card = t := by
    rw [Finset.card_sdiff_add_card_inter, hU₀t]
  have hinterle : ((U₀ ∩ Bad).card : ℝ) ≤ 4 * (1 - ε) ^ k * (t : ℝ) := by
    rw [Finset.inter_comm]; exact hbad2
  have hUeq : ((U₀ \ Bad).card : ℝ) = (t : ℝ) - ((U₀ ∩ Bad).card : ℝ) := by
    have h : ((U₀ \ Bad).card : ℝ) + ((U₀ ∩ Bad).card : ℝ) = (t : ℝ) := by exact_mod_cast hUcard
    linarith
  have hUlb : (1 - ε / 16) * (t : ℝ) ≤ ((U₀ \ Bad).card : ℝ) := by
    rw [hUeq]; exact bc_Ulb htnn hσle hinterle
  have hUn₂R : (n₂ : ℝ) ≤ ((U₀ \ Bad).card : ℝ) := by
    refine bc_half hε' (Nat.cast_nonneg _) ?_
    rw [← htR]; exact hUlb
  have hUn₂ : n₂ ≤ (U₀ \ Bad).card := by exact_mod_cast hUn₂R
  have hUC : (U₀ \ Bad).card ≤ C := by omega
  refine ⟨U₀ \ Bad, Bad, (Finset.sdiff_subset).trans hU₀S, Finset.filter_subset _ _,
    Finset.sdiff_disjoint, hUn₂, hUC, ?_, ?_⟩
  · -- the exceptional set is small
    have h3R : ((4 * K * K * Bad.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      calc (4 : ℝ) * (K : ℝ) * (K : ℝ) * (Bad.card : ℝ)
          ≤ 4 * (K : ℝ) * (K : ℝ) * (4 * (1 - ε) ^ k * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hbad1 (by positivity)
        _ = ((16 * (K : ℝ) * (K : ℝ)) * ((1 - ε) ^ k)) * (n : ℝ) := by ring
        _ ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_right hσK hnnn
        _ ≤ (n : ℝ) := bc_eps_le hε' hnnn
    exact_mod_cast h3R
  · -- the surviving vertices are dense into the bottom set
    intro v hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.1 hv
    have hnotbad : ((nonNbrs E S v) ∩ U₀).card < y := by
      by_contra hcon
      exact hvB (Finset.mem_filter.2 ⟨hvS, by omega⟩)
    have hUS : U₀ \ Bad ⊆ S := (Finset.sdiff_subset).trans hU₀S
    rw [resLink_eq_sdiff_nonNbrs hUS v]
    have hsplit : ((U₀ \ Bad) \ nonNbrs E S v).card + ((U₀ \ Bad) ∩ nonNbrs E S v).card
        = (U₀ \ Bad).card := Finset.card_sdiff_add_card_inter _ _
    have hle : ((U₀ \ Bad) ∩ nonNbrs E S v).card ≤ y - 1 := by
      have hmono : ((U₀ \ Bad) ∩ nonNbrs E S v).card ≤ ((nonNbrs E S v) ∩ U₀).card := by
        refine Finset.card_le_card fun a ha => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha
        exact Finset.mem_inter.2 ⟨h2, (Finset.mem_sdiff.1 h1).1⟩
      omega
    have hcR : ((U₀ \ Bad).card : ℝ) - ((y : ℝ) - 1)
        ≤ (((U₀ \ Bad) \ nonNbrs E S v).card : ℝ) := by
      have hcast : (((U₀ \ Bad) ∩ nonNbrs E S v).card : ℝ) ≤ (y : ℝ) - 1 := by
        have h := (Nat.cast_le (α := ℝ)).2 hle
        rwa [Nat.cast_sub (by omega : (1 : ℕ) ≤ y), Nat.cast_one] at h
      have hs : (((U₀ \ Bad) \ nonNbrs E S v).card : ℝ)
          + (((U₀ \ Bad) ∩ nonNbrs E S v).card : ℝ) = ((U₀ \ Bad).card : ℝ) := by
        exact_mod_cast hsplit
      linarith
    exact bc_final (hf ((U₀ \ Bad).card) hUn₂ hUC) (Nat.cast_nonneg _)
      (bc_dens hε.le hε' htnn hy_ub hUlb) hcR

/-- **The twice-repaired bottom-set clause is a theorem.**  The form in which the schedule is at
the bottom of its window at *every* scale; only the scales up to the window `C` are used
(`BKLO.vortexBottomClauseR2_of_schedule_window`). -/
theorem vortexBottomClauseR2_of_schedule {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100)
    {f : ℕ → ℝ} {n₂ C K k : ℕ} (hK : 2 ≤ K) (hk1 : 1 ≤ k)
    (hf : ∀ s : ℕ, n₂ ≤ s → f s ≤ 9 / 10 + ε / 2)
    (hkσ : (1 - ε) ^ k ≤ ε / (16 * (K : ℝ) * (K : ℝ)))
    (hkn₂ : (1000 : ℝ) * k ≤ ε * n₂) (hC : 2 * n₂ ≤ C) :
    VortexBottomClauseR2 ε f n₂ C K :=
  vortexBottomClauseR2_of_schedule_window hε hε' hK hk1 (fun s hs _ => hf s hs) hkσ hkn₂ hC

end BKLO
