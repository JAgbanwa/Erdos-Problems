/-
# The two §10 inputs are not vacuous.

`BKLO/InputsVortex.lean` states the two §10 inputs `VortexScheduleExists` and `CoverDownK3`.  Both
are true theorems of BKLO (see the discussion there and in `RESIDUAL.md`), but neither is proved in
this project, so it matters to check formally that neither is *vacuously* true: that the
configurations they quantify over really occur, so that each input makes a genuine demand and the
main theorem is not being derived from an unsatisfiable hypothesis.

This file proves exactly that.  The witnesses are complete graphs: for `|W| ≡ 3 (mod 6)` the edge
set `cliqueEdges W` is triangle-divisible (every degree `|W| - 1` is even and the number of edges
`|W|(|W|-1)/2` is a multiple of three) and has minimum degree `|W| - 1 ≥ c|W|` for every `c < 1`
once `|W|` is large.  Nested subsets of the prescribed relative sizes are then chosen inside `W`.

Everything here is `sorry`-free.
-/
import BKLO.VortexEngine

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The complete edge set on a finite vertex set -/

theorem sym2_filter_isDiag (W : Finset V) :
    (W.sym2).filter (fun e => e.IsDiag) = W.image (fun a => s(a, a)) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_image,
      Sym2.isDiag_iff_proj_eq, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, by tauto⟩
    · rintro ⟨x, hx, h⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨⟨hx, hx⟩, rfl⟩

/-- The complete edge set on `W` has `|W| choose 2` edges. -/
theorem card_cliqueEdges (W : Finset V) : (cliqueEdges W).card = W.card.choose 2 := by
  classical
  have h1 : (W.sym2).card = (W.card + 1).choose 2 := Finset.card_sym2 W
  have h2 : ((W.sym2).filter (fun e => e.IsDiag)).card = W.card := by
    rw [sym2_filter_isDiag, Finset.card_image_of_injective _ (fun a b h => by
      simpa using (Sym2.eq_iff.1 h).elim (fun h => h.1) (fun h => h.1))]
  have h3 := Finset.card_filter_add_card_filter_not (s := W.sym2) (p := fun e => e.IsDiag)
  have h4 : (cliqueEdges W).card = (W.sym2).card - W.card := by
    unfold cliqueEdges; omega
  have h5 : (W.card + 1).choose 2 = W.card + W.card.choose 2 := by
    rw [Nat.choose_succ_succ W.card 1, Nat.choose_one_right]
  omega

/-- In the complete edge set on `W`, every vertex of `W` has degree `|W| - 1`. -/
theorem edeg_cliqueEdges_of_mem {W : Finset V} {v : V} (hv : v ∈ W) :
    edeg (cliqueEdges W) v = W.card - 1 := by
  classical
  have hfil : (cliqueEdges W).filter (fun e => v ∈ e) = (W.erase v).image (fun u => s(v, u)) := by
    ext e
    induction e using Sym2.ind with
    | _ p q =>
      simp only [Finset.mem_filter, mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq,
        Finset.mem_image, Finset.mem_erase, Sym2.eq_iff]
      constructor
      · rintro ⟨⟨hmem, hne⟩, hvpq⟩
        rcases hvpq with rfl | rfl
        · exact ⟨q, ⟨fun h => hne h.symm, hmem q (Or.inr rfl)⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨p, ⟨fun h => hne h, hmem p (Or.inl rfl)⟩, Or.inr ⟨rfl, rfl⟩⟩
      · rintro ⟨u, ⟨hu1, hu2⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
          · rintro z (rfl | rfl)
            exacts [hv, hu2]
          · exact fun h => hu1 h.symm
        · refine ⟨⟨?_, ?_⟩, Or.inr rfl⟩
          · rintro z (rfl | rfl)
            exacts [hu2, hv]
          · exact fun h => hu1 h
  have hinj : Set.InjOn (fun u => s(v, u)) (W.erase v) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  rw [edeg, hfil, Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv]

theorem cliqueEdges_nonempty {W : Finset V} (h : 2 ≤ W.card) : (cliqueEdges W).Nonempty := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
  refine ⟨s(a, b), mem_cliqueEdgesV.2 ⟨fun z hz => ?_, by simpa using hab⟩⟩
  rcases Sym2.mem_iff.1 hz with rfl | rfl
  exacts [ha, hb]

/-- The complete edge set on a vertex set of size `≡ 3 (mod 6)` is triangle-divisible. -/
theorem triDivisible_cliqueEdges_univ {N : ℕ} (t : ℕ) (hN : N = 6 * t + 3) :
    TriDivisible (cliqueEdges (Finset.univ : Finset (Fin N))) := by
  classical
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  constructor
  · intro v
    show Even (edeg (cliqueEdges (Finset.univ : Finset (Fin N))) v)
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard]
    exact ⟨(N - 1) / 2, by omega⟩
  · rw [card_cliqueEdges, hcard]
    have hc2 : N.choose 2 = 3 * ((2 * t + 1) * (3 * t + 1)) := by
      rw [Nat.choose_two_right]
      have h : N * (N - 1) = 6 * ((2 * t + 1) * (3 * t + 1)) := by
        have h1 : N - 1 = 6 * t + 2 := by omega
        rw [h1, hN]; ring
      rw [h]
      omega
    exact ⟨(2 * t + 1) * (3 * t + 1), hc2⟩

/-! ### Non-vacuity of the hypotheses of `CoverDownK3` -/

/-- **The hypotheses of `CoverDownK3` are satisfiable**, for every ambient density `c < 1`, every
size ratio `K ≥ 2` and every size threshold `n₀` the input might supply, and with all of `W''`, `F`
and `F ∩ cliqueEdges W''` nonempty — so the conclusion of the input is a genuine demand at each of
its clauses. -/
theorem coverDownK3_hypotheses_realizable {c : ℝ} (hc : c < 1) {K : ℕ} (hK : 2 ≤ K) (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧ (F ∩ cliqueEdges W'').Nonempty := by
  classical
  -- choose the size `N = 6t + 3`, large enough both for the minimum-degree condition and for the
  -- two nested levels `W' = N/K`, `W'' = N/K²` to be nonempty
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - c))
  set t : ℕ := max (max k (n₀ + 3)) (4 * K * K) with ht
  set N : ℕ := 6 * t + 3 with hN
  have hKpos : 0 < K := by omega
  have htK : 4 * K * K ≤ t := le_max_right _ _
  have hNt : (k : ℝ) ≤ (N : ℝ) := by
    have hkt : k ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
    have : k ≤ N := by simp only [hN]; omega
    exact_mod_cast this
  have hKKN : K * K * 1 < N := by
    simp only [hN]
    linarith only [htK]
  obtain ⟨-, -, -, hKm, hmm⟩ := vortex_next_level_sizes hK (le_refl 1) hKKN
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (n := N / K)
      (by rw [hcard]; exact Nat.div_le_self _ _)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := (N / K) / K)
      (by rw [hW'card]; exact Nat.div_le_self _ _)
  have hW''le : K * ((N / K) / K) ≤ N / K := Nat.le.intro (Nat.div_add_mod (N / K) K)
  have hW''pos : 2 ≤ (N / K) / K := by
    rw [Nat.le_div_iff_mul_le hKpos, Nat.le_div_iff_mul_le hKpos]
    simp only [hN]
    linarith only [htK]
  refine ⟨N, Finset.univ, W', W'', cliqueEdges (Finset.univ : Finset (Fin N)), ?_, ?_, ?_, ?_, ?_,
    ?_, Finset.Subset.refl _, triDivisible_cliqueEdges_univ (t := t) rfl, ?_, ?_⟩
  · rw [hcard]
    have : n₀ + 3 ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
    simp only [hN]; omega
  · exact hW'sub
  · exact hW''sub
  · rw [hcard, hW'card]; exact hKm
  · rw [hcard, hW'card]; exact hmm
  · rw [hW'card, hW''card]; exact hW''le
  · intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard]
    have h1 : (0 : ℝ) < 1 - c := by linarith only [hc]
    have h2 : (1 : ℝ) ≤ (1 - c) * (N : ℝ) := by
      have : 1 / (1 - c) ≤ (N : ℝ) := le_trans hk.le hNt
      rw [div_le_iff₀ h1] at this
      linarith only [this]
    have h3 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have : 1 ≤ N := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [h3]
    linarith only [h2]
  · have : cliqueEdges (Finset.univ : Finset (Fin N)) ∩ cliqueEdges W'' = cliqueEdges W'' :=
      Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
    rw [this]
    exact cliqueEdges_nonempty (by omega)


/-! ### Non-vacuity of the hypotheses of `VortexScheduleExists` -/

/-- **The hypotheses of the good-bottom clause of `VortexScheduleExists` are satisfiable**: there
are arbitrarily large edge sets of minimum degree at least `(9/10 + ε)|S|`. -/
theorem vortexSchedule_bottom_hypotheses_realizable {ε : ℝ} (hε' : ε < 1 / 10) (n₂ : ℕ) :
    ∃ (N : ℕ) (S : Finset (Fin N)) (E : Finset (Sym2 (Fin N))),
      n₂ ≤ S.card ∧ E ⊆ cliqueEdges S ∧
      (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 / 10 - ε))
  set N : ℕ := max (max n₂ k) 1 with hN
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  refine ⟨N, Finset.univ, cliqueEdges (Finset.univ : Finset (Fin N)), by rw [hcard]; omega,
    Finset.Subset.refl _, ?_⟩
  intro v _
  rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard]
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    have : k ≤ N := by simp only [hN]; omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < 1 / 10 - ε := by linarith only [hε']
  have hbig : (1 : ℝ) ≤ (1 / 10 - ε) * (N : ℝ) := by
    have h := le_trans hk.le hkN
    rw [div_le_iff₀ hpos] at h
    linarith only [h]
  have h3 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have : 1 ≤ N := by simp only [hN]; omega
    push_cast [Nat.cast_sub this]
    ring
  rw [h3]
  linarith only [hbig]

/-- **The hypotheses of the descent clause of `VortexScheduleExists` are satisfiable.**  Whatever
schedule `f`, bottom threshold `n₂` and bound `C` the input supplies, there are arbitrarily large
configurations `U ⊆ W` and edge sets `E` meeting every hypothesis of the descent clause — so that
clause, too, is a genuine demand. -/
theorem vortexSchedule_descent_hypotheses_realizable (hSched : VortexScheduleExists)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (n₀ : ℕ) :
    ∃ (f : ℕ → ℝ) (n₂ C : ℕ), n₀ ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
      ∃ (N m : ℕ) (W U : Finset (Fin N)) (E : Finset (Sym2 (Fin N))),
        n₂ ≤ U.card ∧ U ⊆ W ∧ U.card < m ∧ 2 * m ≤ W.card ∧ E ⊆ cliqueEdges W ∧
        (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) := by
  classical
  obtain ⟨f, n₂, C, hn₀n₂, hn₂C, hn₂pos, hfbd, -, -⟩ := hSched ε hε n₀
  refine ⟨f, n₂, C, hn₀n₂, hn₂C, hn₂pos, hfbd, ?_⟩
  -- a complete graph on `N` vertices, `N` large, with a bottom set of size `n₂`
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 / 10 - ε))
  set N : ℕ := max (max (5 * n₂ + 5) k) 1 with hN
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  obtain ⟨U, hUsub, hUcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (n := n₂)
      (by rw [hcard]; simp only [hN]; omega)
  refine ⟨N, 2 * n₂, Finset.univ, U, cliqueEdges (Finset.univ : Finset (Fin N)), by omega, hUsub,
    by omega, ?_, Finset.Subset.refl _, ?_⟩
  · rw [hcard]; simp only [hN]; omega
  · intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard]
    have hN₂ : n₂ ≤ N := by simp only [hN]; omega
    have hfN := (hfbd N hN₂).2
    have hkN : (k : ℝ) ≤ (N : ℝ) := by
      have : k ≤ N := by simp only [hN]; omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < 1 / 10 - ε := by linarith only [hε']
    have hbig : (1 : ℝ) ≤ (1 / 10 - ε) * (N : ℝ) := by
      have h := le_trans hk.le hkN
      rw [div_le_iff₀ hpos] at h
      linarith only [h]
    have h3 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have : 1 ≤ N := by simp only [hN]; omega
      push_cast [Nat.cast_sub this]
      ring
    rw [h3]
    -- `f N ≤ 9/10 + ε` and `N ≥ 1/(1/10 - ε)` give `f N · N ≤ N - 1`
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith only [hfN, hbig, hε, hN0]

end BKLO
