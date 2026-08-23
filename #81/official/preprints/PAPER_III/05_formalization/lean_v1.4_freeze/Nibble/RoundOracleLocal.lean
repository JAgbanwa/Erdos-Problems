/-
# Nibble — LOCAL peel of the single-round oracle atom (parallel track)

This file runs the local half of the "ambos en paralelo" strategy for the corrected nibble atom
`roundOracleExistsCeil_holds` (see `Nibble.AdaptiveAssembly`).  It does NOT touch Aristotle's version
of `AdaptiveAssembly`; instead it isolates the SOLE genuinely-open ingredient into one named residual
`RoundStepSchedule`, and proves — sorry-free — that this residual already yields
`RoundOracleExistsCeil` through the proved constructor `hasRoundOracle_of_scheduled_invariant`.

The point of the peel: the invariant *plumbing* (`hP0`, `hdisj`) is discharged here structurally by
BAKING the standing disjointness clause into the round-indexed invariant `P`, so that what remains
in `RoundStepSchedule` is exactly the per-round STEP: from a round-`j` admissible residual with more
than a `β`-fraction uncovered, produce a retained `R'` that (i) re-establishes the round-`(j+1)`
invariant and (ii) covers a `c`-fraction of the still-uncovered set.  This is the parameter-schedule
core (degradation of `μ_j, η_j, d_j`, the codegree and the exceptional set over `T` rounds with
`(1-c)^T ≤ β`), fed by `Nibble.AdaptiveSchedule.adaptive_crux_satisfiable` and the Freedman retention
bricks (`exists_good_retention_freedman`).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Superseded (2026-08-06).**  The tight-band track now proves the very conclusion this residual was
introduced to reach: `Nibble.roundOracleExistsCeil_of_sharpRound` (`Nibble.TightNibble`) derives
`RoundOracleExistsCeil` — sorry-free and axiom-clean — from the single one-round hypothesis
`Nibble.SharpRoundHyp` (`Nibble.Tight.SharpRound`), by iterating `Nibble.tight_round_step` along the
schedule `Nibble.exists_tightParams`.  The invariant `P` it feeds to
`hasRoundOracle_of_scheduled_invariant` is exactly the one `RoundStepSchedule` asks for.  Accordingly
`roundStepSchedule_holds` below is now PROVED by that same tight-band construction (returning the
invariant instead of the assembled oracle), so this file too is sorry-free; nothing in the tight-band
chain depends on it.
-/
import Nibble.AdaptiveAssembly
import Nibble.AdaptiveRounds
import Nibble.AdaptiveSchedule
import Nibble.GoodRetentionFinset
import Nibble.RegularMost
import Nibble.TightSchedule
import Nibble.Tight.SharpRoundAssembly

open Hypergraph Finset

namespace Nibble

/-- **The isolated per-round schedule residual.**  For uniformity `r` and target `β`, there are
richness/threshold parameters `μ, η, d₀ > 0`, a per-round covering fraction `c ∈ (0,1]` and a round
count `T` with `(1-c)^T ≤ β`, such that every admissible input (majority near-regular, low codegree,
GLOBAL degree ceiling) carries a round-indexed invariant `P` with:

* `P 0 H ∅` (base),
* `P` bakes in the standing disjointness `∀ e ∈ H', Disjoint e S` (so the oracle's `hdisj` is free),
* the per-round STEP: while more than a `β`-fraction is uncovered, one retained round re-establishes
  `P` at `j+1` and covers a `c`-fraction of the uncovered set.

This is `RoundOracleExistsCeil` with the oracle construction (`hasRoundOracle_of_scheduled_invariant`)
factored OUT — the remaining content is purely the parameter schedule. -/
def RoundStepSchedule : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ T : ℕ, (1 - c) ^ T ≤ β ∧
        ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
          IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
          (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
          ∃ P : ℕ → Finset (Finset V) → Finset V → Prop,
            P 0 H ∅ ∧
            (∀ (j : ℕ) (H' : Finset (Finset V)) (S : Finset V), P j H' S →
              ∀ e ∈ H', Disjoint e S) ∧
            (∀ j, j < T → ∀ (H' : Finset (Finset V)) (S : Finset V), P j H' S →
              β * (Fintype.card V : ℝ) < (Fintype.card V : ℝ) - (S.card : ℝ) →
              ∃ R' : Finset (Finset V), R' ⊆ H' ∧
                P (j + 1) (Hypergraph.residual H' R') (S ∪ support (roundMatching R')) ∧
                c * ((Fintype.card V : ℝ) - (S.card : ℝ))
                  ≤ ((support (roundMatching R')).card : ℝ))

/-- **The peel is sorry-free: the schedule residual already implies the one-round oracle atom.**
Every quantifier of `RoundOracleExistsCeil` is matched by `RoundStepSchedule`, and the oracle itself
is produced by the proved `hasRoundOracle_of_scheduled_invariant`.  Hence discharging
`RoundStepSchedule` discharges `roundOracleExistsCeil_holds` (and thereby the whole ceiling route). -/
theorem roundOracleExistsCeil_of_roundStepSchedule (h : RoundStepSchedule) :
    RoundOracleExistsCeil := by
  intro r hr β hβ
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, c, hc0, hc1, T, hT, hsched⟩ := h r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, c, hc0, hc1, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  obtain ⟨P, hP0, hdisj, hstep⟩ := hsched H d hd hd0 huni hreg hcodeg hceil
  exact hasRoundOracle_of_scheduled_invariant H hc0.le hc1 T hT P hP0 hdisj hstep

set_option maxHeartbeats 1000000 in
/-- **The schedule residual, discharged.**  This is the parallel-track counterpart of
`Nibble.roundOracleExistsCeil_holds`: the tight-band schedule `Nibble.TightParams r β`
(`Nibble.exists_tightParams`) run through the single round `Nibble.tight_round_step`, packaged as the
round-indexed invariant `P` instead of the assembled oracle.  The sharp round is supplied by
`Nibble.sharpRoundHyp_of_two_gamma_le_eps`, so nothing is assumed. -/
theorem roundStepSchedule_holds : RoundStepSchedule := by
  classical
  intro r hr β hβ
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1` is vacuous: more than a `β`-fraction can never be uncovered
    refine ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, le_rfl, 1, by simpa using hβ.le, ?_⟩
    intro V _ _ H d _ _ _ _ _ _
    refine ⟨fun _ H' S => ∀ e ∈ H', Disjoint e S,
      fun e _ => Finset.disjoint_empty_right e, fun _ _ _ hP => hP, ?_⟩
    intro j _ H' S _ hlt
    exfalso
    have hS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    nlinarith
  obtain ⟨Pm⟩ := exists_tightParams r hr hβ hβ1
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨D₀, hD₀, c₀, hc₀, hround⟩ :=
    sharpRoundHyp_of_two_gamma_le_eps r hr Pm.gam Pm.eps Pm.exc (β / 2) Pm.gam_pos Pm.gam_le
      Pm.eps_le Pm.two_gam_le_eps Pm.exc_pos Pm.exc_le (by linarith) (by linarith)
  -- the parameters of the interface
  obtain ⟨mu, hmudef⟩ : ∃ m : ℝ,
      m = min Pm.wid (min (c₀ * Pm.lomin) (min (1 / (2 * (D₀ + 1))) (1 / 2))) := ⟨_, rfl⟩
  have hD1 : (0 : ℝ) < 2 * (D₀ + 1) := by linarith
  have hmupos : 0 < mu := by
    rw [hmudef]
    exact lt_min Pm.wid_pos (lt_min (mul_pos hc₀ Pm.lomin_pos)
      (lt_min (div_pos one_pos hD1) (by norm_num)))
  have hmu_wid : mu ≤ Pm.wid := by rw [hmudef]; exact min_le_left _ _
  have hmu_c0 : mu ≤ c₀ * Pm.lomin := by
    rw [hmudef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmu_D : mu ≤ 1 / (2 * (D₀ + 1)) := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmu_half : mu ≤ 1 / 2 := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcpos : (0 : ℝ) < Pm.gam / (16 * r) := div_pos Pm.gam_pos (by linarith)
  have hcle : Pm.gam / (16 * r) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [Pm.gam_le]
  refine ⟨mu, hmupos, Pm.eta, Pm.eta_pos, max 1 (D₀ / Pm.lomin),
    lt_of_lt_of_le one_pos (le_max_left _ _), Pm.gam / (16 * r), hcpos, hcle, Pm.T, Pm.decay, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_max_left _ _) hd0
  have hDlo : D₀ ≤ d * Pm.lomin := by
    have h := le_trans (le_max_right (1 : ℝ) (D₀ / Pm.lomin)) hd0
    rw [div_le_iff₀ Pm.lomin_pos] at h
    exact h
  have hcodsmall : mu * d ≤ c₀ * (d * Pm.lomin) := by nlinarith
  -- the vertex count is at least the round's degree threshold
  have hNbig : 0 < (Fintype.card V : ℝ) → D₀ ≤ (Fintype.card V : ℝ) := by
    intro hNpos
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    have hetahalf : Pm.eta ≤ β / 2 := le_trans Pm.sig_init (Pm.sig_le 0 (Nat.zero_le _))
    have hExcnn : (0 : ℝ) ≤ (Exc.card : ℝ) := Nat.cast_nonneg _
    have hExclt : (Exc.card : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Exc := by
      by_contra hcon
      push_neg at hcon
      have : Exc = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [this, Finset.card_univ] at hExclt
      exact absurd hExclt (lt_irrefl _)
    have hdeg := (hExcdeg v hv).1
    have hcg := card_ge_of_codegree huni hr1 hcodeg v
    have hdegnn : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
    by_contra hcon
    push_neg at hcon
    have hmu_D' : mu * (2 * (D₀ + 1)) ≤ 1 := by
      rw [le_div_iff₀ hD1] at hmu_D
      linarith
    have hstep1 : d / 2 ≤ (degree H v : ℝ) := by nlinarith
    have hr1R : (1 : ℝ) ≤ (r : ℝ) - 1 := by linarith
    have hstep2 : (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := by nlinarith
    have hstep3 : d / 2 ≤ ((Fintype.card V : ℝ) - 1) * (mu * d) := by linarith
    have hstep4 : (1 : ℝ) / 2 ≤ ((Fintype.card V : ℝ) - 1) * mu := by
      have hmul : d * (1 / 2) ≤ d * (((Fintype.card V : ℝ) - 1) * mu) := by linarith
      exact le_of_mul_le_mul_left hmul hd
    nlinarith only [hstep4, hmu_D', hcon, hmupos,
      mul_pos hmupos (show (0 : ℝ) < D₀ - (Fintype.card V : ℝ) by linarith)]
  refine ⟨fun j H' S => (∀ e ∈ H', Disjoint e S) ∧
      ∃ (K : Finset (Finset V)) (E : Finset V), K ⊆ H' ∧ IsUniform K r ∧
        (∀ e ∈ K, Disjoint e S) ∧
        (∀ v : V, (degree K v : ℝ) ≤ d * Pm.hi j) ∧
        (∀ v : V, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ)) ∧
        (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ mu * d) ∧
        (E.card : ℝ) ≤ Pm.sig j * (Fintype.card V : ℝ),
    ?_, (fun j H' S hP => hP.1), ?_⟩
  · -- initialisation
    obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
    refine ⟨fun e _ => Finset.disjoint_empty_right e, H, Exc, Finset.Subset.refl _, huni,
      fun e _ => Finset.disjoint_empty_right e, ?_, ?_, hcodeg, ?_⟩
    · intro v
      have h1 : (1 : ℝ) + mu ≤ Pm.hi 0 := by linarith [Pm.init_hi]
      have := hceil v
      nlinarith
    · intro v _ hvE
      have h1 : Pm.lo 0 ≤ 1 - mu := by linarith [Pm.init_lo]
      have := (hExcdeg v hvE).1
      nlinarith
    · have hNnn : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
      exact le_trans hExc (mul_le_mul_of_nonneg_right Pm.sig_init hNnn)
  · -- one round of the schedule
    rintro j hj H' S ⟨hH'disj, K, E, hKH', huniK, hKdisj, hhi, hlo, hcodK, hE⟩ hlt
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨R', hR'K, hcov, K', E', hK'res, huniK', hK'disj, hhi', hlo', hcodK', hE'⟩ :=
      tight_round_step hr Pm hc₀.le hround hd (mul_nonneg hmupos.le hd.le) hDlo hcodsmall
        (hNbig hNpos) hj huniK hKdisj hhi hlo hcodK hE hlt
    refine ⟨R', Finset.Subset.trans hR'K hKH', ⟨?_, K', E', ?_, huniK', hK'disj, hhi', hlo',
      hcodK', hE'⟩, hcov⟩
    · intro e he
      rw [Finset.disjoint_union_right]
      exact ⟨hH'disj e (Hypergraph.residual_subset H' R' he),
        Hypergraph.residual_disjoint_covered he⟩
    · exact Finset.Subset.trans hK'res (Finset.filter_subset_filter _ hKH')

/-- The one-round oracle atom, assembled LOCALLY from the schedule residual (sorry-free modulo
`roundStepSchedule_holds`). -/
theorem roundOracleExistsCeil_holds_local : RoundOracleExistsCeil :=
  roundOracleExistsCeil_of_roundStepSchedule roundStepSchedule_holds

end Nibble
