import E18.NibbleSchedule

/-!
# E18 — the one-round oracle and the regular nibble with explicit constants

Adapted copies of `Nibble.roundOracleExistsCeil_holds` and
`Nibble.nibbleTheoremMostCeil_holds` in which the witnesses `μ, η, d₀, c` are the
explicit definitions `muT, excT, d0T, cT` (for `0 < β < 1`), respectively
`muN, etaN, d0N` for every `β > 0` (via `β ↦ min β (1/2)`).
-/

open Finset Hypergraph

namespace E18.Nib

/-- The degree threshold of the sharp round, `256 r / (α² γ) + 96/ε + 4` with `α = β/2`. -/
noncomputable def D0T (r : ℕ) (β : ℝ) : ℝ :=
  256 * r / ((β / 2) ^ 2 * gamT r β) + 96 / epsT r β + 4
/-- The codegree constant of the sharp round, `θ ε² γ α² / (16384 r)` with `θ = exc`, `α = β/2`. -/
noncomputable def c0T (r : ℕ) (β : ℝ) : ℝ :=
  excT r β * epsT r β ^ 2 * gamT r β * (β / 2) ^ 2 / (16384 * r)
/-- The near-regularity / codegree tolerance `μ`. -/
noncomputable def muT (r : ℕ) (β : ℝ) : ℝ :=
  min (8 * gamT r β) (min (c0T r β * lominT r β) (min (1 / (2 * (D0T r β + 1))) (1 / 2)))
/-- The degree threshold `d₀ = max 1 (D₀ / lomin)`. -/
noncomputable def d0T (r : ℕ) (β : ℝ) : ℝ := max 1 (D0T r β / lominT r β)
/-- The per-round covering fraction `c = γ/(16 r)`. -/
noncomputable def cT (r : ℕ) (β : ℝ) : ℝ := gamT r β / (16 * r)

set_option maxHeartbeats 1000000 in
/-- **Explicit one-round covering oracle** (adapted copy of
`Nibble.roundOracleExistsCeil_holds`, case `β < 1`). -/
theorem roundOracle_explicit (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < muT r β ∧ 0 < excT r β ∧ 0 < d0T r β ∧ 0 < cT r β ∧ cT r β ≤ 1 ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d →
        d0T r β ≤ d →
        IsUniform H r → NearlyRegularMost H d (muT r β) (excT r β) →
        CodegreeBounded H (muT r β * d) →
        (∀ x : V, (degree H x : ℝ) ≤ (1 + muT r β) * d) →
        Nibble.HasRoundOracle H (cT r β) β := by
  classical
  obtain ⟨Pm, hPgam, hPeps, hPexc, hPeta, hPwid, hPlomin, -⟩ :=
    exists_tightParams_explicit r hr hβ hβ1
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set D₀ : ℝ := 256 * r / ((β / 2) ^ 2 * Pm.gam) + 96 / Pm.eps + 4 with hD₀def
  set c₀ : ℝ := Pm.exc * Pm.eps ^ 2 * Pm.gam * (β / 2) ^ 2 / (16384 * r) with hc₀def
  have hD₀ : 0 < D₀ := by
    have := Pm.gam_pos; have := Pm.eps_pos; positivity
  have hc₀ : 0 < c₀ := by
    have := Pm.gam_pos; have := Pm.eps_pos; have := Pm.exc_pos
    have : (0 : ℝ) < r := by linarith
    positivity
  have hround : Nibble.SharpRoundFor r Pm.gam Pm.eps Pm.exc (β / 2) D₀ c₀ :=
    Nibble.sharpRoundFor_of_two_gamma_le_eps r hr Pm.gam Pm.eps Pm.exc (β / 2)
    Pm.gam_pos Pm.gam_le Pm.eps_le Pm.two_gam_le_eps Pm.exc_pos Pm.exc_le (by linarith)
    (by linarith)
  have hD0eq : D0T r β = D₀ := by rw [hD₀def, D0T, hPgam, hPeps]
  have hc0eq : c0T r β = c₀ := by rw [hc₀def, c0T, hPgam, hPeps, hPexc]
  obtain ⟨mu, hmudef⟩ : ∃ m : ℝ,
      m = min Pm.wid (min (c₀ * Pm.lomin) (min (1 / (2 * (D₀ + 1))) (1 / 2))) := ⟨_, rfl⟩
  have hmueq : muT r β = mu := by rw [hmudef, muT, hPwid, hPlomin, hD0eq, hc0eq]
  have hd0eq : d0T r β = max 1 (D₀ / Pm.lomin) := by rw [d0T, hD0eq, hPlomin]
  have hceq : cT r β = Pm.gam / (16 * r) := by rw [cT, hPgam]
  rw [hmueq, hd0eq, hceq, ← hPexc]
  have hetaexc : Pm.eta = Pm.exc := hPeta.trans hPexc.symm
  have hD1 : (0 : ℝ) < 2 * (D₀ + 1) := by linarith
  have hmupos : 0 < mu := by
    rw [hmudef]
    exact lt_min Pm.wid_pos (lt_min (mul_pos hc₀ Pm.lomin_pos)
      (lt_min (div_pos one_pos hD1) (by norm_num)))
  have hmu_c0 : mu ≤ c₀ * Pm.lomin := by
    rw [hmudef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmu_D : mu ≤ 1 / (2 * (D₀ + 1)) := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmu_half : mu ≤ 1 / 2 := by
    rw [hmudef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hmu_wid : mu ≤ Pm.wid := by rw [hmudef]; exact min_le_left _ _
  have hcpos : (0 : ℝ) < Pm.gam / (16 * r) := div_pos Pm.gam_pos (by linarith)
  have hcle : Pm.gam / (16 * r) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [Pm.gam_le]
  refine ⟨hmupos, Pm.exc_pos, lt_of_lt_of_le one_pos (le_max_left _ _), hcpos, hcle, ?_⟩
  intro V _ _ H d hd hd0 huni hreg hcodeg hceil
  rw [← hetaexc] at hreg
  have hd1 : (1 : ℝ) ≤ d := le_trans (le_max_left _ _) hd0
  have hDlo : D₀ ≤ d * Pm.lomin := by
    have h := le_trans (le_max_right (1 : ℝ) (D₀ / Pm.lomin)) hd0
    rw [div_le_iff₀ Pm.lomin_pos] at h
    exact h
  have hcodsmall : mu * d ≤ c₀ * (d * Pm.lomin) := by
    linarith only [mul_le_mul_of_nonneg_right hmu_c0 (show (0 : ℝ) ≤ d by linarith only [hd1])]
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
    have hcg := Nibble.card_ge_of_codegree huni hr1 hcodeg v
    have hdegnn : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
    by_contra hcon
    push_neg at hcon
    have hmu_D' : mu * (2 * (D₀ + 1)) ≤ 1 := by
      rw [le_div_iff₀ hD1] at hmu_D
      linarith
    have hstep1 : d / 2 ≤ (degree H v : ℝ) := by nlinarith
    have hr1R : (1 : ℝ) ≤ (r : ℝ) - 1 := by linarith
    have hstep2 : (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := by
      linarith only [mul_le_mul_of_nonneg_right hr1R hdegnn]
    have hstep3 : d / 2 ≤ ((Fintype.card V : ℝ) - 1) * (mu * d) := by linarith
    have hstep4 : (1 : ℝ) / 2 ≤ ((Fintype.card V : ℝ) - 1) * mu := by
      have hmul : d * (1 / 2) ≤ d * (((Fintype.card V : ℝ) - 1) * mu) := by
        linarith only [hstep3]
      exact le_of_mul_le_mul_left hmul hd
    nlinarith only [hstep4, hmu_D', hcon, hmupos,
      mul_pos hmupos (show (0 : ℝ) < D₀ - (Fintype.card V : ℝ) by linarith)]
  refine Nibble.hasRoundOracle_of_scheduled_invariant H hcpos.le hcle Pm.T Pm.decay
    (fun j H' S => (∀ e ∈ H', Disjoint e S) ∧
      ∃ (K : Finset (Finset V)) (E : Finset V), K ⊆ H' ∧ IsUniform K r ∧
        (∀ e ∈ K, Disjoint e S) ∧
        (∀ v : V, (degree K v : ℝ) ≤ d * Pm.hi j) ∧
        (∀ v : V, v ∉ S → v ∉ E → d * Pm.lo j ≤ (degree K v : ℝ)) ∧
        (∀ x y : V, x ≠ y → (codegree K x y : ℝ) ≤ mu * d) ∧
        (E.card : ℝ) ≤ Pm.sig j * (Fintype.card V : ℝ))
    ?_ (fun j H' S hP => hP.1) ?_
  · obtain ⟨Exc, hExc, hExcdeg⟩ := hreg
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
  · rintro j hj H' S ⟨hH'disj, K, E, hKH', huniK, hKdisj, hhi, hlo, hcodK, hE⟩ hlt
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) := by nlinarith
    obtain ⟨R', hR'K, hcov, K', E', hK'res, huniK', hK'disj, hhi', hlo', hcodK', hE'⟩ :=
      Nibble.tight_round_step hr Pm hc₀.le hround hd (mul_nonneg hmupos.le hd.le) hDlo hcodsmall
        (hNbig hNpos) hj huniK hKdisj hhi hlo hcodK hE hlt
    refine ⟨R', Finset.Subset.trans hR'K hKH', ⟨?_, K', E', ?_, huniK', hK'disj, hhi', hlo',
      hcodK', hE'⟩, hcov⟩
    · intro e he
      rw [Finset.disjoint_union_right]
      exact ⟨hH'disj e (Hypergraph.residual_subset H' R' he),
        Hypergraph.residual_disjoint_covered he⟩
    · exact Finset.Subset.trans hK'res (Finset.filter_subset_filter _ hKH')

/-! ## The regular nibble (`NibbleTheoremMostCeil`) with explicit constants -/

/-- The conclusion of `Nibble.NibbleTheoremMostCeil` at fixed constants `μ, η, d₀`. -/
def MostCeilAt (r : ℕ) (β μ η d₀ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), 0 < d → d₀ ≤ d →
    IsUniform H r → NearlyRegularMost H d μ η → CodegreeBounded H (μ * d) →
    (∀ x : V, (degree H x : ℝ) ≤ (1 + μ) * d) →
    ∃ M : Finset (Finset V), IsMatching H M ∧
      (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ)

/-- The normalised target `min β (1/2)`. -/
noncomputable def betaN (β : ℝ) : ℝ := min β (1 / 2)
/-- Explicit `μ` of the regular nibble, for every `β > 0`. -/
noncomputable def muN (r : ℕ) (β : ℝ) : ℝ := muT r (betaN β)
/-- Explicit `η` of the regular nibble, for every `β > 0`. -/
noncomputable def etaN (r : ℕ) (β : ℝ) : ℝ := excT r (betaN β)
/-- Explicit `d₀` of the regular nibble, for every `β > 0`. -/
noncomputable def d0N (r : ℕ) (β : ℝ) : ℝ := d0T r (betaN β)

/-- **`NibbleTheoremMostCeil` with explicit constants.** -/
theorem mostCeil_explicit (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    0 < muN r β ∧ 0 < etaN r β ∧ 0 < d0N r β ∧ MostCeilAt r β (muN r β) (etaN r β) (d0N r β) := by
  have hb0 : 0 < betaN β := lt_min hβ (by norm_num)
  have hb1 : betaN β < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hbβ : betaN β ≤ β := min_le_left _ _
  obtain ⟨hmu, hexc, hd0, hc0, hc1, hO⟩ := roundOracle_explicit r hr (betaN β) hb0 hb1
  refine ⟨hmu, hexc, hd0, ?_⟩
  intro V _ _ H d hd hd0' huni hreg hcodeg hceil
  obtain ⟨R, lam, T, hR, hlam0, hTβ, horacle⟩ :=
    Nibble.exists_adaptive_strategy_of_roundOracle H hc0 hc1 hb0
      (hO H d hd hd0' huni hreg hcodeg hceil)
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  obtain ⟨M, hM, hcard⟩ := Hypergraph.exists_matching_of_oracle_seq_lt hR huni hr1 hlam0 T hTβ horacle
  refine ⟨M, hM, le_trans ?_ hcard⟩
  have hX : (0 : ℝ) ≤ (Fintype.card V : ℝ) / r := by positivity
  nlinarith

end E18.Nib
