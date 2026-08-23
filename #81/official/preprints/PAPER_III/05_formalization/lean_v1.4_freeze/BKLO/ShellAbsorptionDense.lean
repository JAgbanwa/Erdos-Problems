/-
# The density-corrected shell absorption and cover-down interfaces.

`BKLO/CoverDownAbsorberConfinement.lean` isolates `BKLO.ShellAbsorption`, and
`BKLO/ShellAbsorptionConfinementWall.lean` shows `sorry`-free that this interface, *as stated*,
carries **hollow** instances: configurations satisfying every one of its hypotheses in which
`F` has no edge at all inside the level `W'` (`BKLO.hollow_instance_realizable`).  In a hollow
instance the confinement allowance `cliqueEdges W' \ cliqueEdges W''` of the conclusion is
unusable, and the interface degenerates into a demand for a reserved decomposition of an
arbitrarily sparse graph (`BKLO.shellAbsorption_forces_sparse_selfdecomposition`).

The omission the wall points at is the **level density** that BKLO's vortex maintains: every level
`W_i` of the vortex induces a graph of large minimum degree, `δ(G[W_i]) ≥ c|W_i|`, and it is the
level's *own* edges that supply the covering edges of the cover-down.  This file adds exactly that
hypothesis, in the weakest form that already excludes the hollow instances:

* `BKLO.ShellAbsorptionDense` — `BKLO.ShellAbsorption` together with
  `∀ v ∈ W', (c - 9/10) * |W'| ≤ edeg (F ∩ cliqueEdges W') v`;
* `BKLO.CoverDownK3DivDense` — `BKLO.CoverDownK3Div` together with the same clause.

The constant `c - 9/10` is positive (the interfaces carry `9/10 < c`) and is *far* less than what
the vortex actually provides: the recursion of `BKLO/CoverDownVortexRecursion.lean` maintains
`(9/10)|W'| ≤ edeg (F ∩ cliqueEdges W') v` at every level (see `BKLO/CoverDownVortexDense.lean`).

What is proved here:

* `BKLO.levelDensity_excludes_hollow`, `BKLO.levelDensity_fails_of_hollow` — the new clause is
  violated by every hollow configuration, so `BKLO.hollow_instance_realizable` is excluded
  outright;
* `BKLO.shellAbsorptionDense_hypotheses_realizable` — the dense hypotheses are nevertheless
  satisfiable at every size and every ratio, so nothing has become vacuous;
* `BKLO.coverDownK3DivDense_of_denseNibble_shellAbsorptionDense` — the absorber-confinement route
  of `BKLO/CoverDownAbsorberConfinement.lean` goes through verbatim for the dense pair: the dense
  max-degree nibble and `ShellAbsorptionDense` give `CoverDownK3DivDense`.

Nothing here asserts `ShellAbsorptionDense` or `CoverDownK3DivDense`.  Everything here is
`sorry`-free.
-/
import BKLO.ShellAbsorptionConfinementWall

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The two density-corrected interfaces -/

/-- **Flexible shell absorption at one vortex step, with a dense level.**

Exactly `BKLO.ShellAbsorption` plus the level-density hypothesis

  `∀ v ∈ W', (c - 9/10) * |W'| ≤ edeg (F ∩ cliqueEdges W') v`,

i.e. the graph `F` induces on the level `W'` a graph of minimum degree at least `(c - 9/10)|W'|`.
This is the hypothesis BKLO's vortex maintains at every level and the one the hollow instances of
`BKLO.hollow_instance_realizable` violate (there `F ∩ cliqueEdges W' = ∅`).  With it, the
confinement allowance `cliqueEdges W' \ cliqueEdges W''` of the conclusion is guaranteed to contain
`Θ(|W'|²)` edges of `F`. -/
def ShellAbsorptionDense : Prop :=
  ∀ (c γ ρ : ℝ) (K : ℕ), 9 / 10 < c → 0 < γ → 0 < ρ → 2 ≤ K →
    ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 V), L ⊆ (F \ cliqueEdges W') \ R →
            (∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) →
            ∃ Q : Finset (Finset V), TriFamilyIn F Q ∧
              R ∪ L ⊆ famEdges Q ∧
              famEdges Q ⊆ (R ∪ L) ∪ (cliqueEdges W' \ cliqueEdges W'') ∧
              ∀ v ∈ W', (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) ≤ γ * (W'.card : ℝ)

/-- **The repaired cover-down step, with a dense level.**  Exactly `BKLO.CoverDownK3Div` plus the
level-density hypothesis of `BKLO.ShellAbsorptionDense`. -/
def CoverDownK3DivDense : Prop :=
  ∀ c γ : ℝ, 9 / 10 < c → 0 < γ → ∃ K n₀ : ℕ, 2 ≤ K ∧
    ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)

/-- The dense interfaces are weakenings: a proof of the plain interface proves the dense one. -/
theorem shellAbsorptionDense_of_shellAbsorption (h : ShellAbsorption) : ShellAbsorptionDense := by
  intro c γ ρ K hc hγ hρ hK
  obtain ⟨η, n₀, hη, habs⟩ := h c γ ρ K hc hγ hρ hK
  exact ⟨η, n₀, hη, fun W W' W'' F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ =>
    habs W W' W'' F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11⟩

/-- The dense cover-down interface is a weakening of the plain one. -/
theorem coverDownK3DivDense_of_coverDownK3Div (h : CoverDownK3Div) : CoverDownK3DivDense := by
  intro c γ hc hγ
  obtain ⟨K, n₀, hK, hCD⟩ := h c γ hc hγ
  exact ⟨K, n₀, hK, fun W W' W'' F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ =>
    hCD W W' W'' F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11⟩

/-! ### The level-density hypothesis excludes the hollow instances -/

/-- **A dense level is not hollow.**  If every vertex of a nonempty `W'` has positive degree inside
`W'` in `F`, then `F` does have edges inside `W'`. -/
theorem levelDensity_excludes_hollow {c' : ℝ} (hc' : 0 < c') {W' : Finset V}
    {F : Finset (Sym2 V)} (hne : W'.Nonempty)
    (hdense : ∀ v ∈ W', c' * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) :
    F ∩ cliqueEdges W' ≠ ∅ := by
  intro hhollow
  obtain ⟨v, hv⟩ := hne
  have h := hdense v hv
  rw [hhollow] at h
  have h0 : edeg (∅ : Finset (Sym2 V)) v = 0 := by simp [edeg]
  rw [h0] at h
  have hpos : (0 : ℝ) < (W'.card : ℝ) := by
    have : 0 < W'.card := Finset.card_pos.2 ⟨v, hv⟩
    exact_mod_cast this
  have := mul_pos hc' hpos
  push_cast at h
  linarith

/-- **Every hollow configuration violates the level-density hypothesis.**  In particular the
configurations of `BKLO.hollow_instance_realizable` — which satisfy all hypotheses of
`BKLO.ShellAbsorption` — are *not* instances of `BKLO.ShellAbsorptionDense`: the ratio bound
`|W| ≤ K²|W'|` with `|W| ≥ 1` makes `W'` nonempty, and a nonempty hollow level has a vertex of
degree `0` inside the level. -/
theorem levelDensity_fails_of_hollow {c' : ℝ} (hc' : 0 < c') {K : ℕ} {W W' : Finset V}
    {F : Finset (Sym2 V)} (hcard : 1 ≤ W.card) (hratio : W.card ≤ K * K * W'.card)
    (hhollow : F ∩ cliqueEdges W' = ∅) :
    ¬ (∀ v ∈ W', c' * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) := by
  intro hdense
  have hpos : 0 < W'.card := by
    rcases Nat.eq_zero_or_pos W'.card with h | h
    · rw [h] at hratio; omega
    · exact h
  exact levelDensity_excludes_hollow hc' (Finset.card_pos.1 hpos) hdense hhollow

/-! ### The dense hypotheses are satisfiable -/

/-- **The hypotheses of the dense interfaces are satisfiable**, for every density `c < 1`, every
ratio `K ≥ 2` and every size threshold `n₀`, with `F ∩ cliqueEdges W''` nonempty.  So adding the
level-density clause has not made the interfaces vacuous: it removes exactly the hollow
configurations. -/
theorem shellAbsorptionDense_hypotheses_realizable {c : ℝ} (hc : c < 1) {K : ℕ} (hK : 2 ≤ K)
    (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      TriDivisible (F ∩ cliqueEdges W') ∧ TriDivisible (F ∩ cliqueEdges W'') ∧
      (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
      (∀ v ∈ W', (c - 9 / 10) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) ∧
      (F ∩ cliqueEdges W'').Nonempty := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - c))
  set a : ℕ := n₀ + K + k + 3 with ha
  set M : ℕ := 6 * a + 3 with hM
  set b : ℕ := (K * M) / 6 + 1 with hb
  set N : ℕ := 6 * b + 3 with hN
  have hM9 : 9 ≤ M := by omega
  have hMK : 3 * K ≤ M := by omega
  have hKM : K * M ≤ N := by
    have h6 : 6 * ((K * M) / 6) + 6 ≥ K * M := by omega
    omega
  have hMN : M ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hKKM : N ≤ K * K * M := by
    have h1 : K * M + K * M ≤ K * (K * M) := by
      have : 2 * (K * M) ≤ K * (K * M) := Nat.mul_le_mul_right _ hK
      omega
    have h2 : 18 ≤ K * M := by
      have : 2 * M ≤ K * M := Nat.mul_le_mul_right _ hK
      omega
    have h3 : K * K * M = K * (K * M) := by ring
    omega
  have hn₀N : n₀ ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hkN : k ≤ N := by
    have : M ≤ K * M := Nat.le_mul_of_pos_left M (by omega)
    omega
  have hcardU : (univ : Finset (Fin N)).card = N := by simp
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (univ : Finset (Fin N))) (n := M)
      (by rw [hcardU]; exact hMN)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := 3) (by rw [hW'card]; omega)
  have hinterW' : cliqueEdges (univ : Finset (Fin N)) ∩ cliqueEdges W' = cliqueEdges W' :=
    Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
  have hinterW'' : cliqueEdges (univ : Finset (Fin N)) ∩ cliqueEdges W'' = cliqueEdges W'' :=
    Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
  refine ⟨N, univ, W', W'', cliqueEdges (univ : Finset (Fin N)), ?_, Finset.subset_univ _,
    hW''sub, ?_, ?_, ?_, Finset.Subset.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcardU]; exact hn₀N
  · rw [hcardU, hW'card]; exact hKM
  · rw [hcardU, hW'card]; exact hKKM
  · rw [hW'card, hW''card]; omega
  · exact triDivisible_cliqueEdges_of_card (t := b) (by rw [hcardU])
  · rw [hinterW']; exact triDivisible_cliqueEdges_of_card (t := a) hW'card
  · rw [hinterW'']; exact triDivisible_cliqueEdges_of_card (t := 0) (by rw [hW''card])
  · intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcardU]
    have h1 : (0 : ℝ) < 1 - c := by linarith
    have hNr : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    have h2 : (1 : ℝ) ≤ (1 - c) * (N : ℝ) := by
      have h3 : 1 / (1 - c) ≤ (N : ℝ) := le_trans hk.le hNr
      rw [div_le_iff₀ h1] at h3
      linarith
    have h4 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have h5 : 1 ≤ N := by omega
      push_cast [Nat.cast_sub h5]
      ring
    rw [h4]
    linarith
  · -- the level is complete, hence dense
    intro v hv
    rw [hinterW', edeg_cliqueEdges_of_mem hv, hW'card]
    have h4 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
      ring
    rw [h4]
    have hMr : (9 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM9
    nlinarith
  · rw [hinterW'']; exact cliqueEdges_nonempty (by omega)

/-! ### The absorber-confinement route, for the dense pair -/

/-- **The absorber-confinement route, density-corrected.**  The dense max-degree nibble and the
density-corrected flexible shell absorption `BKLO.ShellAbsorptionDense` give the density-corrected
repaired cover-down step `BKLO.CoverDownK3DivDense`.

This is `BKLO.coverDownK3Div_of_denseNibble_shellAbsorption` with the level-density hypothesis
carried along: it is a hypothesis of the conclusion `CoverDownK3DivDense` and is handed to
`ShellAbsorptionDense` unchanged, so the route costs nothing extra. -/
theorem coverDownK3DivDense_of_denseNibble_shellAbsorptionDense
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDegDense)
    (hAbs : ShellAbsorptionDense) : CoverDownK3DivDense := by
  classical
  intro c γ hc hγ
  set ρ : ℝ := (c - 9 / 10) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ρ)
  set K : ℕ := max 2 m with hKdef
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKm : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_max_right 2 m
  have hKρ : 1 / ρ < (K : ℝ) := lt_of_lt_of_le hm hKm
  obtain ⟨η, n₁, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK2
  obtain ⟨n₂, hnib⟩ := nibbleMaxDeg_of_inputs_dense hDross hNib hη
  refine ⟨K, max n₁ n₂, hK2, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense hdenseW'
  -- the shell
  set E : Finset (Sym2 V) := F \ cliqueEdges W' with hEdef
  have hEF : E ⊆ F := Finset.sdiff_subset
  have hdivE : TriDivisible E := triDivisible_shell hdivF hdivF'
  -- the reservation
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F (le_trans (le_max_left _ _) hcard) hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF'
      hdivF'' hdense hdenseW'
  have hRE : R ⊆ E := hRsub
  -- `|W'| ≤ ρ |W|`
  have hWcard : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  have hW'ρ : (W'.card : ℝ) ≤ ρ * (W.card : ℝ) := by
    have h1 : (K : ℝ) * (W'.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hKW
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) < ρ * (K : ℝ) := by
      rw [div_lt_iff₀ hρ] at hKρ
      linarith
    have h3 : (W'.card : ℝ) * (K : ℝ) ≤ (W.card : ℝ) := by linarith only [h1]
    have hW'nonneg : (0 : ℝ) ≤ (W'.card : ℝ) := by positivity
    nlinarith [hW'nonneg, hKpos]
  -- the nibble on the shell, minus the reservation
  have hER : E \ R ⊆ cliqueEdges W := (Finset.sdiff_subset.trans hEF).trans hFW
  have hmindeg : ∀ v ∈ W, (9 / 10 : ℝ) * (W.card : ℝ) ≤ (edeg (E \ R) v : ℝ) := by
    intro v hv
    have h1 : edeg F v ≤ edeg E v + edeg (cliqueEdges W') v :=
      edeg_le_sdiff_add_edeg F (cliqueEdges W') v
    have h2 : edeg E v ≤ edeg (E \ R) v + edeg R v := edeg_le_sdiff_add_edeg E R v
    have h3 : edeg (cliqueEdges W') v ≤ W'.card := edeg_cliqueEdges_le' W' v
    have h1' : (edeg F v : ℝ) ≤ (edeg E v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    have h2' : (edeg E v : ℝ) ≤ (edeg (E \ R) v : ℝ) + (edeg R v : ℝ) := by exact_mod_cast h2
    have h3' : (edeg (cliqueEdges W') v : ℝ) ≤ (W'.card : ℝ) := by exact_mod_cast h3
    have h4 := hdense v hv
    have h5 := hRdeg v
    have : c * (W.card : ℝ) ≤ (edeg (E \ R) v : ℝ) + ρ * (W.card : ℝ) + ρ * (W.card : ℝ) := by
      linarith
    have hcρ : c - 2 * ρ = 9 / 10 := by rw [hρdef]; ring
    nlinarith [this]
  obtain ⟨P₁, hP₁, hP₁deg⟩ :=
    hnib W (E \ R) (le_trans (le_max_right _ _) hcard) hER hmindeg
  -- the leftover
  set L : Finset (Sym2 V) := (E \ R) \ famEdges P₁ with hLdef
  have hfamP₁ : famEdges P₁ ⊆ E \ R := famEdges_subset_of_triFamilyIn hP₁
  have hLsub : L ⊆ (F \ cliqueEdges W') \ R := Finset.sdiff_subset
  have hLdeg : ∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ) := hP₁deg
  -- the remainder is what the shell has left after the nibble
  have hRL : R ∪ L = E \ famEdges P₁ := by
    ext e
    simp only [Finset.mem_union, hLdef, Finset.mem_sdiff]
    constructor
    · rintro (he | ⟨⟨he, -⟩, hne⟩)
      · exact ⟨hRE he, fun hmem => (Finset.mem_sdiff.1 (hfamP₁ hmem)).2 he⟩
      · exact ⟨he, hne⟩
    · rintro ⟨he, hne⟩
      by_cases hR : e ∈ R
      · exact Or.inl hR
      · exact Or.inr ⟨⟨he, hR⟩, hne⟩
  have hdivRL : TriDivisible (R ∪ L) := by
    rw [hRL]
    exact triDivisible_sdiff_famEdges (hP₁.mono Finset.sdiff_subset) hdivE
  -- the absorption
  obtain ⟨Q, hQ, hQcov, hQsub, hQdeg⟩ := habs2 L hLsub hLdeg hdivRL
  -- the two families are edge-disjoint
  have hEW' : ∀ e ∈ E, e ∉ cliqueEdges W' := fun e he => (Finset.mem_sdiff.1 he).2
  have hdisjQP : Disjoint (famEdges Q) (famEdges P₁) := by
    refine Finset.disjoint_left.2 fun e heQ heP => ?_
    have heE : e ∈ E \ R := hfamP₁ heP
    have h1 : e ∉ R := (Finset.mem_sdiff.1 heE).2
    have h2 : e ∉ L := by
      simp only [hLdef, Finset.mem_sdiff, not_and, not_not]
      intro _; exact heP
    have h3 : e ∉ cliqueEdges W' := hEW' e (Finset.mem_sdiff.1 heE).1
    rcases Finset.mem_union.1 (hQsub heQ) with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      exacts [h1 h', h2 h']
    · exact h3 (Finset.mem_sdiff.1 h).1
  have hQ' : TriFamilyIn (F \ famEdges P₁) Q := by
    refine triFamilyIn_sdiff hQ fun t ht => ?_
    refine Finset.disjoint_of_subset_left ?_ hdisjQP
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  have hP₁' : TriFamilyIn F P₁ := hP₁.mono (Finset.sdiff_subset.trans hEF)
  refine ⟨P₁ ∪ Q, triFamilyIn_union hP₁' hQ', ?_, ?_, ?_⟩
  · -- the leftover is inside `W'`
    intro e he
    rw [Finset.mem_sdiff, famEdges_union, Finset.mem_union] at he
    obtain ⟨heF, hne⟩ := he
    push_neg at hne
    by_contra hW'e
    have heE : e ∈ E := Finset.mem_sdiff.2 ⟨heF, hW'e⟩
    have : e ∈ R ∪ L := by rw [hRL]; exact Finset.mem_sdiff.2 ⟨heE, hne.1⟩
    exact hne.2 (hQcov this)
  · -- `F ∩ cliqueEdges W''` is untouched
    intro e he
    rw [Finset.mem_inter] at he
    obtain ⟨heF, heW''⟩ := he
    have heW' : e ∈ cliqueEdges W' := cliqueEdges_mono hW'' heW''
    refine Finset.mem_sdiff.2 ⟨heF, ?_⟩
    rw [famEdges_union, Finset.mem_union]
    rintro (h | h)
    · exact hEW' e (Finset.mem_sdiff.1 (hfamP₁ h)).1 heW'
    · rcases Finset.mem_union.1 (hQsub h) with h' | h'
      · rw [hRL] at h'
        exact hEW' e (Finset.mem_sdiff.1 h').1 heW'
      · exact (Finset.mem_sdiff.1 h').2 heW''
  · -- the `W'`-degree is preserved up to `γ|W'|`
    intro v hv
    have hsub : F ∩ cliqueEdges W' ⊆
        (F \ famEdges (P₁ ∪ Q)) ∪ (famEdges Q ∩ cliqueEdges W') := by
      intro e he
      rw [Finset.mem_inter] at he
      by_cases hmem : e ∈ famEdges (P₁ ∪ Q)
      · rw [famEdges_union, Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact absurd he.2 (hEW' e (Finset.mem_sdiff.1 (hfamP₁ h)).1)
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨he.1, hmem⟩)
    have h1 : edeg (F ∩ cliqueEdges W') v
        ≤ edeg (F \ famEdges (P₁ ∪ Q)) v + edeg (famEdges Q ∩ cliqueEdges W') v :=
      le_trans (edeg_mono hsub v) (edeg_union_le _ _ v)
    have h1' : (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges (P₁ ∪ Q)) v : ℝ) + (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    linarith [hQdeg v hv]

end BKLO
