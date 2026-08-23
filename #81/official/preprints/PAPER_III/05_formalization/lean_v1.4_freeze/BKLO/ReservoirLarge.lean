/-
# The reservoir clause at a **large** protected level: the repair.

`BKLO.not_reservoirClauseResidual` (`BKLO/ReservoirPairingRefutation.lean`) refutes the reservoir
clause of §10 through its quantifier over the protected level `W''`: at a singleton `W''` the
damage bound `γ|W''| = ε/8 < 1` forbids the link cover *any* edge running into `W''`, while the
perturbation budget `2η|W| ≥ 1` lets an adversarial link system put a vertex of `W''` into the link
of an outer vertex, whose crossing edge then has to be covered by a triangle spending an edge into
`W''`.

The repair is to restrict the clause to the protected levels that actually occur in the engine:
in the vortex recursion `W''` is either **empty** (the last cover-down step, when the next level is
already the bottom set) or a genuine vortex level, hence of size at least `n₂`.  This file adds
that hypothesis — and nothing else — to the clause, as `BKLO.ReservoirClauseR4`, and redoes the two
steps of the derivation that consume it:

* `BKLO.coverDownStepR_of_reservoirClauseR4` — one cover-down step (the proof of
  `BKLO.coverDownStepR_of_reservoirClauseR`, with the size hypothesis passed on);
* `BKLO.coverDown_vortex_denseR2Large` — the recursion down the vortex (the proof of
  `BKLO.coverDown_vortex_denseR2`, which applies the step exactly twice: at `W'' = ∅`, where the
  hypothesis is vacuous, and at a level `W'' ⊇ U`, where `n₂ ≤ |U| ≤ |W''|`).

So the repair costs the derivation nothing: `BKLO.VortexReservoirEngineR4` still yields the main
theorem (`BKLO/MainR4.lean`).

Everything here is `sorry`-free.
-/
import BKLO.VortexEngineFusedR2
import BKLO.EngineR3

open Finset

namespace BKLO

/-! ### The repaired clause -/

/-- **The reservoir clause at a large protected level.**  Identical to `BKLO.ReservoirClauseR`
except for the added hypothesis that the protected level `W''` is either empty or at least as large
as the scale `n₂` — which is what the vortex recursion always hands it, and without which the
clause is false (`BKLO.not_reservoirClauseResidual`). -/
def ReservoirClauseR4 (ε η : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    (W''.Nonempty → n₂ ≤ W''.card) →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
    ∃ R : Finset (Sym2 V), R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * η * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ X : V → Finset V,
        (∀ u ∈ W \ W', X u ⊆ W') →
        (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
        (∀ u ∈ W \ W', Even (X u).card) →
        (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
          ≤ 2 * η * (W.card : ℝ)) →
        ∃ Q : Finset (Finset V), IsLinkCoverR F W' W'' (W \ W') X (ε / 8) Q)

/-- The repaired clause is weaker than the original one. -/
theorem reservoirClauseR4_of_reservoirClauseR {ε η : ℝ} {f : ℕ → ℝ} {n₂ K : ℕ}
    (h : ReservoirClauseR ε η f n₂ K) : ReservoirClauseR4 ε η f n₂ K :=
  fun W W' W'' F h1 h2 h3 h4 h5 h6 _ h7 h8 h9 h10 h11 =>
    h W W' W'' F h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

/-- **The repaired fused §10 interface.**  `BKLO.VortexReservoirEngineR3` with the reservoir clause
replaced by its form at a large protected level. -/
def VortexReservoirEngineR4 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ (n₀ : ℕ) (N : ℝ → ℕ), ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ),
    2 ≤ K ∧ (8 : ℝ) / ε ≤ (K : ℝ) ∧ 0 < η ∧
    n₀ ≤ n₂ ∧ N η ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) ∧
    VortexBottomClauseR2 ε f n₂ C K ∧ VortexDescentClauseR3 f n₂ K ∧ ReservoirClauseR4 ε η f n₂ K

/-- **The repaired residual reservoir clause.**  `BKLO.ReservoirClauseResidual` with
`BKLO.ReservoirClauseR4` in place of `BKLO.ReservoirClauseR`. -/
def ReservoirClauseResidual4 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ (η : ℝ) (n₃ : ℕ), 0 < η ∧ ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      ReservoirClauseR4 ε η f n₂ K

/-! ### One cover-down step -/

variable {V : Type*} [DecidableEq V]

/-- **One cover-down step, from the repaired reservoir clause.**  The proof of
`BKLO.coverDownStepR_of_reservoirClauseR`, with the size hypothesis on the protected level passed
on to the clause. -/
theorem coverDownStepR_of_reservoirClauseR4
    {ε η : ℝ} (hε : 0 < ε) {f : ℕ → ℝ} {n₂ K Nnib : ℕ}
    (hKε : (8 : ℝ) / ε ≤ (K : ℝ)) (hNn₂ : Nnib ≤ n₂)
    (hnib : ∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
      Nnib ≤ S.card → E ⊆ cliqueEdges S → (∀ v ∈ S, (9 / 10 : ℝ) * S.card ≤ edeg E v) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        ∀ v : V, (edeg (E \ famEdges P) v : ℝ) ≤ η * (S.card : ℝ))
    (hres : ReservoirClauseR4 ε η f n₂ K) :
    ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      (W''.Nonempty → n₂ ≤ W''.card) →
      F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + ε / 8 * (W'.card : ℝ)) ∧
        ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
          ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + ε / 8 * (W''.card : ℝ) := by
  classical
  intro V _ W W' W'' F hcard hW'W hW''W' hr1 hr2 hr3 hbig hFW hdiv hdeg hclean hbetween
  obtain ⟨R, hRF, hRcross, hRdeg, hapex, hlink⟩ :=
    hres W W' W'' F hcard hW'W hW''W' hr1 hr2 hr3 hbig hFW hdiv hdeg hclean hbetween
  -- the next level is a small fraction of the current one
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (by positivity) hKε
  have h8 : (8 : ℝ) ≤ (K : ℝ) * ε := by
    rw [div_le_iff₀ hε] at hKε
    linarith
  have h1 : (K : ℝ) * (W'.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hr1
  have hW'small : (W'.card : ℝ) ≤ ε / 8 * (W.card : ℝ) := by
    have hc : (0 : ℝ) ≤ (W'.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- the nibble applies to `F` minus the reservoir and minus the edges inside `W'`
  have hFpW : F \ (R ∪ cliqueEdges W') ⊆ cliqueEdges W := (Finset.sdiff_subset).trans hFW
  have hdeg' : ∀ v ∈ W, (9 / 10 : ℝ) * (W.card : ℝ)
      ≤ (edeg (F \ (R ∪ cliqueEdges W')) v : ℝ) := by
    intro v hv
    have hsplit : edeg F v ≤ edeg (F \ (R ∪ cliqueEdges W')) v + edeg (R ∪ cliqueEdges W') v :=
      edeg_le_sdiff_add_edeg F (R ∪ cliqueEdges W') v
    have hunion : edeg (R ∪ cliqueEdges W') v ≤ edeg R v + edeg (cliqueEdges W') v :=
      edeg_union_le R (cliqueEdges W') v
    have hcl : edeg (cliqueEdges W') v ≤ W'.card := edeg_cliqueEdges_le' W' v
    have hsplit' : (edeg F v : ℝ)
        ≤ (edeg (F \ (R ∪ cliqueEdges W')) v : ℝ) + (edeg (R ∪ cliqueEdges W') v : ℝ) := by
      exact_mod_cast hsplit
    have hunion' : (edeg (R ∪ cliqueEdges W') v : ℝ)
        ≤ (edeg R v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by exact_mod_cast hunion
    have hcl' : (edeg (cliqueEdges W') v : ℝ) ≤ (W'.card : ℝ) := by exact_mod_cast hcl
    have hR := hRdeg v
    have hF := hdeg v hv
    linarith
  obtain ⟨P₀, hP₀, hP₀deg⟩ :=
    hnib W (F \ (R ∪ cliqueEdges W')) (le_trans hNn₂ hcard) hFpW hdeg'
  exact coverDown_of_reservoirR hW''W' hFW hdiv hRF hRcross hapex hlink hP₀ hP₀deg

/-! ### The recursion down the vortex -/

/-- **Running the cover-down along the whole vortex, with the protected level either empty or a
genuine level.**  The proof of `BKLO.coverDown_vortex_denseR2`: the cover-down step is applied at
`W'' = ∅` and at a level `W''` containing the bottom set `U`, so the new hypothesis is available
at both call sites. -/
theorem coverDown_vortex_denseR2Large {c₁ γ : ℝ} {f : ℕ → ℝ} {n₂ n₀ K : ℕ} {U : Finset V}
    (hK : 2 ≤ K)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      (W''.Nonempty → n₂ ≤ W''.card) →
      F ⊆ cliqueEdges W → TriDivisible F → (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, c₁ * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        (∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ)) ∧
        ∀ v ∈ W', ((resLink F W'' v).card : ℝ)
          ≤ ((resLink (F \ famEdges P) W'' v).card : ℝ) + γ * (W''.card : ℝ))
    (hdesc : ∀ (W : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
      U ⊆ W → K * U.card ≤ m → 2 * m ≤ W.card → W.card ≤ K * K * m → E ⊆ cliqueEdges W →
      (∀ v ∈ W, f W.card * (W.card : ℝ) ≤ (edeg E v : ℝ)) →
      (∀ v ∈ W, f U.card * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) →
      ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
        ∀ v ∈ W, f m * (m : ℝ) ≤ ((resLink E W' v).card : ℝ))
    (hf : ∀ s : ℕ, n₂ ≤ s → c₁ + γ ≤ f s) (hn₀ : n₀ ≤ n₂) (hn₂ : 0 < n₂) (hU : n₂ ≤ U.card) :
    ∀ (fuel : ℕ) (W W' : Finset V) (F : Finset (Sym2 V)),
      W.card ≤ fuel → F ⊆ cliqueEdges W → TriDivisible F →
      (∀ v ∈ W, c₁ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      U ⊆ W' → W' ⊆ W → K * W'.card ≤ W.card → W.card ≤ K * K * W'.card →
      (W' = U ∨ K * U.card ≤ W'.card) →
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
      (∀ v ∈ W, c₁ * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
      (∀ v ∈ W', f U.card * (U.card : ℝ) ≤ ((resLink F U v).card : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧ F \ famEdges P ⊆ cliqueEdges U := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro W W' F hfuel _ _ _ hUW' hW'W _ _ _ _ _ _
    have h1 : U.card ≤ W'.card := Finset.card_le_card hUW'
    have h2 : W'.card ≤ W.card := Finset.card_le_card hW'W
    omega
  | succ fuel ih =>
    intro W W' F hfuel hFW hdiv hdeg hUW' hW'W hr1 hr2 hdisj hclean hbetween hbottom
    have hUcard : U.card ≤ W'.card := Finset.card_le_card hUW'
    have hW'card : W'.card ≤ W.card := Finset.card_le_card hW'W
    have hn₂W' : n₂ ≤ W'.card := le_trans hU hUcard
    have hn₀W : n₀ ≤ W.card := le_trans (le_trans hn₀ hn₂W') hW'card
    have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFW he)).2
    by_cases hWU : W' = U
    · -- the bottom set has been reached: one last cover-down, with an empty protected level
      obtain ⟨P, hP, hcov, -, -, -⟩ :=
        hCD W W' ∅ F hn₀W hW'W (Finset.empty_subset _) hr1 hr2 (by simp)
          (fun h => absurd h (by simp)) hFW hdiv hdeg hclean hbetween
      exact ⟨P, hP, by rw [← hWU]; exact hcov⟩
    · -- otherwise the bottom set is at least `K` times smaller than the current level
      have hKU : K * U.card ≤ W'.card := hdisj.resolve_left hWU
      have hUpos : 1 ≤ U.card := by omega
      have hbottom' : ∀ v ∈ W',
          f U.card * (U.card : ℝ) ≤ ((resLink (F ∩ cliqueEdges W') U v).card : ℝ) := by
        intro v hv
        rw [resLink_inter_cliqueEdges (hUW' : U ⊆ W') hv hnd]
        exact hbottom v hv
      -- choose the level after the next, together with the density of `F` into it seen from `W'`
      obtain ⟨W'', hUW'', hW''W', hW''r1, hW''r2, hW''disj, hres''⟩ :
          ∃ W'' : Finset V, U ⊆ W'' ∧ W'' ⊆ W' ∧ K * W''.card ≤ W'.card ∧
            W'.card ≤ K * K * W''.card ∧ (W'' = U ∨ K * U.card ≤ W''.card) ∧
            ∀ v ∈ W', f W''.card * (W''.card : ℝ) ≤ ((resLink F W'' v).card : ℝ) := by
        by_cases hsmall : W'.card ≤ K * K * U.card
        · exact ⟨U, Finset.Subset.refl _, hUW', hKU, hsmall, Or.inl rfl, hbottom⟩
        · push_neg at hsmall
          obtain ⟨hKa, ham, h2m, hKm, hmm⟩ := vortex_next_level_sizes hK hUpos hsmall
          obtain ⟨W'', hUW'', hW''W', hcard'', hres''⟩ :=
            hdesc W' (F ∩ cliqueEdges W') (W'.card / K) hUW' hKa h2m hmm
              Finset.inter_subset_right hclean hbottom'
          refine ⟨W'', hUW'', hW''W', by rw [hcard'']; exact hKm, by rw [hcard'']; exact hmm,
            Or.inr (by rw [hcard'']; exact hKa), ?_⟩
          intro v hv
          have h := hres'' v hv
          rw [resLink_inter_cliqueEdges hW''W' hv hnd] at h
          rwa [hcard'']
      have hn₂W'' : n₂ ≤ W''.card := le_trans hU (Finset.card_le_card hUW'')
      -- the density of the level after next, in its internal form
      have hclean'' : ∀ v ∈ W'',
          f W''.card * (W''.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W'') v : ℝ) := by
        intro v hv
        rw [edeg_inter_cliqueEdges_eq_card_resLink hv hnd]
        exact hres'' v (hW''W' hv)
      -- cover down one level
      obtain ⟨P₁, hP₁, hcov₁, hkeep₁, hdam₁, hdam₁'⟩ :=
        hCD W W' W'' F hn₀W hW'W hW''W' hr1 hr2 hW''r1 (fun _ => hn₂W'') hFW hdiv hdeg hclean
          hbetween
      set F₁ := F \ famEdges P₁ with hF₁
      have hdiv₁ : TriDivisible F₁ := triDivisible_sdiff_famEdges hP₁ hdiv
      have hdeg₁ : ∀ v ∈ W', c₁ * (W'.card : ℝ) ≤ (edeg F₁ v : ℝ) := fun v hv =>
        edeg_leftover_of_coverDown (hdam₁ v hv) (hclean v hv) (hf _ hn₂W')
      have hclean₁ : ∀ v ∈ W'',
          f W''.card * (W''.card : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges W'') v : ℝ) := by
        intro v hv
        rw [inter_cliqueEdges_eq_of_keep (Finset.Subset.refl W'') Finset.sdiff_subset hkeep₁]
        exact hclean'' v hv
      -- the between-levels density at the next pair, from the density into `W''` minus the damage
      have hbetween₁ : ∀ v ∈ W', c₁ * (W''.card : ℝ) ≤ ((resLink F₁ W'' v).card : ℝ) := by
        intro v hv
        have h1 := hres'' v hv
        have h2 := hdam₁' v hv
        have h3 : c₁ + γ ≤ f W''.card := hf _ hn₂W''
        have h4 : (0 : ℝ) ≤ (W''.card : ℝ) := Nat.cast_nonneg _
        nlinarith
      -- the density into the bottom set survives, because the step protects `W''`
      have hbottom₁ : ∀ v ∈ W'', f U.card * (U.card : ℝ) ≤ ((resLink F₁ U v).card : ℝ) := by
        intro v hv
        refine le_trans (hbottom v (hW''W' hv)) ?_
        exact_mod_cast Finset.card_le_card (resLink_subset_of_keep hUW'' hkeep₁ hv hnd)
      -- and recurse on the next level
      have hW'pos : 1 ≤ W'.card := by omega
      have hfuel' : W'.card ≤ fuel := by
        have : 2 * W'.card ≤ K * W'.card := Nat.mul_le_mul_right _ hK
        omega
      obtain ⟨P₂, hP₂, hcov₂⟩ :=
        ih W' W'' F₁ hfuel' hcov₁ hdiv₁ hdeg₁ hUW'' hW''W' hW''r1 hW''r2 hW''disj hclean₁
          hbetween₁ hbottom₁
      refine ⟨P₁ ∪ P₂, triFamilyIn_union hP₁ hP₂, ?_⟩
      rw [sdiff_famEdges_union]
      exact hcov₂

end BKLO
