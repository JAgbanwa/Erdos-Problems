/-
# One descent step of the vortex, with its losses made explicit.

`BKLO/LevelSampling.lean` produces a random level and bounds its non-neighbourhoods.  This file
translates that into the vocabulary the vortex uses — `edeg`, `resLink` and a density schedule —
and records the three losses a descent step really costs: the deficiency `(f_W - f_U)|U|` of the
forced bottom set, the cost `(1 - f_W)|D|` of the avoidance set, and a sampling error `θm` that
can be made as small as one likes at the cost of taking `m` large.

The `D = ∅` specialisation `BKLO.descent_level_of_density_of_empty` is exactly the conclusion the
vortex recursion consumes (compare `BKLO.descent_of_R2`), and
`BKLO.descent_level_inherits_density` is the cleanest case: a bottom set as dense as the level it
sits in costs nothing at all, so the density passes to the next level up to `θ`.

Everything here is `sorry`-free.
-/
import BKLO.LevelSampling

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The descent step in the language of the vortex -/

/-- Inside a subset, links and non-neighbours partition the subset. -/
theorem card_resLink_add_card_nonNbrs {E : Finset (Sym2 V)} {X : Finset V} (v : V) :
    (resLink E X v).card + (nonNbrs E X v).card = X.card := by
  have hsub : resLink E X v ⊆ X := Finset.filter_subset _ _
  have hle : (resLink E X v).card ≤ X.card := Finset.card_le_card hsub
  rw [nonNbrs, Finset.card_sdiff_of_subset hsub]
  omega

/-- **One descent step of the vortex, with its losses made explicit.**

From a level `W` of density `f_W` and a forced bottom set `U ⊆ W` of density `f_U` as seen from
`W \ D`, a level `W'` of the prescribed size `m` exists, avoiding `D`, whose density is `f_W`
diminished by exactly three terms: the deficiency `(f_W - f_U)|U|` of the forced part, the cost
`(1 - f_W)|D|` of the avoidance set, and an arbitrarily small sampling error `θm`.

The hypothesis `hloss` is the statement that the schedule has that much slack between the scale
`|W|` and the scale `m`.  Outside `D` the new level carries the full density `f_m·m`; a vertex of
`D`, about which nothing is assumed at the scale of `U`, carries `f_m·m - f_W|U|`. -/
theorem descent_level_of_density {W U D : Finset V} {E : Finset (Sym2 V)} {m : ℕ}
    {fW fU fm θ Kr : ℝ}
    (hUW : U ⊆ W) (hDW : D ⊆ W) (hUD : Disjoint U D)
    (hUm : 2 * U.card ≤ m) (hpool : 2 * m + D.card ≤ W.card) (hWK : (W.card : ℝ) ≤ Kr * (m : ℝ))
    (hfW0 : 0 ≤ fW) (hfW1 : fW ≤ 1) (hfU : fU ≤ fW)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hKr : 1 ≤ Kr) (hm : 10 ^ 6 * Kr ≤ θ ^ 4 * (m : ℝ))
    (hE : E ⊆ cliqueEdges W)
    (hdens : ∀ v ∈ W, fW * (W.card : ℝ) ≤ (edeg E v : ℝ))
    (hbot : ∀ v ∈ W \ D, fU * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ))
    (hloss : fm * (m : ℝ)
      ≤ fW * (m : ℝ) - (fW - fU) * (U.card : ℝ) - (1 - fW) * (D.card : ℝ) - θ * (m : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ Disjoint W' D ∧ W'.card = m ∧
      (∀ v ∈ W \ D, fm * (m : ℝ) ≤ ((resLink E W' v).card : ℝ)) ∧
      (∀ v ∈ W, fm * (m : ℝ) - fW * (U.card : ℝ) ≤ ((resLink E W' v).card : ℝ)) := by
  classical
  have hnd : ∀ e ∈ E, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hE he)).2
  -- the non-neighbour form of the density hypothesis
  have hdensN : ∀ v ∈ W, ((nonNbrs E W v).card : ℝ) ≤ (1 - fW) * (W.card : ℝ) := by
    intro v hv
    have hres : (resLink E W v).card = edeg E v := by
      rw [← edeg_inter_cliqueEdges_eq_card_resLink hv hnd, Finset.inter_eq_left.2 hE]
    have hpart : (resLink E W v).card + (nonNbrs E W v).card = W.card :=
      card_resLink_add_card_nonNbrs v
    have hpartR : ((resLink E W v).card : ℝ) + ((nonNbrs E W v).card : ℝ) = (W.card : ℝ) := by
      exact_mod_cast hpart
    have := hdens v hv
    rw [hres] at hpartR
    linarith
  -- the bound for the forced part
  set NU : V → ℝ := fun v => if v ∈ D then (U.card : ℝ) else (1 - fU) * (U.card : ℝ) with hNUdef
  have huR0 : (0:ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
  have hNUle : ∀ v ∈ W, ((nonNbrs E U v).card : ℝ) ≤ NU v := by
    intro v hv
    have hpart : (resLink E U v).card + (nonNbrs E U v).card = U.card :=
      card_resLink_add_card_nonNbrs v
    have hpartR : ((resLink E U v).card : ℝ) + ((nonNbrs E U v).card : ℝ) = (U.card : ℝ) := by
      exact_mod_cast hpart
    by_cases hvD : v ∈ D
    · have hnn : (0:ℝ) ≤ ((resLink E U v).card : ℝ) := Nat.cast_nonneg _
      simp only [hNUdef, if_pos hvD]
      linarith
    · have hb := hbot v (Finset.mem_sdiff.2 ⟨hv, hvD⟩)
      simp only [hNUdef, if_neg hvD]
      linarith
  have hNUβ : ∀ v ∈ W, (1 - fW) * (U.card : ℝ) ≤ NU v := by
    intro v hv
    by_cases hvD : v ∈ D
    · simp only [hNUdef, if_pos hvD]
      have h := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) - fW ≤ 1) huR0
      linarith only [h]
    · simp only [hNUdef, if_neg hvD]
      exact mul_le_mul_of_nonneg_right (by linarith) huR0
  obtain ⟨W', hUW', hW'W, hW'D, hW'card, hW'dens⟩ :=
    exists_level_of_nonNbrs (β := 1 - fW) (θ := θ) (Kr := Kr) (NU := NU)
      hUW hDW hUD hUm hpool hWK (by linarith) (by linarith) hθ0 hθ1 hKr hm hdensN hNUle hNUβ
  refine ⟨W', hUW', hW'W, hW'D, hW'card, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvW, hvD⟩ := Finset.mem_sdiff.1 hv
    have hpart : (resLink E W' v).card + (nonNbrs E W' v).card = W'.card :=
      card_resLink_add_card_nonNbrs v
    have hpartR : ((resLink E W' v).card : ℝ) + ((nonNbrs E W' v).card : ℝ) = (m : ℝ) := by
      rw [← hW'card]; exact_mod_cast hpart
    have hb := hW'dens v hvW
    simp only [hNUdef, if_neg hvD] at hb
    linarith
  · intro v hvW
    have hpart : (resLink E W' v).card + (nonNbrs E W' v).card = W'.card :=
      card_resLink_add_card_nonNbrs v
    have hpartR : ((resLink E W' v).card : ℝ) + ((nonNbrs E W' v).card : ℝ) = (m : ℝ) := by
      rw [← hW'card]; exact_mod_cast hpart
    have hb := hW'dens v hvW
    have hfu : (0:ℝ) ≤ (fW - fU) * (U.card : ℝ) := mul_nonneg (by linarith) huR0
    have hfWU : (0:ℝ) ≤ fW * (U.card : ℝ) := mul_nonneg hfW0 huR0
    by_cases hvD : v ∈ D
    · simp only [hNUdef, if_pos hvD] at hb
      linarith
    · simp only [hNUdef, if_neg hvD] at hb
      linarith

/-- **The descent step in the form the vortex recursion consumes**: no avoidance set, and one
single density conclusion.  Compare `BKLO.descent_of_R2`: this is exactly the conclusion of the
descent clause of `BKLO.VortexReservoirEngineR2`, under the extra hypothesis `hloss` that the
schedule loses, between the scale `|W|` and the scale `m`, at least the deficiency of the forced
bottom set plus a sampling error. -/
theorem descent_level_of_density_of_empty {W U : Finset V} {E : Finset (Sym2 V)} {m : ℕ}
    {fW fU fm θ Kr : ℝ}
    (hUW : U ⊆ W) (hUm : 2 * U.card ≤ m) (hpool : 2 * m ≤ W.card)
    (hWK : (W.card : ℝ) ≤ Kr * (m : ℝ))
    (hfW0 : 0 ≤ fW) (hfW1 : fW ≤ 1) (hfU : fU ≤ fW)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hKr : 1 ≤ Kr) (hm : 10 ^ 6 * Kr ≤ θ ^ 4 * (m : ℝ))
    (hE : E ⊆ cliqueEdges W)
    (hdens : ∀ v ∈ W, fW * (W.card : ℝ) ≤ (edeg E v : ℝ))
    (hbot : ∀ v ∈ W, fU * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ))
    (hloss : fm * (m : ℝ) ≤ fW * (m : ℝ) - (fW - fU) * (U.card : ℝ) - θ * (m : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W, fm * (m : ℝ) ≤ ((resLink E W' v).card : ℝ) := by
  classical
  obtain ⟨W', hUW', hW'W, -, hW'card, hstrong, -⟩ :=
    descent_level_of_density (D := (∅ : Finset V)) (fW := fW) (fU := fU) (fm := fm)
      hUW (Finset.empty_subset _) (Finset.disjoint_empty_right _) hUm (by simpa using hpool)
      hWK hfW0 hfW1 hfU hθ0 hθ1 hKr hm hE hdens
      (fun v hv => hbot v (Finset.mem_sdiff.1 hv).1) (by simpa using hloss)
  exact ⟨W', hUW', hW'W, hW'card, fun v hv => hstrong v (by simpa using hv)⟩

/-- **A level inherits the density.**  The cleanest case of `BKLO.descent_level_of_density`: with
no avoidance set and a forced bottom set that is as dense as `W` itself, the only loss is the
sampling error `θ`. -/
theorem descent_level_inherits_density {W U : Finset V} {E : Finset (Sym2 V)} {m : ℕ}
    {fW θ Kr : ℝ}
    (hUW : U ⊆ W) (hUm : 2 * U.card ≤ m) (hpool : 2 * m ≤ W.card)
    (hWK : (W.card : ℝ) ≤ Kr * (m : ℝ))
    (hfW0 : 0 ≤ fW) (hfW1 : fW ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hKr : 1 ≤ Kr) (hm : 10 ^ 6 * Kr ≤ θ ^ 4 * (m : ℝ))
    (hE : E ⊆ cliqueEdges W)
    (hdens : ∀ v ∈ W, fW * (W.card : ℝ) ≤ (edeg E v : ℝ))
    (hbot : ∀ v ∈ W, fW * (U.card : ℝ) ≤ ((resLink E U v).card : ℝ)) :
    ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
      ∀ v ∈ W, (fW - θ) * (m : ℝ) ≤ ((resLink E W' v).card : ℝ) :=
  descent_level_of_density_of_empty (fU := fW) (fm := fW - θ) hUW hUm hpool hWK hfW0 hfW1
    le_rfl hθ0 hθ1 hKr hm hE hdens hbot (by ring_nf; linarith)

end BKLO
