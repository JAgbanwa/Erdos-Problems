/-
# AX2 §10 the faithful way: vortex + cover-down, with divisibility fixing.

This file discharges the §10 conclusion (`BKLO.NearOptimalConclusion`, and with it the main
theorem) along BKLO's own route — a vortex `S ⊇ W₁ ⊇ W₂ ⊇ … ⊇ U` whose levels are covered down one
after the other, the leftover of a level being absorbed by the next one — and **without** the
class-matched routed sweep of `BKLO/AX2*.lean`.  No ledger, no per-vertex routing, no reservoir:
the only interfaces used are the repaired cover-down `BKLO.CoverDownK3Div`
(`BKLO/CoverDownRepaired.lean`) and a vortex schedule.

The one thing the recursion has to supply on its own is what makes `CoverDownK3Div` applicable at
all: its two divisibility hypotheses on the levels.  A level produced by sampling never induces a
triangle-divisible edge set, so at every level the recursion performs a **divisibility fix**
(`BKLO.exists_levelDivFix`): a bounded family of triangles, all of whose vertices lie in the
current level, is removed, after which the next level induces a divisible edge set.  Removing such
a family

* keeps the current level divisible (a triangle inside the level removes three of its edges and two
  from each of three degrees), so the fixes never undo one another;
* costs every vertex at most `12` edges, which is why every density hypothesis survives it; and
* is *part of the decomposition*: the fixing triangles are returned with the rest.

The fixes are also made to avoid the bottom set `U` (the `Y` parameter of `BKLO.exists_levelDivFix`)
whenever the level is at least four times larger than `U`; below that the recursion is at most one
step away from the bottom, so the bottom set absorbs at most a single fix.  This is the content of
the two bottom invariants `hgoodU` / `hclean0` of the recursion.
-/
import BKLO.LevelDivFix
import BKLO.VortexEngine
import BKLO.CoverDownRepaired
import BKLO.TriDecompDenseFromInputs

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Bookkeeping -/

/-- The empty edge set is triangle-divisible. -/
theorem triDivisible_empty : TriDivisible (∅ : Finset (Sym2 V)) := by
  refine ⟨fun v => ?_, by simp⟩
  simp

theorem cliqueEdges_empty : cliqueEdges (∅ : Finset V) = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun e he => ?_
  induction e using Sym2.ind with
  | _ a b => exact absurd ((mem_cliqueEdgesV.1 he).1 a (by simp)) (by simp)

theorem inter_cliqueEdges_empty (F : Finset (Sym2 V)) :
    F ∩ cliqueEdges (∅ : Finset V) = ∅ := by
  rw [cliqueEdges_empty, Finset.inter_empty]

/-- Removing a set of edges commutes with restricting to a vertex set. -/
theorem sdiff_inter_cliqueEdges (F Z : Finset (Sym2 V)) (X : Finset V) :
    (F \ Z) ∩ cliqueEdges X = (F ∩ cliqueEdges X) \ Z := by
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- A triangle family inside the edge set induced on `W'` is a triangle family of the whole edge
set. -/
theorem triFamilyIn_of_inter {F : Finset (Sym2 V)} {W' : Finset V} {Q : Finset (Finset V)}
    (hQ : TriFamilyIn (F ∩ cliqueEdges W') Q) : TriFamilyIn F Q :=
  ⟨hQ.1, fun t ht => (hQ.2.1 t ht).trans Finset.inter_subset_left, hQ.2.2⟩

/-- The damage a fixing family does to a degree. -/
theorem edeg_sdiff_ge {F Z : Finset (Sym2 V)} (v : V) (d : ℕ) (h : edeg Z v ≤ d) :
    edeg F v ≤ edeg (F \ Z) v + d :=
  le_trans (edeg_le_edeg_sdiff_add_edeg F Z v) (Nat.add_le_add_left h _)

/-! ### The vortex schedule, with the slack the divisibility fix costs

`BKLO.VortexScheduleExists` (`BKLO/InputsVortex.lean`) asks for a level of a prescribed size inside
a set on which the current edge set has exactly the density the schedule prescribes.  The recursion
below hands it a set from which one divisibility fix has been removed, i.e. a set on which the
density is short of the schedule's by at most `12` edges at a vertex — a shortfall the descent has
in hand many times over, since the schedule's drop from one scale to the next is proportional to
the scale.  This is the only difference between `VortexScheduleSlack` and `VortexScheduleExists`. -/
def VortexScheduleSlack : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ n₀ : ℕ, ∃ (f : ℕ → ℝ) (n₂ C : ℕ),
    n₀ ≤ n₂ ∧ n₂ ≤ C ∧ 0 < n₂ ∧
    (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + ε) ∧
    -- good bottom sets of bounded size
    (∀ {V : Type} [DecidableEq V] (S : Finset V) (E : Finset (Sym2 V)),
        n₂ ≤ S.card → E ⊆ cliqueEdges S →
        (∀ v ∈ S, (9 / 10 + ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
        ∃ U : Finset V, U ⊆ S ∧ n₂ ≤ U.card ∧ U.card ≤ C ∧
          ∀ v ∈ U, f U.card * (U.card : ℝ) ≤ (edeg (E ∩ cliqueEdges U) v : ℝ)) ∧
    -- one level of descent, of a prescribed size, keeping a prescribed bottom set
    (∀ {V : Type} [DecidableEq V] (W U : Finset V) (E : Finset (Sym2 V)) (m : ℕ),
        n₂ ≤ U.card → U ⊆ W → U.card ≤ m → 2 * m ≤ W.card → E ⊆ cliqueEdges W →
        (∀ v ∈ W, f W.card * (W.card : ℝ) - 12 ≤ (edeg E v : ℝ)) →
        ∃ W' : Finset V, U ⊆ W' ∧ W' ⊆ W ∧ W'.card = m ∧
          ∀ v ∈ W', f m * (m : ℝ) ≤ (edeg (E ∩ cliqueEdges W') v : ℝ))

/-! ### One fixed level -/

/-- One step of the recursion, packaged: the divisibility fix at the level `X` inside the ambient
set `W'`, followed by the cover-down of `W` onto `W'`.  Everything the step needs about the fix is
recorded in the conclusion. -/
theorem coverDown_step_fixed {c₀ γ : ℝ} {W W' X Y : Finset V} {F : Finset (Sym2 V)}
    {K n₀ : ℕ} (hFix : LevelDivFixProp)
    (hCD : ∀ (W W' W'' : Finset V) (F : Finset (Sym2 V)),
      n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
      K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
      F ⊆ cliqueEdges W → TriDivisible F →
      TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
      (∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn F P ∧
        F \ famEdges P ⊆ cliqueEdges W' ∧
        F ∩ cliqueEdges W'' ⊆ F \ famEdges P ∧
        ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
          ≤ (edeg (F \ famEdges P) v : ℝ) + γ * (W'.card : ℝ))
    (hn₀ : n₀ ≤ W.card) (hW'W : W' ⊆ W) (hXW' : X ⊆ W') (hYX : Y ⊆ X)
    (hr1 : K * W'.card ≤ W.card) (hr2 : W.card ≤ K * K * W'.card) (hXr : K * X.card ≤ W'.card)
    (hK : 2 ≤ K) (h4Y : 4 * Y.card ≤ X.card) (hX100 : 100 ≤ X.card)
    (hFW : F ⊆ cliqueEdges W) (hdiv : TriDivisible F) (hdivW' : TriDivisible (F ∩ cliqueEdges W'))
    (hdegW' : ∀ v ∈ W', (9 / 10 : ℝ) * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ))
    (hdegX : ∀ v ∈ X, (9 / 10 : ℝ) * (X.card : ℝ) ≤ (edeg (F ∩ cliqueEdges X) v : ℝ))
    (hdegW : ∀ v ∈ W, c₀ * (W.card : ℝ) + 12 ≤ (edeg F v : ℝ)) :
    ∃ (R : Finset (Finset V)) (F₁ : Finset (Sym2 V)),
      TriFamilyIn F R ∧ F \ famEdges R = F₁ ∧
      F₁ ⊆ cliqueEdges W' ∧ TriDivisible F₁ ∧ TriDivisible (F₁ ∩ cliqueEdges X) ∧
      F₁ ∩ cliqueEdges Y = F ∩ cliqueEdges Y ∧
      (∀ Z : Finset V, Z ⊆ X → ∀ v : V,
        (edeg (F ∩ cliqueEdges Z) v : ℝ) ≤ (edeg (F₁ ∩ cliqueEdges Z) v : ℝ) + 12) ∧
      ∀ v ∈ W', (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg F₁ v : ℝ) + γ * (W'.card : ℝ) + 12 := by
  classical
  have h2X : 2 * X.card ≤ W'.card := le_trans (Nat.mul_le_mul_right _ hK) hXr
  -- the divisibility fix, inside the current level
  obtain ⟨Q, hQfam, hQsub, hQdeg, hQY, hQdiv⟩ :=
    hFix W' X Y (F ∩ cliqueEdges W')
      hXW' hYX h2X h4Y hX100 Finset.inter_subset_right hdegW' (by
        intro v hv
        rw [inter_cliqueEdges_inter hXW']
        exact hdegX v hv)
  set F' : Finset (Sym2 V) := F \ famEdges Q with hF'
  have hQF : TriFamilyIn F Q := triFamilyIn_of_inter hQfam
  have hQsubF : famEdges Q ⊆ F ∩ cliqueEdges W' := famEdges_subset_of_triFamilyIn hQfam
  have hF'W : F' ⊆ cliqueEdges W := (Finset.sdiff_subset).trans hFW
  have hF'div : TriDivisible F' := triDivisible_sdiff_famEdges hQF hdiv
  have hF'W' : F' ∩ cliqueEdges W' = (F ∩ cliqueEdges W') \ famEdges Q :=
    sdiff_inter_cliqueEdges F (famEdges Q) W'
  have hF'divW' : TriDivisible (F' ∩ cliqueEdges W') := by
    rw [hF'W']
    exact triDivisible_sdiff_famEdges hQfam hdivW'
  have hF'divX : TriDivisible (F' ∩ cliqueEdges X) := by
    have : F' ∩ cliqueEdges X = ((F ∩ cliqueEdges W') \ famEdges Q) ∩ cliqueEdges X := by
      rw [← hF'W', Finset.inter_assoc, Finset.inter_eq_right.2 (cliqueEdges_mono hXW')]
    rw [this]
    exact hQdiv
  -- the degrees, after the fix
  have hdmg : ∀ v : V, edeg F v ≤ edeg F' v + 12 := fun v => edeg_sdiff_ge v 12 (hQdeg v)
  have hdmgR : ∀ v : V, (edeg F v : ℝ) ≤ (edeg F' v : ℝ) + 12 := by
    intro v; exact_mod_cast hdmg v
  have hdegW'' : ∀ v ∈ W, c₀ * (W.card : ℝ) ≤ (edeg F' v : ℝ) := by
    intro v hv
    have := hdegW v hv
    have := hdmgR v
    linarith
  -- the cover-down
  obtain ⟨P, hP, hcov, hkeep, hdam⟩ :=
    hCD W W' X F' hn₀ hW'W hXW' hr1 hr2 hXr hF'W hF'div hF'divW' hF'divX hdegW''
  refine ⟨Q ∪ P, F' \ famEdges P, triFamilyIn_union hQF hP, by rw [sdiff_famEdges_union], hcov,
    triDivisible_sdiff_famEdges hP hF'div, ?_, ?_, ?_, ?_⟩
  · -- divisibility of the level after the next survives the cover-down
    rw [inter_cliqueEdges_eq_of_keep (Finset.Subset.refl X) Finset.sdiff_subset hkeep]
    exact hF'divX
  · -- the bottom set is untouched: the fix avoids it and the cover-down protects it
    have h1 : (F' \ famEdges P) ∩ cliqueEdges Y = F' ∩ cliqueEdges Y := by
      have hYXsub : Y ⊆ X := hYX
      exact inter_cliqueEdges_eq_of_keep hYXsub Finset.sdiff_subset hkeep
    rw [h1]
    -- and the fix avoids `cliqueEdges Y`
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_inter_right Finset.sdiff_subset
    · intro e he
      obtain ⟨heF, heY⟩ := Finset.mem_inter.1 he
      refine Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨heF, fun hmem => ?_⟩, heY⟩
      exact Finset.disjoint_left.1 hQY hmem heY
  · -- the damage of the fix on any part of the level after the next
    intro Z hZX v
    have h1 : (F' \ famEdges P) ∩ cliqueEdges Z = F' ∩ cliqueEdges Z :=
      inter_cliqueEdges_eq_of_keep hZX Finset.sdiff_subset hkeep
    rw [h1]
    have h2 : edeg (F ∩ cliqueEdges Z) v ≤ edeg (F' ∩ cliqueEdges Z) v + 12 := by
      have h3 : (F ∩ cliqueEdges Z) \ famEdges Q = F' ∩ cliqueEdges Z :=
        (sdiff_inter_cliqueEdges F (famEdges Q) Z).symm
      have := edeg_sdiff_ge (F := F ∩ cliqueEdges Z) v 12 (hQdeg v)
      rwa [h3] at this
    exact_mod_cast h2
  · -- the damage of the whole step at the current level
    intro v hv
    have h1 := hdam v hv
    have h2 : edeg (F ∩ cliqueEdges W') v ≤ edeg (F' ∩ cliqueEdges W') v + 12 := by
      have := edeg_sdiff_ge (F := F ∩ cliqueEdges W') v 12 (hQdeg v)
      rwa [← hF'W'] at this
    have h2R : (edeg (F ∩ cliqueEdges W') v : ℝ) ≤ (edeg (F' ∩ cliqueEdges W') v : ℝ) + 12 := by
      exact_mod_cast h2
    linarith

end BKLO
