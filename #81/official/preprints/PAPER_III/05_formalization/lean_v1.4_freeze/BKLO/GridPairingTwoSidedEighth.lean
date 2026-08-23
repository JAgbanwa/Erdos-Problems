/-
# The residual of AX2 §10 at the **re-sized** two-sided grid design

`BKLO/AX2CellStepRepair.lean` prescribes two changes to the reservoir, both bounded:

1. a **perturbation scale** `cleanEtaEighth ε K = cleanEta ε K / 8` in place of `cleanEta ε K`,
   which turns the adversary's budget from a quarter of a class into a *thirty-second* of it
   (`BKLO.twoSided_perturbation_eighth`);
2. an **eighth class balance**, carried out in `BKLO/ReservoirDesignSharpEighth.lean` and
   `BKLO/ReservoirDesignTwoSidedEighth.lean`, so the equalized trace is `c = q - q/8`.

The first change is free upstream: the scale `η` is existentially quantified in
`BKLO.ReservoirPairingResidual4`, and the second only enlarges the size threshold from
`BKLO.reservoirThreshold` to `BKLO.reservoirThresholdEighth`.  This file threads both through the
reduction, exactly as `BKLO/GridPairingTwoSided.lean` does at the old sizing.

* `BKLO.cleanEtaEighth` — the re-sized perturbation scale;
* `BKLO.twoSided_perturbation_eighth` — `32 n ≤ t` at the re-sized scale;
* `BKLO.GridPairingClauseTwoSidedEighth`, `BKLO.GridPairingResidualTwoSidedEighth` — the pairing
  demand at the re-sized design;
* `BKLO.reservoirPairingResidual4_of_gridPairingResidualTwoSidedEighth` — the reduction, with the
  re-sized reservoir actually constructed by
  `BKLO.exists_reservoir_twosided_structured_eighth`;
* `BKLO.triangle_decomposition_of_inputs_and_gridPairingTwoSidedEighth` — the main theorem of the
  AX2 half from it.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingTwoSided
import BKLO.ReservoirDesignTwoSidedEighth

open Finset

namespace BKLO

/-- **The re-sized perturbation scale**, an eighth of `BKLO.cleanEta`. -/
noncomputable def cleanEtaEighth (ε : ℝ) (K : ℕ) : ℝ := cleanEta ε K / 8

theorem cleanEtaEighth_pos {ε : ℝ} {K : ℕ} (hK : 0 < K) : 0 < cleanEtaEighth ε K := by
  have := cleanEta_pos (ε := ε) hK
  simp only [cleanEtaEighth]
  linarith

theorem cleanEtaEighth_le_cleanEta {ε : ℝ} {K : ℕ} (hK : 0 < K) :
    cleanEtaEighth ε K ≤ cleanEta ε K := by
  have := (cleanEta_pos (ε := ε) hK).le
  simp only [cleanEtaEighth]
  linarith

variable {V : Type*} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The adversary's perturbation at the re-sized scale is a thirty-second of a class.**  This is
the bound `32 * (resLink R W' u \ X u).card ≤ t` the cell prescription of
`BKLO.exists_cell_balanced_leftovers_of_resized` asks for. -/
theorem twoSided_perturbation_eighth
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hK : 0 < K)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * cleanEtaEighth ε K * (W.card : ℝ)) :
    32 * n ≤ gridClassSize ε K W'.card := by
  have h1 := eight_cleanEta_mul_card_le_twoSided hgrid hK
  have hn' : (n : ℝ) ≤ cleanEta ε K * (W.card : ℝ) / 4 := by
    simp only [cleanEtaEighth] at hn
    linarith
  have h2 : ((32 * n : ℕ) : ℝ) ≤ ((gridClassSize ε K W'.card : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

/-- **The pairing clause at the re-sized two-sided grid reservoir.**  `BKLO.GridPairingClauseTwoSided`
with the design replaced by the eighth-balanced one and the perturbation scale by
`BKLO.cleanEtaEighth`. -/
def GridPairingClauseTwoSidedEighth (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F R : Finset (Sym2 V))
      (C : ℕ → Finset V) (x y : V → ℕ) (X : V → Finset V),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    (W''.Nonempty → n₂ ≤ W''.card) →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
    R ⊆ F → IsCrossing W W' R →
    (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) →
    (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) →
    IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y →
    (∀ u ∈ W \ W', X u ⊆ W') →
    (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
    (∀ u ∈ W \ W', Even (X u).card) →
    (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ)
      ≤ 2 * cleanEtaEighth ε K * (W.card : ℝ)) →
    (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ)
      ≤ 2 * cleanEtaEighth ε K * (W.card : ℝ)) →
    (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * cleanEtaEighth ε K * (W.card : ℝ)) →
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' (W \ W') X (ε / 8) g

/-- **The remaining residual of AX2 §10, at the re-sized two-sided grid design.** -/
def GridPairingResidualTwoSidedEighth : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingClauseTwoSidedEighth ε f n₂ K

/-- **The reduction, at the re-sized reservoir.**  The re-sized design is *constructed* here, by
`BKLO.exists_reservoir_twosided_structured_eighth`, from the same density hypothesis
`(9/10 + ε/4)|W'| ≤ |resLink F W' v|` as before; only the size threshold is enlarged, which is free
because `n₃` is existentially quantified. -/
theorem reservoirPairingResidual4_of_gridPairingResidualTwoSidedEighth
    (h : GridPairingResidualTwoSidedEighth) : ReservoirPairingResidual4 := by
  intro ε hε hε' K hK hKε
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  refine ⟨cleanEtaEighth ε K, max n₃ (reservoirThresholdEighth ε K),
    cleanEtaEighth_pos hKpos, ?_⟩
  intro f n₂ hn₂ hwin V _ W W' W'' F hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, hapex, hsparse', hgrid⟩ :=
    exists_reservoir_twosided_structured_eighth hε hε' hKε hW''W' hKW' hW'K hKW'' hres
      (le_trans (le_trans (le_max_right _ _) hn₂) hn₂W)
  refine ⟨R, hRF, hcross, hsparse, ?_, ?_⟩
  · -- the apex abundance is only asked at the smaller scale
    intro u hu v hv
    have h1 := hapex u hu v hv
    have h2 : cleanEtaEighth ε K ≤ cleanEta ε K := cleanEtaEighth_le_cleanEta hKpos
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [h1, h2, h3]
  intro X hXW' hXF hXeven hXadd hXdel hXmult
  obtain ⟨g, hg⟩ :=
    hmain f n₂ (le_trans (le_max_left _ _) hn₂) hwin W W' W'' F R C x y X hn₂W hW'W hW''W'
      hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres hRF hcross hsparse hsparse' hgrid
      hXW' hXF hXeven hXadd hXdel hXmult
  -- the load field, at the coarser perturbation scale of the grid design
  have hXmult' : ∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * reservoirEta ε K * (W.card : ℝ) := by
    intro a ha
    refine le_trans (hXmult a ha) ?_
    have h1 : cleanEtaEighth ε K ≤ reservoirEta ε K :=
      le_trans (cleanEtaEighth_le_cleanEta hKpos) (cleanEta_le hKpos)
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [h1, h2]
  exact ⟨g, isPairedLinkSystem_of_core hg
    (link_load_of_reservoir_design hε hKpos hW'K hsparse' hXmult')⟩

/-- **The §10 interface, from the pairing demand at the re-sized two-sided grid design.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualTwoSidedEighth
    (h : GridPairingResidualTwoSidedEighth) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_pairingResidual4
    (reservoirPairingResidual4_of_gridPairingResidualTwoSidedEighth h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the pairing demand
at the re-sized two-sided grid design.** -/
theorem triangle_decomposition_of_inputs_and_gridPairingTwoSidedEighth
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualTwoSidedEighth) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_pairing4 hDross hNib hDirac
    (reservoirPairingResidual4_of_gridPairingResidualTwoSidedEighth hRes)

end BKLO
