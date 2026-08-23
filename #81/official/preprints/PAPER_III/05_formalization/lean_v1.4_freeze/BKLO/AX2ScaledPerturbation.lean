/-
# The residual of AX2 §10 at a **finer perturbation scale**

`BKLO/GridPairingTwoSidedEighth.lean` threads the perturbation scale
`BKLO.cleanEtaEighth ε K = cleanEta ε K / 8` through the reduction, which turns the adversary's
budget into a thirty-second of a class (`BKLO.twoSided_perturbation_eighth : 32 d ≤ t`).

`BKLO/AX2SweepWideAudit.lean` shows that this scale is **too coarse** for the routed part of the
partner-class ledger: at `32 d ≤ t` the demand a single cell puts on a class already exceeds the
class fibre (`BKLO.plan_load_at_current_scale_witness`), whereas at a scale of the shape
`64 K² d ≤ t` it is a factor `2 K²` below it (`BKLO.plan_load_at_scaled_perturbation_witness`,
which at `K = 2` uses `1024 d ≤ t`).

The scale is a **free parameter**: `η` is existentially quantified in
`BKLO.ReservoirPairingResidual4`, and `BKLO.vortexReservoirEngineR4_of_pairingResidual4` is uniform
in it — a smaller `η` only makes the pairing clause's hypotheses stronger and raises the size
threshold `n₀`.  This file re-threads the whole reduction at

```
cleanEtaScaled ε K = cleanEta ε K / (2048 K²),      i.e.   8192 K² d ≤ t,
```

which is finer than both the `64 K² d ≤ t` of the audit's statement and the `1024 d ≤ t` its
`K = 2` witness uses (`2 ≤ K` gives `8192 K² ≥ 32768 ≥ max (64 K²) 1024` there, and `8192 K²`
dominates `64 K²` at every `K`).

* `BKLO.cleanEtaScaled` — the finer perturbation scale;
* `BKLO.twoSided_perturbation_scaled` — `8192 K² d ≤ t` at that scale;
* `BKLO.scaled_perturbation_finer_than_64Ksq` — the finer scale implies the audit's `64 K² d ≤ t`;
* `BKLO.GridPairingClauseTwoSidedScaled`, `BKLO.GridPairingResidualTwoSidedScaled` — the pairing
  demand at the finer scale;
* `BKLO.reservoirPairingResidual4_of_gridPairingResidualTwoSidedScaled` — the reduction;
* `BKLO.triangle_decomposition_of_inputs_and_gridPairingTwoSidedScaled` — the AX2 half of the main
  theorem from it, at the unchanged density budget `(9/10 + ε) n ≤ δ(G)`.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingTwoSidedEighth

open Finset

namespace BKLO

/-- **The finer perturbation scale**, `cleanEta / (2048 K²)`. -/
noncomputable def cleanEtaScaled (ε : ℝ) (K : ℕ) : ℝ := cleanEta ε K / (2048 * (K : ℝ) ^ 2)

theorem cleanEtaScaled_pos {ε : ℝ} {K : ℕ} (hK : 0 < K) : 0 < cleanEtaScaled ε K := by
  have h1 := cleanEta_pos (ε := ε) hK
  have h2 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  simp only [cleanEtaScaled]
  positivity

theorem cleanEtaScaled_le_cleanEta {ε : ℝ} {K : ℕ} (hK : 0 < K) :
    cleanEtaScaled ε K ≤ cleanEta ε K := by
  have h1 := (cleanEta_pos (ε := ε) hK).le
  have h2 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have h3 : (1 : ℝ) ≤ 2048 * (K : ℝ) ^ 2 := by nlinarith
  simp only [cleanEtaScaled]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

variable {V : Type*} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **The adversary's perturbation at the finer scale is a `8192 K²`-th of a class.** -/
theorem twoSided_perturbation_scaled
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hK : 0 < K)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * cleanEtaScaled ε K * (W.card : ℝ)) :
    8192 * (K * K) * n ≤ gridClassSize ε K W'.card := by
  have h1 := eight_cleanEta_mul_card_le_twoSided hgrid hK
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hWr : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2048 * (K : ℝ) ^ 2 := by nlinarith
  have hn' : 8192 * (K : ℝ) ^ 2 * (n : ℝ) ≤ 8 * cleanEta ε K * (W.card : ℝ) := by
    simp only [cleanEtaScaled] at hn
    rw [show 2 * (cleanEta ε K / (2048 * (K : ℝ) ^ 2)) * (W.card : ℝ)
        = (2 * cleanEta ε K * (W.card : ℝ)) / (2048 * (K : ℝ) ^ 2) from by ring,
      le_div_iff₀ hden] at hn
    nlinarith only [hn]
  have h2 : ((8192 * (K * K) * n : ℕ) : ℝ) ≤ ((gridClassSize ε K W'.card : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h2

/-- **The finer scale implies the audit's scale `64 K² d ≤ t`.** -/
theorem scaled_perturbation_finer_than_64Ksq {K d t : ℕ} (h : 8192 * (K * K) * d ≤ t) :
    64 * (K * K) * d ≤ t := le_trans (by nlinarith) h

/-- **The finer scale implies the `1024 d ≤ t` the audit's `K = 2` witness uses.** -/
theorem scaled_perturbation_finer_than_1024 {K d t : ℕ} (hK : 2 ≤ K)
    (h : 8192 * (K * K) * d ≤ t) : 1024 * d ≤ t := by
  refine le_trans ?_ h
  have : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

/-- **The pairing clause at the finer perturbation scale.**  `BKLO.GridPairingClauseTwoSidedEighth`
with `BKLO.cleanEtaEighth` replaced by `BKLO.cleanEtaScaled`. -/
def GridPairingClauseTwoSidedScaled (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
      ≤ 2 * cleanEtaScaled ε K * (W.card : ℝ)) →
    (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ)
      ≤ 2 * cleanEtaScaled ε K * (W.card : ℝ)) →
    (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * cleanEtaScaled ε K * (W.card : ℝ)) →
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' (W \ W') X (ε / 8) g

/-- **The remaining residual of AX2 §10, at the finer perturbation scale.** -/
def GridPairingResidualTwoSidedScaled : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingClauseTwoSidedScaled ε f n₂ K

/-- **The reduction, at the finer perturbation scale.**  Choosing a smaller cleanliness `η` for the
design is free: it only strengthens the clause's hypotheses. -/
theorem reservoirPairingResidual4_of_gridPairingResidualTwoSidedScaled
    (h : GridPairingResidualTwoSidedScaled) : ReservoirPairingResidual4 := by
  intro ε hε hε' K hK hKε
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  refine ⟨cleanEtaScaled ε K, max n₃ (reservoirThresholdEighth ε K),
    cleanEtaScaled_pos hKpos, ?_⟩
  intro f n₂ hn₂ hwin V _ W W' W'' F hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, hapex, hsparse', hgrid⟩ :=
    exists_reservoir_twosided_structured_eighth hε hε' hKε hW''W' hKW' hW'K hKW'' hres
      (le_trans (le_trans (le_max_right _ _) hn₂) hn₂W)
  refine ⟨R, hRF, hcross, hsparse, ?_, ?_⟩
  · intro u hu v hv
    have h1 := hapex u hu v hv
    have h2 : cleanEtaScaled ε K ≤ cleanEta ε K := cleanEtaScaled_le_cleanEta hKpos
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [h1, h2, h3]
  intro X hXW' hXF hXeven hXadd hXdel hXmult
  obtain ⟨g, hg⟩ :=
    hmain f n₂ (le_trans (le_max_left _ _) hn₂) hwin W W' W'' F R C x y X hn₂W hW'W hW''W'
      hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres hRF hcross hsparse hsparse' hgrid
      hXW' hXF hXeven hXadd hXdel hXmult
  have hXmult' : ∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * reservoirEta ε K * (W.card : ℝ) := by
    intro a ha
    refine le_trans (hXmult a ha) ?_
    have h1 : cleanEtaScaled ε K ≤ reservoirEta ε K :=
      le_trans (cleanEtaScaled_le_cleanEta hKpos) (cleanEta_le hKpos)
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [h1, h2]
  exact ⟨g, isPairedLinkSystem_of_core hg
    (link_load_of_reservoir_design hε hKpos hW'K hsparse' hXmult')⟩

/-- **The §10 interface, from the pairing demand at the finer perturbation scale.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualTwoSidedScaled
    (h : GridPairingResidualTwoSidedScaled) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_pairingResidual4
    (reservoirPairingResidual4_of_gridPairingResidualTwoSidedScaled h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the pairing demand
at the finer perturbation scale.**  The density budget is unchanged: `(9/10 + ε) n ≤ δ(G)`. -/
theorem triangle_decomposition_of_inputs_and_gridPairingTwoSidedScaled
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualTwoSidedScaled) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_pairing4 hDross hNib hDirac
    (reservoirPairingResidual4_of_gridPairingResidualTwoSidedScaled hRes)

end BKLO
