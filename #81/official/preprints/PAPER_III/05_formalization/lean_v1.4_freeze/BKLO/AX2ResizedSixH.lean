/-
# The one-link class-matched demand at the reservoir re-sized to `6 h ≤ t`

`BKLO.TwoSidedUsedClassMatchedResizedPairing` (`BKLO/TwoSidedUsedClassMatchedResized.lean`) is
stated at the sizing `512 ≤ t`, where `t = BKLO.gridClassSize ε K |W'| = ⌊|W'| / (10 h²)⌋` is the
nominal class size.  The sizing is discharged, inside
`BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized`, from the size threshold
`5120 h² K² ≤ n₂` alone; raising that threshold raises `t` at no cost anywhere else in the engine
(`BKLO.gridClassSize_ge_of_card_ge`).

This file carries out step 1 of the repair prescribed in `BKLO/AX2CellFreeStepPin.lean`: the same
demand at the sizing `6 h ≤ t`.  At that sizing a class holds `q ≥ 4 h` places
(`3 t ≤ 4 q` and `6 h ≤ t` give `4 h ≤ q`, `BKLO.index_plan_capacity_of_resized`), so there is room
in a class for one planned place per routing index per unit of demand — which is what an
index-structured plan needs.

* `BKLO.TwoSidedUsedClassMatchedResized6hPairing` — the demand at `6 h ≤ t`;
* `BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6h`,
  `BKLO.gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6h`,
  `BKLO.triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized6h` — the chain to the
  main theorem, with the size threshold raised from `5120 h² K²` to `60 h³ K²`.

The density budget is untouched: the hypothesis of the main theorem is still
`(9/10 + ε) n ≤ δ(G)`, and `ε` enters only through `BKLO.gridSize`; the re-sizing is a raise of the
size threshold `n₀`, uniform in the engine.

Everything here is `sorry`-free; the demand itself is not proved here.
-/
import BKLO.TwoSidedUsedClassMatchedResized

open Finset

namespace BKLO

/-- **The one-link class-matched pairing demand at the reservoir re-sized to `6 h ≤ t`.**  This is
`BKLO.TwoSidedUsedClassMatchedResizedPairing` with the sizing hypothesis `512 ≤ t` strengthened to
`6 h ≤ t`; at `0 < ε ≤ 1/100` and `2 ≤ K` the grid is wide (`h ≥ 6400 K² ≥ 25600`), so the new
hypothesis implies the old one. -/
def TwoSidedUsedClassMatchedResized6hPairing : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ} (X : V → Finset V),
    IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    7 * q ≤ 8 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 6 * gridSize ε K ≤ gridClassSize ε K W'.card →
    ∃ (ρ σ : V → ℕ → ℕ) (Inv : Finset V → (V → V → V) → (V → Finset V) → Prop),
      (∀ w β, ρ w β < gridSize ε K) ∧ (∀ w α, σ w α < gridSize ε K) ∧
      ClassMatchingFibres ε K W W' x y ρ σ ∧
      Inv (∅ : Finset V) (fun _ a => a) (fun _ => ∅) ∧
      (∀ S g Exc, Inv S g Exc → ExcLedgerSpread ε K W' C g S Exc) ∧
      ∀ (S : Finset V) (g₀ : V → V → V) (Exc : V → Finset V) (u : V) (n m : ℕ)
        (U : Finset (Sym2 V)),
        u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
        32 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card →
        32 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card →
        (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
        (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
        UsedForbidden X g₀ S W'' U →
        12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
        S ⊆ W \ W' → u ∉ S →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
        IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g₀ Exc →
        Inv S g₀ Exc →
        ∃ (p : V → V) (e : Finset V),
          (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
          (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
          IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ (insert u S)
            (Function.update g₀ u p) (Function.update Exc u e) ∧
          Inv (insert u S) (Function.update g₀ u p) (Function.update Exc u e)

/-- **The pairing clause at the re-sized two-sided design, from the demand at `6 h ≤ t`.**  The
only change from `BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized` is the size
threshold, raised from `5120 h² K²` to `60 h³ K²`, which is what `6 h ≤ t` costs. -/
theorem gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6h
    (hpair : TwoSidedUsedClassMatchedResized6hPairing)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hK : 2 ≤ K) {f : ℕ → ℝ} {n₂ : ℕ}
    (hn₂ : (16 : ℝ) / ε ≤ (n₂ : ℝ))
    (hn₂size : 60 * (gridSize ε K * gridSize ε K * gridSize ε K) * (K * K) ≤ n₂) :
    GridPairingClauseTwoSidedEighth ε f n₂ K := by
  intro V _ W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres hRF hcross hsparse hsparse' hgrid8 hXW' hXF hXeven hXadd8 hXdel8 hXmult8
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hKpos : 0 < K := by omega
  set hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y :=
    hgrid8.toIsGridTwoSidedReservoir with hgriddef
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFW he)).2
  have hM : W''.Nonempty → (16 : ℝ) / ε ≤ (W''.card : ℝ) := by
    intro hne
    have h1 : (n₂ : ℝ) ≤ (W''.card : ℝ) := by exact_mod_cast hbig hne
    linarith
  -- the perturbation, weakened to the coarse scale the sweep machinery uses
  have hweak : ∀ n : ℕ, (n : ℝ) ≤ 2 * cleanEtaEighth ε K * (W.card : ℝ) →
      (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ) := by
    intro n hn
    have h1 : cleanEtaEighth ε K ≤ cleanEta ε K := cleanEtaEighth_le_cleanEta hKpos
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hn, h1, h2]
  have hXadd : ∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ) := fun u hu => hweak _ (hXadd8 u hu)
  have hXdel : ∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ) := fun u hu => hweak _ (hXdel8 u hu)
  have hXmult : ∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ) := fun a ha => hweak _ (hXmult8 a ha)
  obtain ⟨q, c, hq, hc, hqc8, -⟩ := hgrid8.exists_sizes_eighth
  have hqc : 3 * q ≤ 4 * c := by omega
  have hW'ge : 60 * (h * h * h) ≤ W'.card := by
    have h1 : (K * K) * (60 * (h * h * h)) ≤ (K * K) * W'.card := by
      calc (K * K) * (60 * (h * h * h)) = 60 * (h * h * h) * (K * K) := by ring
        _ ≤ n₂ := hn₂size
        _ ≤ W.card := hn₂W
        _ ≤ K * K * W'.card := hW'K
    exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hKpos hKpos)
  have hbig6h : 6 * h ≤ gridClassSize ε K W'.card := by
    rw [gridClassSize]
    refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
    calc 6 * h * (10 * gridSize ε K * gridSize ε K) = 60 * (h * h * h) := by rw [hhdef]; ring
      _ ≤ W'.card := hW'ge
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have hbig512 : 512 ≤ gridClassSize ε K W'.card := by
    have : 25600 ≤ h := le_trans (by omega) hwide
    omega
  -- the class matching and the invariant supplied by the demand
  obtain ⟨ρ, σ, Inv, hρlt, hσlt, hfib, hInv0, hInvSpread, hstep⟩ :=
    hpair X hgrid8 hnd hW'W hq hc hqc8 hε hε' hK hbig6h
  -- the invariant of the sweep
  set J : Finset V → (V → V → V) → Prop := fun S g =>
    S ⊆ W \ W' ∧ ∃ Exc : V → Finset V,
      IsClassMatchedSweep h C R W' X x y ρ σ S g Exc ∧ Inv S g Exc with hJdef
  have hJ0 : J (∅ : Finset V) (fun _ a => a) := by
    refine ⟨Finset.empty_subset _, fun _ => ∅, ?_, hInv0⟩
    intro a α β _ _ _ w hw
    exact absurd hw (Finset.notMem_empty w)
  have hJled : ∀ S g, J S g → LedgerSpread ε K W' C X x y S g := by
    rintro S g ⟨hSD, Exc, hsweep, hInv⟩
    exact ledgerSpread_of_classMatchedSweep hgrid hε hε' hKpos hbig512 hρlt hσlt hfib hSD
      hXmult hsweep (hInvSpread S g Exc hInv)
  have hJstep : IsSpreadStepUsed ε K W W' W'' F R X c J := by
    intro S g₀ u n m U hu hXu hXeven' hadd hdel hUdeg hUused hmargin hSD huS hmaps hinv hJ
    obtain ⟨Exc, hsweep, hInv⟩ := hJ.2
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven'
        (twoSided_perturbation_eighth hgrid hKpos (hXadd8 u hu))
        (twoSided_perturbation_eighth hgrid hKpos (hXdel8 u hu))
        hadd hdel hUdeg hUused hmargin hSD huS hmaps hinv hsweep hInv
    exact ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, Function.update Exc u e, h5, h6⟩
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_ruleUsed hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the re-sized design, from the demand at `6 h ≤ t`.** -/
theorem gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6h
    (hpair : TwoSidedUsedClassMatchedResized6hPairing) : GridPairingResidualTwoSidedEighth := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊
    (60 * (gridSize ε K * gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6h hpair hε hε'
      (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **The §10 interface, from the demand at `6 h ≤ t`.** -/
theorem vortexReservoirEngineR4_of_twoSidedUsedClassMatchedResized6h
    (hpair : TwoSidedUsedClassMatchedResized6hPairing) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSidedEighth
    (gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6h hpair)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
class-matched pairing demand at the reservoir re-sized to `6 h ≤ t`.**  The density budget is
unchanged — `(9/10 + ε) n ≤ δ(G)` — the re-sizing being a raise of the size threshold only. -/
theorem triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedResized6h
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hpair : TwoSidedUsedClassMatchedResized6hPairing) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSidedEighth hDross hNib hDirac
    (gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6h hpair)

end BKLO
