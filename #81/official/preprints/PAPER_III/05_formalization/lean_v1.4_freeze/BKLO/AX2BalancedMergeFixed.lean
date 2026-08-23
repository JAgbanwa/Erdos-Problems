/-
# The repaired one-link step of the balanced counted invariant, and the chain it closes

`BKLO/AX2BalancedMergeRefutation.lean` refutes `BKLO.RoutedSweepInvCellCountBalancedWide6hStep`
as stated.  The defect is a *quantifier* defect: the step constrains the link system `X` only at
the presented link `u`, so at a history link `w ∈ S` the set `X w` may miss the reserved link of
`w` entirely, and the history is then free to burn every edge between two classes of the presented
link.

This file states the repair — the same step with the perturbation budget asked at *every* swept
link,

```
∀ w ∈ S, 32 * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card,
∀ w ∈ S, 32 * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card
```

— and re-threads the whole chain against it:

* `BKLO.RoutedSweepInvCellCountBalancedWide6hStepFixed` — the repaired one-link step;
* `BKLO.TwoSidedUsedClassMatchedResized6hPairingFixed` — the one-link class-matched demand of
  `BKLO/AX2ResizedSixH.lean` carrying the same two sweep-wide clauses;
* `BKLO.twoSidedUsedClassMatchedResized6hPairingFixed_of_cell_step_countWide` — the repaired step
  supplies the repaired demand;
* `BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hFixed`,
  `BKLO.gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hFixed`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countWideFixed` — the chain to the AX2 half
  of the main theorem, at the unchanged density budget `(9/10 + ε) n ≤ δ(G)`.

The two clauses are *free* at the point the sweep is built: `BKLO.GridPairingClauseTwoSidedEighth`
hands the engine the perturbation budget `‖X u △ resLink R W' u‖ ≤ 2 η₈ |W|` at **every**
`u ∈ W \ W'`, and the sweep only ever swings links of `W \ W'`
(`BKLO.exists_pairedLinkCore_of_step_invariant` maintains `S ⊆ W \ W'`).  So every swept link is a
perturbed link of the design, carrying its own budget, and
`BKLO.twoSided_perturbation_eighth` converts it to the `32 · ≤ t` scale the sweep machinery uses —
exactly as it already did at the presented link.

Everything here is `sorry`-free.
-/
import BKLO.AX2BalancedMerge

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The repaired one-link step -/

/-- **The repaired one-link routed step of the balanced counted invariant.**  This is
`BKLO.RoutedSweepInvCellCountBalancedWide6hStep` with the two *sweep-wide* perturbation
hypotheses added: the link system is asked to stay within the perturbation budget of the design at
every link of the history, not only at the presented link.  This is what the surrounding
development produces, and it is what
`BKLO.not_routedSweepInvCellCountBalancedWide6hStep` — whose history lives at links whose `X w`
misses `resLink R W' w` entirely — violates. -/
def RoutedSweepInvCellCountBalancedWide6hStepFixed : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V}
    {F R : Finset (Sym2 V)} {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ},
    IsGridTwoSidedReservoirEighth ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    7 * q ≤ 8 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 6 * gridSize ε K ≤ gridClassSize ε K W'.card →
    ∀ {φ : V → ℕ}, (∀ w, φ w < gridSize ε K) →
    (∀ p q j : ℕ, (((W \ W').filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card)
      ≤ (((W \ W').filter (fun w => x w = p ∧ y w = q)).card) / gridSize ε K + 1) →
    ∀ {X : V → Finset V},
    ∃ L M : V → Finset V, CellSpreadLeftoverPlan ε K W W' x y L ∧
      ForeignSpreadLeftoverPlanWide ε K W W' M ∧
      ∀ {S : Finset V} {g₀ : V → V → V} {Exc : V → Finset V} {u : V} {n m : ℕ}
        {U : Finset (Sym2 V)},
      u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
      32 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card →
      32 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card →
      (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
      (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
      UsedForbidden X g₀ S W'' U →
      12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
      S ⊆ W \ W' → u ∉ S →
      (∀ w ∈ S, 32 * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card) →
      (∀ w ∈ S, 32 * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card) →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      IsClassMatchedSweep (gridSize ε K) C R W' X x y
        (fun w β => crossShift (gridSize ε K) φ β w)
        (fun w α => crossShiftInv (gridSize ε K) φ α w) S g₀ Exc →
      RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M S g₀ Exc →
      ∃ (p : V → V) (e : Finset V),
        (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
        (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
        IsClassMatchedSweep (gridSize ε K) C R W' X x y
          (fun w β => crossShift (gridSize ε K) φ β w)
          (fun w α => crossShiftInv (gridSize ε K) φ α w)
          (insert u S) (Function.update g₀ u p) (Function.update Exc u e) ∧
        RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M (insert u S)
          (Function.update g₀ u p) (Function.update Exc u e)

/-! ### The demand of `BKLO/AX2ResizedSixH.lean`, with the same two clauses -/

/-- **The one-link class-matched pairing demand at `6 h ≤ t`, with the sweep-wide perturbation
budget.**  `BKLO.TwoSidedUsedClassMatchedResized6hPairing` with the two extra hypotheses at the
history links.  They cost nothing at the point of use: the engine's link system is perturbed at
every link of `W \ W'`, and the sweep only swings links of `W \ W'`. -/
def TwoSidedUsedClassMatchedResized6hPairingFixed : Prop :=
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
        (∀ w ∈ S, 32 * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card) →
        (∀ w ∈ S, 32 * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card) →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
        IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g₀ Exc →
        Inv S g₀ Exc →
        ∃ (p : V → V) (e : Finset V),
          (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
          (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
          IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ (insert u S)
            (Function.update g₀ u p) (Function.update Exc u e) ∧
          Inv (insert u S) (Function.update g₀ u p) (Function.update Exc u e)

/-! ### The repaired step supplies the repaired demand -/

/-- **The re-sized `6 h ≤ t` residual demand of AX2 §10, from the repaired balanced one-link
step.**  Identical to `BKLO.twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countBalanced`;
the two sweep-wide clauses are passed straight through. -/
theorem twoSidedUsedClassMatchedResized6hPairingFixed_of_cell_step_countWide
    (hstep : RoutedSweepInvCellCountBalancedWide6hStepFixed) :
    TwoSidedUsedClassMatchedResized6hPairingFixed := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig
  classical
  set hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y :=
    hgrid8.toIsGridTwoSidedReservoir with hgriddef
  have hwide : 6400 * (K * K) ≤ gridSize ε K := gridSize_ge_of_eps_small hε hε' K
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have ht512 : 512 ≤ gridClassSize ε K W'.card := by
    have h1 : 6400 * 4 ≤ 6400 * (K * K) := Nat.mul_le_mul_left _ hKK
    omega
  obtain ⟨φ, hφlt, hφcell⟩ :=
    exists_cell_balanced_shift (W \ W') x y (gridSize_pos ε K)
  obtain ⟨L, M, hL, hM, hstep'⟩ :=
    hstep hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig hφlt hφcell (X := X)
  refine ⟨fun w β => crossShift (gridSize ε K) φ β w,
    fun w α => crossShiftInv (gridSize ε K) φ α w,
    RoutedSweepInvCellCountBalanced ε K W W' C x y φ L M,
    fun w β => crossShift_lt (gridSize_pos ε K) φ β w,
    fun w α => crossShiftInv_lt (gridSize_pos ε K) φ α w,
    classMatchingFibres_of_cellBalanced hgrid hφlt hφcell,
    routedSweepInvCellCountBalanced_empty φ L M, ?_, ?_⟩
  · intro S g Exc hInv
    exact excLedgerSpread_of_routedSweepInvCellCountBalancedWide (W'' := W'') (F := F) (R := R)
      hgrid hε hε' hK ht512 hφlt hφcell hL hM hInv
  · intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
      hSadd hSdel hmaps hginv hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hSadd hSdel
      hmaps hginv hsweep hInv

/-! ### The chain to the main theorem, re-threaded -/

/-- **The pairing clause at the re-sized two-sided design, from the repaired demand.**  The proof
of `BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6h`, with the two sweep-wide
clauses discharged at the step: a swept link lies in `W \ W'`, where the design's own perturbation
budget applies. -/
theorem gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hFixed
    (hpair : TwoSidedUsedClassMatchedResized6hPairingFixed)
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
  -- the perturbation budget of the design, at the scale the sweep uses, at *every* link
  have hXadd32 : ∀ u ∈ W \ W', 32 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card :=
    fun u hu => twoSided_perturbation_eighth hgrid hKpos (hXadd8 u hu)
  have hXdel32 : ∀ u ∈ W \ W', 32 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card :=
    fun u hu => twoSided_perturbation_eighth hgrid hKpos (hXdel8 u hu)
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
        hadd hdel hUdeg hUused hmargin hSD huS
        (fun w hw => hXadd32 w (hSD hw)) (fun w hw => hXdel32 w (hSD hw))
        hmaps hinv hsweep hInv
    exact ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, Function.update Exc u e, h5, h6⟩
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_ruleUsed hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the re-sized design, from the repaired demand.** -/
theorem gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hFixed
    (hpair : TwoSidedUsedClassMatchedResized6hPairingFixed) :
    GridPairingResidualTwoSidedEighth := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊
    (60 * (gridSize ε K * gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hFixed hpair
      hε hε' (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the *repaired*
balanced one-link counted step.**  The density budget is unchanged: `(9/10 + ε) n ≤ δ(G)`. -/
theorem triangle_decomposition_of_inputs_and_cell_step_countWideFixed
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountBalancedWide6hStepFixed) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSidedEighth hDross hNib hDirac
    (gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hFixed
      (twoSidedUsedClassMatchedResized6hPairingFixed_of_cell_step_countWide hstep))

end BKLO
