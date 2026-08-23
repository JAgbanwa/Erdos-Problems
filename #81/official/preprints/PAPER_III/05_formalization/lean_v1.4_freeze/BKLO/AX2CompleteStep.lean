/-
# The one-link step with the **complete** hypothesis set of the sweep

Every defect found so far in the one-link routed step of the balanced counted invariant is a
*statement* defect of the same kind: the step abstracts the sweep history `S` too weakly.

* `BKLO/AX2BalancedMergeRefutation.lean` — the step of `BKLO/AX2BalancedMerge.lean` constrains the
  link system only at the presented link, so a history link may have `X w` disjoint from its
  reserved link: false.
* `BKLO/AX2BalancedMergeFixed.lean` — the repair with the two *per-link* perturbation clauses
  added at every swept link, and the whole chain re-threaded against it;
* `BKLO/AX2SweepWideAudit.lean` — those two clauses do not bound the perturbation
  **multiplicity**: how many links of the history one and the same place may be perturbed at.

The sweep history is never an arbitrary family: `S` is a prefix of the real sweep, and every link
of it is a perturbed design link of `BKLO.GridPairingClauseTwoSidedEighth`, carrying *all* of that
clause's properties.  This file states the step **once**, with the complete set of properties the
sweep-construction point actually supplies, and re-threads the chain against it:

* `BKLO.RoutedSweepInvCellCountBalancedWide6hStepComplete` — the one-link step whose history
  hypotheses are the full set;
* `BKLO.TwoSidedUsedClassMatchedResized6hPairingComplete` — the matching one-link demand;
* `BKLO.twoSidedUsedClassMatchedResized6hPairingComplete_of_cell_step_countWideComplete`;
* `BKLO.gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hComplete`,
  `BKLO.gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hComplete`,
  `BKLO.triangle_decomposition_of_inputs_and_cell_step_countWideComplete` — the chain to the AX2
  half of the main theorem, at the unchanged density budget `(9/10 + ε) n ≤ δ(G)`.

## The audit of the sweep-construction point

`BKLO.GridPairingClauseTwoSidedEighth` hands the engine, for the link system `X` it is called on:

* `hXW'` — `X u ⊆ W'` at every `u ∈ W \ W'`;
* `hXF` — `s(u, a) ∈ F` for every `a ∈ X u`;
* `hXeven` — `Even (X u).card`;
* `hXadd8`, `hXdel8` — the two perturbation budgets, which
  `BKLO.twoSided_perturbation_eighth` turns into `32 · ≤ t`;
* `hXmult8` — the perturbation **multiplicity** budget, at the same scale.

and the sweep only ever swings links of `W \ W'`
(`BKLO.exists_pairedLinkCore_of_step_invariant` maintains `S ⊆ W \ W'`), so each of these is
available at every link of the history.  The sweep engine itself produces, at every link it has
already paired, an involution of that link by edges of `F`:
`∀ b ∈ X w, g w b ∈ X w`, `g w (g w b) = b`, `g w b ≠ b`, `s(b, g w b) ∈ F`.  All of that is
carried here.

Everything here is `sorry`-free except the step
`BKLO.routedSweepInvCellCountBalancedWide6hStepComplete_holds`, whose state is recorded in
`AX2_COMPLETE_STEP_REPORT.md`.
-/
import BKLO.AX2BalancedMergeFixed

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### The one-link step, with the complete history hypotheses -/

/-- **The one-link routed step of the balanced counted invariant, with the complete hypothesis
set.**  `BKLO.RoutedSweepInvCellCountBalancedWide6hStepFixed` with every further property of a
swept link that the sweep-construction point supplies:

* the link system is a *perturbed design link* at every history link — `X w ⊆ W'`, `Even (X w).card`,
  `s(w, a) ∈ F` for `a ∈ X w`, and the two perturbation budgets `32 · ≤ t`;
* the perturbation **multiplicity** budget `32 · ≤ t`, at every place of `W'`, over the whole
  design (the clause `hXmult8` of `BKLO.GridPairingClauseTwoSidedEighth`, which
  `BKLO/AX2SweepWideAudit.lean` shows is the one that blocks the class exhaustion of the
  two-clause refutation);
* the history pairing is an `F`-legal fixed-point-free involution of each of its links.

None of this weakens the chain: each clause is discharged where the sweep is built. -/
def RoutedSweepInvCellCountBalancedWide6hStepComplete : Prop :=
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
      -- (d), (e): every swept link is a perturbed design link
      (∀ w ∈ S, X w ⊆ W') →
      (∀ w ∈ S, Even (X w).card) →
      (∀ w ∈ S, ∀ a ∈ X w, s(w, a) ∈ F) →
      -- (a), (b): the two per-link perturbation budgets
      (∀ w ∈ S, 32 * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card) →
      (∀ w ∈ S, 32 * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card) →
      -- (c): the perturbation multiplicity budget, over the whole design
      (∀ a ∈ W', 32 * (((W \ W').filter (fun w => a ∈ X w \ resLink R W' w)).card)
        ≤ gridClassSize ε K W'.card) →
      -- (f): the history pairing is an `F`-legal fixed-point-free involution of each link
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ≠ b) →
      (∀ w ∈ S, ∀ b ∈ X w, s(b, g₀ w b) ∈ F) →
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

/-- The complete step is implied by the two-clause one: it has strictly more hypotheses. -/
theorem routedSweepInvCellCountBalancedWide6hStepComplete_of_fixed
    (hstep : RoutedSweepInvCellCountBalancedWide6hStepFixed) :
    RoutedSweepInvCellCountBalancedWide6hStepComplete := by
  intro V _ ε K W W' W'' F R C x y q c hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig φ hφlt hφcell X
  obtain ⟨L, M, hL, hM, hstep'⟩ :=
    hstep hgrid8 hnd hW'W hq hcres hqc8 hε hε' hK hbig hφlt hφcell (X := X)
  refine ⟨L, M, hL, hM, ?_⟩
  intro S g₀ Exc u n m U hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS
    _hSW' _hSeven _hSF hSadd hSdel _hSmult hmaps hginv _hne _hF hsweep hInv
  exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hSadd hSdel
    hmaps hginv hsweep hInv

/-! ### The demand of `BKLO/AX2ResizedSixH.lean`, with the complete hypothesis set -/

/-- **The one-link class-matched pairing demand at `6 h ≤ t`, with the complete hypothesis set.**
`BKLO.TwoSidedUsedClassMatchedResized6hPairingFixed` carrying the same complete list. -/
def TwoSidedUsedClassMatchedResized6hPairingComplete : Prop :=
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
        (∀ w ∈ S, X w ⊆ W') →
        (∀ w ∈ S, Even (X w).card) →
        (∀ w ∈ S, ∀ a ∈ X w, s(w, a) ∈ F) →
        (∀ w ∈ S, 32 * (X w \ resLink R W' w).card ≤ gridClassSize ε K W'.card) →
        (∀ w ∈ S, 32 * (resLink R W' w \ X w).card ≤ gridClassSize ε K W'.card) →
        (∀ a ∈ W', 32 * (((W \ W').filter (fun w => a ∈ X w \ resLink R W' w)).card)
          ≤ gridClassSize ε K W'.card) →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ≠ b) →
        (∀ w ∈ S, ∀ b ∈ X w, s(b, g₀ w b) ∈ F) →
        IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g₀ Exc →
        Inv S g₀ Exc →
        ∃ (p : V → V) (e : Finset V),
          (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
          (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
          IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ (insert u S)
            (Function.update g₀ u p) (Function.update Exc u e) ∧
          Inv (insert u S) (Function.update g₀ u p) (Function.update Exc u e)

/-! ### The complete step supplies the complete demand -/

/-- **The re-sized `6 h ≤ t` residual demand of AX2 §10, from the complete balanced one-link
step.**  The complete list of history clauses is passed straight through. -/
theorem twoSidedUsedClassMatchedResized6hPairingComplete_of_cell_step_countWideComplete
    (hstep : RoutedSweepInvCellCountBalancedWide6hStepComplete) :
    TwoSidedUsedClassMatchedResized6hPairingComplete := by
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
      hSW' hSeven hSF hSadd hSdel hSmult hmaps hginv hne hFleg hsweep hInv
    exact hstep' hu hXu hXeven hadd32 hdel32 hadd hdel hUdeg hUused hmargin hSD huS hSW' hSeven
      hSF hSadd hSdel hSmult hmaps hginv hne hFleg hsweep hInv

/-! ### The chain to the main theorem, re-threaded -/

/-- **The pairing clause at the re-sized two-sided design, from the complete demand.**  Every added
history clause is discharged here, where the sweep is built: a swept link lies in `W \ W'`, where
the design's own budgets apply, and the sweep's own invariant carries the `F`-legality and
fixed-point-freeness of the history pairing. -/
theorem gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hComplete
    (hpair : TwoSidedUsedClassMatchedResized6hPairingComplete)
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
  -- the three budgets of the design, at the scale the sweep uses
  have hXadd32 : ∀ u ∈ W \ W', 32 * (X u \ resLink R W' u).card ≤ gridClassSize ε K W'.card :=
    fun u hu => twoSided_perturbation_eighth hgrid hKpos (hXadd8 u hu)
  have hXdel32 : ∀ u ∈ W \ W', 32 * (resLink R W' u \ X u).card ≤ gridClassSize ε K W'.card :=
    fun u hu => twoSided_perturbation_eighth hgrid hKpos (hXdel8 u hu)
  have hXmult32 : ∀ a ∈ W',
      32 * (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card)
        ≤ gridClassSize ε K W'.card :=
    fun a ha => twoSided_perturbation_eighth hgrid hKpos (hXmult8 a ha)
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
  obtain ⟨ρ, σ, Inv, hρlt, hσlt, hfib, hInv0, hInvSpread, hstep⟩ :=
    hpair X hgrid8 hnd hW'W hq hc hqc8 hε hε' hK hbig6h
  -- the invariant of the sweep: it carries the `F`-legality of the history pairing as well
  set J : Finset V → (V → V → V) → Prop := fun S g =>
    S ⊆ W \ W' ∧ (∀ w ∈ S, ∀ b ∈ X w, g w b ≠ b) ∧ (∀ w ∈ S, ∀ b ∈ X w, s(b, g w b) ∈ F) ∧
    ∃ Exc : V → Finset V,
      IsClassMatchedSweep h C R W' X x y ρ σ S g Exc ∧ Inv S g Exc with hJdef
  have hJ0 : J (∅ : Finset V) (fun _ a => a) := by
    refine ⟨Finset.empty_subset _, ?_, ?_, fun _ => ∅, ?_, hInv0⟩
    · intro w hw; exact absurd hw (Finset.notMem_empty w)
    · intro w hw; exact absurd hw (Finset.notMem_empty w)
    · intro a α β _ _ _ w hw
      exact absurd hw (Finset.notMem_empty w)
  have hJled : ∀ S g, J S g → LedgerSpread ε K W' C X x y S g := by
    rintro S g ⟨hSD, -, -, Exc, hsweep, hInv⟩
    exact ledgerSpread_of_classMatchedSweep hgrid hε hε' hKpos hbig512 hρlt hσlt hfib hSD
      hXmult hsweep (hInvSpread S g Exc hInv)
  have hJstep : IsSpreadStepUsed ε K W W' W'' F R X c J := by
    intro S g₀ u n m U hu hXu hXeven' hadd hdel hUdeg hUused hmargin hSD huS hmaps hinv hJ
    obtain ⟨-, hgne, hgF, Exc, hsweep, hInv⟩ := hJ
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven'
        (twoSided_perturbation_eighth hgrid hKpos (hXadd8 u hu))
        (twoSided_perturbation_eighth hgrid hKpos (hXdel8 u hu))
        hadd hdel hUdeg hUused hmargin hSD huS
        (fun w hw => hXW' w (hSD hw)) (fun w hw => hXeven w (hSD hw))
        (fun w hw => hXF w (hSD hw))
        (fun w hw => hXadd32 w (hSD hw)) (fun w hw => hXdel32 w (hSD hw)) hXmult32
        hmaps hinv hgne hgF hsweep hInv
    refine ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, ?_, ?_, Function.update Exc u e,
      h5, h6⟩
    · intro w hw b hb
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [Function.update_self]; exact h3 b hb
      · rw [Function.update_of_ne (by rintro rfl; exact huS hwS)]; exact hgne w hwS b hb
    · intro w hw b hb
      rcases Finset.mem_insert.1 hw with rfl | hwS
      · rw [Function.update_self]; exact (h4 b hb).1
      · rw [Function.update_of_ne (by rintro rfl; exact huS hwS)]; exact hgF w hwS b hb
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_ruleUsed hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the re-sized design, from the complete demand.** -/
theorem gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hComplete
    (hpair : TwoSidedUsedClassMatchedResized6hPairingComplete) :
    GridPairingResidualTwoSidedEighth := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊
    (60 * (gridSize ε K * gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSidedEighth_of_usedClassMatchedResized6hComplete
      hpair hε hε' (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the *complete*
balanced one-link counted step.**  The density budget is unchanged: `(9/10 + ε) n ≤ δ(G)`. -/
theorem triangle_decomposition_of_inputs_and_cell_step_countWideComplete
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hstep : RoutedSweepInvCellCountBalancedWide6hStepComplete) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSidedEighth hDross hNib hDirac
    (gridPairingResidualTwoSidedEighth_of_usedClassMatchedResized6hComplete
      (twoSidedUsedClassMatchedResized6hPairingComplete_of_cell_step_countWideComplete hstep))

end BKLO
