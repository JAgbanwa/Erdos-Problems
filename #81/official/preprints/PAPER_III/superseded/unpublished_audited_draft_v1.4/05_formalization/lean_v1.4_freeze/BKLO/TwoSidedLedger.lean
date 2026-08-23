/-
# The ledger of a sweep at the two-sided design: what the earlier links can cost.

`BKLO.twoSided_step_of_ledger` (`BKLO/GridPairingStepTwoSided.lean`) pairs up one more link of a
two-sided grid design as soon as the edges already used by the earlier links have small degree
inside it.  This file *computes* that degree from the data of the sweep, and reduces it to a single
spread count.

* `BKLO.resLink_notMem_protected` — the classes of the design avoid the protected level, so the
  reserved link of an outer vertex never meets it: the part of a perturbed link inside the
  protected level is at most the perturbation.
* `BKLO.resLink_usedPairs_subset` — an earlier outer vertex `w` uses at most **one** edge at a
  given vertex `a`, namely `s(a, g₀ w a)`; this is where the involution invariant of the sweep is
  used.
* `BKLO.card_resLink_usedPairs_cell_split` — hence the used degree at `a` inside the link of `u`
  splits into the outer vertices of `u`'s own cell (whose number is free, by
  `BKLO.twoSided_cell_fibre_budget`) and the **cross-cell spread**: the earlier vertices of other
  cells whose partner of `a` landed inside the link of `u`.
* `BKLO.twoSided_step_of_spread` — one more link is paired up, Dirac's theorem included, as soon as
  the cross-cell spread and the number of saturated vertices of the link are at most `h t / 128`.

So at the two-sided design every ingredient of the sweep is a theorem except one count: how often
the partners already chosen for a vertex `a` land in the link being processed, when the two outer
vertices lie in different cells of the grid.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingStepTwoSided

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-! ### The protected level is invisible to the reserved links -/

/-- The classes of a two-sided design avoid the protected level, so the reserved link of an outer
vertex does too. -/
theorem resLink_notMem_protected (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {u : V} (hu : u ∈ W \ W') {a : V} (ha : a ∈ resLink R W' u) : a ∉ W'' := by
  have h1 := hgrid.linkSubset u hu ha
  have h2 : a ∈ gridRegion (gridSize ε K) C (x u) (y u) := (Finset.mem_inter.1 h1).2
  rw [gridRegion_eq_biUnion] at h2
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 h2
  have hlt : i < gridSize ε K * gridSize ε K :=
    gridIdx_lt (hgrid.rowLt u hu) (hgrid.colLt u hu) hi
  exact fun hW'' => (Finset.disjoint_left.1 (hgrid.classAvoid i hlt)) hai hW''

/-- Hence a *perturbed* link meets the protected level in at most as many places as the
perturbation itself. -/
theorem card_inter_protected_le (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {u : V} (hu : u ∈ W \ W') {Xu : Finset V} {n : ℕ}
    (hadd : (Xu \ resLink R W' u).card ≤ n) : (Xu ∩ W'').card ≤ n := by
  refine le_trans (Finset.card_le_card ?_) hadd
  intro a ha
  obtain ⟨haX, haW''⟩ := Finset.mem_inter.1 ha
  exact Finset.mem_sdiff.2 ⟨haX, fun hcon => resLink_notMem_protected hgrid hu hcon haW''⟩

/-! ### One earlier link uses one edge at a vertex -/

/-- An outer vertex `w` already processed uses exactly one edge at a vertex `a` of its link, namely
`s(a, g₀ w a)`.  (The involution invariant of the sweep is what makes this true.) -/
theorem resLink_usedPairs_subset {X : V → Finset V} {g₀ : V → V → V} {S : Finset V}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) (Y : Finset V) (a : V) :
    resLink (usedPairs X g₀ S) Y a
      ⊆ (S.filter (fun w => a ∈ X w ∧ g₀ w a ∈ Y)).image (fun w => g₀ w a) := by
  classical
  intro z hz
  obtain ⟨hzY, hzU⟩ := mem_resLink.1 hz
  obtain ⟨w, hw, b, hb, heq⟩ := mem_usedPairs.1 hzU
  rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1
    refine Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, hb, ?_⟩, h2.symm⟩
    exact h2 ▸ hzY
  · have haX : a ∈ X w := h1 ▸ hmaps w hw b hb
    have hga : g₀ w a = z := by rw [h1, hinv w hw b hb, h2]
    exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, haX, hga ▸ hzY⟩, hga⟩

/-- **The used degree splits into the competition of one cell and the cross-cell spread.** -/
theorem card_resLink_usedPairs_cell_split {X : V → Finset V} {g₀ : V → V → V} {S D : Finset V}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) (hSD : S ⊆ D) {u a : V} {sp : ℕ}
    (hspread : (S.filter (fun w =>
        ¬ (x w = x u ∧ y w = y u) ∧ a ∈ X w ∧ g₀ w a ∈ X u)).card ≤ sp) :
    (resLink (usedPairs X g₀ S) (X u) a).card
      ≤ (D.filter (fun w => x w = x u ∧ y w = y u)).card + sp := by
  classical
  set T : Finset V := S.filter (fun w => a ∈ X w ∧ g₀ w a ∈ X u) with hTdef
  have h1 : (resLink (usedPairs X g₀ S) (X u) a).card ≤ T.card :=
    le_trans (Finset.card_le_card (resLink_usedPairs_subset hmaps hinv (X u) a))
      Finset.card_image_le
  have hsplit : (T.filter (fun w => x w = x u ∧ y w = y u)).card
      + (T.filter (fun w => ¬ (x w = x u ∧ y w = y u))).card = T.card :=
    Finset.card_filter_add_card_filter_not _
  have h2 : (T.filter (fun w => x w = x u ∧ y w = y u)).card
      ≤ (D.filter (fun w => x w = x u ∧ y w = y u)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    obtain ⟨hwT, hwc⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD (Finset.mem_of_mem_filter w hwT), hwc⟩
  have h3 : (T.filter (fun w => ¬ (x w = x u ∧ y w = y u))).card ≤ sp := by
    refine le_trans (Finset.card_le_card ?_) hspread
    intro w hw
    obtain ⟨hwT, hwc⟩ := Finset.mem_filter.1 hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hwT
    exact Finset.mem_filter.2 ⟨hwS, hwc, hwa⟩
  omega

/-! ### One step of the sweep, from the cross-cell spread alone -/

section Spread

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **One more link is paired up, from the cross-cell spread alone.**  At a two-sided grid design,
with an admissible perturbation of the links and a sweep whose earlier pairings are involutions of
their own links, the next link is paired up — avoiding the edges already used, avoiding the
protected level, and keeping the protected-level load under budget — as soon as

* for every vertex `a` of the link, the earlier outer vertices of *other* cells that paired `a`
  into the link being processed number at most `sp`, and
* at most `ns` vertices of the link are already at their protected-level budget,

with `128 (sp + ns) ≤ h t`.  Every other ingredient — Dirac's threshold, the perturbation, the
competition of `u`'s own cell, and the protected level — is discharged here. -/
theorem twoSided_step_of_spread (hDirac : PerfectMatchingDirac)
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    {X : V → Finset V} {u : V} (hu : u ∈ W \ W') (hXW' : X u ⊆ W') (hXeven : Even (X u).card)
    (hadd : ((X u \ resLink R W' u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hdel : ((resLink R W' u \ X u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    {S : Finset V} (hSD : S ⊆ W \ W') {g₀ : V → V → V}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
    {γ : ℝ} {sp ns : ℕ}
    (hspread : ∀ a ∈ X u, (S.filter (fun w =>
      ¬ (x w = x u ∧ y w = y u) ∧ a ∈ X w ∧ g₀ w a ∈ X u)).card ≤ sp)
    (hsat : ((X u).filter (fun v =>
        ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
          ≤ γ * (W''.card : ℝ)))).card ≤ ns)
    (hbudget : 128 * (sp + ns) ≤ gridSize ε K * gridClassSize ε K W'.card) :
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
      (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
      (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
      (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
      (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
        ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1 ≤ γ * (W''.card : ℝ)) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  obtain ⟨q, c, hq, hc, hqc, -⟩ := hgrid.exists_sizes
  -- the class sizes
  have hhpos : 0 < h := gridSize_pos ε K
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hK.ne' hK.ne')
  have hh : 5 ≤ h := by nlinarith only [hwide, hKK]
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hq3 : 3 * t ≤ 4 * q := by
    have h1 := hgrid.classCardGe 0 hhh
    have h2 := hq 0 hhh
    rw [← htdef] at h1
    omega
  -- the perturbation
  set n : ℕ := max ((X u \ resLink R W' u).card) ((resLink R W' u \ X u).card) with hndef
  have hnr : (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ) := by
    rcases max_cases ((X u \ resLink R W' u).card) ((resLink R W' u \ X u).card) with
      ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hndef, he]
    · exact hadd
    · exact hdel
  have hn : 4 * n ≤ t := twoSided_perturbation_quarter hgrid hK hnr
  -- the competition of `u`'s own cell
  set Ncell : ℕ := ((W \ W').filter (fun w => x w = x u ∧ y w = y u)).card with hNdef
  have hcell : 64 * Ncell ≤ h * t := twoSided_cell_fibre_budget hgrid hε hε' hK (x u) (y u)
  -- the used degree
  have hused : ∀ a ∈ X u, (resLink (usedPairs X g₀ S) (X u) a).card ≤ Ncell + sp := fun a ha =>
    card_resLink_usedPairs_cell_split hmaps hinv hSD (hspread a ha)
  -- the protected level
  have hbad : (X u ∩ W'').card ≤ n :=
    card_inter_protected_le hgrid hu (le_max_left _ _)
  -- the margin
  have hspread' : 64 * (sp + (ns + n)) ≤ h * t := by
    have h32 : 32 * t ≤ h * t := Nat.mul_le_mul_right t (by omega)
    omega
  have hmargin : 12 * n + 8 * ((Ncell + sp) + (ns + n)) ≤ (2 * h - 1) * c :=
    twoSided_sweep_budget_of_spread hh hn (m := (Ncell + sp) + (ns + n))
      (Ncell := Ncell) (s := sp + (ns + n)) (by omega) hcell hspread' hq3 hqc
  exact twoSided_step_of_ledger hDirac hgrid hnd hW'W hq hc hqc hu hXW' hXeven
    (le_max_left _ _) (le_max_right _ _) hused hbad hsat hmargin

end Spread

/-! ### The one-link demand, with the invariants of the sweep

The rule that pairs up one more link may use the fact that the pairings already chosen are
involutions of their own links — this is what `BKLO.resLink_usedPairs_subset` needs, and it makes
the demand strictly weaker than `BKLO.GridPairingStepClauseTwoSided`. -/

def GridPairingStepClauseTwoSidedInv (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ u ∈ W \ W', X u ⊆ W') →
    (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
    (∀ u ∈ W \ W', Even (X u).card) →
    (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    ∀ S : Finset V, S ⊆ W \ W' → ∀ g₀ : V → V → V,
      (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
      ∀ u ∈ W \ W', u ∉ S →
      ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
        (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
        (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
        (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
        (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
          ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
            ≤ ε / 8 * (W''.card : ℝ))

/-- **The one-link residual, with the invariants of the sweep.** -/
def GridPairingResidualStepTwoSidedInv : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingStepClauseTwoSidedInv ε f n₂ K

/-- **The sweep closes the gap between the two clauses**, invariants included. -/
theorem gridPairingClauseTwoSided_of_stepInv {ε : ℝ} (hε : 0 ≤ ε) {f : ℕ → ℝ} {n₂ K : ℕ}
    (h : GridPairingStepClauseTwoSidedInv ε f n₂ K) : GridPairingClauseTwoSided ε f n₂ K := by
  intro V _ W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult
  exact exists_pairedLinkCore_of_step_inv (by linarith)
    (h W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
      hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult)

/-- **The one-link residual with invariants implies the residual of §10 at the two-sided
design.** -/
theorem gridPairingResidualTwoSided_of_stepInv (h : GridPairingResidualStepTwoSidedInv) :
    GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  exact ⟨n₃, fun f n₂ hn₂ hwin => gridPairingClauseTwoSided_of_stepInv hε.le (hmain f n₂ hn₂ hwin)⟩

/-- **The §10 interface, from the one-link residual with invariants.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualStepTwoSidedInv
    (h : GridPairingResidualStepTwoSidedInv) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided (gridPairingResidualTwoSided_of_stepInv h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
pairing demand at the two-sided grid design, with the invariants of the sweep available.** -/
theorem triangle_decomposition_of_inputs_and_gridPairingStepTwoSidedInv
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualStepTwoSidedInv) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_stepInv hRes)

end BKLO
