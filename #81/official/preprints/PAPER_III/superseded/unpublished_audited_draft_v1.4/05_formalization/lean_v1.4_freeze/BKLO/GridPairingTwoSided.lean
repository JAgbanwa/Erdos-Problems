/-
# The residual of AX2 §10, at the **two-sided** grid design.

`BKLO.exists_reservoir_twosided_structured` (`BKLO/ReservoirDesignTwoSided.lean`) equalizes the
reserved links of the sharp design over the classes of their regions: the link of an outer vertex
meets each of the `2h - 1` classes of its row and column in the *same* number `c` of places, and
`c` is at least three quarters of the common class size.

This removes the obstruction that refutes the pairing demand at the sharp design.  The sharp
balance `IsGridSharpReservoir.classBalancedSharp` is one-sided: a host graph in which every outer
vertex misses a quarter of each class of its column and nothing of its row satisfies every field of
the sharp design and makes every link heavier on its row side by `Θ(h t)`, which
`BKLO.not_gridPairingResidualSharp` turns into a row-capacity refutation.  At the two-sided design
the row part and the column part of every link have *exactly the same size*
(`IsGridTwoSidedReservoir.rowColBalanced`), so no pair of any link is forced to stay inside one
side and the count has no purchase.  The Dirac margin survives the equalization
(`BKLO/TwoSidedLinkMargin.lean`): every vertex of a perturbed link still has at least half of it as
neighbours, even after the edges already used by a sweep are deleted.

* `BKLO.GridPairingClauseTwoSided`, `BKLO.GridPairingResidualTwoSided` — the pairing demand at a
  two-sided grid reservoir;
* `BKLO.reservoirPairingResidual4_of_gridPairingResidualTwoSided` — the reduction;
* `BKLO.triangle_decomposition_of_inputs_and_gridPairingTwoSided` — the main theorem of the AX2
  half, from the three classical inputs and the two-sided residual.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedLinkMargin

open Finset

namespace BKLO

/-- **The pairing clause at a two-sided grid reservoir.** -/
def GridPairingClauseTwoSided (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' (W \ W') X (ε / 8) g

/-- **The remaining residual of AX2 §10.**  At the two-sided grid design, and for an adversarial
admissible perturbation of its links, produce one globally edge-disjoint system of fixed-point-free
involutions of the perturbed links. -/
def GridPairingResidualTwoSided : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingClauseTwoSided ε f n₂ K

/-- **The reduction.**  The repaired residual of §10 in pairing form follows from the pairing
demand at the two-sided grid design: the design, its sparsity, its apex abundance, the avoidance of the
protected level and the load bound of the pairing system are all theorems. -/
theorem reservoirPairingResidual4_of_gridPairingResidualTwoSided (h : GridPairingResidualTwoSided) :
    ReservoirPairingResidual4 := by
  intro ε hε hε' K hK hKε
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  refine ⟨cleanEta ε K, max n₃ (reservoirThreshold ε K), cleanEta_pos hKpos, ?_⟩
  intro f n₂ hn₂ hwin V _ W W' W'' F hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, hapex, hsparse', hgrid⟩ :=
    exists_reservoir_twosided_structured hε hε' hKε hW''W' hKW' hW'K hKW'' hres
      (le_trans (le_trans (le_max_right _ _) hn₂) hn₂W)
  refine ⟨R, hRF, hcross, hsparse, hapex, ?_⟩
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
    have h1 : cleanEta ε K ≤ reservoirEta ε K := cleanEta_le hKpos
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [h1, h2]
  exact ⟨g, isPairedLinkSystem_of_core hg
    (link_load_of_reservoir_design hε hKpos hW'K hsparse' hXmult')⟩

/-- **The §10 interface, from the pairing demand at the two-sided grid design.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualTwoSided (h : GridPairingResidualTwoSided) :
    VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_pairingResidual4
    (reservoirPairingResidual4_of_gridPairingResidualTwoSided h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the pairing demand
at the two-sided grid design.** -/
theorem triangle_decomposition_of_inputs_and_gridPairingTwoSided
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualTwoSided) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_pairing4 hDross hNib hDirac
    (reservoirPairingResidual4_of_gridPairingResidualTwoSided hRes)

end BKLO
