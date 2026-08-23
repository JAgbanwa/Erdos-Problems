/-
# The residual of AX2 §10, at the clean grid design.

`BKLO.GridPairingResidual` and its first repair `BKLO.GridPairingResidualFull` are both false —
`BKLO.not_gridPairingResidual`, `BKLO.not_gridPairingResidualFull` — and both refutations use
protected vertices *inside* the classes of the design.  `BKLO.exists_reservoir_clean_structured`
removes them: it builds a design whose classes avoid `W''` and whose reservoir touches no
protected vertex, at the price of classes of unequal (but still nearly nominal) size and of half
the perturbation scale.

This file states the remaining residual of AX2 §10 at that design and redoes the reduction:

* `BKLO.GridPairingClauseClean`, `BKLO.GridPairingResidualClean` — the pairing demand at a clean
  grid reservoir;
* `BKLO.reservoirPairingResidual4_of_gridPairingResidualClean` — the reduction;
* `BKLO.triangle_decomposition_of_inputs_and_gridPairingClean` — the main theorem of the AX2 half,
  from the three classical inputs and the clean residual.

Neither refutation applies here.  The first needed `X u₀ = W''` for some outer vertex, and now
every reservoir link is disjoint from `W''`; the second needed `Σ_u |X u ∩ W''|` to exceed the
`loadInner` budget, and now `X u ∩ W''` is contained in the perturbation `X u \ resLink R W' u`,
of size at most `2η|W|`, so the whole load put on the pool is at most `2η|W|·|W''|` against a
budget of `(ε/8)|W''|` per class vertex — a margin of a factor `Θ(εh²)`.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignClean
import BKLO.ReservoirPairingStructured

open Finset

namespace BKLO

/-- **The pairing clause at a clean grid reservoir.** -/
def GridPairingClauseClean (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
    IsGridCleanReservoir ε K W W' W'' F R C x y →
    (∀ u ∈ W \ W', X u ⊆ W') →
    (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
    (∀ u ∈ W \ W', Even (X u).card) →
    (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ)) →
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' (W \ W') X (ε / 8) g

/-- **The remaining residual of AX2 §10.**  At the clean grid design, and for an adversarial
admissible perturbation of its links, produce one globally edge-disjoint system of fixed-point-free
involutions of the perturbed links. -/
def GridPairingResidualClean : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingClauseClean ε f n₂ K

/-- **The reduction.**  The repaired residual of §10 in pairing form follows from the pairing
demand at the clean grid design: the design, its sparsity, its apex abundance, the avoidance of the
protected level and the load bound of the pairing system are all theorems. -/
theorem reservoirPairingResidual4_of_gridPairingResidualClean (h : GridPairingResidualClean) :
    ReservoirPairingResidual4 := by
  intro ε hε hε' K hK hKε
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  refine ⟨cleanEta ε K, max n₃ (reservoirThreshold ε K), cleanEta_pos hKpos, ?_⟩
  intro f n₂ hn₂ hwin V _ W W' W'' F hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, hapex, hsparse', hgrid⟩ :=
    exists_reservoir_clean_structured hε hKε hW''W' hKW' hW'K hKW'' hres
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

/-- **The §10 interface, from the pairing demand at the clean grid design.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualClean (h : GridPairingResidualClean) :
    VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_pairingResidual4
    (reservoirPairingResidual4_of_gridPairingResidualClean h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the pairing demand
at the clean grid design.** -/
theorem triangle_decomposition_of_inputs_and_gridPairingClean
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualClean) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_pairing4 hDross hNib hDirac
    (reservoirPairingResidual4_of_gridPairingResidualClean hRes)

end BKLO
