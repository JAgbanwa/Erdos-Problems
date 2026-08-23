/-
# The repaired residual, with the reservoir **built**.

`BKLO.ReservoirPairingResidual4` (`BKLO/ReservoirPairingLarge.lean`) still asks for two things at
once: a reservoir, and a system of pairings of its perturbed links.  The reservoir is not a
residual any more — `BKLO.exists_reservoir_structured` (`BKLO/ReservoirDesignStructured.lean`)
builds it, together with the grid structure of the design — and neither is the `load` field of
`BKLO.IsPairedLinkSystem`, which `BKLO.link_load_of_reservoir_design` proves at that reservoir.

This file discharges both, and leaves the pairing alone:

* `BKLO.IsPairedLinkCore` — `BKLO.IsPairedLinkSystem` without its `load` field;
* `BKLO.GridPairingClause`, `BKLO.GridPairingResidual` — the pairing demand at a *given* grid
  reservoir, with all the structure of the design available as hypotheses;
* `BKLO.reservoirPairingResidual4_of_gridPairingResidual` — the reduction.

So the whole of AX2 §10 is now reduced to `BKLO.GridPairingResidual`: at the explicit grid
reservoir of `BKLO/ReservoirDesign.lean`, and for an adversarial admissible perturbation of its
links, produce one globally edge-disjoint system of fixed-point-free involutions.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignStructured
import BKLO.ReservoirPairingLarge
import BKLO.LinkLoad

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The pairing demand, without the load field -/

/-- **The core of a paired link system**: `BKLO.IsPairedLinkSystem` with its `load` field — the
one bound that does not mention the pairings at all, and that
`BKLO.link_load_of_reservoir_design` proves at the reservoir of the grid design — omitted. -/
structure IsPairedLinkCore (F : Finset (Sym2 V)) (W' W'' D : Finset V) (X : V → Finset V)
    (γ : ℝ) (g : V → V → V) : Prop where
  /-- `g u` maps the link of `u` to itself. -/
  mem : ∀ u ∈ D, ∀ a ∈ X u, g u a ∈ X u
  /-- `g u` is an involution on the link of `u`. -/
  invol : ∀ u ∈ D, ∀ a ∈ X u, g u (g u a) = a
  /-- `g u` has no fixed point on the link of `u`. -/
  ne : ∀ u ∈ D, ∀ a ∈ X u, g u a ≠ a
  /-- the pairs are edges of `F`. -/
  edge : ∀ u ∈ D, ∀ a ∈ X u, s(a, g u a) ∈ F
  /-- no pair lies inside the protected level. -/
  avoid : ∀ u ∈ D, ∀ a ∈ X u, a ∉ W'' ∨ g u a ∉ W''
  /-- the pairs of different outer vertices are different edges. -/
  distinct : ∀ u ∈ D, ∀ a ∈ X u, ∀ v ∈ D, ∀ b ∈ X v, s(a, g u a) = s(b, g v b) → u = v
  /-- each vertex of `W'` is paired into `W''` at most `γ|W''|` times. -/
  loadInner : ∀ v ∈ W', ((D.filter (fun u => v ∈ X u ∧ g u v ∈ W'')).card : ℝ)
    ≤ γ * (W''.card : ℝ)

/-- The core plus the load bound is a paired link system. -/
theorem isPairedLinkSystem_of_core {F : Finset (Sym2 V)} {W' W'' D : Finset V} {X : V → Finset V}
    {γ : ℝ} {g : V → V → V} (h : IsPairedLinkCore F W' W'' D X γ g)
    (hload : ∀ v ∈ W', ((D.filter (fun u => v ∈ X u)).card : ℝ) ≤ γ * (W'.card : ℝ)) :
    IsPairedLinkSystem F W' W'' D X γ g :=
  ⟨h.mem, h.invol, h.ne, h.edge, h.avoid, h.distinct, hload, h.loadInner⟩

/-! ### The pairing demand at a grid reservoir -/

/-- **The pairing clause at a given grid reservoir.**  `BKLO.ReservoirPairingClause4` with the
reservoir supplied — together with the whole structure of the grid design — instead of demanded,
and with the `load` field of the pairing system dropped. -/
def GridPairingClause (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
    IsGridReservoir ε K W W' F R C x y →
    (∀ u ∈ W \ W', X u ⊆ W') →
    (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
    (∀ u ∈ W \ W', Even (X u).card) →
    (∀ u ∈ W \ W',
      ((X u \ resLink R W' u).card : ℝ) ≤ 2 * reservoirEta ε K * (W.card : ℝ)) →
    (∀ u ∈ W \ W',
      ((resLink R W' u \ X u).card : ℝ) ≤ 2 * reservoirEta ε K * (W.card : ℝ)) →
    (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * reservoirEta ε K * (W.card : ℝ)) →
    ∃ g : V → V → V, IsPairedLinkCore F W' W'' (W \ W') X (ε / 8) g

/-- **The residual of AX2 §10, with the reservoir built.** -/
def GridPairingResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingClause ε f n₂ K

/-- **The reduction.**  The repaired residual of §10 in pairing form follows from the pairing
demand at the grid reservoir: the reservoir itself, its sparsity, its apex abundance and the load
bound of the pairing system are all theorems. -/
theorem reservoirPairingResidual4_of_gridPairingResidual (h : GridPairingResidual) :
    ReservoirPairingResidual4 := by
  intro ε hε hε' K hK hKε
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  refine ⟨reservoirEta ε K, max n₃ (reservoirThreshold ε K), reservoirEta_pos hKpos, ?_⟩
  intro f n₂ hn₂ hwin V _ W W' W'' F hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres
  obtain ⟨R, C, x, y, hRF, hcross, hsparse, hapex, hsparse', hgrid⟩ :=
    exists_reservoir_structured hε hKε hKW' hW'K hres
      (le_trans (le_trans (le_max_right _ _) hn₂) hn₂W)
  refine ⟨R, hRF, hcross, hsparse, hapex, ?_⟩
  intro X hXW' hXF hXeven hXadd hXdel hXmult
  obtain ⟨g, hg⟩ :=
    hmain f n₂ (le_trans (le_max_left _ _) hn₂) hwin W W' W'' F R C x y X hn₂W hW'W hW''W'
      hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres hRF hcross hsparse hsparse' hgrid
      hXW' hXF hXeven hXadd hXdel hXmult
  exact ⟨g, isPairedLinkSystem_of_core hg
    (link_load_of_reservoir_design hε hKpos hW'K hsparse' hXmult)⟩

/-- **The repaired §10 interface, from the pairing demand at the grid reservoir.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidual (h : GridPairingResidual) :
    VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_pairingResidual4 (reservoirPairingResidual4_of_gridPairingResidual h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the pairing demand
at the grid reservoir.** -/
theorem triangle_decomposition_of_inputs_and_gridPairing
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidual) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_pairing4 hDross hNib hDirac
    (reservoirPairingResidual4_of_gridPairingResidual hRes)

end BKLO
