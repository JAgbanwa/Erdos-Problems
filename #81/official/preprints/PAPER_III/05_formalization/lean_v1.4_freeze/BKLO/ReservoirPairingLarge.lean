/-
# The repaired reservoir clause, reduced to **pairings**.

`BKLO/ReservoirPairing.lean` reduces the reservoir clause of §10 to a statement about involutions
of the perturbed reservoir links, `BKLO.ReservoirPairingResidual`.  That residual is **false**
(`BKLO.not_reservoirPairingResidual`), for the same reason as the clause it reduces: at a singleton
protected level `W''` its `loadInner` budget `γ|W''| = ε/8 < 1` forbids any pair running into
`W''`, while an adversarial link system may put the vertex of `W''` into a link.

This file redoes the reduction for the repaired clause `BKLO.ReservoirClauseR4`
(`BKLO/ReservoirLarge.lean`), in which the protected level is empty or of size at least `n₂`:

* `BKLO.ReservoirPairingClause4` — the pairing form of the repaired clause;
* `BKLO.ReservoirPairingResidual4` — its residual;
* `BKLO.reservoirClauseResidual4_of_pairingResidual4` and
  `BKLO.vortexReservoirEngineR4_of_pairingResidual4` — the reduction, unchanged from
  `BKLO/ReservoirPairing.lean`, since the added hypothesis is simply passed on;
* `BKLO.triangle_decomposition_of_inputs_and_pairing4` — the main theorem from the three classical
  inputs and the repaired pairing residual.

Everything here is `sorry`-free.
-/
import BKLO.EngineR4Assembly
import BKLO.LinkCoverAssembly

open Finset

namespace BKLO

/-- **The repaired reservoir clause in pairing form.**  `BKLO.ReservoirClauseR4` with the
link-covering conclusion replaced by the existence of a system of pairings
(`BKLO.IsPairedLinkSystem`); the cover is supplied by
`BKLO.isLinkCoverR_of_pairedLinkSystem`. -/
def ReservoirPairingClause4 (ε η : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
    (W''.Nonempty → n₂ ≤ W''.card) →
    F ⊆ cliqueEdges W → TriDivisible F →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
    (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) →
    (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) →
    ∃ R : Finset (Sym2 V), R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * η * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ X : V → Finset V,
        (∀ u ∈ W \ W', X u ⊆ W') →
        (∀ u ∈ W \ W', ∀ a ∈ X u, s(u, a) ∈ F) →
        (∀ u ∈ W \ W', Even (X u).card) →
        (∀ u ∈ W \ W', ((X u \ resLink R W' u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ u ∈ W \ W', ((resLink R W' u \ X u).card : ℝ) ≤ 2 * η * (W.card : ℝ)) →
        (∀ a ∈ W', (((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
          ≤ 2 * η * (W.card : ℝ)) →
        ∃ g : V → V → V, IsPairedLinkSystem F W' W'' (W \ W') X (ε / 8) g)

/-- **The pairing form of the repaired reservoir clause implies the repaired reservoir clause.** -/
theorem reservoirClauseR4_of_pairingClause4 {ε η : ℝ} {f : ℕ → ℝ} {n₂ K : ℕ}
    (h : ReservoirPairingClause4 ε η f n₂ K) : ReservoirClauseR4 ε η f n₂ K := by
  intro V _ W W' W'' F hn₂ hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres
  obtain ⟨R, hRF, hRcross, hsparse, hapex, hpair⟩ :=
    h W W' W'' F hn₂ hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW' hres
  refine ⟨R, hRF, hRcross, hsparse, hapex, ?_⟩
  intro X hXW' hXF hXeven hXadd hXdel hXmult
  obtain ⟨g, hg⟩ := hpair X hXW' hXF hXeven hXadd hXdel hXmult
  exact isLinkCoverR_of_pairedLinkSystem hW''W'
    (fun u hu => (Finset.mem_sdiff.1 hu).2) hXW' hXF hg

/-- **The repaired residual reservoir clause in pairing form.** -/
def ReservoirPairingResidual4 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ (η : ℝ) (n₃ : ℕ), 0 < η ∧ ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      ReservoirPairingClause4 ε η f n₂ K

/-- **The repaired residual of §10 is implied by its pairing form.** -/
theorem reservoirClauseResidual4_of_pairingResidual4 (h : ReservoirPairingResidual4) :
    ReservoirClauseResidual4 := by
  intro ε hε hε' K hK hKε
  obtain ⟨η, n₃, hη, hmain⟩ := h ε hε hε' K hK hKε
  exact ⟨η, n₃, hη, fun f n₂ hn₂ hwin => reservoirClauseR4_of_pairingClause4 (hmain f n₂ hn₂ hwin)⟩

/-- **The repaired fused §10 interface follows from the repaired pairing residual.** -/
theorem vortexReservoirEngineR4_of_pairingResidual4 (h : ReservoirPairingResidual4) :
    VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_reservoir4 (reservoirClauseResidual4_of_pairingResidual4 h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the repaired
pairing residual.** -/
theorem triangle_decomposition_of_inputs_and_pairing4
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : ReservoirPairingResidual4) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_reservoir4 hDross hNib hDirac
    (reservoirClauseResidual4_of_pairingResidual4 hRes)

end BKLO
