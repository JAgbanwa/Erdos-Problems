/-
# The reservoir clause, reduced to **pairings**.

`BKLO.ReservoirClauseR` asks, of the reservoir `R` it produces, three things: vertex sparsity, apex
abundance, and — the hard one — that *every* admissible perturbed link system `X` admit a link
cover `Q`, i.e. a single edge-disjoint family of triangles covering the crossing edges of **all**
outer vertices `u ∈ W \ W'` at once, with the two damage bounds.

A link cover is, by `BKLO.isLinkCover_of_pairing`, nothing but a system of pairings: a triangle of
the cover through `u` is forced to be `{u, a, b}` with `a, b ∈ X u`, so the cover *is* a
fixed-point-free involution of each `X u` by `F`-edges, and the conditions on the family translate
into: the pairs of different outer vertices are different edges, and the number of links through a
vertex of `W'` is bounded.  That is the content of `BKLO.IsPairedLinkSystem`
(`BKLO/LinkCoverAssembly.lean`), and `BKLO.isLinkCoverR_of_pairedLinkSystem` turns such a system
into the cover, damage bounds included.

This file uses that to state the reservoir clause in its pairing form,
`BKLO.ReservoirPairingClause`, and its residual `BKLO.ReservoirPairingResidual`, and proves

  `BKLO.reservoirClauseResidual_of_pairingResidual :
      ReservoirPairingResidual → ReservoirClauseResidual`.

So the last residual of §10 is reduced to a statement in which no triangle family, no cover and no
decomposition occurs: only reservoirs and involutions of their perturbed links.  In particular the
reduction is not circular — the target `BKLO.triangle_decomposition_of_inputs_and_reservoir` does
not occur in it, and neither does any covering statement — and it is not refuted: the perturbation
scale `η` is existentially quantified, as `BKLO.not_reservoirClauseR_of_eta_large` requires.

Everything here is `sorry`-free.
-/
import BKLO.LinkCoverAssembly
import BKLO.EngineR3Assembly

open Finset

namespace BKLO

/-- **The reservoir clause in pairing form.**  Identical to `BKLO.ReservoirClauseR` except that the
link-covering conclusion is replaced by the existence of a *system of pairings*
(`BKLO.IsPairedLinkSystem`) of the perturbed links: the covering family of triangles, and with it
all the bookkeeping of `BKLO.IsLinkCoverR`, is supplied by
`BKLO.isLinkCoverR_of_pairedLinkSystem`. -/
def ReservoirPairingClause (ε η : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
    n₂ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
    K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
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

/-- **The pairing form of the reservoir clause implies the reservoir clause.** -/
theorem reservoirClauseR_of_pairingClause {ε η : ℝ} {f : ℕ → ℝ} {n₂ K : ℕ}
    (h : ReservoirPairingClause ε η f n₂ K) : ReservoirClauseR ε η f n₂ K := by
  intro V _ W W' W'' F hn₂ hW'W hW''W' hKW' hW'K hKW'' hFW hdiv hdegW hdegW' hres
  obtain ⟨R, hRF, hRcross, hsparse, hapex, hpair⟩ :=
    h W W' W'' F hn₂ hW'W hW''W' hKW' hW'K hKW'' hFW hdiv hdegW hdegW' hres
  refine ⟨R, hRF, hRcross, hsparse, hapex, ?_⟩
  intro X hXW' hXF hXeven hXadd hXdel hXmult
  obtain ⟨g, hg⟩ := hpair X hXW' hXF hXeven hXadd hXdel hXmult
  exact isLinkCoverR_of_pairedLinkSystem hW''W'
    (fun u hu => (Finset.mem_sdiff.1 hu).2) hXW' hXF hg

/-- **The residual reservoir clause in pairing form.**  Same shape as
`BKLO.ReservoirClauseResidual`, with `BKLO.ReservoirPairingClause` in place of
`BKLO.ReservoirClauseR`. -/
def ReservoirPairingResidual : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ (η : ℝ) (n₃ : ℕ), 0 < η ∧ ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      ReservoirPairingClause ε η f n₂ K

/-- **The last residual of §10 is implied by its pairing form.**  Together with
`BKLO.vortexReservoirEngineR3_of_reservoir` and `BKLO.triangle_decomposition_of_inputs_reservoir3`
this replaces `BKLO.ReservoirClauseResidual` by a statement about involutions of perturbed
reservoir links. -/
theorem reservoirClauseResidual_of_pairingResidual (h : ReservoirPairingResidual) :
    ReservoirClauseResidual := by
  intro ε hε hε' K hK hKε
  obtain ⟨η, n₃, hη, hmain⟩ := h ε hε hε' K hK hKε
  exact ⟨η, n₃, hη, fun f n₂ hn₂ hwin => reservoirClauseR_of_pairingClause (hmain f n₂ hn₂ hwin)⟩

/-- **The thrice-repaired fused §10 interface follows from the pairing residual.** -/
theorem vortexReservoirEngineR3_of_pairingResidual (h : ReservoirPairingResidual) :
    VortexReservoirEngineR3 :=
  vortexReservoirEngineR3_of_reservoir (reservoirClauseResidual_of_pairingResidual h)

end BKLO
