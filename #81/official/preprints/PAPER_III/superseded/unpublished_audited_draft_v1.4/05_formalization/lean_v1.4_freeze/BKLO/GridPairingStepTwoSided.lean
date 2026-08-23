/-
# The §10 residual at the two-sided design, reduced to **one link at a time**.

`BKLO.GridPairingResidualTwoSided` (`BKLO/GridPairingTwoSided.lean`) asks, at a two-sided grid
design and for an adversarial admissible perturbation of its links, for one *globally*
edge-disjoint system of fixed-point-free involutions of the links, with the protected level avoided
and its load under budget.

The sweep of `BKLO/TwoSidedSweep.lean` reduces that global demand to a local one: pair up the link
of **one** outer vertex `u`, avoiding the edges already used by the outer vertices processed before
it and keeping the protected-level load under budget.  This file states that local demand
(`BKLO.GridPairingStepClauseTwoSided`, `BKLO.GridPairingResidualStepTwoSided`) and proves that it
implies the global one, hence the main theorem of the AX2 half.

What is left in the local demand is a single quantitative question, with a concrete witness: the
edges already used by the earlier links must not cover too much of the link being processed.  At
the two-sided design the margin available for them is `(2h-1)c` (`BKLO/TwoSidedLinkMargin.lean`),
and `BKLO.twoSided_step_of_ledger` below discharges the local demand — Dirac's theorem included —
as soon as the used edges have degree at most `m` inside the link, with `12n + 8m ≤ (2h-1)c` and
the protected level handled.  So the whole of AX2 §10, at the two-sided design, now rests on a
ledger bound for a sweep, and on nothing else.

Everything here is `sorry`-free.
-/
import BKLO.GridPairingTwoSided
import BKLO.TwoSidedSweep

open Finset

namespace BKLO

/-- **The one-link (sweep-step) pairing clause at a two-sided grid reservoir.**  Instead of the
whole system, only one more link has to be paired up: its pairs must be edges of `F` outside the
protected level, they must avoid the edges already used by the outer vertices processed before it,
and they must keep the protected-level load under budget. -/
def GridPairingStepClauseTwoSided (ε : ℝ) (f : ℕ → ℝ) (n₂ K : ℕ) : Prop :=
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
    ∀ S : Finset V, S ⊆ W \ W' → ∀ g₀ : V → V → V, ∀ u ∈ W \ W', u ∉ S →
      ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
        (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
        (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
        (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
        (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
          ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
            ≤ ε / 8 * (W''.card : ℝ))

/-! ### The one-link demand, from a ledger bound -/

section Ledger

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The edges a step of the sweep must refuse besides the ones already used: those inside the
protected part `Bad = X u ∩ W''` of the link, and those joining it to a vertex whose
protected-level load is already at its budget. -/
theorem card_resLink_crossStars_le (Bad Tgt Y : Finset V) (a : V) :
    (resLink (crossStars Bad (fun _ => Tgt)) Y a).card ≤ (Tgt ∪ Bad).card := by
  classical
  refine Finset.card_le_card ?_
  intro z hz
  obtain ⟨-, hzF⟩ := mem_resLink.1 hz
  obtain ⟨b, hb, w, hw, heq⟩ := mem_crossStars.1 hzF
  rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Finset.mem_union_left _ (h2 ▸ hw)
  · exact Finset.mem_union_right _ (h2 ▸ hb)

/-- **The one-link demand of the sweep, from a ledger bound.**  At a two-sided grid design, one
more link is paired up — avoiding the edges already used, avoiding the protected level, and keeping
the protected-level load under budget — as soon as

* the edges already used have degree at most `m₀` inside the link,
* the link meets the protected level in at most `nb` vertices,
* at most `ns` vertices of the link are already at their protected-level budget, and
* `12n + 8(m₀ + ns + nb)` fits in the margin `(2h-1)c` of the design.

So the whole of AX2 §10 at the two-sided design rests on the ledger bound: how much of the link
being processed the earlier links have already used. -/
theorem twoSided_step_of_ledger (hDirac : PerfectMatchingDirac)
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q c : ℕ}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    (hc : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (resLink R W' u ∩ C i).card = c)
    (hqc : 3 * q ≤ 4 * c)
    {X : V → Finset V} {u : V} (hu : u ∈ W \ W') (hXW' : X u ⊆ W') (hXeven : Even (X u).card)
    {n : ℕ} (hadd : (X u \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X u).card ≤ n)
    {S : Finset V} {g₀ : V → V → V} {γ : ℝ} {m₀ nb ns : ℕ}
    (hused : ∀ a ∈ X u, (resLink (usedPairs X g₀ S) (X u) a).card ≤ m₀)
    (hbad : (X u ∩ W'').card ≤ nb)
    (hsat : ((X u).filter (fun v =>
        ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
          ≤ γ * (W''.card : ℝ)))).card ≤ ns)
    (hmargin : 12 * n + 8 * (m₀ + (ns + nb)) ≤ (2 * gridSize ε K - 1) * c) :
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
      (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
      (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
      (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
      (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
        ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1 ≤ γ * (W''.card : ℝ)) := by
  classical
  set Bad : Finset V := X u ∩ W'' with hBaddef
  set Sat : Finset V := (X u).filter (fun v =>
    ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
      ≤ γ * (W''.card : ℝ))) with hSatdef
  set Forb : Finset (Sym2 V) := crossStars Bad (fun _ => Sat ∪ Bad) with hForbdef
  set U : Finset (Sym2 V) := usedPairs X g₀ S ∪ Forb with hUdef
  -- the forbidden edges add little to the used degree
  have hUdeg : ∀ a ∈ X u, (resLink U (X u) a).card ≤ m₀ + (ns + nb) := by
    intro a ha
    have hsplit : resLink U (X u) a ⊆ resLink (usedPairs X g₀ S) (X u) a ∪ resLink Forb (X u) a := by
      intro z hz
      obtain ⟨hzX, hzU⟩ := mem_resLink.1 hz
      rcases Finset.mem_union.1 hzU with h1 | h1
      · exact Finset.mem_union_left _ (mem_resLink.2 ⟨hzX, h1⟩)
      · exact Finset.mem_union_right _ (mem_resLink.2 ⟨hzX, h1⟩)
    have h1 := hused a ha
    have h2 : (resLink Forb (X u) a).card ≤ ((Sat ∪ Bad) ∪ Bad).card :=
      card_resLink_crossStars_le Bad (Sat ∪ Bad) (X u) a
    have h3 : ((Sat ∪ Bad) ∪ Bad).card ≤ ns + nb := by
      have h4 : (Sat ∪ Bad) ∪ Bad = Sat ∪ Bad := by
        ext z; simp only [Finset.mem_union]; tauto
      rw [h4]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add hsat hbad)
    have h5 := Finset.card_le_card hsplit
    have h6 := Finset.card_union_le (resLink (usedPairs X g₀ S) (X u) a) (resLink Forb (X u) a)
    omega
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ :=
    exists_pairing_of_twoSided_link_avoiding hDirac hgrid hnd hW'W hq hc hqc hu hXW' hXeven
      hadd hdel hUdeg hmargin
  refine ⟨p, hp1, hp2, hp3, fun a ha => (hp4 a ha).1, ?_, ?_, ?_⟩
  · -- no pair inside the protected level
    intro a ha
    by_contra hcon
    push_neg at hcon
    obtain ⟨haW'', hpaW''⟩ := hcon
    refine (hp4 a ha).2 (Finset.mem_union_right _ ?_)
    exact crossStars_mem (Finset.mem_inter.2 ⟨ha, haW''⟩)
      (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hp1 a ha, hpaW''⟩))
  · -- the pairs avoid the edges already used
    intro a ha hcon
    exact (hp4 a ha).2 (Finset.mem_union_left _ hcon)
  · -- the protected-level load stays under budget
    intro v _ hvX hpv
    by_contra hcon
    have hvSat : v ∈ Sat := Finset.mem_filter.2 ⟨hvX, hcon⟩
    have hpvBad : p v ∈ Bad := Finset.mem_inter.2 ⟨hp1 v hvX, hpv⟩
    refine (hp4 v hvX).2 (Finset.mem_union_right _ ?_)
    have : s(p v, v) ∈ Forb := crossStars_mem hpvBad (Finset.mem_union_left _ hvSat)
    rwa [Sym2.eq_swap] at this

end Ledger

/-- **The one-link residual.** -/
def GridPairingResidualStepTwoSided : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 100 → ∀ K : ℕ, 800 ≤ K → (8 : ℝ) / ε ≤ (K : ℝ) →
    ∃ n₃ : ℕ, ∀ (f : ℕ → ℝ) (n₂ : ℕ), n₃ ≤ n₂ →
      (∀ s : ℕ, n₂ ≤ s → 9 / 10 + ε / 2 ≤ f s ∧ f s ≤ 9 / 10 + 3 * ε / 4) →
      GridPairingStepClauseTwoSided ε f n₂ K

/-- **The sweep closes the gap between the two clauses.** -/
theorem gridPairingClauseTwoSided_of_step {ε : ℝ} (hε : 0 ≤ ε) {f : ℕ → ℝ} {n₂ K : ℕ}
    (h : GridPairingStepClauseTwoSided ε f n₂ K) : GridPairingClauseTwoSided ε f n₂ K := by
  intro V _ W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult
  exact exists_pairedLinkCore_of_step (by linarith)
    (h W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
      hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult)

/-- **The one-link residual implies the residual of §10 at the two-sided design.** -/
theorem gridPairingResidualTwoSided_of_step (h : GridPairingResidualStepTwoSided) :
    GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  obtain ⟨n₃, hmain⟩ := h ε hε hε' K hK hKε
  exact ⟨n₃, fun f n₂ hn₂ hwin => gridPairingClauseTwoSided_of_step hε.le (hmain f n₂ hn₂ hwin)⟩

/-- **The §10 interface, from the one-link residual at the two-sided design.** -/
theorem vortexReservoirEngineR4_of_gridPairingResidualStepTwoSided
    (h : GridPairingResidualStepTwoSided) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided (gridPairingResidualTwoSided_of_step h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
pairing demand at the two-sided grid design.** -/
theorem triangle_decomposition_of_inputs_and_gridPairingStepTwoSided
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRes : GridPairingResidualStepTwoSided) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_step hRes)

end BKLO
