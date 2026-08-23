/-
# AX2 §10 at the two-sided design, from **one class-matched link**.

This is the reduction the whole two-sided development aims at.  The sweep engine
(`BKLO.exists_pairedLinkCore_of_step_invariant`) is run with the invariant

> the links already processed follow a fixed class matching `(ρ, σ)` of the design, outside a set
> of leftovers whose load on every cell is small,

and `BKLO.ledgerSpread_of_classMatchedSweep` turns that invariant into the ledger bound
`BKLO.LedgerSpread`, which is all that `BKLO.twoSided_step_of_spread` needs.  What is left is the
single deterministic one-link demand `BKLO.TwoSidedClassMatchedPairing`:

> at a two-sided grid design there is a class matching with small fibres such that one more link
> can always be paired up — avoiding the used edges, by edges of `F` — following that matching
> outside a set of leftovers whose load stays spread.

The freedom the demand may use is exactly the freedom the design leaves: a class matching whose
target varies inside a cell (a shift balanced on every cell exists,
`BKLO.exists_cell_balanced_shift`), a bipartite matching between two classes of a region (their
half-degree hypothesis holds by `IsGridTwoSidedReservoir.classBalancedSharp` and `linkClassGe`, and
`BKLO.exists_matching_of_half_degree` turns it into a matching), and a least-loaded choice of the
leftovers, of which there are at most as many per link as the perturbation allows.

* `BKLO.gridPairingClauseTwoSided_of_classMatchedPairing`,
* `BKLO.gridPairingResidualTwoSided_of_classMatchedPairing`,
* `BKLO.vortexReservoirEngineR4_of_twoSidedClassMatchedPairing`,
* `BKLO.triangle_decomposition_of_inputs_and_twoSidedClassMatchedPairing` — the AX2 half of
  Erdős #81 from the three classical inputs and this single demand.

**Caveat (added after the fact): the demand below is FALSE, so the main theorem stated from it is
vacuous.**  `BKLO.not_twoSidedClassMatchedPairing`
(`BKLO/TwoSidedClassMatchedObstruction.lean`) refutes it at an explicit two-sided grid design over
the naturals, and `BKLO.not_twoSidedClassMatchedPairingRegime`
(`BKLO/TwoSidedClassMatchedRegime.lean`) refutes it again with the four hypotheses of
`gridPairingClauseTwoSided_of_classMatchedPairing` (`0 < ε`, `ε ≤ 1/100`, `2 ≤ K`, `512 ≤ t`)
added, so the failure is not an artifact of a degenerate regime.  The reason is the
quantification, not the plan: the demand must serve an *arbitrary* past `(S, g₀, Exc)` that merely
sits at the leftover budget `BKLO.ExcLedgerSpread`, and an *arbitrary* forbidden set `U` whose
degree bound `12n + 8m ≤ (2h-1)c` is far larger than a class.  Choose a past that has already
exhausted the leftover budget at one vertex `a`, and a `U` that blocks the one class into which the
class matching may send `a`: neither branch of the conclusion is then available.

The repaired demand is `BKLO.TwoSidedClassMatchedInvariantPairing`
(`BKLO/TwoSidedClassMatchedInvariant.lean`): the same one-link demand, but with the past described
by an invariant that the prover *chooses* (as in `BKLO.TwoSidedClassDirectedRule`).  It is weaker
than the demand below (`twoSidedClassMatchedInvariantPairing_of_classMatchedPairing`), it is not
refuted by the counterexamples above, and it yields the same AX2 main theorem
(`BKLO.triangle_decomposition_of_inputs_and_twoSidedClassMatchedInvariant`).

Nothing below has been changed: the statements are kept exactly as they were.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassMatched
import BKLO.BipartiteMatching

open Finset

namespace BKLO

/-- **The one-link class-matched pairing demand.**  At a two-sided grid design there is a class
matching `(ρ, σ)` with small fibres such that one more link can always be paired up, avoiding a
forbidden edge set of small degree inside the link, following the matching outside a set of
leftovers, and keeping the load of the leftovers on every cell inside `h t / 256`. -/
def TwoSidedClassMatchedPairing : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ} (X : V → Finset V),
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    3 * q ≤ 4 * c →
    ∃ ρ σ : V → ℕ → ℕ,
      (∀ w β, ρ w β < gridSize ε K) ∧ (∀ w α, σ w α < gridSize ε K) ∧
      ClassMatchingFibres ε K W W' x y ρ σ ∧
      ∀ (S : Finset V) (g₀ : V → V → V) (Exc : V → Finset V) (u : V) (n m : ℕ)
        (U : Finset (Sym2 V)),
        u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
        (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
        (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
        12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
        S ⊆ W \ W' → u ∉ S →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
        IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g₀ Exc →
        ExcLedgerSpread ε K W' C g₀ S Exc →
        ∃ (p : V → V) (e : Finset V),
          (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
          (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
          IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ (insert u S)
            (Function.update g₀ u p) (Function.update Exc u e) ∧
          ExcLedgerSpread ε K W' C (Function.update g₀ u p) (insert u S)
            (Function.update Exc u e)

/-- **The pairing clause at the two-sided design, from the one-link class-matched pairing.** -/
theorem gridPairingClauseTwoSided_of_classMatchedPairing (hpair : TwoSidedClassMatchedPairing)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hK : 2 ≤ K) {f : ℕ → ℝ} {n₂ : ℕ}
    (hn₂ : (16 : ℝ) / ε ≤ (n₂ : ℝ))
    (hn₂size : 5120 * (gridSize ε K * gridSize ε K) * (K * K) ≤ n₂) :
    GridPairingClauseTwoSided ε f n₂ K := by
  intro V _ W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hKpos : 0 < K := by omega
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFW he)).2
  have hM : W''.Nonempty → (16 : ℝ) / ε ≤ (W''.card : ℝ) := by
    intro hne
    have h1 : (n₂ : ℝ) ≤ (W''.card : ℝ) := by exact_mod_cast hbig hne
    linarith
  obtain ⟨q, c, hq, hc, hqc, -⟩ := hgrid.exists_sizes
  have hW'ge : 5120 * (h * h) ≤ W'.card := by
    have h1 : (K * K) * (5120 * (h * h)) ≤ (K * K) * W'.card := by
      calc (K * K) * (5120 * (h * h)) = 5120 * (h * h) * (K * K) := by ring
        _ ≤ n₂ := hn₂size
        _ ≤ W.card := hn₂W
        _ ≤ K * K * W'.card := hW'K
    exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hKpos hKpos)
  have hbig512 : 512 ≤ gridClassSize ε K W'.card := by
    rw [gridClassSize]
    refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
    calc 512 * (10 * gridSize ε K * gridSize ε K) = 5120 * (h * h) := by rw [hhdef]; ring
      _ ≤ W'.card := hW'ge
  -- the class matching supplied by the demand
  obtain ⟨ρ, σ, hρlt, hσlt, hfib, hstep⟩ := hpair X hgrid hnd hW'W hq hc hqc
  -- the invariant of the sweep
  set J : Finset V → (V → V → V) → Prop := fun S g =>
    S ⊆ W \ W' ∧ ∃ Exc : V → Finset V,
      IsClassMatchedSweep h C R W' X x y ρ σ S g Exc ∧ ExcLedgerSpread ε K W' C g S Exc with hJdef
  have hJ0 : J (∅ : Finset V) (fun _ a => a) := by
    refine ⟨Finset.empty_subset _, fun _ => ∅, ?_, ?_⟩
    · intro a α β _ _ _ w hw
      exact absurd hw (Finset.notMem_empty w)
    · intro a _ P _ Q _
      simp [excLoad]
  have hJled : ∀ S g, J S g → LedgerSpread ε K W' C X x y S g := by
    rintro S g ⟨hSD, Exc, hsweep, hspread⟩
    exact ledgerSpread_of_classMatchedSweep hgrid hε hε' hKpos hbig512 hρlt hσlt hfib hSD
      hXmult hsweep hspread
  have hJstep : IsSpreadStep ε K W W' F R X c J := by
    intro S g₀ u n m U hu hXu hXeven' hadd hdel hUdeg hmargin hSD huS hmaps hinv hJ
    obtain ⟨Exc, hsweep, hspread⟩ := hJ.2
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven' hadd hdel hUdeg hmargin hSD huS hmaps hinv
        hsweep hspread
    exact ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, Function.update Exc u e, h5, h6⟩
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_rule hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the two-sided design, from the one-link class-matched
pairing.** -/
theorem gridPairingResidualTwoSided_of_classMatchedPairing
    (hpair : TwoSidedClassMatchedPairing) : GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊ (5120 * (gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSided_of_classMatchedPairing hpair hε hε'
      (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **The §10 interface, from the one-link class-matched pairing.** -/
theorem vortexReservoirEngineR4_of_twoSidedClassMatchedPairing
    (hpair : TwoSidedClassMatchedPairing) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided
    (gridPairingResidualTwoSided_of_classMatchedPairing hpair)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
class-matched pairing demand at the two-sided grid design.** -/
theorem triangle_decomposition_of_inputs_and_twoSidedClassMatchedPairing
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hpair : TwoSidedClassMatchedPairing) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_classMatchedPairing hpair)

end BKLO
