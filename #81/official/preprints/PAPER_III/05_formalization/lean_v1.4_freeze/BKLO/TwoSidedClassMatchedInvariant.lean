/-
# AX2 §10 at the two-sided design, from **one class-matched link with an invariant of its own**.

`BKLO.TwoSidedClassMatchedPairing` (`BKLO/TwoSidedClassMatchedResidual.lean`) asks for one more
link to be paired for an *arbitrary* past `(S, g₀, Exc)` that merely satisfies the leftover budget
`BKLO.ExcLedgerSpread`, and against an *arbitrary* forbidden set `U` of small degree.  That demand
is false: `BKLO.not_twoSidedClassMatchedPairing` and `BKLO.not_twoSidedClassMatchedPairingRegime`
refute it, in the degenerate and in the intended regime.  A past sitting exactly at the budget
cannot afford one more leftover, while `U` may block the single class into which the class matching
sends a vertex — neither branch of the conclusion is then available.

The defect is the *quantification*, not the plan: a sweep gets to choose its own past.  The demand
below is the same one-link demand with the past described by an invariant `Inv` **of the prover's
own choosing**, which need only start at the empty sweep and imply the leftover budget.  This is
the class-matched form of the interface `BKLO.TwoSidedClassDirectedRule`
(`BKLO/TwoSidedClassLedger.lean`), and it is weaker than the refuted demand
(`twoSidedClassMatchedInvariantPairing_of_classMatchedPairing`), so nothing is assumed that the
earlier statement did not already assume.

* `BKLO.gridPairingClauseTwoSided_of_classMatchedInvariant`,
* `BKLO.gridPairingResidualTwoSided_of_classMatchedInvariant`,
* `BKLO.vortexReservoirEngineR4_of_twoSidedClassMatchedInvariant`,
* `BKLO.triangle_decomposition_of_inputs_and_twoSidedClassMatchedInvariant` — the AX2 half of
  Erdős #81 from the three classical inputs and this single demand.

**Caveat (added after the fact): the demand below is FALSE as well, so the main theorem stated
from it is vacuous.**  `BKLO.not_twoSidedClassMatchedInvariantPairing`
(`BKLO/TwoSidedClassMatchedInvariantObstruction.lean`) refutes it, by the counterexample of
`BKLO.not_twoSidedClassMatchedPairing` applied at the **empty** sweep — a past at which every
invariant of the demand holds, by the demand's own first clause `Inv ∅ (fun _ a => a) (fun _ => ∅)`.
Describing the past by an invariant therefore repairs nothing; the defect is the quantification over
the forbidden set `U`, which is allowed to block a whole class although no sweep ever produces such
a set.  The repaired demand is `BKLO.TwoSidedUsedClassMatchedInvariantPairing`
(`BKLO/TwoSidedUsedClassMatched.lean`), which ties `U` to the pairs the sweep has already used and
to the protected level (`BKLO.UsedForbidden`) and assumes the regime in which the demand is applied;
it yields the same AX2 main theorem
(`BKLO.triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedInvariant`).

Nothing below has been changed: the statements are kept exactly as they were.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassMatchedResidual

open Finset

namespace BKLO

/-- **The one-link class-matched pairing demand, with an invariant of the sweep.**  At a two-sided
grid design there is a class matching `(ρ, σ)` with small fibres, together with an invariant `Inv`
of the sweeps already performed, such that

* `Inv` holds at the empty sweep,
* `Inv` implies the leftover budget `BKLO.ExcLedgerSpread`,
* one more link can always be paired up — avoiding a forbidden edge set of small degree inside the
  link, by edges of `F`, following the matching outside a set of leftovers — maintaining both the
  class-matched discipline and `Inv`.

Unlike `BKLO.TwoSidedClassMatchedPairing`, the past is *not* an arbitrary triple satisfying the
budget: it is whatever `Inv` describes.  That is what a sweep can actually deliver, and the sweep
engine `BKLO.exists_pairedLinkCore_of_step_invariant` asks for nothing more. -/
def TwoSidedClassMatchedInvariantPairing : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ} (X : V → Finset V),
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    3 * q ≤ 4 * c →
    ∃ (ρ σ : V → ℕ → ℕ) (Inv : Finset V → (V → V → V) → (V → Finset V) → Prop),
      (∀ w β, ρ w β < gridSize ε K) ∧ (∀ w α, σ w α < gridSize ε K) ∧
      ClassMatchingFibres ε K W W' x y ρ σ ∧
      Inv (∅ : Finset V) (fun _ a => a) (fun _ => ∅) ∧
      (∀ S g Exc, Inv S g Exc → ExcLedgerSpread ε K W' C g S Exc) ∧
      ∀ (S : Finset V) (g₀ : V → V → V) (Exc : V → Finset V) (u : V) (n m : ℕ)
        (U : Finset (Sym2 V)),
        u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
        (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
        (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
        12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
        S ⊆ W \ W' → u ∉ S →
        (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
        IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g₀ Exc →
        Inv S g₀ Exc →
        ∃ (p : V → V) (e : Finset V),
          (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
          (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
          IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ (insert u S)
            (Function.update g₀ u p) (Function.update Exc u e) ∧
          Inv (insert u S) (Function.update g₀ u p) (Function.update Exc u e)

/-- The demand with an invariant is **weaker** than the refuted demand
`BKLO.TwoSidedClassMatchedPairing`: take for the invariant the leftover budget itself. -/
theorem twoSidedClassMatchedInvariantPairing_of_classMatchedPairing
    (hpair : TwoSidedClassMatchedPairing) : TwoSidedClassMatchedInvariantPairing := by
  intro V _ ε K W W' W'' F R C x y q c X hgrid hnd hW'W hq hc hqc
  obtain ⟨ρ, σ, hρlt, hσlt, hfib, hstep⟩ := hpair X hgrid hnd hW'W hq hc hqc
  refine ⟨ρ, σ, fun S g Exc => ExcLedgerSpread ε K W' C g S Exc, hρlt, hσlt, hfib, ?_, ?_, ?_⟩
  · intro a _ P _ Q _
    simp [excLoad]
  · exact fun S g Exc h => h
  · intro S g₀ Exc u n m U hu hXu hXeven hadd hdel hUdeg hmargin hSD huS hmaps hinv hsweep hInv
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven hadd hdel hUdeg hmargin hSD huS hmaps hinv hsweep hInv
    exact ⟨p, e, h1, h2, h3, h4, h5, h6⟩

/-- **The pairing clause at the two-sided design, from the one-link class-matched pairing with an
invariant.** -/
theorem gridPairingClauseTwoSided_of_classMatchedInvariant
    (hpair : TwoSidedClassMatchedInvariantPairing)
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
  -- the class matching and the invariant supplied by the demand
  obtain ⟨ρ, σ, Inv, hρlt, hσlt, hfib, hInv0, hInvSpread, hstep⟩ :=
    hpair X hgrid hnd hW'W hq hc hqc
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
  have hJstep : IsSpreadStep ε K W W' F R X c J := by
    intro S g₀ u n m U hu hXu hXeven' hadd hdel hUdeg hmargin hSD huS hmaps hinv hJ
    obtain ⟨Exc, hsweep, hInv⟩ := hJ.2
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven' hadd hdel hUdeg hmargin hSD huS hmaps hinv
        hsweep hInv
    exact ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, Function.update Exc u e, h5, h6⟩
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_rule hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the two-sided design, from the one-link class-matched
pairing with an invariant.** -/
theorem gridPairingResidualTwoSided_of_classMatchedInvariant
    (hpair : TwoSidedClassMatchedInvariantPairing) : GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊ (5120 * (gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSided_of_classMatchedInvariant hpair hε hε'
      (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **The §10 interface, from the one-link class-matched pairing with an invariant.** -/
theorem vortexReservoirEngineR4_of_twoSidedClassMatchedInvariant
    (hpair : TwoSidedClassMatchedInvariantPairing) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided
    (gridPairingResidualTwoSided_of_classMatchedInvariant hpair)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
class-matched pairing demand with an invariant of the sweep.**  This is the form of the demand that
survives `BKLO.not_twoSidedClassMatchedPairing`: the past is the sweep's own, not an arbitrary
triple at the leftover budget. -/
theorem triangle_decomposition_of_inputs_and_twoSidedClassMatchedInvariant
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hpair : TwoSidedClassMatchedInvariantPairing) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_classMatchedInvariant hpair)

end BKLO
