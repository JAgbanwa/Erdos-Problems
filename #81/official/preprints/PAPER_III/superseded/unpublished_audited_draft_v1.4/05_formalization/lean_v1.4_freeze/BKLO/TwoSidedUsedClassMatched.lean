/-
# AX2 §10 at the two-sided design, from one class-matched link **whose forbidden set is the
sweep's own**.

`BKLO.TwoSidedClassMatchedPairing` (`BKLO/TwoSidedClassMatchedResidual.lean`) and its repair
`BKLO.TwoSidedClassMatchedInvariantPairing` (`BKLO/TwoSidedClassMatchedInvariant.lean`) are both
**false**:

* `BKLO.not_twoSidedClassMatchedPairing`, `BKLO.not_twoSidedClassMatchedPairingRegime` — the past
  may be an arbitrary triple sitting at the leftover budget;
* `BKLO.not_twoSidedClassMatchedInvariantPairing`
  (`BKLO/TwoSidedClassMatchedInvariantObstruction.lean`) — describing the past by an invariant of
  the prover's own choosing does *not* repair the demand, because the counterexample needs no past
  at all: it applies the one-link step at the **empty** sweep, where every invariant of the demand
  holds by its own first clause.

What is wrong in both is the quantification over the forbidden set `U`.  The demand lets `U` be an
arbitrary edge set of degree `m` with `12 n + 8 m ≤ (2h-1) c` inside the link, and `m` may then be
as large as a whole class — enough to block, at a vertex `a` of the row part, the single class into
which a class matching may send `a`.  No sweep ever meets such a `U`: the `U` that
`BKLO.twoSided_step_of_rule` hands to the rule is

```
U = usedPairs X g₀ S ∪ crossStars (X u ∩ W'') (fun _ => Sat ∪ (X u ∩ W''))
```

— the pairs the sweep has **already used**, whose distribution over the classes the sweep itself
controls through its ledger, together with edges that touch the protected level `W''`.  This file
states the one-link demand for that `U`, and only for it:

* `BKLO.UsedForbidden` — every edge of `U` is a pair already used by the sweep or touches `W''`;
* `BKLO.IsSpreadStepUsed`, `BKLO.twoSided_step_of_ruleUsed` — the interface and the one-link step
  of `BKLO/TwoSidedClassLedger.lean` with that hypothesis added; the proof is the one of
  `BKLO.twoSided_step_of_rule`, which supplies the hypothesis for its own `U`;
* `BKLO.TwoSidedUsedClassMatchedInvariantPairing` — the one-link class-matched demand with an
  invariant of the sweep, with `U` tied to the sweep, and in the regime in which it is used
  (`0 < ε`, `ε ≤ 1/100`, `2 ≤ K`, `512 ≤ t`; the regime is *needed*: at a design with `h t < 256`
  the leftover budget `h t / 256` is `0`, so a perturbed link whose classes cannot be matched
  size-for-size refutes any leftover-free demand);
* `BKLO.gridPairingClauseTwoSided_of_usedClassMatchedInvariant`,
  `BKLO.gridPairingResidualTwoSided_of_usedClassMatchedInvariant`,
  `BKLO.vortexReservoirEngineR4_of_twoSidedUsedClassMatchedInvariant`,
  `BKLO.triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedInvariant` — the AX2 half of
  Erdős #81 from the three classical inputs and this single demand.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassMatchedInvariant

open Finset

namespace BKLO

/-- **The forbidden set of a real sweep step.**  Every forbidden edge is either a pair the sweep
has already used, or an edge touching the protected level `W''`.  This is exactly what the `U` of
`BKLO.twoSided_step_of_rule` satisfies, and it is the hypothesis whose absence refutes
`BKLO.TwoSidedClassMatchedPairing` and `BKLO.TwoSidedClassMatchedInvariantPairing`. -/
def UsedForbidden {V : Type} [DecidableEq V] (X : V → Finset V) (g₀ : V → V → V)
    (S W'' : Finset V) (U : Finset (Sym2 V)) : Prop :=
  ∀ a b : V, s(a, b) ∈ U → s(a, b) ∈ usedPairs X g₀ S ∨ a ∈ W'' ∨ b ∈ W''

/-- **One step of a spread discipline, against the sweep's own forbidden edges.**  As
`BKLO.IsSpreadStep`, with the forbidden set `U` required to consist of used pairs and edges meeting
the protected level. -/
def IsSpreadStepUsed {V : Type} [DecidableEq V] (ε : ℝ) (K : ℕ) (W W' W'' : Finset V)
    (F R : Finset (Sym2 V)) (X : V → Finset V) (c : ℕ)
    (J : Finset V → (V → V → V) → Prop) : Prop :=
  ∀ (S : Finset V) (g₀ : V → V → V) (u : V) (n m : ℕ) (U : Finset (Sym2 V)),
    u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
    (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
    (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
    UsedForbidden X g₀ S W'' U →
    12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
    S ⊆ W \ W' → u ∉ S →
    (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
    J S g₀ →
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
      (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      J (insert u S) (Function.update g₀ u p)

section Step

variable {V : Type} [DecidableEq V] {X : V → Finset V}

/-- **One more link is paired up, from a spread discipline against the sweep's own forbidden
edges.**  Word for word `BKLO.twoSided_step_of_rule`, whose concrete forbidden set does satisfy
`BKLO.UsedForbidden`. -/
theorem twoSided_step_of_ruleUsed
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q c : ℕ} {J : Finset V → (V → V → V) → Prop}
    (hJled : ∀ S g, J S g → LedgerSpread ε K W' C X x y S g)
    (hJstep : IsSpreadStepUsed ε K W W' W'' F R X c J)
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    (hqc : 3 * q ≤ 4 * c) (hW''W' : W'' ⊆ W')
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (hM : W''.Nonempty → (16 : ℝ) / ε ≤ (W''.card : ℝ))
    {u : V} (hu : u ∈ W \ W') (hXW' : X u ⊆ W') (hXeven : Even (X u).card)
    (hadd : ((X u \ resLink R W' u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hdel : ((resLink R W' u \ X u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hXmult : ∀ a ∈ W', (((W \ W').filter (fun v => a ∈ X v \ resLink R W' v)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    {S : Finset V} (hSD : S ⊆ W \ W') (huS : u ∉ S) {g₀ : V → V → V}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
    (hJ : J S g₀) :
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
      (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
      (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
      (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
      (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
        ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
          ≤ ε / 8 * (W''.card : ℝ)) ∧
      J (insert u S) (Function.update g₀ u p) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hK0 : 0 < K := by omega
  have hhpos : 0 < h := gridSize_pos ε K
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hK0.ne' hK0.ne')
  have hh21 : 21 ≤ h := by linarith only [hwide, hKK]
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
  have hn : 4 * n ≤ t := twoSided_perturbation_quarter hgrid hK0 hnr
  -- the competition of `u`'s own cell
  set Ncell : ℕ := ((W \ W').filter (fun w => x w = x u ∧ y w = y u)).card with hNdef
  have hcell : 64 * Ncell ≤ h * t := twoSided_cell_fibre_budget hgrid hε hε' hK0 (x u) (y u)
  -- the ledger and the saturated vertices
  set SP : ℕ := h * t / 16 with hSPdef
  have hSP : 16 * SP ≤ h * t := by
    have := Nat.div_mul_le_self (h * t) 16
    omega
  set ns : ℕ := h * t / 64 with hnsdef
  have hns : 64 * ns ≤ h * t := by
    have := Nat.div_mul_le_self (h * t) 64
    omega
  -- the forbidden edges of the protected level
  set Bad : Finset V := X u ∩ W'' with hBaddef
  set Sat : Finset V := (X u).filter (fun v =>
    ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
      ≤ ε / 8 * (W''.card : ℝ))) with hSatdef
  set Forb : Finset (Sym2 V) := crossStars Bad (fun _ => Sat ∪ Bad) with hForbdef
  set U : Finset (Sym2 V) := usedPairs X g₀ S ∪ Forb with hUdef
  have hbad : Bad.card ≤ n := card_inter_protected_le hgrid hu (le_max_left _ _)
  have hforb : ∀ a ∈ X u, (resLink Forb (X u) a).card ≤ ns + n := by
    intro a _
    by_cases hW''ne : W''.Nonempty
    · have hsat : Sat.card ≤ ns := by
        have hkey := twoSided_card_saturated_le hgrid hε hK hSD hmaps hinv hXmult hW''W'
          (hM hW''ne) (X u)
        rw [← hhdef, ← htdef, ← hSatdef] at hkey
        omega
      have h1 : (resLink Forb (X u) a).card ≤ ((Sat ∪ Bad) ∪ Bad).card :=
        card_resLink_crossStars_le Bad (Sat ∪ Bad) (X u) a
      have h2 : (Sat ∪ Bad) ∪ Bad = Sat ∪ Bad := by
        ext z; simp only [Finset.mem_union]; tauto
      rw [h2] at h1
      have h3 : (Sat ∪ Bad).card ≤ Sat.card + Bad.card := Finset.card_union_le _ _
      omega
    · have hempty : W'' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hW''ne
      have hBad0 : Bad = ∅ := by rw [hBaddef, hempty, Finset.inter_empty]
      have hForb0 : Forb = ∅ := by
        rw [hForbdef, hBad0]
        simp [crossStars]
      simp [hForb0, resLink]
  -- the used degree, from the ledger
  have hlink : resLink R W' u ⊆ gridRegion h C (x u) (y u) := fun z hz =>
    (Finset.mem_inter.1 (hgrid.linkSubset u hu hz)).2
  have hused : ∀ a ∈ X u, (resLink (usedPairs X g₀ S) (X u) a).card ≤ Ncell + SP + n := by
    intro a ha
    have h1 := card_resLink_usedPairs_region_split (D := W \ W') hmaps hinv hSD hlink (a := a)
    have h2 : regionLoad h C X g₀ S x y a (x u) (y u) ≤ SP := by
      have := hJled S g₀ hJ a (hXW' ha) (x u) (hgrid.rowLt u hu) (y u) (hgrid.colLt u hu)
      rw [← hhdef, ← htdef] at this
      exact this
    have h3 : (X u \ resLink R W' u).card ≤ n := le_max_left _ _
    omega
  have hUdeg : ∀ a ∈ X u, (resLink U (X u) a).card ≤ (Ncell + SP + n) + (ns + n) := by
    intro a ha
    have hsplit : resLink U (X u) a
        ⊆ resLink (usedPairs X g₀ S) (X u) a ∪ resLink Forb (X u) a := by
      intro z hz
      obtain ⟨hzX, hzU⟩ := mem_resLink.1 hz
      rcases Finset.mem_union.1 hzU with h1 | h1
      · exact Finset.mem_union_left _ (mem_resLink.2 ⟨hzX, h1⟩)
      · exact Finset.mem_union_right _ (mem_resLink.2 ⟨hzX, h1⟩)
    have h1 := hused a ha
    have h2 := hforb a ha
    have h3 := Finset.card_le_card hsplit
    have h4 := Finset.card_union_le (resLink (usedPairs X g₀ S) (X u) a) (resLink Forb (X u) a)
    omega
  have hmargin : 12 * n + 8 * ((Ncell + SP + n) + (ns + n)) ≤ (2 * h - 1) * c :=
    twoSided_margin_ledger hh21 hn hcell hSP hns (le_refl n) (le_refl _) hq3 hqc
  -- the rule
  have hUused : UsedForbidden X g₀ S W'' U := by
    intro a b hab
    rcases Finset.mem_union.1 hab with h1 | h1
    · exact Or.inl h1
    · obtain ⟨z, hz, w, -, heq⟩ := mem_crossStars.1 h1
      have hzW'' : z ∈ W'' := (Finset.mem_inter.1 hz).2
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h2, -⟩ | ⟨-, h2⟩
      · exact Or.inr (Or.inl (h2 ▸ hzW''))
      · exact Or.inr (Or.inr (h2 ▸ hzW''))
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5⟩ :=
    hJstep S g₀ u n ((Ncell + SP + n) + (ns + n)) U hu hXW' hXeven (le_max_left _ _)
      (le_max_right _ _) hUdeg hUused hmargin hSD huS hmaps hinv hJ
  refine ⟨p, hp1, hp2, hp3, fun a ha => (hp4 a ha).1, ?_, ?_, ?_, hp5⟩
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
    have hmem : s(p v, v) ∈ Forb := crossStars_mem hpvBad (Finset.mem_union_left _ hvSat)
    rwa [Sym2.eq_swap] at hmem
end Step

/-! ### The demand, in the regime in which it is used -/

/-- **The one-link class-matched pairing demand, with an invariant of the sweep, against the
sweep's own forbidden edges, in the regime in which it is used.**

At a two-sided grid design with `0 < ε ≤ 1/100`, `2 ≤ K` and classes of at least `512` places
there is a class matching `(ρ, σ)` with small fibres, together with an invariant `Inv` of the
sweeps already performed, such that

* `Inv` holds at the empty sweep,
* `Inv` implies the leftover budget `BKLO.ExcLedgerSpread`,
* one more link can always be paired up — avoiding the edges the sweep has already used and the
  edges touching the protected level, by edges of `F`, following the matching outside a set of
  leftovers — maintaining both the class-matched discipline and `Inv`.

This is `BKLO.TwoSidedClassMatchedInvariantPairing` with the two defects that refute it removed:
the forbidden set is the sweep's own (`BKLO.UsedForbidden`), and the regime hypotheses of
`BKLO.gridPairingClauseTwoSided_of_classMatchedInvariant` are available — both of them are used by
the counterexamples, and both are available at the only place the demand is ever applied. -/
def TwoSidedUsedClassMatchedInvariantPairing : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ} (X : V → Finset V),
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    3 * q ≤ 4 * c →
    0 < ε → ε ≤ 1 / 100 → 2 ≤ K → 512 ≤ gridClassSize ε K W'.card →
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
        UsedForbidden X g₀ S W'' U →
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

/-- **The pairing clause at the two-sided design, from the one-link class-matched pairing with an
invariant against the sweep's own forbidden edges.** -/
theorem gridPairingClauseTwoSided_of_usedClassMatchedInvariant
    (hpair : TwoSidedUsedClassMatchedInvariantPairing)
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
    hpair X hgrid hnd hW'W hq hc hqc hε hε' hK hbig512
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
  have hJstep : IsSpreadStepUsed ε K W W' W'' F R X c J := by
    intro S g₀ u n m U hu hXu hXeven' hadd hdel hUdeg hUused hmargin hSD huS hmaps hinv hJ
    obtain ⟨Exc, hsweep, hInv⟩ := hJ.2
    obtain ⟨p, e, h1, h2, h3, h4, h5, h6⟩ :=
      hstep S g₀ Exc u n m U hu hXu hXeven' hadd hdel hUdeg hUused hmargin hSD huS hmaps hinv
        hsweep hInv
    exact ⟨p, h1, h2, h3, h4, Finset.insert_subset hu hSD, Function.update Exc u e, h5, h6⟩
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    twoSided_step_of_ruleUsed hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, k1, k2, k3, k4, k5, k6, k7, k8⟩

/-- **The remaining residual of AX2 §10 at the two-sided design, from the one-link class-matched
pairing with an invariant against the sweep's own forbidden edges.** -/
theorem gridPairingResidualTwoSided_of_usedClassMatchedInvariant
    (hpair : TwoSidedUsedClassMatchedInvariantPairing) : GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  refine ⟨max ⌈(16 : ℝ) / ε⌉₊ (5120 * (gridSize ε K * gridSize ε K) * (K * K)),
    fun f n₂ hn₂ _hwin => gridPairingClauseTwoSided_of_usedClassMatchedInvariant hpair hε hε'
      (by omega) ?_ ?_⟩
  · have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hn₂
    linarith
  · exact le_trans (le_max_right _ _) hn₂

/-- **The §10 interface, from the one-link class-matched pairing with an invariant against the
sweep's own forbidden edges.** -/
theorem vortexReservoirEngineR4_of_twoSidedUsedClassMatchedInvariant
    (hpair : TwoSidedUsedClassMatchedInvariantPairing) : VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided
    (gridPairingResidualTwoSided_of_usedClassMatchedInvariant hpair)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the one-link
class-matched pairing demand with an invariant of the sweep against the sweep's own forbidden
edges.**  This is the form of the demand that survives every counterexample known here:
`BKLO.not_twoSidedClassMatchedPairing`, `BKLO.not_twoSidedClassMatchedPairingRegime` and
`BKLO.not_twoSidedClassMatchedInvariantPairing` all need a forbidden set `U` that no sweep
produces. -/
theorem triangle_decomposition_of_inputs_and_twoSidedUsedClassMatchedInvariant
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hpair : TwoSidedUsedClassMatchedInvariantPairing) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_usedClassMatchedInvariant hpair)

end BKLO
