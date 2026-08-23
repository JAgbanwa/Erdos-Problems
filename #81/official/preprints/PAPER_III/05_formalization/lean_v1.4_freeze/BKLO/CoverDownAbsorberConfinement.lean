/-
# The absorber-confinement route to the repaired cover-down step.

This file develops the *absorber-confinement* route to `BKLO.CoverDownK3Div`
(`BKLO/CoverDownRepaired.lean`) and measures exactly what it costs.

The route, at one vortex step `W ⊇ W' ⊇ W''` with `F` dense and triangle-divisible:

1. **Reserve, then cover the shell.**  Work in the *shell* `F \ cliqueEdges W'` — the edges of `F`
   that meet `W \ W'`.  It is triangle-divisible (`BKLO.triDivisible_shell`) and, because
   `|W'| ≤ |W| / K`, it still has minimum degree `≥ (9/10)|W|` after a sparse reservation `R` is
   removed.  The dense max-degree nibble (`BKLO.nibbleMaxDeg_of_inputs_dense`) covers all of it
   except a leftover `L` of maximum degree `≤ η|W|`.  The nibble uses **no** edge inside `W'`, so
   it costs nothing against the `γ|W'|` budget and never touches `F ∩ cliqueEdges W''`.
2. **Absorb the remainder.**  The remainder `R ∪ L` — sparse, triangle-divisible, spanning `W` — is
   covered exactly by triangles that use, besides `R ∪ L` itself, only edges inside `W'` and none
   inside `W''`.  This is the interface `BKLO.ShellAbsorption` isolated below.

`BKLO.coverDownK3Div_of_denseNibble_shellAbsorption` proves, `sorry`-free, that these two
ingredients give `CoverDownK3Div`.

What `ShellAbsorption` is, precisely, is a **flexible reservation**: the reserved set `R` is chosen
*before* the leftover `L` (the quantifier order is `∃ R, ∀ L`), and `R` must serve *every* admissible
leftover.  That order is forced, not stylistic: `BKLO/CoverDownConfinementLimits.lean` shows
`sorry`-free that after the nibble no unused edge is left to build an absorber from, so a per-set
absorber such as `BKLO.sparseAbsorberExistence_nine` (`∀ H, ∃ A`) cannot be invoked at that point.

Everything here is `sorry`-free.  Nothing here asserts `ShellAbsorption`, and nothing here asserts
`CoverDownK3Div`.
-/
import BKLO.CoverDownRepaired
import BKLO.NibbleMaxDegDense
import BKLO.Reservoir
import BKLO.CoverDownObstruction

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The shell of a vortex step -/

/-- **The shell is triangle-divisible.**  If `F` and the graph it induces on `W'` are
triangle-divisible, so is the set of edges of `F` meeting `W \ W'`. -/
theorem triDivisible_shell {W' : Finset V} {F : Finset (Sym2 V)} (hF : TriDivisible F)
    (hF' : TriDivisible (F ∩ cliqueEdges W')) : TriDivisible (F \ cliqueEdges W') := by
  classical
  have h : F \ cliqueEdges W' = F \ (F ∩ cliqueEdges W') := by
    ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [h]
  exact TriDivisible.sdiff Finset.inter_subset_left hF hF'

/-! ### The missing ingredient: flexible, reserved absorption of the shell remainder -/

/-- **Flexible shell absorption at one vortex step.**

Given the data of one repaired cover-down step (the same hypotheses as `BKLO.CoverDownK3Div`, with
the ratio `K` supplied by the caller), there is a *reservation* `R` inside the shell
`F \ cliqueEdges W'`, of maximum degree at most `ρ|W|`, such that **every** sparse
triangle-divisible remainder `R ∪ L` left over inside the shell after `R` is removed can be covered
exactly by an edge-disjoint family of triangles of `F` which

* uses no shell edge other than those of `R ∪ L` (so it is compatible with any nibble that produced
  `L`),
* uses no edge inside `W''`, and
* uses at most `γ|W'|` edges inside `W'` at each vertex.

The quantifier order `∃ R, ∀ L` is the *flexibility* of the absorber: `R` is reserved before the
leftover is known.  This is the ingredient the absorber-confinement route needs and which the
per-set absorber of `BKLO.sparseAbsorberExistence_nine` (`∀ H, ∃ A`) does not supply; see
`BKLO/CoverDownConfinementLimits.lean`.

Nothing in this development asserts `ShellAbsorption`. -/
def ShellAbsorption : Prop :=
  ∀ (c γ ρ : ℝ) (K : ℕ), 9 / 10 < c → 0 < γ → 0 < ρ → 2 ≤ K →
    ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧
      ∀ {V : Type} [DecidableEq V] (W W' W'' : Finset V) (F : Finset (Sym2 V)),
        n₀ ≤ W.card → W' ⊆ W → W'' ⊆ W' →
        K * W'.card ≤ W.card → W.card ≤ K * K * W'.card → K * W''.card ≤ W'.card →
        F ⊆ cliqueEdges W → TriDivisible F →
        TriDivisible (F ∩ cliqueEdges W') → TriDivisible (F ∩ cliqueEdges W'') →
        (∀ v ∈ W, c * (W.card : ℝ) ≤ (edeg F v : ℝ)) →
        ∃ R : Finset (Sym2 V), R ⊆ F \ cliqueEdges W' ∧
          (∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ)) ∧
          ∀ L : Finset (Sym2 V), L ⊆ (F \ cliqueEdges W') \ R →
            (∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) →
            TriDivisible (R ∪ L) →
            ∃ Q : Finset (Finset V), TriFamilyIn F Q ∧
              R ∪ L ⊆ famEdges Q ∧
              famEdges Q ⊆ (R ∪ L) ∪ (cliqueEdges W' \ cliqueEdges W'') ∧
              ∀ v ∈ W', (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) ≤ γ * (W'.card : ℝ)

/-- **The absorption step is handed a sparse graph.**  Whatever the reservation `R` of degree at
most `ρ|W|` and the nibble leftover `L` of degree at most `η|W|`, the remainder the absorber has to
cover has maximum degree at most `(ρ + η)|W|`.  So the route does drop the *density* (the input `F`
has minimum degree `≥ c|W|` with `c > 9/10`); what it does not drop is the *scale*: the remainder
still spans `W`. -/
theorem shellAbsorption_input_sparse {W : Finset V} {R L : Finset (Sym2 V)} {ρ η : ℝ}
    (hR : ∀ v : V, (edeg R v : ℝ) ≤ ρ * (W.card : ℝ))
    (hL : ∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ)) (v : V) :
    (edeg (R ∪ L) v : ℝ) ≤ (ρ + η) * (W.card : ℝ) := by
  have h := edeg_union_le R L v
  have h' : (edeg (R ∪ L) v : ℝ) ≤ (edeg R v : ℝ) + (edeg L v : ℝ) := by exact_mod_cast h
  have := hR v
  have := hL v
  nlinarith [hR v, hL v]

/-! ### The route -/

/-- **The absorber-confinement route.**  The dense max-degree nibble (fed by Dross's threshold) and
flexible shell absorption give the repaired cover-down step `BKLO.CoverDownK3Div`.

The proof runs the two steps described at the head of this file.  Its two quantitative points are:

* the ratio `K` is chosen so large that `|W'| ≤ ρ|W|` with `ρ = (c - 9/10)/2`, so that deleting both
  the edges inside `W'` and the reservation `R` leaves the shell with minimum degree `≥ (9/10)|W|`,
  which is what the dense nibble consumes;
* the nibble is run on the *shell only*, so it spends **no** edge inside `W'`; the whole `γ|W'|`
  budget of the conclusion is therefore available to the absorption step, and the untouchability of
  `F ∩ cliqueEdges W''` is automatic for the nibble's triangles. -/
theorem coverDownK3Div_of_denseNibble_shellAbsorption
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDegDense)
    (hAbs : ShellAbsorption) : CoverDownK3Div := by
  classical
  intro c γ hc hγ
  set ρ : ℝ := (c - 9 / 10) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ρ)
  set K : ℕ := max 2 m with hKdef
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKm : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_max_right 2 m
  have hKρ : 1 / ρ < (K : ℝ) := lt_of_lt_of_le hm hKm
  obtain ⟨η, n₁, hη, habs⟩ := hAbs c γ ρ K hc hγ hρ hK2
  obtain ⟨n₂, hnib⟩ := nibbleMaxDeg_of_inputs_dense hDross hNib hη
  refine ⟨K, max n₁ n₂, hK2, ?_⟩
  intro V inst W W' W'' F hcard hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF' hdivF'' hdense
  -- the shell
  set E : Finset (Sym2 V) := F \ cliqueEdges W' with hEdef
  have hEF : E ⊆ F := Finset.sdiff_subset
  have hdivE : TriDivisible E := triDivisible_shell hdivF hdivF'
  -- the reservation
  obtain ⟨R, hRsub, hRdeg, habs2⟩ :=
    habs W W' W'' F (le_trans (le_max_left _ _) hcard) hW' hW'' hKW hKKW hKW'' hFW hdivF hdivF'
      hdivF'' hdense
  have hRE : R ⊆ E := hRsub
  -- `|W'| ≤ ρ |W|`
  have hWcard : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
  have hW'ρ : (W'.card : ℝ) ≤ ρ * (W.card : ℝ) := by
    have h1 : (K : ℝ) * (W'.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hKW
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : 0 < K := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) < ρ * (K : ℝ) := by
      rw [div_lt_iff₀ hρ] at hKρ
      linarith
    have h3 : (W'.card : ℝ) * (K : ℝ) ≤ (W.card : ℝ) := by linarith only [h1]
    have hW'nonneg : (0 : ℝ) ≤ (W'.card : ℝ) := by positivity
    nlinarith [hW'nonneg, hKpos]
  -- the nibble on the shell, minus the reservation
  have hER : E \ R ⊆ cliqueEdges W := (Finset.sdiff_subset.trans hEF).trans hFW
  have hmindeg : ∀ v ∈ W, (9 / 10 : ℝ) * (W.card : ℝ) ≤ (edeg (E \ R) v : ℝ) := by
    intro v hv
    have h1 : edeg F v ≤ edeg E v + edeg (cliqueEdges W') v :=
      edeg_le_sdiff_add_edeg F (cliqueEdges W') v
    have h2 : edeg E v ≤ edeg (E \ R) v + edeg R v := edeg_le_sdiff_add_edeg E R v
    have h3 : edeg (cliqueEdges W') v ≤ W'.card := edeg_cliqueEdges_le' W' v
    have h1' : (edeg F v : ℝ) ≤ (edeg E v : ℝ) + (edeg (cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    have h2' : (edeg E v : ℝ) ≤ (edeg (E \ R) v : ℝ) + (edeg R v : ℝ) := by exact_mod_cast h2
    have h3' : (edeg (cliqueEdges W') v : ℝ) ≤ (W'.card : ℝ) := by exact_mod_cast h3
    have h4 := hdense v hv
    have h5 := hRdeg v
    have : c * (W.card : ℝ) ≤ (edeg (E \ R) v : ℝ) + ρ * (W.card : ℝ) + ρ * (W.card : ℝ) := by
      linarith
    have hcρ : c - 2 * ρ = 9 / 10 := by rw [hρdef]; ring
    nlinarith [this]
  obtain ⟨P₁, hP₁, hP₁deg⟩ :=
    hnib W (E \ R) (le_trans (le_max_right _ _) hcard) hER hmindeg
  -- the leftover
  set L : Finset (Sym2 V) := (E \ R) \ famEdges P₁ with hLdef
  have hfamP₁ : famEdges P₁ ⊆ E \ R := famEdges_subset_of_triFamilyIn hP₁
  have hLsub : L ⊆ (F \ cliqueEdges W') \ R := Finset.sdiff_subset
  have hLdeg : ∀ v : V, (edeg L v : ℝ) ≤ η * (W.card : ℝ) := hP₁deg
  -- the remainder is what the shell has left after the nibble
  have hRL : R ∪ L = E \ famEdges P₁ := by
    ext e
    simp only [Finset.mem_union, hLdef, Finset.mem_sdiff]
    constructor
    · rintro (he | ⟨⟨he, -⟩, hne⟩)
      · exact ⟨hRE he, fun hmem => (Finset.mem_sdiff.1 (hfamP₁ hmem)).2 he⟩
      · exact ⟨he, hne⟩
    · rintro ⟨he, hne⟩
      by_cases hR : e ∈ R
      · exact Or.inl hR
      · exact Or.inr ⟨⟨he, hR⟩, hne⟩
  have hdivRL : TriDivisible (R ∪ L) := by
    rw [hRL]
    exact triDivisible_sdiff_famEdges (hP₁.mono Finset.sdiff_subset) hdivE
  -- the absorption
  obtain ⟨Q, hQ, hQcov, hQsub, hQdeg⟩ := habs2 L hLsub hLdeg hdivRL
  -- the two families are edge-disjoint
  have hEW' : ∀ e ∈ E, e ∉ cliqueEdges W' := fun e he => (Finset.mem_sdiff.1 he).2
  have hdisjQP : Disjoint (famEdges Q) (famEdges P₁) := by
    refine Finset.disjoint_left.2 fun e heQ heP => ?_
    have heE : e ∈ E \ R := hfamP₁ heP
    have h1 : e ∉ R := (Finset.mem_sdiff.1 heE).2
    have h2 : e ∉ L := by
      simp only [hLdef, Finset.mem_sdiff, not_and, not_not]
      intro _; exact heP
    have h3 : e ∉ cliqueEdges W' := hEW' e (Finset.mem_sdiff.1 heE).1
    rcases Finset.mem_union.1 (hQsub heQ) with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      exacts [h1 h', h2 h']
    · exact h3 (Finset.mem_sdiff.1 h).1
  have hQ' : TriFamilyIn (F \ famEdges P₁) Q := by
    refine triFamilyIn_sdiff hQ fun t ht => ?_
    refine Finset.disjoint_of_subset_left ?_ hdisjQP
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  have hP₁' : TriFamilyIn F P₁ := hP₁.mono (Finset.sdiff_subset.trans hEF)
  refine ⟨P₁ ∪ Q, triFamilyIn_union hP₁' hQ', ?_, ?_, ?_⟩
  · -- the leftover is inside `W'`
    intro e he
    rw [Finset.mem_sdiff, famEdges_union, Finset.mem_union] at he
    obtain ⟨heF, hne⟩ := he
    push_neg at hne
    by_contra hW'e
    have heE : e ∈ E := Finset.mem_sdiff.2 ⟨heF, hW'e⟩
    have : e ∈ R ∪ L := by rw [hRL]; exact Finset.mem_sdiff.2 ⟨heE, hne.1⟩
    exact hne.2 (hQcov this)
  · -- `F ∩ cliqueEdges W''` is untouched
    intro e he
    rw [Finset.mem_inter] at he
    obtain ⟨heF, heW''⟩ := he
    have heW' : e ∈ cliqueEdges W' := cliqueEdges_mono hW'' heW''
    refine Finset.mem_sdiff.2 ⟨heF, ?_⟩
    rw [famEdges_union, Finset.mem_union]
    rintro (h | h)
    · exact hEW' e (Finset.mem_sdiff.1 (hfamP₁ h)).1 heW'
    · rcases Finset.mem_union.1 (hQsub h) with h' | h'
      · rw [hRL] at h'
        exact hEW' e (Finset.mem_sdiff.1 h').1 heW'
      · exact (Finset.mem_sdiff.1 h').2 heW''
  · -- the `W'`-degree is preserved up to `γ|W'|`
    intro v hv
    have hsub : F ∩ cliqueEdges W' ⊆
        (F \ famEdges (P₁ ∪ Q)) ∪ (famEdges Q ∩ cliqueEdges W') := by
      intro e he
      rw [Finset.mem_inter] at he
      by_cases hmem : e ∈ famEdges (P₁ ∪ Q)
      · rw [famEdges_union, Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact absurd he.2 (hEW' e (Finset.mem_sdiff.1 (hfamP₁ h)).1)
        · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, he.2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨he.1, hmem⟩)
    have h1 : edeg (F ∩ cliqueEdges W') v
        ≤ edeg (F \ famEdges (P₁ ∪ Q)) v + edeg (famEdges Q ∩ cliqueEdges W') v :=
      le_trans (edeg_mono hsub v) (edeg_union_le _ _ v)
    have h1' : (edeg (F ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (F \ famEdges (P₁ ∪ Q)) v : ℝ) + (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) := by
      exact_mod_cast h1
    linarith [hQdeg v hv]

end BKLO
