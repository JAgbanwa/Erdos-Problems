/-
# Nibble — one good round (assembled) : cover many vertices AND preserve regularity

Standalone, Mathlib-only. Assembles `exists_covering_avoiding_bad` (one round covers many while
avoiding a bad event) with the concrete regularity-failure event from `RegularityBad`. The result is
the single-round existence at the heart of the nibble iteration: for a near-regular, low-codegree
`r`-uniform hypergraph, provided the Chebyshev variance bound `∑Var/c² < 1`, there is ONE outcome `ω`
that simultaneously

* **preserves near-regularity**: every vertex keeps residual degree `> deg(v)·(1−rΔp) − c`, and
* **covers many vertices**: its round matching has `≥ |H|·p·(1−p)^{rΔ} − |V|·P(Bad)` edges.

This is exactly the per-round step the iteration threads (defining the retention strategy `R` at such
an `ω`). The remaining work (step 2) is the induction maintaining the hypotheses across rounds.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.OneRoundGood
import Nibble.RegularityBad
import Nibble.Chebyshev
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **One good round (assembled).** There is an outcome `ω` that keeps every residual degree above
`deg(v)·(1−rΔp) − c` (near-regularity preserved) and whose round matching covers
`≥ |H|·p·(1−p)^{rΔ} − |V|·P(Bad)` vertices. -/
theorem exists_good_round {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) {c : ℝ} (hc : 0 < c)
    (hsmall : (∑ v : V, ENNReal.ofReal
        (Var[fun ω => (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ);
          (ℙ : Measure Ω)] / c ^ 2)) < 1) :
    ∃ ω,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
                ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
        ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  obtain ⟨ω, hω_notin, hcov⟩ := exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ
    (measurableSet_regularityBad ρ) (regularityBad_prob_lt_one ρ hp0 hp1 hr hΔ hc hsmall)
  refine ⟨ω, fun v => ?_, hcov⟩
  by_contra hle
  push_neg at hle
  exact hω_notin ⟨v, hle⟩

/-- **Good round via FREEDMAN (STEP 3c).**  (Named `..._uncond` because its dependency-positivity
hypothesis `hVpos` is unconditional, unlike the `0 < degree H v`-conditioned one of
`Nibble.exists_good_round_freedman` in `GoodRoundFreedman.lean`; the two files were previously
declaring the SAME fully qualified name, which made them unimportable together.) Same conclusion as `exists_good_round`, but the
regularity-failure probability is controlled by the exponential Freedman bound
(`regularityBad_prob_lt_one_freedman`) instead of the vacuous Chebyshev variance sum — so this holds
with a SMALL slack `c` (whenever `|V|·2·exp(−c²/(2(Δ²rΔp+(Δ/3)c))) < 1`), breaking the vacuousness of
clause (a). Reuses the generic `exists_covering_avoiding_bad`. -/
theorem exists_good_round_freedman_uncond [Fintype V] {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {c : ℝ} (hc0 : 0 ≤ c)
    (hVpos : ∀ v : V, 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hcond : (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1) :
    ∃ ω,
      (∀ v : V, (degree H v : ℝ) * (1 - r * Δ * p) - c
          < (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ))
      ∧ (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
          - (Fintype.card V : ℝ) * ((ℙ : Measure Ω) {ω | ∃ v : V,
              (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
                ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
        ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  obtain ⟨ω, hω_notin, hcov⟩ := exists_covering_avoiding_bad ρ hp0 hp1 hr1 hr hΔ
    (measurableSet_regularityBad ρ)
    (regularityBad_prob_lt_one_freedman ρ hp0 hp1 hr hΔ hΔ0 hc0 hVpos hcond)
  refine ⟨ω, fun v => ?_, hcov⟩
  by_contra hle
  push_neg at hle
  exact hω_notin ⟨v, hle⟩

end Nibble
