/-
# Nibble — McDiarmid regularity-failure bound : union bound and `P < 1`

Standalone, Mathlib-only. The McDiarmid replacement for the Chebyshev regularity-failure chain
(`RegularityBadTwoSided`). Where the Chebyshev route bounds each per-vertex deviation probability by
`Var/c²` (forcing the useless window `c ≳ √(n)·Δ`), this transports the **exponential-tail** bound
`residualDeg_config_concentration_sharp` (M8-sharp) into the abstract `BernoulliRetention` language,
instantiated at the concrete config retention `bernoulliConfigRetention`.

* `residualDeg_config_mcdiarmid_tail` — per-vertex exponential tail at the concrete config retention.
* `all_vertices_residualDeg_concentration_mcdiarmid` — union bound `≤ ∑_v 2·exp(…)`.
* `regularityBadMcDiarmid_prob_lt_one` — `P(Bad₂) < 1` whenever `∑_v 2·exp(…) < 1`.

The `∑_v` bound only needs `c² ≳ (∑_{e∈H} C_e²)·log n`, feasible with `c ≈ √(d log n) ≪ d` — the
window the nibble parameter tuning requires, which Chebyshev could not deliver.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.McDiarmidResidualSharp
import Nibble.BernoulliConfig
import Nibble.RegularityBad
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Abbreviation for the McDiarmid coefficient sum `∑_{e ∈ H} C_e²` appearing in the tail. -/
noncomputable def mcdiarmidCoeffSum (H : Finset (Finset V)) : ℝ :=
  ∑ e ∈ H, (∑ x ∈ e ∪ support (H.filter (fun g => ¬ Disjoint e g)), degree H x : ℝ) ^ 2

/-- Abbreviation for the count-sharp McDiarmid coefficient sum at a fixed vertex. -/
noncomputable def mcdiarmidNeighborCoeffSum (H : Finset (Finset V)) (v : V) : ℝ :=
  ∑ e ∈ H, (neighborCoef H v e : ℝ) ^ 2

/-- **Per-vertex exponential tail at the concrete config retention.** Transports the sharp M8 bound
`residualDeg_config_concentration_sharp` (stated with `Measure.pi ν` and `.real`) into the
`BernoulliRetention` language of the near-regularity chain, at `ρ = bernoulliConfigRetention`. -/
theorem residualDeg_config_mcdiarmid_tail (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) {c : ℝ} (hc0 : 0 ≤ c) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    (ℙ : Measure (Finset V → Bool))
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
      ≤ ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H))) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  set μ : Measure Bool := bernoulliConfigMeasure p hp0 hp1 with hμ
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => μ)); infer_instance
  -- rewrite `retainedSet` to the true-filter (in both the deviation and the mean)
  have hrs : ∀ ω : Finset V → Bool,
      retainedSet H (bernoulliConfigRetention H hp0 hp1) ω = H.filter (fun e => ω e = true) :=
    fun ω => retainedSet_bernoulliConfig H hp0 hp1 ω
  simp only [hrs]
  -- M8-sharp at ν = μ; its event/mean/measure coincide definitionally with the goal's
  have hsharp := residualDeg_config_concentration_sharp (V := V) H v μ hc0
  rw [← ENNReal.ofReal_toReal (measure_ne_top (ℙ : Measure (Finset V → Bool)) _)]
  exact ENNReal.ofReal_le_ofReal hsharp

/-- **Union bound (McDiarmid).** The probability that *some* vertex's residual degree deviates from
its mean by `≥ c` is at most `∑_v 2·exp(−c²/(2 ∑_{e∈H} C_e²))`. Same union structure as the Chebyshev
`all_vertices_residualDeg_concentration`, with the exponential per-vertex tail. -/
theorem all_vertices_residualDeg_concentration_mcdiarmid (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ} (hc0 : 0 ≤ c) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    (ℙ : Measure (Finset V → Bool)) (⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|})
      ≤ ∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H))) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  calc (ℙ : Measure (Finset V → Bool)) (⋃ v ∈ (Finset.univ : Finset V),
          {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
            - (ℙ : Measure (Finset V → Bool))[fun ω =>
                (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|})
      ≤ ∑ v ∈ (Finset.univ : Finset V), (ℙ : Measure (Finset V → Bool))
          {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
            - (ℙ : Measure (Finset V → Bool))[fun ω =>
                (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H))) :=
        Finset.sum_le_sum (fun v _ => residualDeg_config_mcdiarmid_tail H hp0 hp1 v hc0)

/-- **McDiarmid regularity-failure probability is `< 1`.** If `∑_v 2·exp(−c²/(2 ∑_{e∈H} C_e²)) < 1`,
then the two-sided deviation event `Bad₂` has probability `< 1` — so a good (near-regular) retained
configuration exists. This is the exponential-tail replacement for `regularityBadTwoSided_prob_lt_one`
that Chebyshev could not supply within the nibble window. -/
theorem regularityBadMcDiarmid_prob_lt_one (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ _v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidCoeffSum H)))) < 1) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    ((ℙ : Measure (Finset V → Bool)) {ω | ∃ v : V,
        c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}).toReal
      < 1 := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  have hsub : {ω | ∃ v : V,
        c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
      ⊆ ⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ v) hv
  have hle := (measure_mono hsub).trans (all_vertices_residualDeg_concentration_mcdiarmid H hp0 hp1 hc0)
  have hlt := lt_of_le_of_lt hle hsmall
  have hne := (hlt.trans_le le_top).ne
  calc _ < (1 : ENNReal).toReal := (ENNReal.toReal_lt_toReal hne (by simp)).mpr hlt
    _ = 1 := by simp

/-- Per-vertex McDiarmid tail using the true count coefficient `neighborCoef`. -/
theorem residualDeg_config_mcdiarmid_neighborCoef_tail (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) {c : ℝ} (hc0 : 0 ≤ c) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    (ℙ : Measure (Finset V → Bool))
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
      ≤ ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v))) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  set μ : Measure Bool := bernoulliConfigMeasure p hp0 hp1 with hμ
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => μ)); infer_instance
  have hrs : ∀ ω : Finset V → Bool,
      retainedSet H (bernoulliConfigRetention H hp0 hp1) ω = H.filter (fun e => ω e = true) :=
    fun ω => retainedSet_bernoulliConfig H hp0 hp1 ω
  simp only [hrs]
  have hsharp := residualDeg_config_concentration_neighborCoef (V := V) H v μ hc0
  rw [← ENNReal.ofReal_toReal (measure_ne_top (ℙ : Measure (Finset V → Bool)) _)]
  simpa [mcdiarmidNeighborCoeffSum] using ENNReal.ofReal_le_ofReal hsharp

/-- Union bound for the count-sharp McDiarmid residual-degree tail. -/
theorem all_vertices_residualDeg_concentration_mcdiarmid_neighborCoef (H : Finset (Finset V))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ} (hc0 : 0 ≤ c) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    (ℙ : Measure (Finset V → Bool)) (⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|})
      ≤ ∑ v : V, ENNReal.ofReal (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v))) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  calc (ℙ : Measure (Finset V → Bool)) (⋃ v ∈ (Finset.univ : Finset V),
          {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
            - (ℙ : Measure (Finset V → Bool))[fun ω =>
                (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|})
      ≤ ∑ v ∈ (Finset.univ : Finset V), (ℙ : Measure (Finset V → Bool))
          {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
            - (ℙ : Measure (Finset V → Bool))[fun ω =>
                (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ v : V, ENNReal.ofReal
        (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v))) :=
        Finset.sum_le_sum (fun v _ => residualDeg_config_mcdiarmid_neighborCoef_tail H hp0 hp1 v hc0)

/-- Count-sharp McDiarmid regularity-failure probability is `< 1`. -/
theorem regularityBadMcDiarmid_neighborCoef_prob_lt_one (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {c : ℝ} (hc0 : 0 ≤ c)
    (hsmall : (∑ v : V, ENNReal.ofReal
      (2 * Real.exp (-c ^ 2 / (2 * mcdiarmidNeighborCoeffSum H v)))) < 1) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    ((ℙ : Measure (Finset V → Bool)) {ω | ∃ v : V,
        c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}).toReal
      < 1 := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  haveI : IsProbabilityMeasure (ℙ : Measure (Finset V → Bool)) := by
    show IsProbabilityMeasure (Measure.pi (fun _ : Finset V => bernoulliConfigMeasure p hp0 hp1))
    infer_instance
  have hsub : {ω | ∃ v : V,
        c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|}
      ⊆ ⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)
          - (ℙ : Measure (Finset V → Bool))[fun ω =>
              (degree (residual H (retainedSet H (bernoulliConfigRetention H hp0 hp1) ω)) v : ℝ)]|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_biUnion (Finset.mem_univ v) hv
  have hle := (measure_mono hsub).trans
    (all_vertices_residualDeg_concentration_mcdiarmid_neighborCoef H hp0 hp1 hc0)
  have hlt := lt_of_le_of_lt hle hsmall
  have hne := (hlt.trans_le le_top).ne
  calc _ < (1 : ENNReal).toReal := (ENNReal.toReal_lt_toReal hne (by simp)).mpr hlt
    _ = 1 := by simp

end Nibble
