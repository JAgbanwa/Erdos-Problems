/-
# Nibble — the named concrete Bernoulli retention on the configuration space

Standalone, Mathlib-only. `BernoulliSpace.exists_bernoulliRetention` only asserts the *existence* of a
probability space carrying a `BernoulliRetention`. To transport the **concrete** McDiarmid tail bound
(`residualDeg_config_concentration_sharp`, which lives on `Measure.pi ν` over `Finset V → Bool`) into
the abstract `BernoulliRetention` language of the near-regularity chain, we need the instance *by
name*, so that `retainedSet` and the mean `𝔼[·]` reduce definitionally to `H.filter (ω · = true)` and
`∫ · ∂(Measure.pi μ)`.

* `bernoulliConfigMeasure p` — the Bernoulli(`p`) measure on `Bool`.
* `bernoulliConfigSpace` — the product `MeasureSpace` on `Finset V → Bool`.
* `bernoulliConfigRetention` — the named `BernoulliRetention` with `A e = {ω | ω e = true}`.
* `retainedSet_bernoulliConfig` — `retainedSet H ρ ω = H.filter (ω · = true)`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Survival
import Nibble.Covered
import Nibble.Prelude

open MeasureTheory ProbabilityTheory

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Bernoulli(`p`) measure on `Bool` for `p ∈ [0,1]`. -/
noncomputable def bernoulliConfigMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli ⟨p, hp0⟩ (by simpa using hp1)).toMeasure

instance bernoulliConfigMeasure.instIsProbabilityMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliConfigMeasure p hp0 hp1) := by
  unfold bernoulliConfigMeasure; infer_instance

/-- The product Bernoulli(`p`) `MeasureSpace` on the configuration space `Finset V → Bool`. -/
noncomputable def bernoulliConfigSpace (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MeasureSpace (Finset V → Bool) :=
  ⟨Measure.pi (fun _ => bernoulliConfigMeasure p hp0 hp1)⟩

/-- The named concrete `BernoulliRetention` on `Finset V → Bool`, with `A e = {ω | ω e = true}`. -/
noncomputable def bernoulliConfigRetention (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    @BernoulliRetention V _ (Finset V → Bool) (bernoulliConfigSpace p hp0 hp1) H p := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  set μ : Measure Bool := bernoulliConfigMeasure p hp0 hp1 with hμ
  refine { A := fun e => {ω | ω e = true}, meas := ?_, indep := ?_, prob := ?_ }
  · intro e
    change MeasurableSet ((fun ω : Finset V → Bool => ω e) ⁻¹' ({true} : Set Bool))
    exact (measurable_pi_apply e) (measurableSet_singleton true)
  · have hfun : iIndepFun (fun e (ω : Finset V → Bool) => ω e) (Measure.pi (fun _ => μ)) := by
      simpa only [id_eq] using
        (iIndepFun_pi (μ := fun _ : Finset V => μ) (X := fun _ => id)
          (fun _ => measurable_id.aemeasurable))
    have hpred : iIndepFun (fun e (ω : Finset V → Bool) => ω e = true) (Measure.pi (fun _ => μ)) := by
      simpa only [Function.comp_apply] using
        hfun.comp (fun _ b => b = true) (fun _ => Measurable.of_discrete)
    have hind : iIndepSet (fun e => {ω : Finset V → Bool | ω e = true}) (Measure.pi (fun _ => μ)) := by
      rw [← iIndep_comap_mem_iff]
      apply (iIndepFun_iff_iIndep _ _ _).1
      simpa using hpred
    change iIndepSet _ (ℙ : Measure (Finset V → Bool))
    simpa [bernoulliConfigSpace, hμ] using hind
  · intro e he
    show (ℙ : Measure (Finset V → Bool)) {ω | ω e = true} = ENNReal.ofReal p
    rw [show (ℙ : Measure (Finset V → Bool)) = Measure.pi (fun _ => μ) from rfl]
    rw [show {ω : Finset V → Bool | ω e = true} = Function.eval e ⁻¹' ({true} : Set Bool) from rfl]
    rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true)]
    rw [Measure.pi_map_eval]
    have hμuniv : μ Set.univ = 1 := measure_univ
    rw [show ∏ j ∈ Finset.univ.erase e, μ Set.univ = 1 from
      Finset.prod_eq_one (fun _ _ => hμuniv), one_smul]
    change (PMF.bernoulli ⟨p, hp0⟩ _).toMeasure {true} = ENNReal.ofReal p
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true), PMF.bernoulli_apply]
    exact ENNReal.coe_nnreal_eq _

/-- **The retained set of the concrete config retention is exactly the `ω`-true filter.** -/
theorem retainedSet_bernoulliConfig (H : Finset (Finset V)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : Finset V → Bool) :
    letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
    retainedSet H (bernoulliConfigRetention H hp0 hp1) ω = H.filter (fun e => ω e = true) := by
  letI : MeasureSpace (Finset V → Bool) := bernoulliConfigSpace p hp0 hp1
  ext e
  simp only [retainedSet, Finset.mem_filter]
  exact and_congr_right fun _ => Iff.rfl

end Nibble
