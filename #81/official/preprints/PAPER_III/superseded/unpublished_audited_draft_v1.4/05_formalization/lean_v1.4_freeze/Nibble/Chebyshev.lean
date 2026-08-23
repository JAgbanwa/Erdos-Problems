/-
# Nibble — Layer Ch : Chebyshev / second-moment concentration of the residual degree

Standalone, Mathlib-only. The concentration route that avoids the conditional-expectation wall of
McDiarmid: express `deg_residual(v)` as a sum of survival indicators, take variance (a finite sum
of covariances, `variance_fun_sum'`), and apply Chebyshev (`meas_ge_le_variance_div_sq`).

Current layer:
* `survivalIndicator ρ e ω` — the `{0,1}` indicator that edge `e` survives into the residual.
* `residualDeg_eq_sum` (Ch1a) — `deg_residual(v) = ∑_{e∋v} survivalIndicator e` pointwise.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round
import Nibble.Conflict
import Nibble.RoundConflict
import Nibble.Survival
import Nibble.Covered
import Nibble.Measurable
import Nibble.DepLocal
import Nibble.Bennett
import Nibble.Subgamma
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]

/-- The survival indicator: `1` if edge `e` avoids the covered set at outcome `ω`, else `0`. -/
noncomputable def survivalIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) (ω : Ω) : ℝ :=
  if Disjoint e (covered (retainedSet H ρ ω)) then 1 else 0

/-- **Ch1a — residual degree as a sum of survival indicators.** -/
theorem residualDeg_eq_sum {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (degree (residual H (retainedSet H ρ ω)) v : ℝ)
      = ∑ e ∈ H.filter (fun f => v ∈ f), survivalIndicator ρ e ω := by
  simp only [survivalIndicator]
  rw [Finset.sum_boole]
  congr 1
  rw [degree, Hypergraph.residual, Finset.filter_comm]

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The survival event of an edge is measurable (complement of the union of covered-events). -/
theorem measurableSet_survival {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    MeasurableSet {ω | Disjoint e (covered (retainedSet H ρ ω))} := by
  have hrepr : {ω | Disjoint e (covered (retainedSet H ρ ω))}
      = (⋃ x ∈ e, {ω | x ∈ support (roundMatching (retainedSet H ρ ω))})ᶜ := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    rw [Finset.disjoint_left]
    constructor
    · intro h x hx hxc; exact h hx hxc
    · intro h x hx hxc; exact h x hx hxc
  rw [hrepr]
  exact (Finset.measurableSet_biUnion _ (fun x _ => measurableSet_vertex_covered ρ x)).compl

/-- The survival indicator is measurable. -/
theorem measurable_survivalIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    Measurable (survivalIndicator ρ e) :=
  Measurable.ite (measurableSet_survival ρ e) measurable_const measurable_const

/-- The survival indicator is `L²` (it is bounded by `1`). -/
theorem memLp_survivalIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    MemLp (survivalIndicator ρ e) 2 (ℙ : Measure Ω) := by
  refine MemLp.of_bound (measurable_survivalIndicator ρ e).aestronglyMeasurable 1 ?_
  filter_upwards with ω
  unfold survivalIndicator
  split_ifs <;> simp

/-- **Ch1 — variance of the residual degree as a double sum of covariances.**
`Var[deg_residual(v)] = ∑_{e,e'∋v} cov(1ₑ, 1ₑ')`. -/
theorem residualDeg_variance {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
      = ∑ e ∈ H.filter (fun f => v ∈ f), ∑ e' ∈ H.filter (fun f => v ∈ f),
          cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)] := by
  have hfun : (fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ))
      = fun ω => ∑ e ∈ H.filter (fun f => v ∈ f), survivalIndicator ρ e ω :=
    funext (fun ω => residualDeg_eq_sum ρ v ω)
  rw [hfun]
  exact variance_fun_sum' (fun e _ => memLp_survivalIndicator ρ e)

/-- **Ch2a — non-interacting edges contribute zero covariance.** If the survival indicators of
`e` and `e'` are independent (their survival depends on disjoint retention bits — the
dependency-locality established via `iIndepFun.indepFun_finset`), their covariance vanishes. -/
theorem cov_survival_eq_zero_of_indep {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e e' : Finset V)
    (h : IndepFun (survivalIndicator ρ e) (survivalIndicator ρ e') (ℙ : Measure Ω)) :
    cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)] = 0 :=
  h.covariance_eq_zero (memLp_survivalIndicator ρ e) (memLp_survivalIndicator ρ e')

/-- **Ch2b(1) — survival event as an explicit boolean combination over `depNbhd`.** The event that
`e` survives equals the complement of the union, over edges `f` meeting `e`, of "f retained and all
its conflicts unretained". Every event used is `ρ.A h` with `h ∈ depNbhd H e`, exhibiting the
read-k structure explicitly. -/
theorem survivalEvent_eq_dep {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    {ω | Disjoint e (covered (retainedSet H ρ ω))}
      = (⋃ f ∈ H.filter (fun f => ¬ Disjoint e f),
          ρ.A f ∩ ⋂ g ∈ conflicts H f, (ρ.A g)ᶜ)ᶜ := by
  ext ω
  have hRsub : retainedSet H ρ ω ⊆ H := Finset.filter_subset _ _
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_iInter, not_exists, not_and]
  rw [disjoint_covered_iff]
  constructor
  · intro h f hf hfA hgc
    rw [Finset.mem_filter] at hf
    have hfR : f ∈ retainedSet H ρ ω := Finset.mem_filter.mpr ⟨hf.1, hfA⟩
    have hfmatch : f ∈ roundMatching (retainedSet H ρ ω) :=
      (mem_roundMatching_iff_conflicts hRsub).mpr ⟨hfR, fun g hg hgR =>
        hgc g hg (Finset.mem_filter.mp hgR).2⟩
    exact absurd (h f hfmatch) hf.2
  · intro h f hfmatch
    by_contra hnd
    have hfR : f ∈ retainedSet H ρ ω := roundMatching_subset _ hfmatch
    have hfRm := Finset.mem_filter.mp hfR
    obtain ⟨hfR', hiso⟩ := (mem_roundMatching_iff_conflicts hRsub).mp hfmatch
    refine h f (Finset.mem_filter.mpr ⟨hfRm.1, hnd⟩) hfRm.2 (fun g hg hgA => ?_)
    exact hiso g hg (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1, hgA⟩)

/-- The σ-algebra generated by the retention events of the dependency neighbourhood of `e`
(in the exact `generateFrom`-of-image form produced by `indep_generateFrom_of_disjoint`). -/
def depSigma {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {t | ∃ g ∈ (↑(depNbhd H e) : Set (Finset V)), ρ.A g = t}

/-- Each retention event of the dependency neighbourhood is `depSigma`-measurable. -/
theorem measurableSet_A_depSigma {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {e g : Finset V} (hg : g ∈ depNbhd H e) :
    MeasurableSet[depSigma ρ e] (ρ.A g) :=
  MeasurableSpace.measurableSet_generateFrom ⟨g, Finset.mem_coe.mpr hg, rfl⟩

/-- **Ch2b(2) — the survival event is `depSigma`-measurable** (read-k measurability). -/
theorem measurableSet_survival_depSigma {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    MeasurableSet[depSigma ρ e] {ω | Disjoint e (covered (retainedSet H ρ ω))} := by
  rw [survivalEvent_eq_dep]
  refine MeasurableSet.compl ?_
  refine Finset.measurableSet_biUnion _ (fun f hf => ?_)
  rw [Finset.mem_filter] at hf
  have hfdep : f ∈ depNbhd H e := mem_depNbhd_of_touch hf.1 hf.2
  refine MeasurableSet.inter (measurableSet_A_depSigma ρ hfdep) ?_
  refine Finset.measurableSet_biInter _ (fun g hg => ?_)
  exact (measurableSet_A_depSigma ρ (conflict_mem_depNbhd hf.1 hf.2 hg)).compl

/-- `survivalIndicator ρ e` is `depSigma ρ e`-measurable. -/
theorem measurable_survivalIndicator_depSigma {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    Measurable[depSigma ρ e] (survivalIndicator ρ e) :=
  Measurable.ite (measurableSet_survival_depSigma ρ e) measurable_const measurable_const

/-- **Ch2b(3) — far-apart survival indicators are independent.** If the dependency neighbourhoods
of `e` and `e'` are disjoint, their survival indicators are independent. -/
theorem indepFun_survival_of_disjoint {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e e' : Finset V)
    (hdisj : Disjoint (depNbhd H e) (depNbhd H e')) :
    IndepFun (survivalIndicator ρ e) (survivalIndicator ρ e') (ℙ : Measure Ω) := by
  have hindep : Indep (depSigma ρ e) (depSigma ρ e') (ℙ : Measure Ω) :=
    (ρ.indep).indep_generateFrom_of_disjoint ρ.meas
      (↑(depNbhd H e)) (↑(depNbhd H e')) (Finset.disjoint_coe.mpr hdisj)
  have hle : MeasurableSpace.comap (survivalIndicator ρ e) inferInstance ≤ depSigma ρ e :=
    measurable_iff_comap_le.mp (measurable_survivalIndicator_depSigma ρ e)
  have hle' : MeasurableSpace.comap (survivalIndicator ρ e') inferInstance ≤ depSigma ρ e' :=
    measurable_iff_comap_le.mp (measurable_survivalIndicator_depSigma ρ e')
  rw [IndepFun_iff_Indep, Indep_iff]
  rw [Indep_iff] at hindep
  exact fun t₁ t₂ ht₁ ht₂ => hindep t₁ t₂ (hle t₁ ht₁) (hle' t₂ ht₂)

/-- **Ch3 — the variance localizes to interacting pairs.** In the covariance double sum, only pairs
of edges with *overlapping* dependency neighbourhoods contribute; far-apart pairs vanish (Ch2). -/
theorem residualDeg_variance_interacting {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
      = ∑ e ∈ H.filter (fun f => v ∈ f),
          ∑ e' ∈ (H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e')),
            cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)] := by
  rw [residualDeg_variance]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun e' he' hne' => ?_)).symm
  simp only [Finset.mem_filter, not_and] at hne'
  have hdisj : Disjoint (depNbhd H e) (depNbhd H e') :=
    not_not.mp (hne' (Finset.mem_filter.mp he'))
  exact cov_survival_eq_zero_of_indep ρ e e' (indepFun_survival_of_disjoint ρ e e' hdisj)

/-- Survival indicators are nonnegative and their product is `≤ 1`. -/
theorem survivalIndicator_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) (ω : Ω) :
    0 ≤ survivalIndicator ρ e ω := by
  unfold survivalIndicator; split_ifs <;> norm_num

/-- **Var-numeric(a) — covariance of survival indicators is `≤ 1`.** -/
theorem cov_survival_le_one {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e e' : Finset V) :
    cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)] ≤ 1 := by
  rw [covariance_eq_sub (memLp_survivalIndicator ρ e) (memLp_survivalIndicator ρ e')]
  simp only [Pi.mul_apply]
  have hbd : ∀ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ≤ 1 := fun ω => by
    unfold survivalIndicator; split_ifs <;> norm_num
  have hmemXY : MemLp (fun ω => survivalIndicator ρ e ω * survivalIndicator ρ e' ω) 1
      (ℙ : Measure Ω) :=
    MemLp.of_bound
      ((measurable_survivalIndicator ρ e).mul (measurable_survivalIndicator ρ e')).aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, survivalIndicator]; split_ifs <;> norm_num))
  have hint := hmemXY.integrable le_rfl
  have h1 : ∫ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ∂(ℙ : Measure Ω) ≤ 1 := by
    calc ∫ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)
        ≤ ∫ _ω, (1 : ℝ) ∂(ℙ : Measure Ω) := integral_mono hint (integrable_const 1) hbd
      _ = 1 := by simp
  have h2 : 0 ≤ (∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω))
      * (∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)) :=
    mul_nonneg (integral_nonneg (survivalIndicator_nonneg ρ e))
      (integral_nonneg (survivalIndicator_nonneg ρ e'))
  linarith

private lemma cov_survival_le_integral_one_sub {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e e' : Finset V) :
    cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)]
      ≤ ∫ ω, (1 - survivalIndicator ρ e' ω) ∂(ℙ : Measure Ω) := by
  rw [covariance_eq_sub (memLp_survivalIndicator ρ e) (memLp_survivalIndicator ρ e')]
  simp only [Pi.mul_apply]
  -- Integrability of X * Y
  have hmemXY : MemLp (fun ω => survivalIndicator ρ e ω * survivalIndicator ρ e' ω) 1
      (ℙ : Measure Ω) :=
    MemLp.of_bound
      ((measurable_survivalIndicator ρ e).mul (measurable_survivalIndicator ρ e')).aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, survivalIndicator]; split_ifs <;> norm_num))
  have hint := hmemXY.integrable le_rfl
  -- XY ≤ X since Y ≤ 1
  have hXYleX : ∀ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ≤ survivalIndicator ρ e ω := by
    intro ω
    unfold survivalIndicator at *
    split_ifs <;> simp_all
  have hintX : Integrable (survivalIndicator ρ e) (ℙ : Measure Ω) :=
    (memLp_survivalIndicator ρ e).integrable one_le_two
  have h1 : ∫ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)
      ≤ ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω) :=
    integral_mono hint hintX hXYleX
  -- E[X] ≤ 1
  have hbd : ∀ ω, survivalIndicator ρ e ω ≤ 1 := fun ω => by
    unfold survivalIndicator; split_ifs <;> norm_num
  have h2 : ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω) ≤ 1 := by
    calc ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω)
        ≤ ∫ _ω, (1 : ℝ) ∂(ℙ : Measure Ω) := integral_mono hintX (integrable_const 1) hbd
      _ = 1 := by simp
  -- E[1 - Y] = 1 - E[Y]
  have hmemY : MemLp (survivalIndicator ρ e') 1 (ℙ : Measure Ω) :=
    MemLp.of_bound (measurable_survivalIndicator ρ e').aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, survivalIndicator]; split_ifs <;> norm_num))
  have hintY := hmemY.integrable le_rfl
  -- E[Y] ≤ 1
  have hbd' : ∀ ω, survivalIndicator ρ e' ω ≤ 1 := fun ω => by
    unfold survivalIndicator; split_ifs <;> norm_num
  have h2' : ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω) ≤ 1 := by
    calc ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)
        ≤ ∫ _ω, (1 : ℝ) ∂(ℙ : Measure Ω) := integral_mono hintY (integrable_const 1) hbd'
      _ = 1 := by simp
  have hE1Y : ∫ ω, (1 - survivalIndicator ρ e' ω) ∂(ℙ : Measure Ω)
      = 1 - ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω) := by
    rw [integral_sub (integrable_const 1) hintY, integral_const]
    simp
  -- Covariance ≤ E[1 - Y]
  rw [hE1Y]
  have h3 : ∫ ω, survivalIndicator ρ e ω * survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)
      - (∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω))
        * (∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω))
      ≤ (∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω))
        * (1 - ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)) := by
    have := sub_le_sub_right h1 ((∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω))
        * (∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω)))
    linarith
  have h4 : (∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω)) * (1 - ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω))
      ≤ 1 - ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω) := by
    have hge0 : 0 ≤ 1 - ∫ ω, survivalIndicator ρ e' ω ∂(ℙ : Measure Ω) := sub_nonneg.mpr h2'
    nlinarith
  linarith

private lemma integral_one_sub_survivalIndicator_eq_measure_hit {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) :
    (∫ ω, (1 - survivalIndicator ρ e ω) ∂(ℙ : Measure Ω))
      = ((ℙ : Measure Ω) {ω | ∃ x ∈ e,
          x ∈ support (roundMatching (retainedSet H ρ ω))}).toReal := by
  set A : Set Ω := {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))} with hAdef
  -- `A` is the complement of the survival event, hence measurable
  have hAeq : A = {ω | Disjoint e (covered (retainedSet H ρ ω))}ᶜ := by
    ext ω
    simp only [hAdef, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [Finset.not_disjoint_iff]
    constructor
    · rintro ⟨x, hx, hxc⟩; exact ⟨x, hx, hxc⟩
    · rintro ⟨x, hx, hxc⟩; exact ⟨x, hx, hxc⟩
  have hAmeas : MeasurableSet A := by rw [hAeq]; exact (measurableSet_survival ρ e).compl
  -- `1 − survivalIndicator = 𝟙_A`
  have hfun : (fun ω => 1 - survivalIndicator ρ e ω) = A.indicator (1 : Ω → ℝ) := by
    funext ω
    simp only [survivalIndicator, Set.indicator_apply, Pi.one_apply, hAdef, Set.mem_setOf_eq]
    by_cases h : ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))
    · rw [if_pos h]
      have hnd : ¬ Disjoint e (covered (retainedSet H ρ ω)) := by
        rw [Finset.not_disjoint_iff]; obtain ⟨x, hx, hxc⟩ := h; exact ⟨x, hx, hxc⟩
      rw [if_neg hnd]; ring
    · rw [if_neg h]
      have hd : Disjoint e (covered (retainedSet H ρ ω)) := by
        rw [Finset.disjoint_left]; intro x hx hxc; exact h ⟨x, hx, hxc⟩
      rw [if_pos hd]; ring
  rw [hfun, integral_indicator_one hAmeas]
  rfl

private lemma measure_edge_hit_toReal_le {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    {e : Finset V} (he : e ∈ H) :
    ((ℙ : Measure Ω) {ω | ∃ x ∈ e,
        x ∈ support (roundMatching (retainedSet H ρ ω))}).toReal
      ≤ (r : ℝ) * Δ * p := by
  have hbdd := prob_edge_hit_le ρ hr hΔ he
  simp only [mul_assoc] at hbdd
  have htop : ((r : ENNReal) * ((Δ : ENNReal) * ENNReal.ofReal p)) ≠ ⊤ := by
    apply_rules [ENNReal.mul_ne_top, ENNReal.ofReal_ne_top]
    all_goals simp
  calc ((ℙ : Measure Ω) {ω | ∃ x ∈ e, x ∈ support (roundMatching (retainedSet H ρ ω))}).toReal
      ≤ ((r : ENNReal) * ((Δ : ENNReal) * ENNReal.ofReal p)).toReal :=
          ENNReal.toReal_mono htop hbdd
    _ = (r : ℝ) * ((Δ : ℝ) * p) := by
          simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0]
    _ = (r : ℝ) * Δ * p := by ring

/-- **Ch2a′ — TIGHTENED covariance bound (the `p`-factor `cov_survival_le_one` drops).** Since
`0 ≤ X,Y ≤ 1`, `cov(X,Y) = E[XY] − E[X]E[Y] ≤ E[X] − E[X]E[Y] = E[X](1−E[Y]) ≤ 1−E[Y] = P(e' covered)`,
and `P(e' covered) ≤ ∑_{u ∈ e'} P(u covered) ≤ ∑_{u ∈ e'} (degree u)·p ≤ |e'|·Δ·p = r·Δ·p` by a union
bound over the `r` vertices of `e'` (each covered only if some incident edge is retained, prob `≤ Δp`).
This replaces the vacuous `cov ≤ 1`: the residual-degree variance then carries the `p`-factor
(`Var ≲ (#interacting pairs)·rΔp` instead of `≤ Δ²`), which is what a Freedman tail needs to give slack
`c ≪ d`. LOAD-BEARING ATOM for de-vacuum-ing the nibble concentration. -/
theorem cov_survival_le_covered {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : IsUniform H r)
    (hΔ : ∀ x, degree H x ≤ Δ) {e e' : Finset V} (he' : e' ∈ H) :
    cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)] ≤ (r : ℝ) * Δ * p := by
  calc
    cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)]
        ≤ ∫ ω, (1 - survivalIndicator ρ e' ω) ∂(ℙ : Measure Ω) :=
      cov_survival_le_integral_one_sub ρ e e'
    _ = ((ℙ : Measure Ω) {ω | ∃ x ∈ e',
          x ∈ support (roundMatching (retainedSet H ρ ω))}).toReal :=
      integral_one_sub_survivalIndicator_eq_measure_hit ρ e'
    _ ≤ (r : ℝ) * Δ * p := measure_edge_hit_toReal_le ρ hp0 hr hΔ he'

/-- **Var-numeric — variance bounded by the number of interacting pairs.** -/
theorem residualDeg_variance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
      ≤ ∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ) := by
  rw [residualDeg_variance_interacting]
  refine Finset.sum_le_sum (fun e _ => ?_)
  calc ∑ e' ∈ (H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e')),
          cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)]
      ≤ ∑ _e' ∈ (H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e')), (1 : ℝ) :=
        Finset.sum_le_sum (fun e' _ => cov_survival_le_one ρ e e')
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Var-numeric′ — variance with the `p`-factor.** Same interaction count as `residualDeg_variance_le`
but each covariance carries the tightened `cov ≤ rΔp` bound (`cov_survival_le_covered`) instead of the
vacuous `cov ≤ 1`. So `Var[deg_res v] ≤ (#interacting pairs at v)·rΔp` — the `p`-factor the Chebyshev
route dropped. (NOTE: `Δ` is still the global max-degree bound; a per-vertex / global-degree-cap
refinement is needed downstream so the exceptional set does not inflate `Δ` past `~d`.) -/
theorem residualDeg_variance_le_p {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
      ≤ (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p) := by
  rw [residualDeg_variance_interacting, Finset.sum_mul]
  refine Finset.sum_le_sum (fun e _ => ?_)
  calc ∑ e' ∈ (H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e')),
          cov[survivalIndicator ρ e, survivalIndicator ρ e'; (ℙ : Measure Ω)]
      ≤ ∑ _e' ∈ (H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e')), ((r : ℝ) * Δ * p) :=
        Finset.sum_le_sum (fun e' he' => cov_survival_le_covered ρ hp0 hp1 hr hΔ
          (Finset.filter_subset _ _ (Finset.filter_subset _ _ he')))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The residual degree at `v` is `L²` (a finite sum of `L²` survival indicators). -/
theorem memLp_residualDeg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    MemLp (fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)) 2 (ℙ : Measure Ω) := by
  have h2 : (fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ))
      = ∑ e ∈ H.filter (fun f => v ∈ f), survivalIndicator ρ e := by
    funext ω; rw [Finset.sum_apply]; exact residualDeg_eq_sum ρ v ω
  rw [h2]
  exact memLp_finset_sum' _ (fun e _ => memLp_survivalIndicator ρ e)

/-- **Ch-Freedman — the residual degree has a SUB-GAMMA MGF (STEP 2, DELEGATE).** The centred residual
degree `X := deg_res(v) − 𝔼[deg_res(v)]` (a single bounded real r.v., `X ≤ Δ`, `𝔼[X]=0`,
`𝔼[X²] = Var ≤ V` from `residualDeg_variance_le_p`) has a sub-gamma MGF with variance proxy `V` and
scale `Δ/3`. Route (all pieces exist, NO conditional-expectation / martingale machinery — `X` is one
r.v.): `mgf_le_bennett` (with `b := Δ`) gives `mgf X t ≤ exp(V(e^{tΔ}−1−tΔ)/Δ²)`; then
`exp_sub_one_sub_le_bernstein` (`u := tΔ`) gives `e^{tΔ}−1−tΔ ≤ (tΔ)²/(2(1−tΔ/3))`, so
`mgf X t ≤ exp(V t²/(2(1−(Δ/3)t)))` = the `HasSubgammaMGF X V (Δ/3)` bound. Feeds `subgamma_tail`
(exponential tail) ⇒ union over `v` ⇒ a Freedman bad-event bound replacing the vacuous Chebyshev one. -/
theorem residualDeg_hasSubgammaMGF {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) (v : V) :
    HasSubgammaMGF
      (fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω))
      ((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
      ((Δ : ℝ) / 3)
      (ℙ : Measure Ω) := by
  let Y : Ω → ℝ := fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)
  let m : ℝ := ∫ ω, Y ω ∂(ℙ : Measure Ω)
  let X : Ω → ℝ := fun ω => Y ω - m
  let W : ℝ := (∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) *
      ((r : ℝ) * Δ * p)
  have hY2 : MemLp Y 2 (ℙ : Measure Ω) := memLp_residualDeg ρ v
  have hYint : Integrable Y (ℙ : Measure Ω) := hY2.integrable one_le_two
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := fun ω => by simp [Y]
  have hY_le : ∀ ω, Y ω ≤ (Δ : ℝ) := fun ω => by
    dsimp [Y, degree]
    exact_mod_cast (le_trans
      (Finset.card_le_card (Finset.filter_subset_filter _
        (residual_subset H (retainedSet H ρ ω))))
      (hΔ v))
  have hm_nonneg : 0 ≤ m := integral_nonneg hY_nonneg
  have hm_le : m ≤ (Δ : ℝ) := by
    calc m = ∫ ω : Ω, Y ω ∂(ℙ : Measure Ω) := rfl
      _ ≤ ∫ _ω : Ω, (Δ : ℝ) ∂(ℙ : Measure Ω) :=
        integral_mono hYint (integrable_const _) hY_le
      _ = (Δ : ℝ) := by simp
  have hX_meas : AEStronglyMeasurable X (ℙ : Measure Ω) :=
    hY2.1.sub (aestronglyMeasurable_const)
  have hX_abs : ∀ ω, |X ω| ≤ (Δ : ℝ) := fun ω => by
    rw [abs_le]
    constructor <;> dsimp [X] <;> linarith [hY_nonneg ω, hY_le ω]
  have hX2 : MemLp X 2 (ℙ : Measure Ω) :=
    MemLp.of_bound hX_meas (Δ : ℝ) (Filter.Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using hX_abs ω))
  have hXint : Integrable X (ℙ : Measure Ω) := hX2.integrable one_le_two
  have hXsqint : Integrable (fun ω => (X ω) ^ 2) (ℙ : Measure Ω) := hX2.integrable_sq
  have hX0 : (ℙ : Measure Ω)[X] = 0 := by
    change (∫ ω, Y ω - m ∂(ℙ : Measure Ω)) = 0
    rw [integral_sub hYint (integrable_const m)]
    simp [m]
  have hXle : ∀ᵐ ω ∂(ℙ : Measure Ω), X ω ≤ (Δ : ℝ) :=
    Filter.Eventually.of_forall (fun ω => (le_abs_self (X ω)).trans (hX_abs ω))
  have hvar : (ℙ : Measure Ω)[fun ω => (X ω) ^ 2] ≤ W := by
    rw [show (∫ ω, (X ω) ^ 2 ∂(ℙ : Measure Ω)) = Var[Y; (ℙ : Measure Ω)] by
      rw [variance_eq_integral hY2.1.aemeasurable]]
    exact residualDeg_variance_le_p ρ hp0 hp1 hr hΔ v
  have hexpint : ∀ t : ℝ, 0 ≤ t → t < 3 / (Δ : ℝ) →
      Integrable (fun ω => Real.exp (t * X ω)) (ℙ : Measure Ω) := by
    intro t ht _
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (t * X ω)) (ℙ : Measure Ω) :=
      (hX_meas.const_mul t).aemeasurable.exp.aestronglyMeasurable
    exact (MemLp.of_bound hmeas (Real.exp (t * (Δ : ℝ)))
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((le_abs_self (X ω)).trans (hX_abs ω)) ht)))).integrable le_rfl
  exact hasSubgammaMGF_of_bounded_above (by exact_mod_cast hΔ0) hX0 hXle hvar
    hXint hXsqint hexpint

/-- **Ch-Freedman(2) — one-vertex UPPER tail (STEP 2b).** Applying `subgamma_tail` to the sub-gamma
MGF `residualDeg_hasSubgammaMGF`: the residual degree at `v` exceeds its mean by `≥ ε` with
probability `≤ exp(−ε²/(2(V + (Δ/3)ε)))` — an EXPONENTIAL tail (with `V` the `p`-factored variance
bound), replacing the polynomial Chebyshev tail. The integrability side-goal reuses the bounded-
support argument (`|deg_res − 𝔼| ≤ Δ`). -/
theorem residualDeg_upper_tail {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) (v : V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω)).real {ω | ε ≤ (degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)}
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * ε))) := by
  let Y : Ω → ℝ := fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)
  let m : ℝ := ∫ ω, Y ω ∂(ℙ : Measure Ω)
  let X : Ω → ℝ := fun ω => Y ω - m
  let W : ℝ := (∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) *
      ((r : ℝ) * Δ * p)
  let k : ℝ := ε / (W + (Δ : ℝ) / 3 * ε)
  have hY2 : MemLp Y 2 (ℙ : Measure Ω) := memLp_residualDeg ρ v
  have hYint : Integrable Y (ℙ : Measure Ω) := hY2.integrable one_le_two
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := fun ω => by simp [Y]
  have hY_le : ∀ ω, Y ω ≤ (Δ : ℝ) := fun ω => by
    dsimp [Y, degree]
    exact_mod_cast (le_trans
      (Finset.card_le_card (Finset.filter_subset_filter _
        (residual_subset H (retainedSet H ρ ω))))
      (hΔ v))
  have hm_nonneg : 0 ≤ m := integral_nonneg hY_nonneg
  have hm_le : m ≤ (Δ : ℝ) := by
    calc m = ∫ ω : Ω, Y ω ∂(ℙ : Measure Ω) := rfl
      _ ≤ ∫ _ω : Ω, (Δ : ℝ) ∂(ℙ : Measure Ω) :=
        integral_mono hYint (integrable_const _) hY_le
      _ = (Δ : ℝ) := by simp
  have hX_meas : AEStronglyMeasurable X (ℙ : Measure Ω) :=
    hY2.1.sub aestronglyMeasurable_const
  have hX_abs : ∀ ω, |X ω| ≤ (Δ : ℝ) := fun ω => by
    rw [abs_le]
    constructor <;> dsimp [X] <;> linarith [hY_nonneg ω, hY_le ω]
  have hW : 0 < W := by exact hV
  have hc : 0 < (Δ : ℝ) / 3 := by positivity
  have hden_pos : 0 < W + (Δ : ℝ) / 3 * ε :=
    add_pos_of_pos_of_nonneg hW (mul_nonneg hc.le hε)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg hε hden_pos.le
  have hint : Integrable (fun ω => Real.exp (k * X ω)) (ℙ : Measure Ω) := by
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (k * X ω))
        (ℙ : Measure Ω) :=
      (hX_meas.const_mul k).aemeasurable.exp.aestronglyMeasurable
    exact (MemLp.of_bound hmeas (Real.exp (k * (Δ : ℝ)))
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((le_abs_self (X ω)).trans (hX_abs ω)) hk_nonneg)))).integrable le_rfl
  have hsub : HasSubgammaMGF X W ((Δ : ℝ) / 3) (ℙ : Measure Ω) :=
    residualDeg_hasSubgammaMGF ρ hp0 hp1 hr hΔ hΔ0 v
  change (ℙ : Measure Ω).real {ω | ε ≤ X ω} ≤
    Real.exp (-ε ^ 2 / (2 * (W + (Δ : ℝ) / 3 * ε)))
  exact subgamma_tail hsub hW hc hε hint

/-- **Ch-Freedman(2′) — one-vertex LOWER tail (STEP 2c).** Symmetric to `residualDeg_upper_tail`: the
residual degree falls below its mean by `≥ ε` with probability `≤ exp(−ε²/(2(V + (Δ/3)ε)))`. Apply
`subgamma_tail` to `−X = 𝔼[deg_res(v)] − deg_res(v)`, which is ALSO bounded above by `Δ`
(`−X ≤ 𝔼 ≤ Δ`, since `deg_res ≥ 0`), so `hasSubgammaMGF_of_bounded_above` gives it the same sub-gamma
MGF `(V, Δ/3)` (`Var[−X] = Var[X]`, `𝔼[−X]=0`). -/
theorem residualDeg_lower_tail {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) (v : V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω)).real {ω | ε ≤ (∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ)
          ∂(ℙ : Measure Ω)) - (degree (residual H (retainedSet H ρ ω)) v : ℝ)}
      ≤ Real.exp (-ε ^ 2 / (2 * ((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * ε))) := by
  let Y : Ω → ℝ := fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)
  let m : ℝ := ∫ ω, Y ω ∂(ℙ : Measure Ω)
  let Z : Ω → ℝ := fun ω => m - Y ω
  let W : ℝ := (∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) *
      ((r : ℝ) * Δ * p)
  let k : ℝ := ε / (W + (Δ : ℝ) / 3 * ε)
  have hY2 : MemLp Y 2 (ℙ : Measure Ω) := memLp_residualDeg ρ v
  have hYint : Integrable Y (ℙ : Measure Ω) := hY2.integrable one_le_two
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := fun ω => by simp [Y]
  have hY_le : ∀ ω, Y ω ≤ (Δ : ℝ) := fun ω => by
    dsimp [Y, degree]
    exact_mod_cast (le_trans
      (Finset.card_le_card (Finset.filter_subset_filter _
        (residual_subset H (retainedSet H ρ ω))))
      (hΔ v))
  have hm_nonneg : 0 ≤ m := integral_nonneg hY_nonneg
  have hm_le : m ≤ (Δ : ℝ) := by
    calc m = ∫ ω : Ω, Y ω ∂(ℙ : Measure Ω) := rfl
      _ ≤ ∫ _ω : Ω, (Δ : ℝ) ∂(ℙ : Measure Ω) :=
        integral_mono hYint (integrable_const _) hY_le
      _ = (Δ : ℝ) := by simp
  have hZ_meas : AEStronglyMeasurable Z (ℙ : Measure Ω) :=
    aestronglyMeasurable_const.sub hY2.1
  have hZ_abs : ∀ ω, |Z ω| ≤ (Δ : ℝ) := fun ω => by
    rw [abs_le]
    constructor <;> dsimp [Z] <;> linarith [hY_nonneg ω, hY_le ω]
  have hZ2 : MemLp Z 2 (ℙ : Measure Ω) :=
    MemLp.of_bound hZ_meas (Δ : ℝ) (Filter.Eventually.of_forall (fun ω => by
      simpa [Real.norm_eq_abs] using hZ_abs ω))
  have hZint : Integrable Z (ℙ : Measure Ω) := hZ2.integrable one_le_two
  have hZsqint : Integrable (fun ω => (Z ω) ^ 2) (ℙ : Measure Ω) := hZ2.integrable_sq
  have hZ0 : (ℙ : Measure Ω)[Z] = 0 := by
    change (∫ ω, m - Y ω ∂(ℙ : Measure Ω)) = 0
    rw [integral_sub (integrable_const m) hYint]
    simp [m]
  have hZle : ∀ᵐ ω ∂(ℙ : Measure Ω), Z ω ≤ (Δ : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by dsimp [Z]; linarith [hY_nonneg ω])
  have hvar : (ℙ : Measure Ω)[fun ω => (Z ω) ^ 2] ≤ W := by
    rw [show (∫ ω, (Z ω) ^ 2 ∂(ℙ : Measure Ω)) = Var[Y; (ℙ : Measure Ω)] by
      rw [variance_eq_integral hY2.1.aemeasurable]
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [Z]
      ring]
    exact residualDeg_variance_le_p ρ hp0 hp1 hr hΔ v
  have hexpint : ∀ t : ℝ, 0 ≤ t → t < 3 / (Δ : ℝ) →
      Integrable (fun ω => Real.exp (t * Z ω)) (ℙ : Measure Ω) := by
    intro t ht _
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (t * Z ω)) (ℙ : Measure Ω) :=
      (hZ_meas.const_mul t).aemeasurable.exp.aestronglyMeasurable
    exact (MemLp.of_bound hmeas (Real.exp (t * (Δ : ℝ)))
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((le_abs_self (Z ω)).trans (hZ_abs ω)) ht)))).integrable le_rfl
  have hsub : HasSubgammaMGF Z W ((Δ : ℝ) / 3) (ℙ : Measure Ω) :=
    hasSubgammaMGF_of_bounded_above (by exact_mod_cast hΔ0) hZ0 hZle hvar
      hZint hZsqint hexpint
  have hW : 0 < W := by exact hV
  have hc : 0 < (Δ : ℝ) / 3 := by positivity
  have hden_pos : 0 < W + (Δ : ℝ) / 3 * ε :=
    add_pos_of_pos_of_nonneg hW (mul_nonneg hc.le hε)
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact div_nonneg hε hden_pos.le
  have hint : Integrable (fun ω => Real.exp (k * Z ω)) (ℙ : Measure Ω) := by
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (k * Z ω))
        (ℙ : Measure Ω) :=
      (hZ_meas.const_mul k).aemeasurable.exp.aestronglyMeasurable
    exact (MemLp.of_bound hmeas (Real.exp (k * (Δ : ℝ)))
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((le_abs_self (Z ω)).trans (hZ_abs ω)) hk_nonneg)))).integrable le_rfl
  change (ℙ : Measure Ω).real {ω | ε ≤ Z ω} ≤
    Real.exp (-ε ^ 2 / (2 * (W + (Δ : ℝ) / 3 * ε)))
  exact subgamma_tail hsub hW hc hε hint

/-- **Ch4 — Chebyshev bound on the residual degree.** The residual degree at `v` deviates from its
mean by `≥ c` with probability at most `Var / c²`. -/
theorem residualDeg_chebyshev {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - (ℙ : Measure Ω)[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|}
      ≤ ENNReal.ofReal
          (Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2) :=
  meas_ge_le_variance_div_sq (memLp_residualDeg ρ v) hc

/-- **Union bound over all vertices.** With probability at most `∑_v Var_v / c²`, some vertex's
residual degree deviates from its mean by `≥ c`; equivalently, all vertices concentrate whp. -/
theorem all_vertices_residualDeg_concentration [Fintype V] {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω) (⋃ v ∈ (Finset.univ : Finset V),
        {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - (ℙ : Measure Ω)[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|})
      ≤ ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2) := by
  calc (ℙ : Measure Ω) (⋃ v ∈ (Finset.univ : Finset V),
          {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - (ℙ : Measure Ω)[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|})
      ≤ ∑ v ∈ (Finset.univ : Finset V), (ℙ : Measure Ω)
          {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - (ℙ : Measure Ω)[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)]|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ v : V, ENNReal.ofReal
          (Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)] / c ^ 2) :=
        Finset.sum_le_sum (fun v _ => residualDeg_chebyshev ρ v hc)

/-- **Ch-Freedman(3) — two-sided one-vertex tail (STEP 2d).** Combining the upper and lower tails:
`{ω | ε ≤ |deg_res(v) − 𝔼|} ⊆ {ε ≤ deg_res − 𝔼} ∪ {ε ≤ 𝔼 − deg_res}` (via `le_abs`), so by
sub-additivity of `Measure.real` and `residualDeg_upper_tail` + `residualDeg_lower_tail`, the two-sided
deviation probability is `≤ 2·exp(−ε²/(2(V + (Δ/3)ε)))`. -/
theorem residualDeg_two_sided_tail {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) (v : V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω)).real {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * ε))) := by
  let Y : Ω → ℝ := fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ)
  let m : ℝ := ∫ ω, Y ω ∂(ℙ : Measure Ω)
  let q : ℝ := Real.exp (-ε ^ 2 / (2 * ((∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
      + (Δ : ℝ) / 3 * ε)))
  have hevent : {ω | ε ≤ |Y ω - m|} =
      {ω | ε ≤ Y ω - m} ∪ {ω | ε ≤ m - Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs, neg_sub]
  have hu : (ℙ : Measure Ω).real {ω | ε ≤ Y ω - m} ≤ q := by
    dsimp [Y, m, q]
    exact residualDeg_upper_tail ρ hp0 hp1 hr hΔ hΔ0 v hε hV
  have hl : (ℙ : Measure Ω).real {ω | ε ≤ m - Y ω} ≤ q := by
    dsimp [Y, m, q]
    exact residualDeg_lower_tail ρ hp0 hp1 hr hΔ hΔ0 v hε hV
  change (ℙ : Measure Ω).real {ω | ε ≤ |Y ω - m|} ≤ 2 * q
  rw [hevent]
  calc
    (ℙ : Measure Ω).real
        ({ω | ε ≤ Y ω - m} ∪ {ω | ε ≤ m - Y ω})
        ≤ (ℙ : Measure Ω).real {ω | ε ≤ Y ω - m} +
          (ℙ : Measure Ω).real {ω | ε ≤ m - Y ω} :=
      measureReal_union_le _ _
    _ ≤ q + q := add_le_add hu hl
    _ = 2 * q := by ring

/-- **Var-uniform — a `v`-independent variance bound** (STEP 2e, needed for the union tail). Since
every pair `(e,e')` through `v` interacts, `#interacting ≤ degree(v)² ≤ Δ²`, so
`Var[deg_res(v)] ≤ Δ²·(rΔp)` uniformly in `v`. Independent of the tails; feeds the union bound with a
single `v`-free tail exponent. -/
theorem residualDeg_variance_le_uniform {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    Var[fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ); (ℙ : Measure Ω)]
      ≤ (Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p) := by
  refine (residualDeg_variance_le_p ρ hp0 hp1 hr hΔ v).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) hp0)
  have hdeg : ((H.filter (fun f => v ∈ f)).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  calc (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
      ≤ ∑ _e ∈ H.filter (fun f => v ∈ f), ((H.filter (fun f => v ∈ f)).card : ℝ) :=
        Finset.sum_le_sum (fun e _ => by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _))
    _ = ((H.filter (fun f => v ∈ f)).card : ℝ) * ((H.filter (fun f => v ∈ f)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Δ : ℝ) * (Δ : ℝ) := mul_le_mul hdeg hdeg (by positivity) (by positivity)
    _ = (Δ : ℝ) ^ 2 := by ring

private lemma residualDeg_proxy_le_uniform {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (hp0 : 0 ≤ p) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    (∑ e ∈ H.filter (fun f => v ∈ f),
        (((H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) *
        ((r : ℝ) * Δ * p)
      ≤ (Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p) := by
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) hp0)
  have hdeg : ((H.filter (fun f => v ∈ f)).card : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast hΔ v
  calc
    (∑ e ∈ H.filter (fun f => v ∈ f),
        (((H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
        ≤ ∑ _e ∈ H.filter (fun f => v ∈ f),
            ((H.filter (fun f => v ∈ f)).card : ℝ) :=
      Finset.sum_le_sum (fun e _ => by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _))
    _ = ((H.filter (fun f => v ∈ f)).card : ℝ) *
          ((H.filter (fun f => v ∈ f)).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Δ : ℝ) * (Δ : ℝ) :=
      mul_le_mul hdeg hdeg (by positivity) (by positivity)
    _ = (Δ : ℝ) ^ 2 := by ring

/-- **Ch-Freedman(4) — union bound (STEP 2f): the FREEDMAN bad-event probability.** Union of the
two-sided tails over all vertices, with the `v`-uniform variance bound making the exponent `v`-free:
`ℙ(∃ v, |deg_res(v) − 𝔼| ≥ ε) ≤ |V| · 2·exp(−ε²/(2(Δ²·rΔp + (Δ/3)ε)))`. This is the EXPONENTIAL
replacement for the Chebyshev `all_vertices_residualDeg_concentration` (`∑ Var/c²`); it is `< 1` for
`ε ~ √(Δ²·rΔp·log|V|)` — i.e. slack `c ≪ d` when `Δ ~ d`. Feeds `exists_good_retention`. -/
theorem all_vertices_residualDeg_freedman [Fintype V] {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hVpos : ∀ v : V, 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω)).real (⋃ v ∈ (Finset.univ : Finset V),
        {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|})
      ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-ε ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * ε)))) := by
  let W : V → ℝ := fun v =>
    (∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) *
      ((r : ℝ) * Δ * p)
  let Wmax : ℝ := (Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
  let q : ℝ := 2 * Real.exp (-ε ^ 2 / (2 * (Wmax + (Δ : ℝ) / 3 * ε)))
  have htail : ∀ v : V, (ℙ : Measure Ω).real
      {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|} ≤ q := by
    intro v
    have hWle : W v ≤ Wmax := by
      dsimp [W, Wmax]
      exact residualDeg_proxy_le_uniform hp0 hΔ v
    have hWpos : 0 < W v := by
      dsimp [W]
      exact hVpos v
    have hdenpos : 0 < 2 * (W v + (Δ : ℝ) / 3 * ε) := by
      have hcε : 0 ≤ (Δ : ℝ) / 3 * ε := mul_nonneg (by positivity) hε
      positivity
    have hdenle : 2 * (W v + (Δ : ℝ) / 3 * ε) ≤
        2 * (Wmax + (Δ : ℝ) / 3 * ε) := by
      gcongr
    calc
      (ℙ : Measure Ω).real
          {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}
          ≤ 2 * Real.exp (-ε ^ 2 / (2 * (W v + (Δ : ℝ) / 3 * ε))) := by
            dsimp [W]
            exact residualDeg_two_sided_tail ρ hp0 hp1 hr hΔ hΔ0 v hε (hVpos v)
      _ ≤ q := by
        dsimp [q]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [Real.exp_le_exp]
        rw [neg_div, neg_div]
        exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg ε) hdenpos hdenle)
  change (ℙ : Measure Ω).real (⋃ v ∈ (Finset.univ : Finset V),
      {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}) ≤
    (Fintype.card V : ℝ) * q
  calc
    (ℙ : Measure Ω).real (⋃ v ∈ (Finset.univ : Finset V),
        {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|})
        ≤ ∑ v ∈ (Finset.univ : Finset V), (ℙ : Measure Ω).real
          {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ (Finset.univ : Finset V), q :=
      Finset.sum_le_sum (fun v _ => htail v)
    _ = (Fintype.card V : ℝ) * q := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Ch-mean — lower bound on the residual-degree mean (STEP 3a).**
`𝔼[deg_res(v)] = ∑_{e∋v} ℙ(e survives) = ∑_{e∋v} (1 − ℙ(e covered)) ≥ degree(v)·(1 − rΔp)`, since each
`ℙ(e covered) ≤ rΔp` (`measure_edge_hit_toReal_le`). Places the regularity bad-event
`{deg_res(v) ≤ (deg v)(1−rΔp) − c}` inside the LOWER-tail regime, letting the Freedman bad-event
replace the Chebyshev `exists_good_round`. -/
theorem residualDeg_mean_ge {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p)
      ≤ ∫ ω, (degree (residual H (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω) := by
  have hfun : (fun ω => (degree (residual H (retainedSet H ρ ω)) v : ℝ))
      = fun ω => ∑ e ∈ H.filter (fun f => v ∈ f), survivalIndicator ρ e ω :=
    funext (fun ω => residualDeg_eq_sum ρ v ω)
  rw [hfun, integral_finset_sum _ (fun e _ => (memLp_survivalIndicator ρ e).integrable one_le_two)]
  have hterm : ∀ e ∈ H.filter (fun f => v ∈ f),
      (1 - (r : ℝ) * Δ * p) ≤ ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω) := by
    intro e he
    have hmem : e ∈ H := Finset.filter_subset _ _ he
    have h1 : ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω)
        = 1 - ∫ ω, (1 - survivalIndicator ρ e ω) ∂(ℙ : Measure Ω) := by
      rw [integral_sub (integrable_const 1)
        ((memLp_survivalIndicator ρ e).integrable one_le_two)]
      simp
    rw [h1, integral_one_sub_survivalIndicator_eq_measure_hit ρ e]
    have h2 := measure_edge_hit_toReal_le ρ hp0 hr hΔ hmem
    linarith
  calc (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p)
      = ∑ _e ∈ H.filter (fun f => v ∈ f), (1 - (r : ℝ) * Δ * p) := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ∑ e ∈ H.filter (fun f => v ∈ f), ∫ ω, survivalIndicator ρ e ω ∂(ℙ : Measure Ω) :=
        Finset.sum_le_sum hterm

/-- **Ch-Freedman(5) — the regularity-failure probability is `< 1` (STEP 3b, Freedman).** The
Freedman replacement for `regularityBad_prob_lt_one` (which needed the vacuous Chebyshev sum): the
bad event `{∃v, deg_res(v) ≤ (deg v)(1−rΔp) − c}` is contained (via the mean bound
`residualDeg_mean_ge`) in `⋃_v {c ≤ |deg_res(v) − 𝔼|}`, so its probability is
`≤ |V|·2·exp(−c²/(2(Δ²rΔp+(Δ/3)c)))` (`all_vertices_residualDeg_freedman`); if that is `< 1` (a
condition satisfiable with `c ≪ d` at `Δ ~ d`), an outcome avoiding the bad event exists. This is what
lets `exists_covering_avoiding_bad` produce a good round with a SMALL slack `c` — breaking the
vacuousness of clause (a). -/
theorem regularityBad_prob_lt_one_freedman [Fintype V] {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {c : ℝ} (hc0 : 0 ≤ c)
    (hVpos : ∀ v : V, 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
    (hcond : (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
        + (Δ : ℝ) / 3 * c)))) < 1) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal < 1 := by
  have hsub : {ω | ∃ v : V, (degree (residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
      ⊆ ⋃ v ∈ (Finset.univ : Finset V), {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_univ, exists_true_left]
    refine ⟨v, ?_⟩
    have hmean := residualDeg_mean_ge ρ hp0 hp1 hr hΔ v
    rw [le_abs]
    exact Or.inr (by linarith)
  calc ((ℙ : Measure Ω) {ω | ∃ v : V, (degree (residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
      ≤ ((ℙ : Measure Ω) (⋃ v ∈ (Finset.univ : Finset V),
          {ω | c ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|})).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * c)))) :=
        all_vertices_residualDeg_freedman ρ hp0 hp1 hr hΔ hΔ0 hc0 hVpos
    _ < 1 := hcond

end Nibble
