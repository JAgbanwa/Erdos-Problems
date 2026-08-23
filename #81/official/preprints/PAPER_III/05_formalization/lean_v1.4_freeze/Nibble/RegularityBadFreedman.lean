/-
# Nibble — Freedman bound for the regularity-bad event

Standalone, Mathlib-only. This is STEP 3b of the Freedman re-cabling: the old Chebyshev route bounded
the bad event

  `{ω | ∃ v, deg_res(v) ≤ deg(v) * (1 - rΔp) - c}`

directly by a variance sum. Here we instead use the mean lower bound
`residualDeg_mean_ge` to place this event inside the two-sided Freedman deviation event

  `{ω | ∃ v, c ≤ |deg_res(v) - E[deg_res(v)]|}`.

Then `all_vertices_residualDeg_freedman` gives the exponential probability bound.
-/
import Nibble.Chebyshev
import Nibble.RegularityBad
import Nibble.InvariantDegree
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Residual degree is bounded by the original degree. -/
theorem degree_residual_le_original {H R : Finset (Finset V)} (v : V) :
    degree (Hypergraph.residual H R) v ≤ degree H v :=
  degree_mono (residual_subset H R) v

/-- A vertex witnessing the one-sided bad event must have positive original degree when `c > 0`. -/
theorem bad_vertex_degree_pos {H : Finset (Finset V)} {p c : ℝ} {r Δ : ℕ} {R : Finset (Finset V)}
    {v : V} (hc : 0 < c)
    (hbad : (degree (Hypergraph.residual H R) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c) :
    0 < degree H v := by
  by_contra hnot
  have hdeg0 : degree H v = 0 := Nat.eq_zero_of_not_pos hnot
  have hres0 : degree (Hypergraph.residual H R) v = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hdeg0] using degree_residual_le_original (H := H) (R := R) v)
  have : (0 : ℝ) ≤ -c := by
    simpa [hdeg0, hres0] using hbad
  linarith only [hc, this]

/-- Active vertices have a positive Freedman variance proxy as soon as the sampling parameter is
positive. This removes the old global nonzero-proxy side condition for isolated vertices. -/
theorem active_residualDeg_proxy_pos {H : Finset (Finset V)} {r Δ : ℕ} {p : ℝ}
    (hr1 : 1 ≤ r) (hΔ0 : 0 < Δ) (hp : 0 < p) :
    ∀ v : V, 0 < degree H v →
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
        * ((r : ℝ) * Δ * p) := by
  intro v hv
  classical
  rw [degree] at hv
  obtain ⟨e, he⟩ := Finset.card_pos.mp hv
  rw [Finset.mem_filter] at he
  obtain ⟨heH, hve⟩ := he
  have houter : e ∈ H.filter (fun f => v ∈ f) := Finset.mem_filter.mpr ⟨heH, hve⟩
  have hende : ¬ Disjoint (depNbhd H e) (depNbhd H e) := by
    rw [Finset.not_disjoint_iff_nonempty_inter]
    refine ⟨e, ?_⟩
    rw [Finset.mem_inter]
    have hne : ¬ Disjoint e e := by
      rw [Finset.not_disjoint_iff_nonempty_inter]
      exact ⟨v, by simp [hve]⟩
    have hdep : e ∈ depNbhd H e := mem_depNbhd_of_touch heH hne
    exact ⟨hdep, hdep⟩
  have hinner_pos :
      0 < (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      ⟨e, Finset.mem_filter.mpr ⟨houter, hende⟩⟩
  have hsum_pos :
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) := by
    exact lt_of_lt_of_le hinner_pos
      (Finset.single_le_sum
        (s := H.filter (fun f => v ∈ f))
        (f := fun e => (((H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
        (fun _ _ => by positivity)
        houter)
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr1
  have hΔpos : 0 < (Δ : ℝ) := by exact_mod_cast hΔ0
  exact mul_pos hsum_pos (mul_pos (mul_pos hrpos hΔpos) hp)

/-- All-active-vertices Freedman union bound. Vertices outside `active` are not included, so the
variance-proxy positivity hypothesis is only needed on active vertices. -/
theorem all_active_vertices_residualDeg_freedman {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {ε : ℝ} (hε : 0 ≤ ε)
    (hVpos : ∀ v : V, 0 < degree H v →
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω)).real (⋃ v ∈ (Finset.univ.filter (fun v : V => 0 < degree H v)),
        {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|})
      ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-ε ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * ε)))) := by
  let Active : Finset V := Finset.univ.filter (fun v : V => 0 < degree H v)
  let Wmax : ℝ := (Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
  let q : ℝ := 2 * Real.exp (-ε ^ 2 / (2 * (Wmax + (Δ : ℝ) / 3 * ε)))
  have htail : ∀ v ∈ Active, (ℙ : Measure Ω).real
      {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|} ≤ q := by
    intro v hv
    have hvpos : 0 < degree H v := by
      simpa [Active] using hv
    have hWle : (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
        ≤ Wmax := by
      dsimp [Wmax]
      have hdeg : ((H.filter (fun f => v ∈ f)).card : ℝ) ≤ Δ := by
        exact_mod_cast hΔ v
      calc
        (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
            ≤ (((H.filter (fun f => v ∈ f)).card : ℝ)
                * ((H.filter (fun f => v ∈ f)).card : ℝ)) * ((r : ℝ) * Δ * p) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp0)
              calc
                (∑ e ∈ H.filter (fun f => v ∈ f),
                  (((H.filter (fun f => v ∈ f)).filter
                    (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
                    ≤ ∑ _e ∈ H.filter (fun f => v ∈ f),
                        ((H.filter (fun f => v ∈ f)).card : ℝ) := by
                      refine Finset.sum_le_sum ?_
                      intro e he
                      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
                  _ = ((H.filter (fun f => v ∈ f)).card : ℝ)
                        * ((H.filter (fun f => v ∈ f)).card : ℝ) := by
                      rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ((Δ : ℝ) * (Δ : ℝ)) * ((r : ℝ) * (Δ : ℝ) * p) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp0)
              have hcardnn : (0 : ℝ) ≤ ((H.filter (fun f => v ∈ f)).card : ℝ) := Nat.cast_nonneg _
              nlinarith only [hdeg, hcardnn]
            _ = (Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p) := by ring
    have hWpos := hVpos v hvpos
    have hdenpos : 0 < 2 * (((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
          + (Δ : ℝ) / 3 * ε) := by
      have hcε : 0 ≤ (Δ : ℝ) / 3 * ε := mul_nonneg (by positivity) hε
      positivity
    have hdenle : 2 * (((∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
          + (Δ : ℝ) / 3 * ε)
        ≤ 2 * (Wmax + (Δ : ℝ) / 3 * ε) := by
      gcongr
    calc
      (ℙ : Measure Ω).real
          {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}
          ≤ 2 * Real.exp (-ε ^ 2 / (2 * (((∑ e ∈ H.filter (fun f => v ∈ f),
              (((H.filter (fun f => v ∈ f)).filter
                (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p))
              + (Δ : ℝ) / 3 * ε))) := by
            exact residualDeg_two_sided_tail ρ hp0 hp1 hr hΔ hΔ0 v hε hWpos
      _ ≤ q := by
        dsimp [q, Wmax]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [Real.exp_le_exp]
        rw [neg_div, neg_div]
        exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg ε) hdenpos hdenle)
  change (ℙ : Measure Ω).real (⋃ v ∈ Active,
      {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}) ≤
    (Fintype.card V : ℝ) * q
  calc
    (ℙ : Measure Ω).real (⋃ v ∈ Active,
        {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|})
        ≤ ∑ v ∈ Active, (ℙ : Measure Ω).real
          {ω | ε ≤ |(degree (residual H (retainedSet H ρ ω)) v : ℝ)
            - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ Active, q :=
      Finset.sum_le_sum (fun v hv => htail v hv)
    _ = (Active.card : ℝ) * q := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card V : ℝ) * q := by
      have hqnn : 0 ≤ q := by dsimp [q]; positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ Active) hqnn

/-- **STEP 3b — Freedman probability bound for the one-sided regularity-bad event.**
The mean lower bound turns
`deg_res(v) ≤ deg(H,v) * (1 - rΔp) - c` into
`c ≤ |deg_res(v) - E[deg_res(v)]|`, so the already-proved all-vertices Freedman tail applies. -/
theorem regularityBad_freedman_prob_toReal_le {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {c : ℝ} (hc : 0 ≤ c)
    (hVpos : ∀ v : V, 0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
      ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * c)))) := by
  let Bad : Set Ω := {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
  let Tail : Set Ω := ⋃ v ∈ (Finset.univ : Finset V),
      {ω | c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}
  have hsub : Bad ⊆ Tail := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    refine Set.mem_biUnion (Finset.mem_univ v) ?_
    have hmean := residualDeg_mean_ge ρ hp0 hp1 hr hΔ v
    have hdev : c ≤
        (∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω))
          - (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ) := by
      linarith only [hv, hmean]
    have hnonpos :
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          - (∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω))
        ≤ 0 := by
      linarith only [hc, hdev]
    change c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
      - ∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|
    rw [abs_of_nonpos hnonpos]
    linarith only [hdev]
  have hmeasure : (ℙ : Measure Ω) Bad ≤ (ℙ : Measure Ω) Tail := measure_mono hsub
  have hTail :
      ((ℙ : Measure Ω)).real Tail
        ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
            + (Δ : ℝ) / 3 * c)))) := by
    simpa [Tail] using all_vertices_residualDeg_freedman ρ hp0 hp1 hr hΔ hΔ0 hc hVpos
  have hmono : ((ℙ : Measure Ω) Bad).toReal ≤ ((ℙ : Measure Ω) Tail).toReal :=
    ENNReal.toReal_mono (measure_ne_top (ℙ : Measure Ω) Tail) hmeasure
  exact hmono.trans hTail

/-- Active-vertex version of the Freedman bound for the one-sided regularity-bad event. This is the
usable form for iteration: isolated vertices cannot witness the bad event when `c > 0`, so the
variance-proxy positivity hypothesis is required only for vertices with positive original degree. -/
theorem regularityBad_freedman_active_prob_toReal_le {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ) {c : ℝ} (hc : 0 < c)
    (hVpos : ∀ v : V, 0 < degree H v →
      0 < (∑ e ∈ H.filter (fun f => v ∈ f),
          (((H.filter (fun f => v ∈ f)).filter
            (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)) :
    ((ℙ : Measure Ω) {ω | ∃ v : V,
        (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
          ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}).toReal
      ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
          + (Δ : ℝ) / 3 * c)))) := by
  let Bad : Set Ω := {ω | ∃ v : V,
      (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        ≤ (degree H v : ℝ) * (1 - r * Δ * p) - c}
  let Tail : Set Ω := ⋃ v ∈ (Finset.univ.filter (fun v : V => 0 < degree H v)),
      {ω | c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|}
  have hsub : Bad ⊆ Tail := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    have hvpos : 0 < degree H v :=
      bad_vertex_degree_pos (H := H) (R := retainedSet H ρ ω) (p := p) (c := c) (r := r) (Δ := Δ)
        (v := v) hc hv
    have hvActive : v ∈ Finset.univ.filter (fun v : V => 0 < degree H v) := by
      simp [hvpos]
    refine Set.mem_biUnion hvActive ?_
    · have hmean := residualDeg_mean_ge ρ hp0 hp1 hr hΔ v
      have hdev : c ≤
          (∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω))
            - (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ) := by
        linarith only [hv, hmean]
      have hnonpos :
          (degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
            - (∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω))
          ≤ 0 := by
        linarith only [hc, hdev]
      change c ≤ |(degree (Hypergraph.residual H (retainedSet H ρ ω)) v : ℝ)
        - ∫ ω', (degree (Hypergraph.residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)|
      rw [abs_of_nonpos hnonpos]
      linarith only [hdev]
  have hmeasure : (ℙ : Measure Ω) Bad ≤ (ℙ : Measure Ω) Tail := measure_mono hsub
  have hTail :
      ((ℙ : Measure Ω)).real Tail
        ≤ (Fintype.card V : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * ((Δ : ℝ) ^ 2 * ((r : ℝ) * Δ * p)
            + (Δ : ℝ) / 3 * c)))) := by
    simpa [Tail] using all_active_vertices_residualDeg_freedman ρ hp0 hp1 hr hΔ hΔ0 (le_of_lt hc) hVpos
  have hmono : ((ℙ : Measure Ω) Bad).toReal ≤ ((ℙ : Measure Ω) Tail).toReal :=
    ENNReal.toReal_mono (measure_ne_top (ℙ : Measure Ω) Tail) hmeasure
  exact hmono.trans hTail

end Nibble
