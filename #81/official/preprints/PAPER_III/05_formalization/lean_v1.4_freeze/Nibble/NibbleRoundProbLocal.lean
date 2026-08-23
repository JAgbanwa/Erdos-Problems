/-
# Nibble — LOCAL attack on `NibbleRoundProb` (the sole remaining probabilistic atom)

`NibbleRoundProb` (RoundOracleKernel.lean) is closed by controlling THREE aggregate events and
taking their union complement:

* **A (cover)** — the round matching covers a `1/(256r)` fraction of the good uncovered vertices.
  Needs a McDiarmid concentration of the matching size (`BoundedDiff` + `Concentration`).
* **B (low)** — at most `δlow·|V|` good uncovered vertices drop below `(1/2−ε/2)L` residual degree.
  Per-vertex lower tail (`residualDeg_lower_tail`) + Markov over vertices (`measure_badCount_gt_le`).
* **C (high)** — at most `blow·|V|` vertices exceed `(1/2+ε)U` residual degree.
  Per-vertex upper tail (`residualDeg_upper_tail`) + the same Markov.

This file proves **B and C** — the two count bounds — as standalone bricks (they need only the
per-vertex tails + `MarkovVertices.measure_badCount_gt_le`, no union bound over `|V|` and `L₀`
independent of `|V|`). The cover bound **A** is the remaining hard step (in progress / delegated in
parallel).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Chebyshev
import Nibble.MarkovVertices
import Nibble.RegularityBad
import Nibble.BoundedDiff
import Nibble.Pruning
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph

namespace Nibble

/-! ## A — the McDiarmid bounded difference of the matching size

The single novel combinatorial input for the cover concentration: toggling one edge changes the
round matching's cardinality by at most `e.card = r`, NOT by `rΔ`.  The reason is the matching
structure — the edges of a matching that meet a fixed `e` inject into the `r` vertices of `e`. -/

section BoundedDifference

variable {V : Type*} [DecidableEq V]

/-- **Matching edges meeting a fixed edge inject into its vertices.**  In a matching `M` (pairwise
disjoint edges), at most `e.card` edges meet `e`, because distinct meeting edges are disjoint and so
pick distinct vertices of `e`. -/
theorem matching_meets_edge_card_le {M : Finset (Finset V)}
    (hM : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint a b) (e : Finset V) :
    (M.filter (fun f => ¬ Disjoint e f)).card ≤ e.card := by
  classical
  set F := M.filter (fun f => ¬ Disjoint e f) with hF
  -- double counting: |F| ≤ ∑_{f∈F} |e ∩ f| = ∑_{x∈e} #{f∈F : x∈f} ≤ ∑_{x∈e} 1 = |e|
  have hstep1 : F.card ≤ ∑ f ∈ F, (e ∩ f).card := by
    rw [Finset.card_eq_sum_ones F]
    refine Finset.sum_le_sum (fun f hf => ?_)
    rw [hF, Finset.mem_filter] at hf
    have : (e ∩ f).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hf.2
    exact this.card_pos
  have hswap : ∑ f ∈ F, (e ∩ f).card = ∑ x ∈ e, (F.filter (fun f => x ∈ f)).card := by
    have : ∀ f ∈ F, (e ∩ f).card = ∑ x ∈ e, (if x ∈ f then 1 else 0) := by
      intro f _
      rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.card_filter]
  have hstep2 : ∀ x ∈ e, (F.filter (fun f => x ∈ f)).card ≤ 1 := by
    intro x _
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, hF, Finset.mem_filter] at ha hb
    by_contra hab
    exact (Finset.disjoint_left.mp (hM a ha.1.1 b hb.1.1 hab) ha.2) hb.2
  calc F.card ≤ ∑ f ∈ F, (e ∩ f).card := hstep1
    _ = ∑ x ∈ e, (F.filter (fun f => x ∈ f)).card := hswap
    _ ≤ ∑ _x ∈ e, 1 := Finset.sum_le_sum hstep2
    _ = e.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- Adding one edge increases the round matching by at most one edge. -/
theorem roundMatching_card_insert_le (R : Finset (Finset V)) (e : Finset V) :
    (roundMatching (insert e R)).card ≤ (roundMatching R).card + 1 := by
  classical
  have hsub : roundMatching (insert e R) ⊆ roundMatching R ∪ {e} := by
    intro f hf
    by_cases h : f ∈ roundMatching R
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (roundMatching_insert_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hf, h⟩))
  calc (roundMatching (insert e R)).card ≤ (roundMatching R ∪ {e}).card :=
        Finset.card_le_card hsub
    _ ≤ (roundMatching R).card + ({e} : Finset (Finset V)).card := Finset.card_union_le _ _
    _ = (roundMatching R).card + 1 := by rw [Finset.card_singleton]

/-- Adding one edge decreases the round matching by at most `e.card` edges (matching structure). -/
theorem roundMatching_card_ge_insert (R : Finset (Finset V)) (e : Finset V) :
    (roundMatching R).card ≤ (roundMatching (insert e R)).card + e.card := by
  classical
  have hM : IsMatching R (roundMatching R) := roundMatching_isMatching (subset_refl R)
  have hsub : roundMatching R ⊆ roundMatching (insert e R)
      ∪ (roundMatching R).filter (fun f => ¬ Disjoint e f) := by
    intro f hf
    by_cases h : f ∈ roundMatching (insert e R)
    · exact Finset.mem_union_left _ h
    · have := roundMatching_erase_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hf, h⟩)
      rw [Finset.mem_filter] at this
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf, this.2⟩)
  have hcard : ((roundMatching R).filter (fun f => ¬ Disjoint e f)).card ≤ e.card :=
    matching_meets_edge_card_le hM.disjoint e
  calc (roundMatching R).card
      ≤ (roundMatching (insert e R)
          ∪ (roundMatching R).filter (fun f => ¬ Disjoint e f)).card := Finset.card_le_card hsub
    _ ≤ (roundMatching (insert e R)).card
          + ((roundMatching R).filter (fun f => ¬ Disjoint e f)).card := Finset.card_union_le _ _
    _ ≤ (roundMatching (insert e R)).card + e.card := by omega

/-- **The McDiarmid bounded difference of the matching size.**  Toggling one edge changes the round
matching's cardinality by at most `e.card`. -/
theorem roundMatching_card_toggle_abs_le (R : Finset (Finset V)) (e : Finset V)
    (he : 1 ≤ e.card) :
    |((roundMatching (insert e R)).card : ℤ) - (roundMatching R).card| ≤ (e.card : ℤ) := by
  have h1 := roundMatching_card_insert_le R e
  have h2 := roundMatching_card_ge_insert R e
  rw [abs_le]
  refine ⟨by omega, by omega⟩

/-- **Config-toggle bounded difference of the matching size (the `hbd` for McDiarmid).**  Viewing
retention as a per-edge bit configuration `ω : Finset V → Bool` (`retained = H.filter (ω · = true)`),
toggling the bit of edge `e` changes the round matching's cardinality by at most `e.card`.  Off-`H`
toggles are inert.  For an `r`-uniform `H` the coefficient is `r` on `H` and `0` off `H`. -/
theorem matchingCardConfig_boundedDiff {H : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r)
    (hr1 : 1 ≤ r) (e : Finset V) (ω ω' : Finset V → Bool) (hagree : ∀ g, g ≠ e → ω g = ω' g) :
    |((roundMatching (H.filter (fun g => ω g = true))).card : ℤ)
       - (roundMatching (H.filter (fun g => ω' g = true))).card|
      ≤ (if e ∈ H then (r : ℤ) else 0) := by
  classical
  by_cases hee : ω e = ω' e
  · have hRR : H.filter (fun g => ω g = true) = H.filter (fun g => ω' g = true) := by
      ext g
      rcases eq_or_ne g e with rfl | hge
      · simp only [Finset.mem_filter, hee]
      · simp only [Finset.mem_filter, hagree g hge]
    rw [hRR]; simp; positivity
  · by_cases heH : e ∈ H
    · have he_card : e.card = r := hr e heH
      have hecard1 : 1 ≤ e.card := by rw [he_card]; exact hr1
      have key : (ω e = false ∧ ω' e = true) ∨ (ω e = true ∧ ω' e = false) := by
        revert hee; cases ω e <;> cases ω' e <;> simp
      rw [if_pos heH]
      rcases key with ⟨h0, h1'⟩ | ⟨h1, h0'⟩
      · have hins : H.filter (fun g => ω' g = true)
            = insert e (H.filter (fun g => ω g = true)) := by
          ext g
          simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · rintro ⟨hg, hgt⟩
            rcases eq_or_ne g e with rfl | hge
            · exact Or.inl rfl
            · exact Or.inr ⟨hg, by rwa [hagree g hge]⟩
          · rintro (rfl | ⟨hg, hgt⟩)
            · exact ⟨heH, h1'⟩
            · have hge : g ≠ e := by rintro rfl; rw [h0] at hgt; simp at hgt
              exact ⟨hg, by rwa [← hagree g hge]⟩
        rw [hins, ← he_card]
        have h := roundMatching_card_toggle_abs_le (H.filter (fun g => ω g = true)) e hecard1
        rw [abs_sub_comm] at h
        exact h
      · have hins : H.filter (fun g => ω g = true)
            = insert e (H.filter (fun g => ω' g = true)) := by
          ext g
          simp only [Finset.mem_insert, Finset.mem_filter]
          constructor
          · rintro ⟨hg, hgt⟩
            rcases eq_or_ne g e with rfl | hge
            · exact Or.inl rfl
            · exact Or.inr ⟨hg, by rwa [← hagree g hge]⟩
          · rintro (rfl | ⟨hg, hgt⟩)
            · exact ⟨heH, h1⟩
            · have hge : g ≠ e := by rintro rfl; rw [h0'] at hgt; simp at hgt
              exact ⟨hg, by rwa [hagree g hge]⟩
        rw [hins, ← he_card]
        exact roundMatching_card_toggle_abs_le (H.filter (fun g => ω' g = true)) e hecard1
    · have hRR : H.filter (fun g => ω g = true) = H.filter (fun g => ω' g = true) := by
        ext g
        rcases eq_or_ne g e with rfl | hge
        · simp only [Finset.mem_filter]
          constructor <;> rintro ⟨hg, _⟩ <;> exact absurd hg heH
        · simp only [Finset.mem_filter, hagree g hge]
      rw [hRR, if_neg heH]; simp

end BoundedDifference

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The per-vertex "neighbour coefficient" appearing in the Freedman tail bricks. -/
noncomputable def nbCoeff (H : Finset (Finset V)) (r Δ : ℕ) (p : ℝ) (v : V) : ℝ :=
  (∑ e ∈ H.filter (fun f => v ∈ f),
    (((H.filter (fun f => v ∈ f)).filter
      (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)

/-- **B — the low-degree count bound (per-vertex lower tail + Markov).**  If every vertex's residual
degree deviates below its mean by `≥ a` with probability at most `q`, then more than a `δ`-fraction
of vertices deviate that far below with probability at most `q/δ`.  This is the vertex-Markov
assembly specialised to the Freedman lower tail; the caller turns "below `(1/2−ε/2)L`" into "below
mean by `(ε/2)L`" using `residualDeg_mean_ge`. -/
theorem low_count_bound {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ)
    {a q δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hq0 : 0 ≤ q)
    (hpos : ∀ v : V, 0 < nbCoeff H r Δ p v)
    (hqbd : ∀ v : V,
      Real.exp (-a ^ 2 / (2 * (nbCoeff H r Δ p v + (Δ : ℝ) / 3 * a))) ≤ q) :
    ((ℙ : Measure Ω) {ω | δ * (Fintype.card V : ℝ) <
        badCount (fun v => {ω | a ≤ (∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ)
          ∂(ℙ : Measure Ω)) - (degree (residual H (retainedSet H ρ ω)) v : ℝ)}) ω}).toReal
      ≤ q / δ := by
  classical
  set Bad : V → Set Ω := fun v => {ω | a ≤ (∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ)
    ∂(ℙ : Measure Ω)) - (degree (residual H (retainedSet H ρ ω)) v : ℝ)} with hBaddef
  have hmeas : ∀ v, MeasurableSet (Bad v) := by
    intro v
    exact measurableSet_le measurable_const
      (measurable_const.sub (measurable_residual_degree ρ v))
  have hqv : ∀ v, ((ℙ : Measure Ω) (Bad v)).toReal ≤ q := by
    intro v
    have htail := residualDeg_lower_tail ρ hp0 hp1 hr hΔ hΔ0 v ha (hpos v)
    have : ((ℙ : Measure Ω)).real (Bad v)
        ≤ Real.exp (-a ^ 2 / (2 * (nbCoeff H r Δ p v + (Δ : ℝ) / 3 * a))) := by
      simpa [Bad, nbCoeff] using htail
    rw [measureReal_def] at this
    exact le_trans this (hqbd v)
  exact measure_badCount_gt_le Bad hmeas hq0 hqv hδ

/-- **C — the high-degree count bound (per-vertex upper tail + Markov).** Symmetric to
`low_count_bound`, using the Freedman upper tail. The caller turns "above `(1/2+ε)U`" into "above
mean by `t`" using an upper bound on the mean. -/
theorem high_count_bound {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (hΔ0 : 0 < Δ)
    {a q δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hq0 : 0 ≤ q)
    (hpos : ∀ v : V, 0 < nbCoeff H r Δ p v)
    (hqbd : ∀ v : V,
      Real.exp (-a ^ 2 / (2 * (nbCoeff H r Δ p v + (Δ : ℝ) / 3 * a))) ≤ q) :
    ((ℙ : Measure Ω) {ω | δ * (Fintype.card V : ℝ) <
        badCount (fun v => {ω | a ≤ (degree (residual H (retainedSet H ρ ω)) v : ℝ)
          - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)}) ω}).toReal
      ≤ q / δ := by
  classical
  set Bad : V → Set Ω := fun v => {ω | a ≤ (degree (residual H (retainedSet H ρ ω)) v : ℝ)
    - ∫ ω', (degree (residual H (retainedSet H ρ ω')) v : ℝ) ∂(ℙ : Measure Ω)} with hBaddef
  have hmeas : ∀ v, MeasurableSet (Bad v) := by
    intro v
    exact measurableSet_le measurable_const
      ((measurable_residual_degree ρ v).sub measurable_const)
  have hqv : ∀ v, ((ℙ : Measure Ω) (Bad v)).toReal ≤ q := by
    intro v
    have htail := residualDeg_upper_tail ρ hp0 hp1 hr hΔ hΔ0 v ha (hpos v)
    have : ((ℙ : Measure Ω)).real (Bad v)
        ≤ Real.exp (-a ^ 2 / (2 * (nbCoeff H r Δ p v + (Δ : ℝ) / 3 * a))) := by
      simpa [Bad, nbCoeff] using htail
    rw [measureReal_def] at this
    exact le_trans this (hqbd v)
  exact measure_badCount_gt_le Bad hmeas hq0 hqv hδ

end Nibble
