/-
# Nibble — the COVER clause of one nibble round (unconditional, sorry-free)

`Nibble.RoundProbRefutation` shows that the packaged statement `NibbleRoundProb` is false: its
degree-ceiling clause cannot be met by any retained set once the degrees are allowed to spread over
the whole band `[L, 8L]`.  The *cover* clause of the round is however unconditionally true, and this
file proves it in the exact form the round needs:

  with retention probability `p = 1/(2rΔ)`, `Δ = max ⌈U⌉ 1` (so `rΔp = 1/2`), a single Bernoulli
  round already covers, for some outcome, at least a `1/(256r)`-fraction of the good uncovered
  vertices.

The proof is a pure first moment: `E[|roundMatching|] ≥ |K|·p(1-p)^{rΔ}`
(`Nibble.matchingSize_expectation_lower`), Bernoulli's inequality `(1-p)^{rΔ} ≥ 1 - rΔp = 1/2`, the
handshake bound `r|K| ≥ L·(#good uncovered)` (`Nibble.edge_count_lower_uncovered`) and
`|support M| = r|M|` (`Nibble.covered_card_eq`), together with `Δ ≤ 9L`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.RoundOracleKernel
import Nibble.CoveredExpectation
import Nibble.BernoulliSpace
import Nibble.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace Nibble

universe u

/-- **The cover clause of one nibble round.**  For `r ≥ 2`, an `r`-uniform `K` whose degrees are all
`≤ U ≤ 8L` and at least `L ≥ 1` at every vertex outside `S ∪ Exc`, there is a retained set
`R' ⊆ K` whose round matching covers at least a `1/(256 r)`-fraction of the good uncovered
vertices.  (This is exactly the first conclusion of `NibbleRoundProb`, which — unlike the two
degree clauses of that statement — is true.) -/
theorem exists_round_cover_fraction {V : Type u} [Fintype V] [DecidableEq V]
    (K : Finset (Finset V)) (S Exc : Finset V) {L U : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hL : 1 ≤ L) (hU8 : U ≤ 8 * L) (hU0 : 0 ≤ U)
    (huni : IsUniform K r)
    (hhi : ∀ v : V, (degree K v : ℝ) ≤ U)
    (hlo : ∀ v : V, v ∉ S → v ∉ Exc → L ≤ (degree K v : ℝ)) :
    ∃ R' : Finset (Finset V), R' ⊆ K ∧
      (1 / (256 * (r : ℝ))) * (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ))
        ≤ ((support (roundMatching R')).card : ℝ) := by
  classical
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  -- the degree ceiling as a natural number
  set Δ : ℕ := max ⌈U⌉₊ 1 with hΔdef
  have hΔpos : 0 < Δ := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hΔposR : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔpos
  have hdegΔ : ∀ x : V, degree K x ≤ Δ := by
    intro x
    have h1 : (degree K x : ℝ) ≤ (⌈U⌉₊ : ℝ) := le_trans (hhi x) (Nat.le_ceil U)
    have h2 : degree K x ≤ ⌈U⌉₊ := by exact_mod_cast h1
    exact le_trans h2 (le_max_left _ _)
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔpos
  have hΔle : (Δ : ℝ) ≤ 9 * L := by
    rw [hΔdef, Nat.cast_max]
    refine max_le ?_ (by push_cast; linarith)
    have := Nat.ceil_lt_add_one hU0
    have : (⌈U⌉₊ : ℝ) < U + 1 := by exact_mod_cast this
    linarith
  -- the retention probability
  set p : ℝ := 1 / (2 * (r : ℝ) * (Δ : ℝ)) with hpdef
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  have hrΔp : (r : ℝ) * (Δ : ℝ) * p = 1 / 2 := by
    rw [hpdef]; field_simp
  have hp1 : p ≤ 1 := by
    rw [hpdef, div_le_one (by positivity)]
    nlinarith only [hrR, hΔ1]
  -- Bernoulli: the survival factor is at least one half
  have hbern : (1 : ℝ) / 2 ≤ (1 - p) ^ (r * Δ) := by
    have h := one_add_mul_le_pow (a := -p) (by linarith) (r * Δ)
    have hcast : ((r * Δ : ℕ) : ℝ) = (r : ℝ) * (Δ : ℝ) := by push_cast; ring
    rw [hcast] at h
    have h2 : (1 : ℝ) + (r : ℝ) * (Δ : ℝ) * (-p) = 1 / 2 := by rw [mul_neg, hrΔp]; norm_num
    have h3 : (1 : ℝ) + (r : ℝ) * (Δ : ℝ) * -p ≤ (1 + -p) ^ (r * Δ) := h
    rw [h2] at h3
    simpa using h3
  -- one outcome with a large round matching
  obtain ⟨Ω, mΩ, hProb, ⟨ρ⟩⟩ := exists_bernoulliRetention K hp0 hp1
  letI := mΩ
  letI := hProb
  obtain ⟨ω, hω⟩ := exists_large_round_matching ρ hp0 hp1 huni hdegΔ
  refine ⟨retainedSet K ρ ω, Finset.filter_subset _ _, ?_⟩
  set R' : Finset (Finset V) := retainedSet K ρ ω with hR'def
  have hR'K : R' ⊆ K := Finset.filter_subset _ _
  -- the support of the round matching
  have hsupp : ((support (roundMatching R')).card : ℝ)
      = (r : ℝ) * ((roundMatching R').card : ℝ) := by
    have := covered_card_eq (H := K) (R := R') huni hR'K
    rw [covered] at this
    exact_mod_cast this
  -- the handshake lower bound on `|K|`
  have hKlow : (((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ)) * L
      ≤ (r : ℝ) * (K.card : ℝ) :=
    edge_count_lower_uncovered huni S Exc (by linarith) hlo
  set G : ℝ := ((Fintype.card V : ℝ) - (S.card : ℝ)) - (Exc.card : ℝ) with hGdef
  rcases le_or_gt G 0 with hG | hG
  · have h1 : (1 / (256 * (r : ℝ))) * G ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hG
    exact le_trans h1 (by positivity)
  · -- the main chain
    have hKpos : 0 ≤ (K.card : ℝ) := Nat.cast_nonneg _
    have hstep1 : (K.card : ℝ) * (p * (1 - p) ^ (r * Δ)) ≤ ((roundMatching R').card : ℝ) := hω
    have hstep2 : (K.card : ℝ) * (p * (1 / 2)) ≤ (K.card : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
      have : p * (1 / 2) ≤ p * (1 - p) ^ (r * Δ) := by
        exact mul_le_mul_of_nonneg_left hbern hp0
      exact mul_le_mul_of_nonneg_left this hKpos
    have hmatch : (K.card : ℝ) * p / 2 ≤ ((roundMatching R').card : ℝ) := by
      have := le_trans hstep2 hstep1
      linarith only [this]
    have hLpos : (0 : ℝ) < L := by linarith only [hΔ1, hΔle]
    -- `r|K| ≥ G·L`
    have hKG : G * L ≤ (r : ℝ) * (K.card : ℝ) := hKlow
    have hcov : (r : ℝ) * ((K.card : ℝ) * p / 2) ≤ ((support (roundMatching R')).card : ℝ) := by
      rw [hsupp]
      exact mul_le_mul_of_nonneg_left hmatch hrpos.le
    have hval : (r : ℝ) * ((K.card : ℝ) * p / 2) = ((r : ℝ) * (K.card : ℝ)) / (4 * (r : ℝ) * Δ) := by
      rw [hpdef]; field_simp; ring
    have hfinal : (1 / (256 * (r : ℝ))) * G ≤ ((r : ℝ) * (K.card : ℝ)) / (4 * (r : ℝ) * Δ) := by
      rw [le_div_iff₀ (by positivity)]
      have h1 : G * L ≤ (r : ℝ) * (K.card : ℝ) := hKG
      have h2 : (Δ : ℝ) ≤ 9 * L := hΔle
      have h3 : (0 : ℝ) < G := hG
      have h4 : 1 / (256 * (r : ℝ)) * G * (4 * (r : ℝ) * (Δ : ℝ)) = G * (Δ : ℝ) / 64 := by
        field_simp; ring
      rw [h4]
      have h5 : G * (Δ : ℝ) / 64 ≤ G * (9 * L) / 64 := by
        have := mul_le_mul_of_nonneg_left h2 (le_of_lt h3)
        linarith
      have h6 : G * (9 * L) / 64 ≤ G * L := by nlinarith
      linarith
    calc (1 / (256 * (r : ℝ))) * G
        ≤ ((r : ℝ) * (K.card : ℝ)) / (4 * (r : ℝ) * Δ) := hfinal
      _ = (r : ℝ) * ((K.card : ℝ) * p / 2) := hval.symm
      _ ≤ ((support (roundMatching R')).card : ℝ) := hcov

/-! ## The per-vertex covering probability

The cover clause above is a bare first moment on the size of the round matching.  A repaired
probabilistic round has to combine the cover with the residual-degree clauses on ONE outcome, and
for that one needs the covering *probability* of a single vertex, not just the expected size of the
matching.  The two lemmas below supply it: the events "`e` is matched" for the edges `e` through a
fixed vertex `v` are pairwise disjoint (two matched edges through `v` would not be disjoint), so
their probabilities add up, giving `ℙ(v covered) ≥ deg(v)·p(1-p)^{rΔ}` — and, at the round's own
retention probability, the vertex-independent constant `1/(36r)`. -/

section CoverProbability

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **The covering probability of a single vertex.**  The events "`e` is in the round matching",
for the edges `e` through `v`, are pairwise disjoint, so
`ℙ(v covered) ≥ deg(v)·p·(1-p)^{rΔ}`. -/
theorem prob_vertex_covered_ge {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) (v : V) :
    (degree H v : ℝ) * (p * (1 - p) ^ (r * Δ))
      ≤ ((ℙ : Measure Ω) {ω | v ∈ support (roundMatching (retainedSet H ρ ω))}).toReal := by
  classical
  set F : Finset (Finset V) := H.filter (fun e => v ∈ e) with hFdef
  have hmemF : ∀ {e : Finset V}, e ∈ F → e ∈ H ∧ v ∈ e := by
    intro e he
    rw [hFdef, Finset.mem_filter] at he
    exact he
  set E : Finset V → Set Ω := fun e => {ω | e ∈ roundMatching (retainedSet H ρ ω)} with hEdef
  have hsub : (⋃ e ∈ F, E e) ⊆ {ω | v ∈ support (roundMatching (retainedSet H ρ ω))} := by
    intro ω hω
    rw [Set.mem_iUnion₂] at hω
    obtain ⟨e, he, hmem⟩ := hω
    exact Finset.mem_biUnion.2 ⟨e, hmem, by simpa using (hmemF he).2⟩
  have hpd : (F : Set (Finset V)).PairwiseDisjoint E := by
    intro e he f hf hef
    simp only [Function.onFun, Set.disjoint_left]
    intro ω hωe hωf
    have hve : v ∈ e := (hmemF (Finset.mem_coe.1 he)).2
    have hvf : v ∈ f := (hmemF (Finset.mem_coe.1 hf)).2
    have hM := roundMatching_isMatching (Finset.Subset.refl (retainedSet H ρ ω))
    exact (Finset.disjoint_left.1 (hM.disjoint e hωe f hωf hef) hve) hvf
  have hmeas : ∀ e ∈ F, MeasurableSet (E e) := fun e he =>
    measurableSet_matchingEvent ρ (hmemF he).1
  have hunion : (ℙ : Measure Ω) (⋃ e ∈ F, E e) = ∑ e ∈ F, (ℙ : Measure Ω) (E e) :=
    measure_biUnion_finset hpd hmeas
  have hterm : ∀ e ∈ F, ENNReal.ofReal (p * (1 - p) ^ (r * Δ)) ≤ (ℙ : Measure Ω) (E e) := by
    intro e he
    have heH : e ∈ H := (hmemF he).1
    show ENNReal.ofReal _ ≤ (ℙ : Measure Ω) {ω | e ∈ roundMatching (retainedSet H ρ ω)}
    rw [matchingEvent_eq ρ heH, edge_survives_prob ρ hp0 hp1 heH]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hp0)
    exact pow_le_pow_of_le_one (by linarith) (by linarith)
      (conflicts_card_le_of_uniform hr hΔ heH)
  have hbig : (F.card : ENNReal) * ENNReal.ofReal (p * (1 - p) ^ (r * Δ))
      ≤ (ℙ : Measure Ω) {ω | v ∈ support (roundMatching (retainedSet H ρ ω))} := by
    calc (F.card : ENNReal) * ENNReal.ofReal (p * (1 - p) ^ (r * Δ))
        = ∑ _e ∈ F, ENNReal.ofReal (p * (1 - p) ^ (r * Δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ F, (ℙ : Measure Ω) (E e) := Finset.sum_le_sum hterm
      _ = (ℙ : Measure Ω) (⋃ e ∈ F, E e) := hunion.symm
      _ ≤ _ := measure_mono hsub
  have hnn : 0 ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hfin := ENNReal.toReal_mono (measure_ne_top (ℙ : Measure Ω) _) hbig
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn] at hfin
  simpa [degree, hFdef] using hfin

/-- **The covering probability at the round's own retention probability.**  With `p = 1/(2rΔ)` and
`Δ ≤ 9L`, every vertex of degree `≥ L` is covered with probability at least `1/(36r)` — a constant
depending only on the uniformity `r`, in particular independent of `|V|` and of the degree
scale. -/
theorem prob_vertex_covered_ge_const {H : Finset (Finset V)} {p L : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hr2 : 2 ≤ r) (hΔ0 : 0 < Δ)
    (hpdef : p = 1 / (2 * (r : ℝ) * (Δ : ℝ))) (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ)
    (hΔle : (Δ : ℝ) ≤ 9 * L) (v : V) (hv : L ≤ (degree H v : ℝ)) :
    1 / (36 * (r : ℝ)) ≤ ((ℙ : Measure Ω) {ω | v ∈ support (roundMatching
      (retainedSet H ρ ω))}).toReal := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ0
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by linarith only [hΔ1]
  have hLpos : (0 : ℝ) < L := by linarith only [hΔle, hΔ1]
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  have hrΔp : (r : ℝ) * (Δ : ℝ) * p = 1 / 2 := by rw [hpdef]; field_simp
  have hp1 : p ≤ 1 := by
    rw [hpdef, div_le_one (by positivity)]
    nlinarith only [hrR, hΔ1]
  have hbern : (1 : ℝ) / 2 ≤ (1 - p) ^ (r * Δ) := by
    have h := one_add_mul_le_pow (a := -p) (by linarith) (r * Δ)
    have hcast : ((r * Δ : ℕ) : ℝ) = (r : ℝ) * (Δ : ℝ) := by push_cast; ring
    rw [hcast] at h
    have h2 : (1 : ℝ) + (r : ℝ) * (Δ : ℝ) * (-p) = 1 / 2 := by rw [mul_neg, hrΔp]; norm_num
    have h3 : (1 : ℝ) + (r : ℝ) * (Δ : ℝ) * -p ≤ (1 + -p) ^ (r * Δ) := h
    rw [h2] at h3
    simpa using h3
  refine le_trans ?_ (prob_vertex_covered_ge ρ hp0 hp1 hr hΔ v)
  have hstep : L * (p * (1 / 2)) ≤ (degree H v : ℝ) * (p * (1 - p) ^ (r * Δ)) := by
    refine mul_le_mul hv (mul_le_mul_of_nonneg_left hbern hp0) (by positivity) (by linarith)
  refine le_trans ?_ hstep
  rw [hpdef]
  rw [div_le_iff₀ (by positivity)]
  have hkey : L * (1 / (2 * (r : ℝ) * (Δ : ℝ)) * (1 / 2)) * (36 * (r : ℝ)) = 9 * L / (Δ : ℝ) := by
    field_simp; ring
  rw [hkey, le_div_iff₀ hΔpos]
  linarith only [hΔle]

end CoverProbability

end Nibble
