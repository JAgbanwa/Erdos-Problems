/-
# Nibble — the weighted (fractional) nibble across load scales

`Nibble.fracNibble_weightedCodegree_pad` (`Nibble.FracNibbleDense`) proves the repaired weighted
nibble `Nibble.FracNibbleWeightedTheorem` up to an additive error governed by the *total
deficiency* `Δ = ∑_{v ∈ R} (1 - load v)` of the fractional matching on the region `R` carrying the
edges: it produces a matching of size at least `(1-β)(∑w + Δ) - (Δ + 1)`.  Since the padding loses
`β·Δ`, that bound is useful exactly when `Δ = O(∑w)`, i.e. when the *average load* on `R` is
bounded below.  This file completes that regime and reduces the general statement to a single,
concretely delimited residual.

* `Nibble.fracNibble_weightedCodegree_dense` — **the dense regime, proved outright.**  For every
  `r ≥ 2`, `β > 0` and `ε > 0` there is `γ > 0` such that every `r`-uniform hypergraph carrying a
  fractional matching `w` of weighted codegree `≤ γ` on a region `R` with `ε|R| ≤ ∑w` has a
  matching of size at least `(1-β)∑w`.  There is **no** additive error and **no** lower bound on
  `∑w`: the three regimes `Δ` large (padding), `Δ` small (near-perfect, so the localised nibble
  applies directly) and `∑w` bounded (then the whole hypergraph lives on boundedly many vertices,
  so all its weights are `≤ γ` and a single edge suffices) are treated separately.
* `Nibble.fracNibble_weightedCodegree_heavy` — the same conclusion whenever every vertex of the
  region carries load at least `λ`, for an arbitrary `λ > 0` fixed in advance.
* `Nibble.exists_matching_of_load_le` — the greedy bound at load level `λ`: if all loads are at
  most `λ` then some matching `M` has `∑w ≤ rλ|M|`; for `λ < 1/r` this *proves* the weighted
  nibble outright.
* `Nibble.FracNibbleWeightedHeavyEdge` — the weighted nibble for hypergraphs in which **every edge
  contains a vertex of load at least `λ`**, `λ > 0` being fixed in advance.
* `Nibble.FracNibbleWeightedMixed` — **the residual**, a formally weaker statement: the same, with
  a distinguished heavy set `X` meeting every edge, all of whose vertices are heavy, all vertices
  outside `X` being light.
* `Nibble.fracNibbleWeightedTheorem_of_mixed`,
  `Nibble.fracNibbleWeightedTheorem_of_heavyEdge` — the residual implies
  `Nibble.FracNibbleWeightedTheorem` in full.  The edges all of whose vertices have load below
  `λ = β/(4r)` are handled by the greedy bound, which beats `(1-β)∑w` by the factor `1/(rλ)`; so
  either they already carry enough weight to finish, or the edges meeting a heavy vertex carry all
  but a `β/4`-fraction of the weight and the residual finishes.

Together with `Nibble.fracNibble_weightedCodegree_heavy` (which is exactly the residual when the
heavy set contains *all* the vertices touched by an edge) this isolates the remaining obligation as
the genuinely *mixed-scale* configuration: edges that contain both a heavy vertex and vertices of
arbitrarily small load.  See `RESIDUAL.md`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.FracNibbleDense
import Nibble.GreedyFracMatching
import Nibble.FracNibbleRepaired

open Finset Hypergraph

namespace Nibble

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ### The load of a region -/

/-- **Double counting on a region.**  If every edge lies inside `R`, the loads of the vertices of
`R` add up to `r·∑w`. -/
theorem sum_load_region (H : Finset (Finset W)) (w : Finset W → ℝ) (R : Finset W) {r : ℕ}
    (hunif : IsUniform H r) (hsub : ∀ T ∈ H, T ⊆ R) :
    ∑ v ∈ R, ∑ T ∈ H.filter (fun T => v ∈ T), w T = (r : ℝ) * ∑ T ∈ H, w T := by
  classical
  calc ∑ v ∈ R, ∑ T ∈ H.filter (fun T => v ∈ T), w T
      = ∑ v ∈ R, ∑ T ∈ H, (if v ∈ T then w T else 0) :=
        Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
    _ = ∑ T ∈ H, ∑ v ∈ R, (if v ∈ T then w T else 0) := Finset.sum_comm
    _ = ∑ T ∈ H, (r : ℝ) * w T := by
        refine Finset.sum_congr rfl (fun T hT => ?_)
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (hsub T hT), Finset.sum_const, hunif T hT, nsmul_eq_mul]
    _ = (r : ℝ) * ∑ T ∈ H, w T := by rw [Finset.mul_sum]

/-- The deficiency of `w` on a region equals `|R| - r∑w`. -/
theorem defic_eq (H : Finset (Finset W)) (w : Finset W → ℝ) (R : Finset W) {r : ℕ}
    (hunif : IsUniform H r) (hsub : ∀ T ∈ H, T ⊆ R) :
    defic H w R = (R.card : ℝ) - (r : ℝ) * ∑ T ∈ H, w T := by
  classical
  rw [defic, Finset.sum_sub_distrib, sum_load_region H w R hunif hsub, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-! ### The greedy bound at a load level -/

/-- **The greedy bound at load level `λ`.**  If every vertex carries load at most `λ` then some
matching `M` satisfies `∑w ≤ rλ|M|`. -/
theorem exists_matching_of_load_le (H : Finset (Finset W)) {r : ℕ} (hr : 1 ≤ r)
    (hunif : IsUniform H r) (w : Finset W → ℝ) (hwnn : ∀ T, 0 ≤ w T) {lam : ℝ} (hlam : 0 < lam)
    (hload : ∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ lam) :
    ∃ M : Finset (Finset W), IsMatching H M ∧ (∑ T ∈ H, w T) ≤ (r : ℝ) * lam * (M.card : ℝ) := by
  classical
  obtain ⟨M, hM, hMle⟩ := exists_matching_sum_le_mul H hr hunif (fun T => w T / lam)
    (fun T => div_nonneg (hwnn T) hlam.le)
    (fun v => by
      rw [show ∑ T ∈ H.filter (fun T => v ∈ T), w T / lam
            = (∑ T ∈ H.filter (fun T => v ∈ T), w T) / lam from (Finset.sum_div _ _ _).symm,
        div_le_one hlam]
      exact hload v)
  refine ⟨M, hM, ?_⟩
  rw [← Finset.sum_div, div_le_iff₀ hlam] at hMle
  nlinarith only [hMle]

/-! ### Every edge is light -/

/-- Every edge of positive weight has weight at most the weighted codegree bound: an `r`-uniform
edge with `r ≥ 2` contains two distinct vertices. -/
theorem weight_le_of_codegree (H : Finset (Finset W)) (w : Finset W → ℝ) {r : ℕ} (hr : 2 ≤ r)
    (hunif : IsUniform H r) (hwnn : ∀ T, 0 ≤ w T) {γ : ℝ}
    (hcod : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ)
    {T : Finset W} (hT : T ∈ H) : w T ≤ γ := by
  classical
  have h2 : 1 < T.card := by rw [hunif T hT]; omega
  obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.mp h2
  refine le_trans ?_ (hcod x z hxz)
  exact Finset.single_le_sum (f := w) (fun T' _ => hwnn T')
    (Finset.mem_filter.mpr ⟨hT, hx, hz⟩)

/-! ### The dense regime -/

/-- **The weighted nibble in the dense regime, without any additive error.**  If the region `R`
carrying the edges satisfies `ε|R| ≤ ∑w` — equivalently the average load on `R` is at least `rε` —
then the repaired weighted nibble holds. -/
theorem fracNibble_weightedCodegree_dense (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (R : Finset W),
        IsUniform H r →
        (∀ T ∈ H, T ⊆ R) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ε * (R.card : ℝ) ≤ ∑ T ∈ H, w T →
        ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  rcases le_or_gt β 1 with hβ1 | hβ1
  swap
  · -- for `β > 1` the conclusion is vacuous
    refine ⟨1, one_pos, ?_⟩
    intro W _ _ H w R _ _ hwnn _ _ _
    refine ⟨∅, ⟨Finset.empty_subset _, by simp⟩, ?_⟩
    have hS : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
    have : (1 - β) * (∑ T ∈ H, w T) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hS
    simpa using this
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  set β' : ℝ := β * ε / (2 * (1 + ε)) with hβ'def
  have hβ' : 0 < β' := by rw [hβ'def]; positivity
  obtain ⟨γ₁, hγ₁, hpad⟩ := fracNibble_weightedCodegree_pad r hr β' hβ'
  obtain ⟨γ₂, hγ₂, η, hη, hon⟩ := fracNibble_weightedCodegree_on r hr β hβ
  set T₀ : ℝ := 1 / γ₁ with hT₀
  set T₂ : ℝ := (T₀ / γ₂) / η with hT₂
  set K : ℝ := max (2 / β) (T₂ / r) with hK
  set N : ℕ := ⌈K / ε⌉₊ with hN
  refine ⟨min (min γ₁ γ₂) (1 / 2 ^ N), by positivity, ?_⟩
  intro W _ _ H w R hunif hsub hwnn hload hcod hdense
  set γ : ℝ := min (min γ₁ γ₂) (1 / 2 ^ N) with hγ
  have hγγ₁ : γ ≤ γ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hγγ₂ : γ ≤ γ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hγN : γ ≤ 1 / 2 ^ N := min_le_right _ _
  set S : ℝ := ∑ T ∈ H, w T with hS
  set Δ : ℝ := defic H w R with hΔ
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun T _ => hwnn T)
  have hΔeq : Δ = (R.card : ℝ) - (r : ℝ) * S := defic_eq H w R hunif hsub
  have hΔ0 : 0 ≤ Δ := by
    rw [hΔ, defic]
    exact Finset.sum_nonneg (fun v _ => by linarith only [hload v])
  have hRle : (R.card : ℝ) ≤ S / ε := by
    rw [le_div_iff₀ hε, mul_comm]; exact hdense
  have hΔle : Δ ≤ S / ε := by
    have : Δ ≤ (R.card : ℝ) := by
      rw [hΔeq]
      nlinarith
    linarith
  have hcod₂ : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ₂ :=
    fun x z h => le_trans (hcod x z h) hγγ₂
  by_cases hSK : K ≤ S
  · have hS2β : 2 / β ≤ S := le_trans (le_max_left _ _) hSK
    have hβS : 1 ≤ β * S / 2 := by
      rw [div_le_iff₀ hβ] at hS2β
      linarith
    by_cases hΔT : T₀ ≤ Δ
    · -- the padding regime: the deficiency is large enough to be absorbed by fresh layers
      obtain ⟨M, hM, hMcard⟩ := hpad H w R hunif hsub hwnn hload
        (fun x z hxz => le_trans (hcod x z hxz) hγγ₁) (by rw [← hΔ]; exact hΔT)
      refine ⟨M, hM, ?_⟩
      rw [← hS, ← hΔ] at hMcard
      have hkey : β' * S + β' * Δ ≤ β * S / 2 := by
        have h1 : β' * Δ ≤ β' * (S / ε) := by nlinarith
        have h2 : β' * S + β' * (S / ε) = β * S / 2 := by
          rw [hβ'def]; field_simp; ring
        linarith
      nlinarith
    · -- the near-perfect regime: few vertices are unsaturated
      push_neg at hΔT
      set Exc : Finset W :=
        R.filter (fun v => ∑ T ∈ H.filter (fun T => v ∈ T), w T < 1 - γ₂) with hExcdef
      have hExcγ : (Exc.card : ℝ) * γ₂ ≤ Δ := by
        have hsum : ∑ v ∈ Exc, (1 - ∑ T ∈ H.filter (fun T => v ∈ T), w T) ≤ Δ := by
          rw [hΔ, defic]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro v _ _
          linarith only [hload v]
        refine le_trans ?_ hsum
        have hconst : (Exc.card : ℝ) * γ₂ = ∑ _v ∈ Exc, γ₂ := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [hconst]
        refine Finset.sum_le_sum (fun v hv => ?_)
        have := (Finset.mem_filter.mp hv).2
        linarith
      have hRlow : T₂ ≤ (R.card : ℝ) := by
        have h1 : (r : ℝ) * S ≤ (R.card : ℝ) := by rw [hΔeq] at hΔ0; linarith
        have h2 : T₂ / r ≤ S := le_trans (le_max_right _ _) hSK
        rw [div_le_iff₀ hrpos] at h2
        nlinarith
      have hExccard : (Exc.card : ℝ) ≤ η * (R.card : ℝ) := by
        have h1 : (Exc.card : ℝ) ≤ T₀ / γ₂ := by
          rw [le_div_iff₀ hγ₂]
          linarith
        have h2 : η * T₂ = T₀ / γ₂ := by rw [hT₂]; field_simp
        nlinarith
      obtain ⟨M, hM, -, hMcard⟩ := hon H w R Exc hunif hsub hwnn hload
        (fun v hvR hvE => by
          by_contra hcon
          push_neg at hcon
          exact hvE (Finset.mem_filter.mpr ⟨hvR, hcon⟩))
        hExccard hcod₂
      exact ⟨M, hM, hMcard⟩
  · -- the bounded regime: the region, hence the whole hypergraph, is bounded
    push_neg at hSK
    have hRcard : R.card ≤ N := by
      have h1 : (R.card : ℝ) ≤ K / ε :=
        le_trans hRle (div_le_div_of_nonneg_right hSK.le hε.le)
      have h2 : (R.card : ℝ) ≤ (N : ℝ) := le_trans h1 (Nat.le_ceil _)
      exact_mod_cast h2
    have hHcard : (H.card : ℝ) ≤ 2 ^ N := by
      have h1 : H ⊆ R.powerset := fun T hT => Finset.mem_powerset.mpr (hsub T hT)
      have h2 : H.card ≤ 2 ^ R.card := by
        simpa [Finset.card_powerset] using Finset.card_le_card h1
      have h3 : (2 : ℕ) ^ R.card ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hRcard
      have h4 : H.card ≤ 2 ^ N := le_trans h2 h3
      exact_mod_cast h4
    have hS1 : S ≤ 1 := by
      have h1 : S ≤ (H.card : ℝ) * γ := by
        rw [hS]
        calc ∑ T ∈ H, w T ≤ ∑ _T ∈ H, γ :=
              Finset.sum_le_sum (fun T hT => weight_le_of_codegree H w hr hunif hwnn hcod hT)
          _ = (H.card : ℝ) * γ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hγ0 : 0 < γ := by positivity
      have h2 : (H.card : ℝ) * γ ≤ 2 ^ N * (1 / 2 ^ N) := by
        have hpow : (0 : ℝ) < 2 ^ N := by positivity
        exact mul_le_mul hHcard hγN hγ0.le hpow.le
      have h3 : (2 : ℝ) ^ N * (1 / 2 ^ N) = 1 := by field_simp
      linarith
    rcases H.eq_empty_or_nonempty with hemp | ⟨T, hT⟩
    · refine ⟨∅, ⟨Finset.empty_subset _, by simp⟩, ?_⟩
      have h0 : S = 0 := by rw [hS, hemp, Finset.sum_empty]
      rw [h0]
      simp
    · refine ⟨{T}, ⟨Finset.singleton_subset_iff.mpr hT, ?_⟩, ?_⟩
      · intro e he f hf hef
        rw [Finset.mem_singleton] at he hf
        exact absurd (he.trans hf.symm) hef
      · rw [Finset.card_singleton]
        have h1 : (1 - β) * S ≤ 1 * S := mul_le_mul_of_nonneg_right (by linarith) hS0
        push_cast
        linarith

/-- **The weighted nibble for uniformly heavy loads.**  If every vertex of the region carries load
at least `λ` then the region has at most `r∑w/λ` vertices, so
`Nibble.fracNibble_weightedCodegree_dense` applies with `ε = λ/r`. -/
theorem fracNibble_weightedCodegree_heavy (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (R : Finset W),
        IsUniform H r →
        (∀ T ∈ H, T ⊆ R) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        (∀ v ∈ R, lam ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  obtain ⟨γ, hγ, hmain⟩ := fracNibble_weightedCodegree_dense r hr β hβ (lam / r)
    (by positivity)
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ H w R hunif hsub hwnn hload hcod hheavy
  refine hmain H w R hunif hsub hwnn hload hcod ?_
  have hsum : ∑ v ∈ R, ∑ T ∈ H.filter (fun T => v ∈ T), w T = (r : ℝ) * ∑ T ∈ H, w T :=
    sum_load_region H w R hunif hsub
  have hlow : lam * (R.card : ℝ) ≤ ∑ v ∈ R, ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
    have hconst : lam * (R.card : ℝ) = ∑ _v ∈ R, lam := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hconst]
    exact Finset.sum_le_sum (fun v hv => hheavy v hv)
  rw [hsum] at hlow
  rw [div_mul_eq_mul_div, div_le_iff₀ hrpos]
  nlinarith

/-! ### Edges with a heavy vertex -/

/-- The repaired weighted nibble for hypergraphs in which every edge contains a vertex of load at
least `λ`, the level `λ > 0` being fixed in advance (so `γ` may depend on it).  The residual
`Nibble.FracNibbleWeightedMixed` below is formally weaker, and suffices. -/
def FracNibbleWeightedHeavyEdge : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∀ lam : ℝ, 0 < lam → ∃ γ : ℝ, 0 < γ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ),
      IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      (∀ T ∈ H, ∃ v ∈ T, lam ≤ ∑ T' ∈ H.filter (fun T' => v ∈ T'), w T') →
      ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-! ### The residual: the mixed-scale configuration -/

/-- **The residual obligation, in its weakest useful form.**  The repaired weighted nibble for the
*two-scale* configuration: there is a set `X` of vertices such that every edge meets `X`, every
vertex of `X` carries load at least `λ`, and every vertex outside `X` carries load at most `λ` —
the level `λ > 0` being fixed in advance, so that the codegree tolerance `γ` may depend on it.

`Nibble.fracNibble_weightedCodegree_heavy` is exactly the case `X ⊇ ⋃H` of this statement (all the
vertices touched by an edge are heavy), so the residual is not vacuous; what is left open is the
genuinely mixed case, in which an edge may contain both a heavy vertex and vertices of arbitrarily
small load.  Note that `|X| ≤ r·∑w/λ` is automatic, so the heavy part of the configuration is
always dense; it is the light vertices, whose number is unbounded in terms of `∑w`, that the
padding argument of `Nibble.fracNibble_weightedCodegree_pad` cannot absorb. -/
def FracNibbleWeightedMixed : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∀ β : ℝ, 0 < β → ∀ lam : ℝ, 0 < lam → ∃ γ : ℝ, 0 < γ ∧
    ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
      (X : Finset W),
      IsUniform H r →
      (∀ T, 0 ≤ w T) →
      (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
      (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
      (∀ T ∈ H, ∃ v ∈ T, v ∈ X) →
      (∀ v ∈ X, lam ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
      (∀ v : W, v ∉ X → ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ lam) →
      ∃ M : Finset (Finset W), IsMatching H M ∧ (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ)

/-- The residual with a distinguished heavy set follows from the residual without one. -/
theorem fracNibbleWeightedMixed_of_heavyEdge (h : FracNibbleWeightedHeavyEdge) :
    FracNibbleWeightedMixed := by
  intro r hr β hβ lam hlam
  obtain ⟨γ, hγ, hmain⟩ := h r hr β hβ lam hlam
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ H w X hunif hwnn hload hcod hmeet hheavy _
  refine hmain H w hunif hwnn hload hcod ?_
  intro T hT
  obtain ⟨v, hvT, hvX⟩ := hmeet T hT
  exact ⟨v, hvT, hheavy v hvX⟩

/-- **The residual implies the repaired weighted nibble.**  Split the edges according to whether
they meet a vertex of load at least `λ = β/(4r)`.  The edges that do not form a hypergraph all of
whose loads are below `λ`, so the greedy bound `Nibble.exists_matching_of_load_le` gives a matching
of size at least `1/(rλ) = 4/β` times their weight; if that already dominates, we are done.
Otherwise the edges meeting a heavy vertex carry all but a `β/4`-fraction of the weight, and the
residual applies to them: a vertex that is heavy in `H` is heavy in the subhypergraph of the edges
meeting the heavy set, because *all* of its edges lie there, while a vertex that is not heavy in
`H` is not heavy in any subhypergraph. -/
theorem fracNibbleWeightedTheorem_of_mixed (h : FracNibbleWeightedMixed) :
    FracNibbleWeightedTheorem := by
  classical
  intro r hr β hβ
  have hrpos : (0 : ℝ) < r := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr
    exact_mod_cast this
  rcases le_or_gt β 1 with hβ1 | hβ1
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro W _ _ H w _ hwnn _ _
    refine ⟨∅, ⟨Finset.empty_subset _, by simp⟩, ?_⟩
    have hS : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
    have : (1 - β) * (∑ T ∈ H, w T) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hS
    simpa using this
  set lam : ℝ := β / (4 * r) with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  obtain ⟨γ, hγ, hmixed⟩ := h r hr (β / 2) (by positivity) lam hlam
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ H w hunif hwnn hload hcod
  set L : W → ℝ := fun v => ∑ T ∈ H.filter (fun T => v ∈ T), w T with hL
  set X : Finset W := Finset.univ.filter (fun v => lam ≤ L v) with hX
  have hmemX : ∀ v : W, v ∈ X ↔ lam ≤ L v := by
    intro v; rw [hX, Finset.mem_filter]; simp
  set HX : Finset (Finset W) := H.filter (fun T => ∃ v ∈ T, v ∈ X) with hHX
  set H0 : Finset (Finset W) := H.filter (fun T => ¬ ∃ v ∈ T, v ∈ X) with hH0
  have hHXsub : HX ⊆ H := Finset.filter_subset _ _
  have hH0sub : H0 ⊆ H := Finset.filter_subset _ _
  set S : ℝ := ∑ T ∈ H, w T with hS
  set SX : ℝ := ∑ T ∈ HX, w T with hSX
  set S0 : ℝ := ∑ T ∈ H0, w T with hS0
  have hsplit : SX + S0 = S := by
    rw [hSX, hS0, hHX, hH0, hS]
    exact Finset.sum_filter_add_sum_filter_not H _ w
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun T _ => hwnn T)
  have hSXnn : 0 ≤ SX := Finset.sum_nonneg (fun T _ => hwnn T)
  have hS0nn : 0 ≤ S0 := Finset.sum_nonneg (fun T _ => hwnn T)
  -- the edges avoiding the heavy vertices carry only small loads
  have hload0 : ∀ v : W, ∑ T ∈ H0.filter (fun T => v ∈ T), w T ≤ lam := by
    intro v
    by_cases hv : v ∈ X
    · have hempty : H0.filter (fun T => v ∈ T) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro T hT
        rw [Finset.mem_filter, hH0, Finset.mem_filter] at hT
        exact hT.1.2 ⟨v, hT.2, hv⟩
      rw [hempty, Finset.sum_empty]
      exact hlam.le
    · have hv' : L v < lam := by
        by_contra hcon
        push_neg at hcon
        exact hv ((hmemX v).mpr hcon)
      refine le_of_lt (lt_of_le_of_lt ?_ hv')
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ hH0sub) (fun T _ _ => hwnn T)
  obtain ⟨M0, hM0, hM0card⟩ := exists_matching_of_load_le H0 (by omega)
    (fun T hT => hunif T (hH0sub hT)) w hwnn hlam hload0
  have hM0H : IsMatching H M0 := ⟨hM0.subset.trans hH0sub, hM0.disjoint⟩
  have hrlam : (r : ℝ) * lam = β / 4 := by rw [hlamdef]; field_simp
  rw [hrlam, ← hS0] at hM0card
  by_cases hcase : S ≤ (4 / β) * S0
  · -- the light edges already carry enough weight
    refine ⟨M0, hM0H, ?_⟩
    have h2 : (4 / β) * S0 ≤ (4 / β) * ((β / 4) * (M0.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hM0card (by positivity)
    have h3 : (4 / β) * ((β / 4) * (M0.card : ℝ)) = (M0.card : ℝ) := by field_simp
    have h1 : S ≤ (M0.card : ℝ) := by linarith
    nlinarith
  · -- almost all the weight sits on edges meeting the heavy set
    push_neg at hcase
    have hmul : (β / 4) * ((4 / β) * S0) < (β / 4) * S :=
      mul_lt_mul_of_pos_left hcase (by positivity)
    have heq : (β / 4) * ((4 / β) * S0) = S0 := by field_simp
    rw [heq] at hmul
    have hloadX : ∀ v : W, ∑ T ∈ HX.filter (fun T => v ∈ T), w T ≤ 1 := by
      intro v
      refine le_trans ?_ (hload v)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ hHXsub) (fun T _ _ => hwnn T)
    have hcodX : ∀ x z : W, x ≠ z → ∑ T ∈ HX.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ := by
      intro x z hxz
      refine le_trans ?_ (hcod x z hxz)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ hHXsub) (fun T _ _ => hwnn T)
    have hfilterX : ∀ v : W, v ∈ X →
        HX.filter (fun T' => v ∈ T') = H.filter (fun T' => v ∈ T') := by
      intro v hv
      refine Finset.Subset.antisymm (Finset.filter_subset_filter _ hHXsub) ?_
      intro T' hT'
      rw [Finset.mem_filter] at hT'
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hT'.1, ⟨v, hT'.2, hv⟩⟩, hT'.2⟩
    obtain ⟨MX, hMX, hMXcard⟩ := hmixed HX w X (fun T hT => hunif T (hHXsub hT)) hwnn hloadX hcodX
      (fun T hT => by
        rw [hHX, Finset.mem_filter] at hT
        exact hT.2)
      (fun v hv => by rw [hfilterX v hv]; exact (hmemX v).mp hv)
      (fun v hv => by
        have hv' : L v ≤ lam := by
          by_contra hcon
          push_neg at hcon
          exact hv ((hmemX v).mpr hcon.le)
        refine le_trans ?_ hv'
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset_filter _ hHXsub) (fun T _ _ => hwnn T))
    refine ⟨MX, ⟨hMX.subset.trans hHXsub, hMX.disjoint⟩, ?_⟩
    rw [← hSX] at hMXcard
    have hSXlow : (1 - β / 4) * S ≤ SX := by nlinarith
    have h2 : (1 - β / 2) * ((1 - β / 4) * S) ≤ (1 - β / 2) * SX :=
      mul_le_mul_of_nonneg_left hSXlow (by linarith)
    have h3 : (1 - β) * S ≤ (1 - β / 2) * ((1 - β / 4) * S) := by nlinarith
    linarith

/-- **The heavy-edge residual implies the repaired weighted nibble**, via
`Nibble.fracNibbleWeightedMixed_of_heavyEdge`. -/
theorem fracNibbleWeightedTheorem_of_heavyEdge (h : FracNibbleWeightedHeavyEdge) :
    FracNibbleWeightedTheorem :=
  fracNibbleWeightedTheorem_of_mixed (fracNibbleWeightedMixed_of_heavyEdge h)

end Nibble
