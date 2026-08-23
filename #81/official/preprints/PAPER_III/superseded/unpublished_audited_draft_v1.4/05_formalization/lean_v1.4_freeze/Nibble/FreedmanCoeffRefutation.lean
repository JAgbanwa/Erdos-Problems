/-
# Nibble — the Freedman neighbour-coefficient is EXACTLY `deg²`, and the explicit bad event is FALSE

This file settles two questions about the Freedman route of `Nibble.MostAssemblyFreedman`.

## 1.  The codegree hypothesis cannot tighten the Freedman variance proxy

The residual-degree Freedman bricks (`Nibble.all_active_vertices_residualDeg_freedman`,
`Nibble.residualDeg_two_sided_tail`) carry, at a vertex `v`, the *neighbour-coefficient sum*

  `W(v) = ∑_{e ∋ v} #{e' ∋ v : depNbhd H e ∩ depNbhd H e' ≠ ∅}`,

and the reduction to `FreedmanCardExplicitBadEventCore` bounds it by `Δ²`.  The plan of tightening
that bound with `CodegreeBounded H (μ d)` **cannot work**: the bound by `Δ²` is not lossy at all.
For any two edges `e, e'` through the same vertex `v` one has `e ∈ depNbhd H e ∩ depNbhd H e'`
(`e` meets itself at `v`, and `e` meets `e'` at `v`), so the inner count is the *whole* v-star and

  `W(v) = deg(v)²`   exactly   (`freedman_neighbourCoeff_sum_eq_degree_sq`),

no matter how small the codegrees are.  The codegree-tightened variance therefore has to be sought
at a different object — it is the SAFE degree, whose loss weight does have a codegree-controlled
variance; see `Nibble.pair_excess_le_codegree` and `Nibble.centered_second_moment_le_codegree`
in `Nibble.Tight.PairExcessCodegree`.

## 2.  The concrete explicit bad-event core is FALSE

With the concrete parameters `p = 1/(100 r Δ)`, `c = √d`, `Δ = ⌈(1+μ)d⌉`, `μ = 1/100` one has
`r Δ p = 1/100`, so the Freedman exponent coefficient is `2(Δ²/100 + Δ c/3) ≥ d²/50`, whence

  `c² / (2 (Δ²·rΔp + Δc/3)) ≤ 50/d ≤ 1/2`  for `d ≥ 100`,

and already `N = 1` violates `N · 2 exp(...) < 1`, because `2 e^{-1/2} > 1`
(`not_freedmanCardExplicitBadEventCore`).  Together with the round-inequality refutation
`Nibble.not_freedmanExplicit_badRoundCore` (which needs no concentration input at all) this closes
the Freedman explicit-parameter route.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DepLocal
import Nibble.MostAssemblyFreedman
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset Hypergraph

namespace Nibble

variable {V : Type*} [DecidableEq V]

/-! ## 1.  The neighbour-coefficient sum is exactly the squared degree -/

/-- Every edge through `v` lies in its own dependency neighbourhood. -/
theorem mem_depNbhd_self {H : Finset (Finset V)} {e : Finset V} {v : V}
    (heH : e ∈ H) (hve : v ∈ e) : e ∈ depNbhd H e := by
  refine mem_depNbhd_of_touch heH ?_
  rw [Finset.not_disjoint_iff_nonempty_inter]
  exact ⟨v, by simp [hve]⟩

/-- **Two edges through a common vertex always have intersecting dependency neighbourhoods.**
This is what makes the Freedman neighbour coefficient insensitive to the codegree. -/
theorem depNbhd_not_disjoint_of_common_vertex {H : Finset (Finset V)} {e e' : Finset V} {v : V}
    (heH : e ∈ H) (hve : v ∈ e) (hve' : v ∈ e') :
    ¬ Disjoint (depNbhd H e) (depNbhd H e') := by
  rw [Finset.not_disjoint_iff]
  refine ⟨e, mem_depNbhd_self heH hve, ?_⟩
  refine mem_depNbhd_of_touch heH ?_
  rw [Finset.not_disjoint_iff_nonempty_inter]
  exact ⟨v, by simp [hve, hve']⟩

/-- **The Freedman neighbour-coefficient sum at `v` is exactly `deg(v)²`.**  No codegree hypothesis
enters, and none can help: the bound by `Δ²` used in the reduction to
`Nibble.FreedmanCardExplicitBadEventCore` is an equality up to the degree ceiling. -/
theorem freedman_neighbourCoeff_sum_eq_degree_sq (H : Finset (Finset V)) (v : V) :
    ∑ e ∈ H.filter (fun f => v ∈ f),
        (((H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card)
      = (degree H v) ^ 2 := by
  classical
  have hinner : ∀ e ∈ H.filter (fun f => v ∈ f),
      ((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))) = H.filter (fun f => v ∈ f) := by
    intro e he
    obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
    refine Finset.filter_true_of_mem ?_
    intro e' he'
    exact depNbhd_not_disjoint_of_common_vertex heH hve (Finset.mem_filter.mp he').2
  rw [Finset.sum_congr rfl (fun e he => by rw [hinner e he])]
  rw [Finset.sum_const, smul_eq_mul, degree, sq]

/-- The real-valued form used by the Freedman tail bricks: the variance proxy at `v` is exactly
`deg(v)² · (r Δ p)`, with no dependence on the codegrees. -/
theorem freedman_variance_proxy_eq {H : Finset (Finset V)} {r Δ : ℕ} {p : ℝ} (v : V) :
    (∑ e ∈ H.filter (fun f => v ∈ f),
        (((H.filter (fun f => v ∈ f)).filter
          (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ)) * ((r : ℝ) * Δ * p)
      = (degree H v : ℝ) ^ 2 * ((r : ℝ) * Δ * p) := by
  classical
  have hcast : (∑ e ∈ H.filter (fun f => v ∈ f),
      (((H.filter (fun f => v ∈ f)).filter
        (fun e' => ¬ Disjoint (depNbhd H e) (depNbhd H e'))).card : ℝ))
      = ((degree H v : ℕ) : ℝ) ^ 2 := by
    rw [← Nat.cast_sum, freedman_neighbourCoeff_sum_eq_degree_sq H v]
    push_cast; ring
  rw [hcast]

/-! ## 2.  The concrete explicit Freedman bad-event core is false -/

/-- `2·exp(-1/2) > 1`. -/
theorem one_lt_two_mul_exp_neg_half : 1 < 2 * Real.exp (-(1 / 2 : ℝ)) := by
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : Real.exp (1 / 2 : ℝ) < 2 := by
    nlinarith [Real.exp_one_lt_d9]
  have hrw : 2 * Real.exp (-(1 / 2 : ℝ)) = 2 / Real.exp (1 / 2 : ℝ) := by
    rw [Real.exp_neg]; ring
  rw [hrw, lt_div_iff₀ hpos]
  linarith only [hlt]

/-- Arithmetic core of the refutation: once the Freedman coefficient is at least `d²/100` while the
deviation scale is `c = √d ≤ d/100`, the exponential factor exceeds `1/2`. -/
theorem one_lt_two_mul_exp_of_large_coeff {d c W : ℝ} (hd : 100 ≤ d) (hc : c ^ 2 = d)
    (hW : d ^ 2 / 100 ≤ W) :
    1 < 2 * Real.exp (-c ^ 2 / (2 * W)) := by
  have hd0 : (0 : ℝ) < d := by linarith only [hd]
  have hW0 : 0 < W := by nlinarith only [hW, hd0]
  have hratio : c ^ 2 / (2 * W) ≤ 1 / 2 := by
    rw [hc, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * W)]
    nlinarith only [hd, hW]
  have hexp : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-c ^ 2 / (2 * W)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith only [hratio]
  linarith [one_lt_two_mul_exp_neg_half]

/-- **The explicit Freedman bad-event core is FALSE** for the concrete parameters
`freedmanExplicitP`, `freedmanExplicitC` at the tolerance `μ = 1/100` used by the route, for every
uniformity `r ≥ 1`, every target `β`, every threshold `d₀` and every size constant `K > 0`.

Reason: with `p = 1/(100 r Δ)` one has `r Δ p = 1/100`, so the Freedman variance proxy is
`Δ²/100 ≥ d²/100`, while the deviation scale is only `c = √d`.  The exponent is then `≥ -50/d`,
which tends to `0`; already `N = 1` breaks the required strict inequality.  This is the concrete
form of `freedman_neighbourCoeff_sum_eq_degree_sq`: the `Δ²` in the proxy is not an artefact of the
reduction, so no codegree tightening can rescue the statement. -/
theorem not_freedmanCardExplicitBadEventCore {r : ℕ} (hr : 1 ≤ r) {β d₀ K : ℝ} (hK : 0 < K) :
    ¬ FreedmanCardExplicitBadEventCore freedmanExplicitP freedmanExplicitC r β
        ((1 : ℝ) / 100) d₀ K := by
  intro hbad
  classical
  set d : ℝ := max (max 100 d₀) (1 / K) with hddef
  have hd100 : (100 : ℝ) ≤ d := le_trans (le_max_left _ _) (le_max_left _ _)
  have hdd₀ : d₀ ≤ d := le_trans (le_max_right _ _) (le_max_left _ _)
  have hdK : 1 / K ≤ d := le_max_right _ _
  have hd0 : (0 : ℝ) < d := by linarith only [hd100]
  have hsize : ((1 : ℕ) : ℝ) ≤ K * d ^ 2 := by
    have h1 : (1 : ℝ) ≤ d * K := by
      rw [div_le_iff₀ hK] at hdK
      linarith only [hdK]
    have hd1 : (1 : ℝ) ≤ d := by linarith only [hd100]
    push_cast
    nlinarith only [h1, hd1]
  have h := hbad 1 d hd0 hdd₀ hsize
  -- the concrete parameters
  set Δn : ℕ := Nat.ceil ((1 + (1 : ℝ) / 100) * d) with hΔndef
  have hΔd : d ≤ (Δn : ℝ) := by
    have h1 : d ≤ (1 + (1 : ℝ) / 100) * d := by nlinarith only [hd0]
    exact le_trans h1 (Nat.le_ceil _)
  have hΔ0 : (0 : ℝ) < (Δn : ℝ) := by linarith only [hd0, hΔd]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hp : freedmanExplicitP r β 1 d = 1 / (100 * (r : ℝ) * (Δn : ℝ)) := rfl
  have hc : freedmanExplicitC r β 1 d = Real.sqrt d := rfl
  -- `r Δ p = 1/100`
  have hrΔp : (r : ℝ) * (Δn : ℝ) * freedmanExplicitP r β 1 d = 1 / 100 := by
    rw [hp]
    field_simp
  have hc2 : (freedmanExplicitC r β 1 d) ^ 2 = d := by
    rw [hc, Real.sq_sqrt hd0.le]
  have hcnn : 0 ≤ freedmanExplicitC r β 1 d := by
    rw [hc]; exact Real.sqrt_nonneg _
  -- the coefficient is at least `d²/100`
  set W : ℝ := (Δn : ℝ) ^ 2 * ((r : ℝ) * (Δn : ℝ) * freedmanExplicitP r β 1 d)
      + (Δn : ℝ) / 3 * freedmanExplicitC r β 1 d with hWdef
  have hWge : d ^ 2 / 100 ≤ W := by
    have h1 : d ^ 2 ≤ (Δn : ℝ) ^ 2 := by nlinarith only [hΔd, hc2]
    have h2 : 0 ≤ (Δn : ℝ) / 3 * freedmanExplicitC r β 1 d := by positivity
    rw [hWdef, hrΔp]
    linarith only [h1, h2]
  have hgt := one_lt_two_mul_exp_of_large_coeff (d := d)
    (c := freedmanExplicitC r β 1 d) (W := W) hd100 hc2 hWge
  rw [Nat.cast_one, one_mul] at h
  exact absurd h (not_lt.mpr hgt.le)

end Nibble
