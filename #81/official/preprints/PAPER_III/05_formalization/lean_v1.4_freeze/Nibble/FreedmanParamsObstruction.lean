/-
# Nibble — obstructions to the outer-layer parameter cores

Standalone, Mathlib-only.  This file records *negative* results about the parameter atoms sitting at
the top of both outer assembly routes (`Nibble.MostAssembly`, Chebyshev, and
`Nibble.MostAssemblyFreedman`, Freedman).  They explain why those atoms cannot be discharged as
stated, and they localise the design change that is required.

Three obstructions are formalised.

* **(O1) The all-vertices round invariant is vacuous unless `c` exceeds the covered degrees.**  The
  residual hypergraph deletes *all* edges meeting a covered vertex, so a covered vertex has residual
  degree `0`.  Clause (a) of the one-round specification
  `(degree H' v) * (1 - rΔp) - c < degree (residual H' R') v`, quantified over ALL vertices,
  therefore forces `c > (degree H' v) * (1 - rΔp)` for every covered `v`
  (`clause_a_forces_slack_gt_covered_degree`).  A one-round strategy with a slack `c` small compared
  with the degree scale can only cover vertices of degree below `c / (1 - rΔp)`.

* **(O2) The Freedman bad-event condition forces `c > (2Δ/3)·log (2|V|)`**
  (`badEvent_forces_range_log_lt`).  This is the quantitative form of (O1) along the Bernstein /
  Freedman route: the range term `(Δ/3)·c` in the exponent alone pushes the deviation scale above
  the maximal degree as soon as `|V| ≥ 3`.

* **(O3) The per-round crux inequality is unsatisfiable for `β < 1/2`**
  (`not_freedmanCardNumericThresholdParameterCore`, `not_freedmanExplicit_badRoundCore`).  This one
  needs no concentration input at all: the crux demands that *each* of the `T` rounds covers a
  `(1 - lam)`-fraction of the *whole* vertex set (rather than of the still-uncovered set), while the
  geometric decay of the degree proxy caps the total available gain,
  `T·(1-lam) ≤ (1-μ)d/(rΔ) < 1/2`.  Bernoulli's inequality then gives `lam ^ T ≥ 1 - T(1-lam) > 1/2`,
  contradicting `lam ^ T ≤ β`.

The moral: the outer layer must compare the per-round gain with the *remaining uncovered* count
`lam ^ k · |V|`, and the round invariant must be restricted to *uncovered* vertices.  Both are
changes to the per-round bricks, not parameter calibrations.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.MostAssemblyFreedman

open Finset Hypergraph

namespace Nibble

/-! ## (O1) Covered vertices make the all-vertices round invariant vacuous -/

/-- A vertex covered by the round matching has residual degree `0`: the residual hypergraph keeps
only edges disjoint from the covered set. -/
theorem degree_residual_eq_zero_of_mem_covered {V : Type*} [Fintype V] [DecidableEq V]
    {H R : Finset (Finset V)} {v : V} (hv : v ∈ covered R) :
    degree (Hypergraph.residual H R) v = 0 := by
  classical
  rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  rw [Hypergraph.residual, Finset.mem_filter] at he
  exact (Finset.disjoint_left.mp he.2 hve) hv

/-- **(O1) The all-vertices clause (a) forces a large slack.**  If the one-round specification
`(degree H' v) * (1 - rΔp) - c < degree (residual H' R') v` holds for every vertex, then the slack
`c` exceeds `(degree H' v) * (1 - rΔp)` for every vertex `v` covered by the round matching.  In
particular a round that covers a vertex of near-average degree `d` must use a slack `c > d(1-rΔp)`:
the "small `c`" regime cannot cover anything. -/
theorem clause_a_forces_slack_gt_covered_degree {V : Type*} [Fintype V] [DecidableEq V]
    {H' R' : Finset (Finset V)} {r Δ : ℕ} {p c : ℝ}
    (hspec : ∀ v : V, (degree H' v : ℝ) * (1 - (r : ℝ) * Δ * p) - c
      < (degree (Hypergraph.residual H' R') v : ℝ))
    {v : V} (hv : v ∈ covered R') :
    (degree H' v : ℝ) * (1 - (r : ℝ) * Δ * p) < c := by
  have h0 : (degree (Hypergraph.residual H' R') v : ℝ) = 0 := by
    rw [degree_residual_eq_zero_of_mem_covered hv]; norm_num
  have h := hspec v
  rw [h0] at h
  linarith only [h]

/-! ## (O2) The Freedman bad-event condition forces a large deviation scale -/

/-- **(O2) Bernstein range obstruction.**  If the Freedman bad-event bound
`N · 2 · exp (-c² / (2 (W + (b/3)·c))) < 1` holds with a nonnegative variance proxy `W` and a
positive range `b`, then `c > (2b/3)·log (2N)`.  Applied with `b = Δ` this says that the Freedman
slack necessarily exceeds `(2Δ/3)·log (2|V|)`, hence exceeds the maximal degree as soon as
`|V| ≥ 3`. -/
theorem badEvent_forces_range_log_lt {N : ℕ} {W b c : ℝ}
    (hN : 1 ≤ N) (hW : 0 ≤ W) (hb : 0 < b) (hc : 0 < c)
    (h : (N : ℝ) * (2 * Real.exp (-c ^ 2 / (2 * (W + b / 3 * c)))) < 1) :
    2 * b / 3 * Real.log (2 * N) < c := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < 2 * (W + b / 3 * c) := by positivity
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by linarith only [hNR]
  have hexp : Real.exp (-c ^ 2 / (2 * (W + b / 3 * c))) < 1 / (2 * (N : ℝ)) := by
    rw [lt_div_iff₀ h2N]
    nlinarith [Real.exp_pos (-c ^ 2 / (2 * (W + b / 3 * c)))]
  have hlog : -c ^ 2 / (2 * (W + b / 3 * c)) < Real.log (1 / (2 * (N : ℝ))) := by
    have h' := Real.log_lt_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at h'
  rw [Real.log_div one_ne_zero (ne_of_gt h2N), Real.log_one, zero_sub] at hlog
  have hlognn : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  rw [div_lt_iff₀ hD] at hlog
  nlinarith only [hW, hb, hc, hD, hlog]

/-! ## (O3) The per-round crux inequality is unsatisfiable for small `β` -/

/-- Geometric-sum bound: for `0 ≤ q < 1`, partial sums are bounded by `1 / (1 - q)`. -/
theorem geom_partial_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (T : ℕ) :
    ∑ i ∈ Finset.range T, q ^ i ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith only [hq1]
  have hgeom : (1 - q) * ∑ i ∈ Finset.range T, q ^ i = 1 - q ^ T := by
    have h := geom_sum_mul (x := q) (n := T)
    linarith only [h, mul_comm (∑ i ∈ Finset.range T, q ^ i) (q - 1)]
  have hqT : 0 ≤ q ^ T := pow_nonneg hq0 T
  rw [le_div_iff₀ h1q]
  linarith only [hgeom, hqT]

/-- Bernoulli step: a per-round deficit budget of at most `1/2` keeps `lam ^ T` at least `1/2`. -/
theorem half_le_pow_of_round_deficit {T : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam)
    (h : (T : ℝ) * (1 - lam) ≤ 1 / 2) : 1 / 2 ≤ lam ^ T := by
  have hbern : 1 + (T : ℝ) * (lam - 1) ≤ (1 + (lam - 1)) ^ T :=
    one_add_mul_le_pow (by linarith) T
  simp only [add_sub_cancel] at hbern
  linarith only [h, hbern]

/-- Extraction of the per-round covering demand from the crux inequality: with a nonnegative
penalty and `0 ≤ η`, the crux forces `1 - lam ≤ gain`. -/
theorem round_deficit_le_gain {lam η G P Nnum rr : ℝ} (hN : 0 < Nnum) (hη : 0 ≤ η)
    (hP : 0 ≤ P) (hrr : 0 ≤ rr) (hG0 : 0 ≤ G)
    (h : (1 - lam) * Nnum ≤ (1 - η) * Nnum * G - rr * P) : 1 - lam ≤ G := by
  have h1 : 0 ≤ rr * P := mul_nonneg hrr hP
  have h2 : (1 - η) * Nnum * G ≤ Nnum * G := by
    linarith only [mul_nonneg (mul_nonneg hη hN.le) hG0]
  have h3 : (1 - lam) * Nnum ≤ Nnum * G := by linarith only [h, h1, h2]
  exact le_of_mul_le_mul_right (by linarith only [h3]) hN

/-- The per-round gain is bounded by the degree proxy ceiling times `p`, whatever the sign of the
proxy. -/
theorem gain_le_proxy_mul {proxy f p Dq : ℝ} (hf0 : 0 ≤ f) (hfp : f ≤ p) (hp0 : 0 ≤ p)
    (hDq : 0 ≤ Dq) (hproxy : proxy ≤ Dq) : proxy * f ≤ Dq * p := by
  rcases le_or_gt 0 proxy with hpx | hpx
  · calc proxy * f ≤ proxy * p := mul_le_mul_of_nonneg_left hfp hpx
      _ ≤ Dq * p := mul_le_mul_of_nonneg_right hproxy hp0
  · have h1 : proxy * f ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hpx) hf0
    have h2 : (0 : ℝ) ≤ Dq * p := mul_nonneg hDq hp0
    linarith only [h1, h2]

/-- **The telescoping obstruction, in general form.**  Suppose that for `T` rounds the crux
inequality of the outer assembly holds: each round `k < T` has nonnegative gain
`G k = ((1-μ)d q^k - c ∑_{i<k} q^i) · p(1-p)^{rΔ}` (with `q = 1 - rΔp`) and covers a
`(1-lam)`-fraction of the whole vertex set, `(1-lam)·Nv ≤ (1-η)·Nv·G k - r·P`.  If moreover
`2(1-μ)d ≤ rΔ` (true whenever `Δ` dominates the degree scale and `r ≥ 2`), then
`lam ^ T ≥ 1/2`, so `lam ^ T ≤ β` is impossible for `β < 1/2`. -/
theorem crux_telescope_false {r Δ T : ℕ} {d mu eta lam p c P Nv β : ℝ}
    (hrR : (2 : ℝ) ≤ (r : ℝ)) (hmu1 : mu ≤ 1) (hd : 0 < d)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hppos : 0 < p) (hΔpos : (0 : ℝ) < (Δ : ℝ))
    (hc0 : 0 ≤ c) (hq : 0 ≤ 1 - (r : ℝ) * Δ * p) (hlam0 : 0 ≤ lam)
    (heta : 0 ≤ eta) (hP : 0 ≤ P) (hNv : 0 < Nv)
    (hβ : β < 1 / 2) (hTβ : lam ^ T ≤ β)
    (hΔd : 2 * ((1 - mu) * d) ≤ (r : ℝ) * (Δ : ℝ))
    (hcrux : ∀ k, k < T →
      0 ≤ ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
          * (p * (1 - p) ^ (r * Δ))
      ∧ (1 - lam) * Nv
          ≤ (1 - eta) * Nv * (((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
                - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
              * (p * (1 - p) ^ (r * Δ)))
            - (r : ℝ) * P) :
    False := by
  classical
  have hrΔp : 0 < (r : ℝ) * (Δ : ℝ) * p := by positivity
  have hq0 : 0 ≤ 1 - (r : ℝ) * (Δ : ℝ) * p := hq
  have hq1 : 1 - (r : ℝ) * (Δ : ℝ) * p < 1 := by linarith only [hrΔp]
  have hD0 : (0 : ℝ) ≤ (1 - mu) * d := by nlinarith only [hmu1, hd]
  have hround : ∀ k ∈ Finset.range T,
      (1 - lam) ≤ (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k * p := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨hgain0, hineq⟩ := hcrux k hk
    have hqk : (0 : ℝ) ≤ (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := pow_nonneg hq0 k
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range k, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ i :=
      Finset.sum_nonneg fun i _ => pow_nonneg hq0 i
    have hf0 : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) :=
      mul_nonneg hp0 (pow_nonneg (by linarith) _)
    have hfp : p * (1 - p) ^ (r * Δ) ≤ p := by
      have h1 : (1 - p) ^ (r * Δ) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      nlinarith only [hppos, h1]
    have hproxy : (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k
          - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ i
        ≤ (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := by
      nlinarith only [hc0, hSnn]
    have hDqnn : (0 : ℝ) ≤ (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k :=
      mul_nonneg hD0 hqk
    exact le_trans (round_deficit_le_gain hNv heta hP (by positivity) hgain0 hineq)
      (gain_le_proxy_mul hf0 hfp hp0 hDqnn hproxy)
  have hsum : (T : ℝ) * (1 - lam)
      ≤ (1 - mu) * d * p * ∑ k ∈ Finset.range T, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := by
    have hs := Finset.sum_le_sum hround
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    calc (T : ℝ) * (1 - lam) ≤ ∑ k ∈ Finset.range T,
            (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k * p := hs
      _ = (1 - mu) * d * p * ∑ k ∈ Finset.range T, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hgeo : ∑ k ∈ Finset.range T, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k
      ≤ 1 / ((r : ℝ) * (Δ : ℝ) * p) := by
    have hg := geom_partial_sum_le hq0 hq1 T
    simpa using hg
  have hTbound : (T : ℝ) * (1 - lam) ≤ 1 / 2 := by
    have hnn : (0 : ℝ) ≤ (1 - mu) * d * p := by positivity
    have hfac := mul_le_mul_of_nonneg_left hgeo hnn
    have hval : (1 - mu) * d * p * (1 / ((r : ℝ) * (Δ : ℝ) * p))
        = (1 - mu) * d / ((r : ℝ) * (Δ : ℝ)) := by
      field_simp
    have hlt : (1 - mu) * d / ((r : ℝ) * (Δ : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith [hsum, hfac, hval ▸ hfac]
  have hhalf := half_le_pow_of_round_deficit hlam0 hTbound
  linarith [hTβ]

/-- **Total-gain cap for a fixed-parameter nibble.**  With one fixed retention probability `p` for
all rounds, the per-round gains `G k = ((1-μ)d q^k - c ∑_{i<k} q^i)·p(1-p)^{rΔ}` sum to at most
`(1-μ)d/(rΔ)` over ANY number of rounds.  Since `Δ` dominates the degree scale and `r ≥ 2`, that is
at most `1/2`: a fixed-parameter nibble can never account for more than half (indeed more than a
`1/r` fraction) of the vertex set. -/
theorem total_gain_le {r Δ T : ℕ} {d mu p c : ℝ}
    (hmu1 : mu ≤ 1) (hd : 0 < d) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hppos : 0 < p)
    (hΔpos : (0 : ℝ) < (Δ : ℝ)) (hc0 : 0 ≤ c) (hrpos : (0 : ℝ) < (r : ℝ))
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p) :
    ∑ k ∈ Finset.range T, (((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
          - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
        * (p * (1 - p) ^ (r * Δ)))
      ≤ (1 - mu) * d / ((r : ℝ) * (Δ : ℝ)) := by
  have hrΔp : 0 < (r : ℝ) * (Δ : ℝ) * p := by positivity
  have hq0 : 0 ≤ 1 - (r : ℝ) * (Δ : ℝ) * p := hq
  have hq1 : 1 - (r : ℝ) * (Δ : ℝ) * p < 1 := by linarith only [hrΔp]
  have hD0 : (0 : ℝ) ≤ (1 - mu) * d := by nlinarith only [hmu1, hd]
  have hterm : ∀ k ∈ Finset.range T,
      ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
          - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
        * (p * (1 - p) ^ (r * Δ))
      ≤ (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k * p := by
    intro k _
    have hqk : (0 : ℝ) ≤ (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := pow_nonneg hq0 k
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range k, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ i :=
      Finset.sum_nonneg fun i _ => pow_nonneg hq0 i
    have hf0 : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) :=
      mul_nonneg hp0 (pow_nonneg (by linarith) _)
    have hfp : p * (1 - p) ^ (r * Δ) ≤ p := by
      have h1 : (1 - p) ^ (r * Δ) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      nlinarith only [hppos, h1]
    exact gain_le_proxy_mul hf0 hfp hp0 (mul_nonneg hD0 hqk) (by nlinarith)
  have hsum := Finset.sum_le_sum hterm
  have hgeo : ∑ k ∈ Finset.range T, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k
      ≤ 1 / ((r : ℝ) * (Δ : ℝ) * p) := by
    have hg := geom_partial_sum_le hq0 hq1 T
    simpa using hg
  have hrew : ∑ k ∈ Finset.range T, (1 - mu) * d * (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k * p
      = (1 - mu) * d * p * ∑ k ∈ Finset.range T, (1 - (r : ℝ) * (Δ : ℝ) * p) ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hnn : (0 : ℝ) ≤ (1 - mu) * d * p := by positivity
  have hfac := mul_le_mul_of_nonneg_left hgeo hnn
  have hval : (1 - mu) * d * p * (1 / ((r : ℝ) * (Δ : ℝ) * p))
      = (1 - mu) * d / ((r : ℝ) * (Δ : ℝ)) := by field_simp
  rw [hrew] at hsum
  linarith [hval ▸ hfac]

/-- **The RELATIVE crux is unsatisfiable too.**  Replacing the crux by the (weaker, and
mathematically correct) demand that round `k` covers a `(1-lam)`-fraction of the *still uncovered*
set — whose size is `lam ^ k · Nv` along the geometric schedule — does not help while the retention
probability `p` is the same in every round: summing `(1-lam)·lam^k ≤ G k` over `k < T` gives
`1 - lam ^ T ≤ ∑ G k ≤ (1-μ)d/(rΔ) ≤ 1/2`, so again `lam ^ T ≥ 1/2 > β`.

Consequence: the outer layer cannot be repaired by changing the crux alone.  The retention
probability must grow from round to round (`p_k ≈ x / (r·d_k)`, tracking the shrinking residual
degree `d_k`), which is an architectural change to the iteration, not a parameter calibration. -/
theorem crux_relative_telescope_false {r Δ T : ℕ} {d mu eta lam p c P Nv β : ℝ}
    (hrR : (2 : ℝ) ≤ (r : ℝ)) (hmu1 : mu ≤ 1) (hd : 0 < d)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hppos : 0 < p) (hΔpos : (0 : ℝ) < (Δ : ℝ))
    (hc0 : 0 ≤ c) (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (heta : 0 ≤ eta) (hP : 0 ≤ P) (hNv : 0 < Nv)
    (hβ : β < 1 / 2) (hTβ : lam ^ T ≤ β)
    (hΔd : 2 * ((1 - mu) * d) ≤ (r : ℝ) * (Δ : ℝ))
    (hcrux : ∀ k, k < T →
      0 ≤ ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
          * (p * (1 - p) ^ (r * Δ))
      ∧ (1 - lam) * lam ^ k * Nv
          ≤ (1 - eta) * Nv * (((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
                - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
              * (p * (1 - p) ^ (r * Δ)))
            - (r : ℝ) * P) :
    False := by
  classical
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith only [hrR]
  have hround : ∀ k ∈ Finset.range T,
      (1 - lam) * lam ^ k
        ≤ ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
              - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
            * (p * (1 - p) ^ (r * Δ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨hgain0, hineq⟩ := hcrux k hk
    set G : ℝ := ((1 - mu) * d * (1 - (r : ℝ) * Δ * p) ^ k
        - c * ∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
      * (p * (1 - p) ^ (r * Δ)) with hG
    have h1 : 0 ≤ (r : ℝ) * P := mul_nonneg (by positivity) hP
    have h2 : (1 - eta) * Nv * G ≤ Nv * G := by
      linarith only [mul_nonneg (mul_nonneg heta hNv.le) hgain0]
    have h4 : (1 - lam) * lam ^ k * Nv ≤ G * Nv := by linarith only [hineq, h1, h2]
    exact le_of_mul_le_mul_right h4 hNv
  have hsum := Finset.sum_le_sum hround
  have hlhs : ∑ k ∈ Finset.range T, (1 - lam) * lam ^ k = 1 - lam ^ T := by
    rw [← Finset.mul_sum]
    have h := geom_sum_mul (x := lam) (n := T)
    linarith only [h, mul_comm (∑ i ∈ Finset.range T, lam ^ i) (lam - 1)]
  have htot := total_gain_le (r := r) (Δ := Δ) (T := T) (d := d) (mu := mu) (p := p) (c := c)
    hmu1 hd hp0 hp1 hppos hΔpos hc0 hrpos hq
  have hhalf : (1 - mu) * d / ((r : ℝ) * (Δ : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hΔd]
  rw [hlhs] at hsum
  linarith only [hβ, hTβ, hsum, htot, hhalf]

/-- **(O3) The type-free Freedman parameter core is FALSE for `β < 1/2`.**

The crux inequality of the outer assembly requires that in *each* of the `T` rounds the per-round
gain covers a `(1-lam)`-fraction of the entire vertex set.  Summing the resulting `T` inequalities
against the geometric decay of the degree proxy bounds `T·(1-lam)` by `(1-μ)d/(rΔ) < 1/2`, whence
`lam ^ T ≥ 1 - T(1-lam) > 1/2 > β` by Bernoulli's inequality — contradicting `lam ^ T ≤ β`.

No concentration input is used: the obstruction is in the *shape* of the crux (comparing the
per-round gain to `|V|` instead of to the still-uncovered count `lam ^ k · |V|`). -/
theorem not_freedmanCardNumericThresholdParameterCore
    {r : ℕ} (hr : 2 ≤ r) {β η d₀ K : ℝ} (hβ : β < 1 / 2) (hη : 0 ≤ η) (hK : 0 < K) :
    ¬ FreedmanCardNumericThresholdParameterCore r β ((1 : ℝ) / 100) η d₀ K := by
  classical
  intro hcore
  obtain ⟨d, hd1, hd0, hsize⟩ :
      ∃ d : ℝ, (1 : ℝ) ≤ d ∧ d₀ ≤ d ∧ ((1 : ℕ) : ℝ) ≤ K * d ^ 2 := by
    refine ⟨max d₀ (max 1 (1 / K)), le_trans (le_max_left 1 (1 / K)) (le_max_right _ _),
      le_max_left _ _, ?_⟩
    have hdK : (1 / K) ≤ max d₀ (max 1 (1 / K)) :=
      le_trans (le_max_right 1 (1 / K)) (le_max_right _ _)
    have hd1 : (1 : ℝ) ≤ max d₀ (max 1 (1 / K)) :=
      le_trans (le_max_left 1 (1 / K)) (le_max_right _ _)
    have hKd : 1 ≤ K * max d₀ (max 1 (1 / K)) := by
      rw [div_le_iff₀ hK] at hdK
      linarith only [hdK]
    push_cast
    nlinarith only [hd1, hKd]
  have hd : 0 < d := lt_of_lt_of_le one_pos hd1
  obtain ⟨p, c, lam, T, hp0, hp1, hppos, hcpos, hq, hlam1, hlam0, hTβ, _hsmall, hcrux⟩ :=
    hcore 1 d hd hd0 hsize
  have hΔd : (1 + (1 : ℝ) / 100) * d ≤ ((Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hΔpos : (0 : ℝ) < ((Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) : ℝ) := by linarith only [hd, hΔd]
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  refine crux_telescope_false (r := r) (Δ := Nat.ceil ((1 + (1 : ℝ) / 100) * d)) (T := T)
    (d := d) (mu := (1 : ℝ) / 100) (eta := η) (lam := lam) (p := p) (c := c)
    (P := ((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) * (2 * Real.exp (-c ^ 2 /
      (2 * (((Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) : ℝ) ^ 2 *
        ((r : ℝ) * (Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) * p)
        + ((Nat.ceil ((1 + (1 : ℝ) / 100) * d) : ℕ) : ℝ) / 3 * c))))))
    (Nv := ((1 : ℕ) : ℝ)) (β := β)
    hrR (by norm_num) hd hp0 hp1 hppos hΔpos (le_of_lt hcpos) hq hlam0 hη (by positivity)
    (by norm_num) hβ hTβ ?_ hcrux
  nlinarith only [hΔd, hrR]

/-- **The concrete residual leaf obligation is FALSE for `β < 1/2`.**  The pair
`FreedmanCardExplicitBadRoundCore` at the concrete parameters
`(p, c, lam, T) = (1/(100 r Δ), √d, min (β/2) (1/2), 1)` cannot hold: combined with the (proved)
basic and proxy cores it yields the type-free numeric parameter core, refuted above.  Hence the
final residual of `nibbleTheoremMostCeilSized_of_freedman_concrete_badRound` is unreachable. -/
theorem not_freedmanExplicit_badRoundCore
    {r : ℕ} (hr : 2 ≤ r) {β η d₀ : ℝ} (hβ0 : 0 < β) (hβ : β < 1 / 2) (hη : 0 ≤ η) :
    ¬ FreedmanCardExplicitBadRoundCore freedmanExplicitP freedmanExplicitC freedmanExplicitLam
        freedmanExplicitT r β ((1 : ℝ) / 100) η d₀ 1 := by
  intro hBadRound
  refine not_freedmanCardNumericThresholdParameterCore (r := r) hr (β := β)
    (η := η) (d₀ := max 1 d₀) (K := 1) hβ hη one_pos ?_
  have hsplit : FreedmanCardExplicitSplitProxyIneqCore freedmanExplicitP freedmanExplicitC
      freedmanExplicitLam freedmanExplicitT r β ((1 : ℝ) / 100) η (max 1 d₀) 1 := by
    refine freedmanCardExplicitSplitProxyIneqCore_of_badRound ?_ ?_ ?_
    · intro N d hd hd0 hsize
      exact freedmanExplicitBasicCore r hr β hβ0 N d hd (le_trans (le_max_left 1 d₀) hd0) hsize
    · intro N d hd hd0 hsize
      exact freedmanExplicitDegreeProxyNonnegCore r β N d hd
        (le_trans (le_max_left 1 d₀) hd0) hsize
    · exact ⟨fun N d hd hd0 hsize =>
        hBadRound.1 N d hd (le_trans (le_max_right 1 d₀) hd0) hsize,
        fun N d hd hd0 hsize =>
        hBadRound.2 N d hd (le_trans (le_max_right 1 d₀) hd0) hsize⟩
  exact freedmanCardNumericThresholdParameterCore_of_explicit
    (freedmanCardExplicitParameterCore_of_split
      (freedmanCardExplicitSplitCore_of_factored
        (freedmanCardExplicitSplitFactoredCore_of_proxyIneq hsplit)))

end Nibble
