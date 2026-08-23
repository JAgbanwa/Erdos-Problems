/-
# Degree-decay invariant (analytic heart of the nibble oracle) — PROVED, sorry-free

Chains `nibbleStrategy_spec` clause (a) across `k` rounds: with `q := 1 - r*Δ*p ≥ 0`, the residual
degree after `k` rounds is bounded below by the geometric telescope `a₀·qᵏ − c·∑_{i<k} qⁱ`.
Standalone, Mathlib-only, reuses only already-proved bricks. Local — no delegation.
-/
import Nibble.NibbleStrategy
import Nibble.Iteration
import Nibble.InvariantDegree
import Nibble.RegularMost
import Nibble.Basic
import Mathlib.Algebra.Order.Ring.Star

open Hypergraph Finset

namespace Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Degree-decay invariant.** For the deterministic strategy `R = nibbleStrategy r Δ p c …`, with
`q := 1 - r*Δ*p ≥ 0`, every vertex's residual degree after `k` rounds is `≥ a₀·qᵏ − c·∑_{i<k} qⁱ`,
where `a₀ = degree H v`. Pure real-analysis induction chaining `nibbleStrategy_spec` clause (a). -/
theorem degree_decay_invariant (r Δ : ℕ) (p c : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ) (v : V) :
    ∀ k, (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p) ^ k
          - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
        ≤ (degree (nibbleResidual (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k) v : ℝ) := by
  set R := nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ with hRdef
  set q : ℝ := 1 - (r : ℝ) * Δ * p with hqdef
  intro k
  induction k with
  | zero =>
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
      show (degree H v : ℝ) ≤ (degree (nibbleResidual R H 0) v : ℝ)
      have : nibbleResidual R H 0 = H := rfl
      rw [this]
  | succ k ih =>
      -- H_k is r-uniform with degrees ≤ Δ, so spec clause (a) applies at round k
      have huni_k : IsUniform (nibbleResidual R H k) r := nibbleResidual_uniform huni R k
      have hdeg_k : ∀ x, degree (nibbleResidual R H k) x ≤ Δ :=
        fun x => degree_nibbleResidual_le H k hdeg0 x
      have hspec := (nibbleStrategy_spec r Δ p c hp0 hp1 hr1 hc hcΔ (nibbleResidual R H k)
        huni_k hdeg_k).1 v
      -- unfold the residual recursion for round k+1
      have hstep : nibbleResidual R H (k + 1)
          = residual (nibbleResidual R H k) (R (nibbleResidual R H k)) := rfl
      rw [hstep]
      -- spec (a): a_k * q - c < degree H_{k+1} v
      have hbound : (degree (nibbleResidual R H k) v : ℝ) * q - c
          < (degree (residual (nibbleResidual R H k) (R (nibbleResidual R H k))) v : ℝ) := by
        rw [hqdef]; exact hspec
      -- geometric telescope identity for the sum
      have hsum : q * (∑ i ∈ Finset.range k, q ^ i) + 1 = ∑ i ∈ Finset.range (k + 1), q ^ i := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_succ, pow_zero]
        ring_nf
      -- chain: RHS_{k+1} ≤ a_k*q - c < degree H_{k+1} v
      have hmul : (degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i) ≤
          (degree (nibbleResidual R H k) v : ℝ) := ih
      have hq_mul : ((degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i)) * q
          ≤ (degree (nibbleResidual R H k) v : ℝ) * q := by
        exact mul_le_mul_of_nonneg_right hmul hq
      calc (degree H v : ℝ) * q ^ (k + 1) - c * (∑ i ∈ Finset.range (k + 1), q ^ i)
          = ((degree H v : ℝ) * q ^ k - c * (∑ i ∈ Finset.range k, q ^ i)) * q - c := by
            rw [← hsum]; ring
        _ ≤ (degree (nibbleResidual R H k) v : ℝ) * q - c := by linarith only [hq_mul]
        _ ≤ (degree (residual (nibbleResidual R H k) (R (nibbleResidual R H k))) v : ℝ) := by
            linarith only [hbound]

/-- **Uniform residual-degree lower bound (non-exceptional vertices).** Combining the degree-decay
invariant with `NearlyRegularMost`'s lower bound `(1-μ)d ≤ degree H v`, every non-exceptional vertex
keeps residual degree `≥ (1-μ)·d·qᵏ − c·∑_{i<k} qⁱ` after `k` rounds — a bound *independent of `v`*. -/
theorem residual_degree_lower_most (r Δ : ℕ) (p c d μ η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ∀ v ∉ Exc, ∀ k,
        (1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)
          ≤ (degree (nibbleResidual (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k) v : ℝ) := by
  obtain ⟨Exc, hExc, hdeg⟩ := hreg
  refine ⟨Exc, hExc, fun v hv k => ?_⟩
  have hlow : (1 - μ) * d ≤ (degree H v : ℝ) := (hdeg v hv).1
  have hqk : (0 : ℝ) ≤ (1 - (r : ℝ) * Δ * p) ^ k := pow_nonneg hq k
  have hstep : (1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
      ≤ (degree H v : ℝ) * (1 - (r : ℝ) * Δ * p) ^ k :=
    mul_le_mul_of_nonneg_right hlow hqk
  have hinv := degree_decay_invariant r Δ p c hp0 hp1 hr1 hc hcΔ hq H huni hdeg0 v k
  linarith only [hstep, hinv]

/-- **Residual edge floor (handshake).** From the `v`-independent residual-degree floor
`F_k := (1-μ)·d·qᵏ − c·S_k` on non-exceptional vertices, the handshake identity
`∑_v degree H_k v = r·|H_k|` gives `(|V| − |Exc|)·F_k ≤ r·|H_k|` — a lower bound on the residual
edge count. (No sign hypothesis on `F_k` needed.) -/
theorem residual_edge_lower_most (r Δ : ℕ) (p c d μ η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η) (k : ℕ) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ((Fintype.card V : ℝ) - (Exc.card : ℝ))
          * ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
              - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
        ≤ (r : ℝ) * ((nibbleResidual (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k).card : ℝ) := by
  obtain ⟨Exc, hExc, hfloor⟩ := residual_degree_lower_most r Δ p c d μ η hp0 hp1 hr1 hc hcΔ hq
    H huni hdeg0 hreg
  refine ⟨Exc, hExc, ?_⟩
  set R := nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ with hRdef
  set Hk := nibbleResidual R H k with hHk
  set F : ℝ := (1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
      - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i) with hFdef
  -- handshake identity, cast to ℝ
  have hsum : ∑ v : V, (degree Hk v : ℝ) = (r : ℝ) * (Hk.card : ℝ) := by
    have hnat := sum_degree Hk (nibbleResidual_uniform huni R k)
    have := congrArg (Nat.cast : ℕ → ℝ) hnat
    push_cast at this
    simpa using this
  -- drop the exceptional vertices (nonneg degrees)
  have h1 : ∑ v ∈ Finset.univ \ Exc, (degree Hk v : ℝ) ≤ ∑ v : V, (degree Hk v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => by positivity)
  -- floor holds on the retained (non-exceptional) vertices
  have h2 : ∑ _v ∈ Finset.univ \ Exc, F ≤ ∑ v ∈ Finset.univ \ Exc, (degree Hk v : ℝ) :=
    Finset.sum_le_sum (fun v hv => by
      have hvnot : v ∉ Exc := (Finset.mem_sdiff.mp hv).2
      exact hfloor v hvnot k)
  -- evaluate the constant sum
  have h3 : ∑ _v ∈ Finset.univ \ Exc, F = ((Fintype.card V : ℝ) - (Exc.card : ℝ)) * F := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ_diff,
        Nat.cast_sub (Finset.card_le_univ _)]
  rw [h3] at h2
  linarith only [hsum, h1, h2]

/-- **Round covering floor (step ii).** Combining `nibbleStrategy_spec` clause (b)
(`|H_k|·P − E ≤ roundMatching.card` with `P := p(1-p)^{rΔ}`, `E := |V|·(|V|Δ²/c²)`),
the matching support identity (`support M = r·M.card`), and the residual edge floor, the vertices
covered in round `k` satisfy `(|V|−|Exc|)·F_k·P − r·E ≤ support(roundMatching (R H_k))`. This is the
whole covering half of the oracle; only parameter selection (step iii) remains. -/
theorem round_cover_lower_most (r Δ : ℕ) (p c d μ η : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2)
    (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η) (k : ℕ) :
    ∃ Exc : Finset V, (Exc.card : ℝ) ≤ η * (Fintype.card V : ℝ) ∧
      ((Fintype.card V : ℝ) - (Exc.card : ℝ))
          * ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
              - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
          * (p * (1 - p) ^ (r * Δ))
        - (r : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2))
      ≤ ((support (roundMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ
            (nibbleResidual (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k)))).card : ℝ) := by
  obtain ⟨Exc, hExc, hedge⟩ := residual_edge_lower_most r Δ p c d μ η hp0 hp1 hr1 hc hcΔ hq
    H huni hdeg0 hreg k
  refine ⟨Exc, hExc, ?_⟩
  set R := nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ with hRdef
  set Hk := nibbleResidual R H k with hHk
  have huni_k : IsUniform Hk r := nibbleResidual_uniform huni R k
  have hdeg_k : ∀ x, degree Hk x ≤ Δ := fun x => degree_nibbleResidual_le H k hdeg0 x
  have hsub : R Hk ⊆ Hk := nibbleStrategy_subset r Δ p c hp0 hp1 hr1 hc hcΔ Hk
  have hb := (nibbleStrategy_spec r Δ p c hp0 hp1 hr1 hc hcΔ Hk huni_k hdeg_k).2
  have hsupp : ((support (roundMatching (R Hk))).card : ℝ)
      = (r : ℝ) * ((roundMatching (R Hk)).card : ℝ) := by
    have hnat := matching_support_card huni_k (roundMatching_isMatching hsub)
    exact_mod_cast hnat
  have hP : (0 : ℝ) ≤ p * (1 - p) ^ (r * Δ) := mul_nonneg hp0 (pow_nonneg (by linarith) _)
  have hrpos : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hProd1 : ((Fintype.card V : ℝ) - (Exc.card : ℝ))
        * ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
            - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
        * (p * (1 - p) ^ (r * Δ))
      ≤ ((r : ℝ) * (Hk.card : ℝ)) * (p * (1 - p) ^ (r * Δ)) :=
    mul_le_mul_of_nonneg_right hedge hP
  have hProd2 : (r : ℝ) * ((Hk.card : ℝ) * (p * (1 - p) ^ (r * Δ))
        - (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2))
      ≤ (r : ℝ) * ((roundMatching (R Hk)).card : ℝ) :=
    mul_le_mul_of_nonneg_left hb hrpos
  rw [hsupp]
  nlinarith only [hProd1, hProd2]

/-- **Oracle from an explicit parameter inequality (step iii, MECHANICAL REDUCTION).** The nibble
covering oracle required by `exists_matching_of_oracle_lt` follows from a clean per-round inequality
on the *gain* `Gₖ := Fₖ·P` (`Fₖ := (1-μ)d·qᵏ − c·Sₖ`, `P := p(1-p)^{rΔ}`): namely `Gₖ ≥ 0` and
`(1-lam)·|V| ≤ (1-η)·|V|·Gₖ − r·E`. Uses `round_cover_lower_most` + `support ≤ |V|`. This isolates
the whole of step (iii) to PURE parameter existence (the `hcrux` hypothesis). -/
theorem oracle_of_crux (r Δ : ℕ) (p c d μ η lam : ℝ) (T : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r) (hc : 0 < c)
    (hcΔ : (Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 < c ^ 2) (hq : 0 ≤ 1 - (r : ℝ) * Δ * p)
    (hlam1 : lam ≤ 1)
    (H : Finset (Finset V)) (huni : IsUniform H r) (hdeg0 : ∀ x, degree H x ≤ Δ)
    (hreg : NearlyRegularMost H d μ η)
    (hcrux : ∀ k, k < T →
      0 ≤ ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
              - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)) * (p * (1 - p) ^ (r * Δ))
      ∧ (1 - lam) * (Fintype.card V : ℝ)
          ≤ (1 - η) * (Fintype.card V : ℝ)
              * (((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
                    - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i))
                  * (p * (1 - p) ^ (r * Δ)))
            - (r : ℝ) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * (Δ : ℝ) ^ 2 / c ^ 2))) :
    ∀ k, k < T →
      (1 - lam) * ((Fintype.card V : ℝ)
          - ((support (nibbleMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k)).card : ℝ))
        ≤ ((support (roundMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ
            (nibbleResidual (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k)))).card : ℝ) := by
  intro k hk
  obtain ⟨Exc, hExc, hcov⟩ :=
    round_cover_lower_most r Δ p c d μ η hp0 hp1 hr1 hc hcΔ hq H huni hdeg0 hreg k
  obtain ⟨hGnn, hkey⟩ := hcrux k hk
  -- normalize associativity: `(N-Exc)*F*P = (N-Exc)*(F*P)` in the covering floor
  rw [mul_assoc ((Fintype.card V : ℝ) - (Exc.card : ℝ))] at hcov
  -- abstract the gain `G := F*P` (folds hcov, hGnn, hkey uniformly)
  set G : ℝ := ((1 - μ) * d * (1 - (r : ℝ) * Δ * p) ^ k
      - c * (∑ i ∈ Finset.range k, (1 - (r : ℝ) * Δ * p) ^ i)) * (p * (1 - p) ^ (r * Δ)) with hGdef
  -- (1-η)|V| ≤ |V| - |Exc|, and G ≥ 0, so (1-η)|V|·G ≤ (|V|-|Exc|)·G
  have hExc' : (1 - η) * (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) - (Exc.card : ℝ) := by
    nlinarith only [hExc]
  have hmono : (1 - η) * (Fintype.card V : ℝ) * G ≤ ((Fintype.card V : ℝ) - (Exc.card : ℝ)) * G :=
    mul_le_mul_of_nonneg_right hExc' hGnn
  -- covered ≤ |V|, and 1 - lam ≥ 0
  have hcovered : ((support (nibbleMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k)).card : ℝ)
      ≤ (Fintype.card V : ℝ) := by exact_mod_cast Finset.card_le_univ _
  have hlamnn : (0 : ℝ) ≤ 1 - lam := by linarith
  have hleft : (1 - lam) * ((Fintype.card V : ℝ)
      - ((support (nibbleMatching (nibbleStrategy r Δ p c hp0 hp1 hr1 hc hcΔ) H k)).card : ℝ))
      ≤ (1 - lam) * (Fintype.card V : ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) hlamnn
  -- chain: goal ≤ (1-lam)|V| ≤ (1-η)|V|·G − E ≤ (|V|-|Exc|)·G − E ≤ covering
  linarith only [hcov, hmono, hkey, hleft]

end Nibble
