/-
# The ρ-window of the §10.12 assembly

`BKLO/Section1012Reconcile.lean` re-runs the proof of BKLO Lemma 10.12 (`r = 2`, `F = K₃`, dense
regime) with the sparsity parameter `ρ` left free, from the *corrected* §7.2 and §9.3 inputs.  This
file collects the arithmetic that surrounds that assembly:

* `BKLO.Cor1011K3AtRho ρ k` — Corollary 10.11 at a single `(ρ, k)`, all of §10.2 that the assembly
  uses — together with the two ways of obtaining it: from `BKLO.Cor1011K3`, and from the
  codegree-regime `BKLO.Cor1011K3Dense` (proved in this development) when `1/(648k²) < ρ`;
* `BKLO.Lemma1012ParamsGen` — the numerical hierarchy `γ = ρ²ε/(1000k²)`, `α = ε/(16k²)` for an
  arbitrary `0 < ρ ≤ 1`;
* the slack inequality `18k√ρ³ ≤ ρ/4` of condition (ii) of Lemma 10.10, which is the only
  constraint the assembly puts on `ρ`: it holds at `ρ = 1/(10000k²)`
  (`BKLO.slack_at_ten_thousand`) and it *fails*, by a factor of nearly three, at the candidate
  `ρ = 1/(625k²)` of `BKLO/RhoReconcile625.lean` (`BKLO.slack_fails_at_625`);
* `BKLO.slack_lower_bound_of_regime` and `BKLO.rho_window_empty`: in the codegree regime
  `1/(648k²) < ρ` the slack always exceeds `0.7ρ`, so the codegree-regime Lemma 10.10 and the
  §10.12 assembly have **disjoint** `ρ`-windows.  This is the precise obstruction to discharging
  Lemma 10.12 from `BKLO.lemma1010K3Dense_holds`.

Everything here is `sorry`-free.
-/
import BKLO.Section1012Assembly
import BKLO.Section1011Dense
import BKLO.RhoReconcile625

open Finset

namespace BKLO

/-! ### Corollary 10.11 at a single `(ρ, k)` -/

/-- `BKLO.Cor1011K3` at a fixed sparsity parameter `ρ` and a fixed number `k` of parts.  This is
all of Corollary 10.11 that the proof of Lemma 10.12 uses. -/
def Cor1011K3AtRho (ρ : ℝ) (k : ℕ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S →
      IsEquitablePartition k P S →
      (∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, 2 ∣ degTo H x W) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
        (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, (degTo H y (beforeParts P idx W) : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ H₀ : Finset (Sym2 V), H₀ ⊆ insideParts H P ∧
        TriDecomp (crossParts H P ∪ H₀) ∧ ∀ v : V, (edeg H₀ v : ℝ) ≤ 2 * α * (S.card : ℝ)

/-- `BKLO.Cor1011K3` at a *single* triple `(α, ρ, k)`.  This is all that the §10.12 assembly of
`BKLO.lemma1012K3'At_of_true_inputs_atAlpha` uses: the assembly applies Corollary 10.11 exactly
once, at `α = ε/(16k²)` and at its own `ρ`.  Unlike `BKLO.Cor1011K3AtRho` it does **not** quantify
over `α`, so it can be supplied by the hierarchy-correct `BKLO.Cor1011K3Hier` whenever
`2kρ ≤ α`. -/
def Cor1011K3AtAlphaRho (α ρ : ℝ) (k : ℕ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V))
      (idx : Finset V → ℕ),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S →
      IsEquitablePartition k P S →
      (∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → idx W ≠ idx W') →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, 2 ∣ degTo H x W) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ W ∈ P, ∀ x ∈ beforeParts P idx W, ∀ x' ∈ beforeParts P idx W, x ≠ x' →
        (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, (degTo H y (beforeParts P idx W) : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ W ∈ P, ∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ H₀ : Finset (Sym2 V), H₀ ⊆ insideParts H P ∧
        TriDecomp (crossParts H P ∪ H₀) ∧ ∀ v : V, (edeg H₀ v : ℝ) ≤ 2 * α * (S.card : ℝ)

theorem cor1011K3AtAlphaRho_of_atRho {α ρ : ℝ} {k : ℕ} (h : Cor1011K3AtRho ρ k) (hα : 0 < α) :
    Cor1011K3AtAlphaRho α ρ k := h α hα

theorem cor1011K3AtRho_of_cor1011K3 {ρ : ℝ} {k : ℕ} (h : Cor1011K3) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hk : 0 < k) : Cor1011K3AtRho ρ k :=
  fun α hα => h α ρ k hα hρ hρ1 hk

/-- The codegree-regime Corollary 10.11 (`BKLO.Cor1011K3Dense`, proved from
`BKLO.lemma1010K3Dense_holds`) supplies `Cor1011K3AtRho ρ k` — but only for `ρ > 1/(648k²)`. -/
theorem cor1011K3AtRho_of_dense {ρ : ℝ} {k : ℕ} (h : Cor1011K3Dense) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hk : 0 < k) (hreg : 1 / (648 * (k : ℝ) ^ 2) < ρ) : Cor1011K3AtRho ρ k :=
  fun α hα => h α ρ k hα hρ hρ1 hk hreg

/-! ### The numerical hierarchy for a free `ρ`

These are the facts about `γ = ρ²ε/(1000k²)` and `α = ε/(16k²)` that the assembly uses, with the
specific value of `ρ` replaced by `0 < ρ ≤ 1`. -/

namespace Lemma1012ParamsGen

variable {kk ε ρ γ α : ℝ}

theorem rho_sq_le (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ρ ^ 2 ≤ ρ := by nlinarith only [h0, h1]

theorem gamma_pos (hk : 30 ≤ kk) (hε : 0 < ε) (hρ : 0 < ρ)
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : 0 < γ := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  rw [hγ]; positivity

theorem gamma_le (hk : 30 ≤ kk) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) (hρ : 0 < ρ)
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : γ ≤ ρ ^ 2 / 2000 := by
  have h := Lemma1012Params.gamma_mul_k hk hε hε3 hγ
  have hγ0 : 0 < γ := gamma_pos hk hε hρ hγ
  nlinarith only [hk, h]

theorem gamma_le_eps4 (hk : 30 ≤ kk) (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) : γ ≤ ε / 4 := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith only [hρ0, hρ1]
  have hkk2 : (900 : ℝ) ≤ kk ^ 2 := by nlinarith only [hk]
  rw [hγ, div_le_iff₀ (by positivity)]
  nlinarith only [hε, hρsq, hkk2]

/-- The final degree bound `3γ + 2α ≤ ε/(2k²)`; it only needs `ρ² ≤ 1`. -/
theorem final_bound (hk : 30 ≤ kk) (hε : 0 < ε) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hγ : γ = ρ ^ 2 * ε / (1000 * kk ^ 2)) (hα : α = ε / (16 * kk ^ 2)) :
    3 * γ + 2 * α ≤ ε / (2 * kk ^ 2) := by
  have hk0 : (0 : ℝ) < kk := by linarith only [hk]
  have hρsq : ρ ^ 2 ≤ 1 := by nlinarith only [hρ0, hρ1]
  have hc : (0 : ℝ) < ε / kk ^ 2 := by positivity
  have h1 : γ ≤ ε / kk ^ 2 / 1000 := by
    have he : γ = ρ ^ 2 * (ε / kk ^ 2) / 1000 := by rw [hγ]; field_simp
    have h2 : ρ ^ 2 * (ε / kk ^ 2) ≤ ε / kk ^ 2 := by nlinarith only [hρsq, hc]
    rw [he]; linarith only [h2]
  have h2 : α = ε / kk ^ 2 / 16 := by rw [hα]; field_simp
  have h3 : ε / (2 * kk ^ 2) = ε / kk ^ 2 / 2 := by field_simp
  rw [h2, h3]; linarith only [hc, h1]

end Lemma1012ParamsGen

/-! ### The ρ-window of the reconciliation is empty -/

/-- **In the codegree regime the slack of condition (ii) exceeds `0.7ρ`.**  If `1/(648k²) < ρ` —
the hypothesis under which `BKLO.lemma1010K3Dense_holds` proves Lemma 10.10 — then
`18k√ρ³ > (7/10)ρ`, since `18k√ρ³ = 18k ρ √ρ` and `√ρ > 1/(18√2 k)`.  The threshold `1/√2 ≈ 0.707`
is exactly the boundary `4(18k√ρ³)² = 2ρ²` of the Cauchy–Schwarz count behind the codegree
regime. -/
theorem slack_lower_bound_of_regime {ρ : ℝ} {k : ℕ} (hk : 0 < k) (hρ : 0 < ρ)
    (hreg : 1 / (648 * (k : ℝ) ^ 2) < ρ) : 7 / 10 * ρ < 18 * (k : ℝ) * Real.sqrt ρ ^ 3 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hspos : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hcube : Real.sqrt ρ ^ 3 = ρ * Real.sqrt ρ := by
    rw [show Real.sqrt ρ ^ 3 = Real.sqrt ρ ^ 2 * Real.sqrt ρ by ring, hs]
  have hlt : (49 : ℝ) / (32400 * (k : ℝ) ^ 2) < 1 / (648 * (k : ℝ) ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg ((k : ℝ))]
  have hsq : (7 / (180 * (k : ℝ))) ^ 2 = (49 : ℝ) / (32400 * (k : ℝ) ^ 2) := by
    field_simp; ring
  have h1 : (7 / (180 * (k : ℝ))) ^ 2 < ρ := by rw [hsq]; linarith only [hreg, hlt]
  have hkey : 7 / (180 * (k : ℝ)) < Real.sqrt ρ := by nlinarith only [hs, hspos, h1]
  have hmul : 18 * (k : ℝ) * ρ * (7 / (180 * (k : ℝ))) < 18 * (k : ℝ) * ρ * Real.sqrt ρ :=
    mul_lt_mul_of_pos_left hkey (by positivity)
  have heq : 18 * (k : ℝ) * ρ * (7 / (180 * (k : ℝ))) = 7 / 10 * ρ := by field_simp; ring
  have heq2 : 18 * (k : ℝ) * (ρ * Real.sqrt ρ) = 18 * (k : ℝ) * ρ * Real.sqrt ρ := by ring
  rw [hcube]
  linarith only [hmul, heq]

/-- **The two demands on `ρ` are contradictory.**  The codegree-regime Lemma 10.10 needs
`1/(648k²) < ρ`, while the §10.12 assembly needs the slack inequality `18k√ρ³ ≤ ρ/4`, i.e.
`ρ ≤ 1/(5184k²)`.  No `ρ` satisfies both, so `BKLO.Cor1011K3Dense` cannot be fed into
`BKLO.lemma1012K3'At_of_true_inputs`.  By `BKLO.slack_lower_bound_of_regime` this is not an
artefact of the constant `1/4`: in the codegree regime the slack is above `0.7ρ`, so no assembly
whose condition (ii) can only afford a slack below `0.7ρ` can use it. -/
theorem rho_window_empty {ρ : ℝ} {k : ℕ} (hk : 0 < k) (hρ : 0 < ρ)
    (hreg : 1 / (648 * (k : ℝ) ^ 2) < ρ) : ¬ 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4 := by
  intro h
  have := slack_lower_bound_of_regime hk hρ hreg
  linarith only [hρ, h, this]

/-- The candidate parameter of `BKLO/RhoReconcile625.lean` is outside the window: at
`ρ = 1/(625k²)` the slack of condition (ii) is `(18/25)ρ`, which exceeds `ρ/4`. -/
theorem slack_fails_at_625 {ρ : ℝ} {k : ℕ} (hk30 : 30 ≤ k)
    (hρ : ρ = 1 / (625 * (k : ℝ) ^ 2)) : ¬ 18 * (k : ℝ) * Real.sqrt ρ ^ 3 ≤ ρ / 4 := by
  have hkR : (30 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk30
  have h := RhoReconcile625.eighteen_sqrt hkR hρ
  have hρ0 : 0 < ρ := RhoReconcile625.rho_pos hkR hρ
  rw [h]
  intro hc
  linarith only [hρ0, hc]

end BKLO
