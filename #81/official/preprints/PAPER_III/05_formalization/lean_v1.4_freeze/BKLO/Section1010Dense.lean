/-
# BKLO Lemma 10.10 for `r = 2` in the regime where the codegree bound suffices

`BKLO.Cex.not_lemma1010K3` shows that BKLO Lemma 10.10, transcribed as `BKLO.Lemma1010K3` without
the paper's hierarchy `ρ ≪ α, 1/k`, is false.  This file proves the lemma in the complementary
regime, where `ρ` is *not* small compared with `1/k²`:

  if `1/(648k²) < ρ`, then hypotheses (i)–(v) of Lemma 10.10 do give the conclusion.

The mechanism is exactly the "codegree → budget" bookkeeping.  Write `n = |W|`, and let
`g = 18k√ρ³` be the slack in hypothesis (ii).

* Hypothesis (ii) forces every apex neighbourhood meeting `W` to have at least `2gn` vertices.
* Hypothesis (iii) bounds pairwise codegrees by `2ρ²n`.
* Corrádi's counting bound (`BKLO.card_le_of_codegree`) then gives, for every `y ∈ W`,
  `d_H(y,U) · (4g² − 2ρ²) ≤ 2g`, i.e. `d_H(y,U) ≤ C(k,ρ)`, a constant — *provided* `4g² > 2ρ²`,
  which is exactly `ρ > 1/(648k²)`.
* A bounded number of apices at each vertex is a budget the greedy sweep can afford: for `n` large
  the accumulated used degree `2 d_H(v,U) ≤ 2C` is below the slack `gn`, so
  `BKLO.exists_triDecomp_of_budget` applies, and the resulting `H_V` has
  `Δ_{H_V}(v) ≤ 2 d_H(v,U) ≤ 2C ≤ 2αn`.

For `ρ ≤ 1/(648k²)` this counting is vacuous — and indeed the hyperplane counterexample of
`BKLO/Section1010Refutation.lean` lives there.  In that regime the paper's proof goes through
Lemma 10.7 / Corollary 10.9, whose content is a *pseudorandom* `K_r`-factor statement (random,
spread-out factors with concentration), not a greedy one; that is the ingredient which is missing
here.

Everything here is `sorry`-free.
-/
import BKLO.CodegreeCounting
import BKLO.StarGreedyBudget
import BKLO.Section1012Defs

open Finset

namespace BKLO

/-! ### The greedy core, with a real-valued budget -/

variable {V : Type} [DecidableEq V]

/-- The greedy sweep in the form in which Lemma 10.10 uses it: the slack `g|W|` of hypothesis (ii)
must dominate twice the apex degree of every `v ∈ W`, and the final bound is whatever bounds twice
that apex degree. -/
theorem dense_core {H : Finset (Sym2 V)} {U W : Finset V} {g α : ℝ}
    (hloop : ∀ e ∈ H, ¬ e.IsDiag) (hUW : Disjoint U W)
    (hEven : ∀ x ∈ U, Even (nbhdIn H x W).card)
    (hii : ∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
      (1 / 2 : ℝ) * (degTo H x W : ℝ) + g * (W.card : ℝ) ≤ (degTo H y (nbhdIn H x W) : ℝ))
    (hbudR : ∀ v ∈ W, 2 * (degTo H v U : ℝ) ≤ g * (W.card : ℝ))
    (hfinal : ∀ v ∈ W, 2 * (degTo H v U : ℝ) ≤ 2 * α * (W.card : ℝ))
    (hαn : 0 ≤ 2 * α * (W.card : ℝ)) :
    ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
      TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ) := by
  classical
  have hgn : 0 ≤ g * (W.card : ℝ) := by
    rcases W.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · exact le_trans (by positivity) (hbudR v hv)
  set d : ℕ := ⌊g * (W.card : ℝ)⌋₊ with hddef
  have hdle : (d : ℝ) ≤ g * (W.card : ℝ) := Nat.floor_le hgn
  have hbud : ∀ v ∈ W, 2 * degTo H v U ≤ d := by
    intro v hv
    refine Nat.le_floor ?_
    have := hbudR v hv
    push_cast
    linarith
  have hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + d ≤ edeg (edgesIn H (nbhdIn H x W)) v := by
    intro x hx v hv
    obtain ⟨mm, hmm⟩ := hEven x hx
    have hhalf : (nbhdIn H x W).card / 2 = mm := by omega
    have hxc : (degTo H x W : ℝ) = (mm : ℝ) + (mm : ℝ) := by
      have h : degTo H x W = mm + mm := hmm
      rw [h]; push_cast; ring
    have hreal := hii x hx v hv
    have hnat : (nbhdIn H x W).card / 2 + d ≤ degTo H v (nbhdIn H x W) := by
      have hcastle : ((mm + d : ℕ) : ℝ) ≤ (degTo H v (nbhdIn H x W) : ℝ) := by
        push_cast
        rw [hxc] at hreal
        linarith
      have hcast : mm + d ≤ degTo H v (nbhdIn H x W) := by exact_mod_cast hcastle
      omega
    exact le_trans hnat (degTo_le_edeg_edgesIn hv)
  obtain ⟨HV, hsub, hdec, hdeg⟩ := exists_triDecomp_of_budget hloop hUW hEven hmindeg hbud
  refine ⟨HV, hsub, hdec, ?_⟩
  intro v
  by_cases hvW : v ∈ W
  · have h1 : ((edeg HV v : ℕ) : ℝ) ≤ ((2 * degTo H v U : ℕ) : ℝ) := by exact_mod_cast hdeg v
    have h2 := hfinal v hvW
    push_cast at h1
    linarith
  · have hzero : edeg HV v = 0 := by
      unfold edeg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hve
      exact hvW ((mem_edgesIn.1 (hsub he)).2 v hve)
    rw [hzero]
    simpa using hαn

/-! ### Lemma 10.10 in the regime `ρ > 1/(648k²)` -/

/-- **BKLO Lemma 10.10 for `r = 2`, with the hierarchy `ρ ≪ 1/k` replaced by its opposite
`1/(648k²) < ρ`.**

This is `BKLO.Lemma1010K3` with the extra hypothesis `1/(648k²) < ρ`, which is exactly what makes
the codegree hypothesis (iii) bound the number of apices at a vertex of `W`.  Hypotheses (iv) and
(v) of the paper are kept, for faithfulness, although the proof below does not use them. -/
def Lemma1010K3Dense : Prop :=
  ∀ (α ρ : ℝ) (k : ℕ), 0 < α → 0 < ρ → ρ < 1 → 0 < k → 1 / (648 * (k : ℝ) ^ 2) < ρ →
    ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (H : Finset (Sym2 V)) (S U W : Finset V),
      n₀ ≤ S.card → (∀ e ∈ H, ¬ e.IsDiag) → H ⊆ cliqueEdges S → U ⊆ S → W ⊆ S →
      Disjoint U W → (S.card : ℝ) / (k : ℝ) - 1 ≤ (W.card : ℝ) →
      (∀ x ∈ U, 2 ∣ degTo H x W) →
      (∀ x ∈ U, ∀ y ∈ nbhdIn H x W,
        (1 / 2 : ℝ) * (degTo H x W : ℝ) + 18 * (k : ℝ) * Real.sqrt ρ ^ 3 * (W.card : ℝ)
          ≤ (degTo H y (nbhdIn H x W) : ℝ)) →
      (∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → (codegTo H x x' W : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ)) →
      (∀ y ∈ W, (degTo H y U : ℝ) ≤ 2 * (k : ℝ) * ρ * (W.card : ℝ)) →
      (∀ y ∈ W, ((1 : ℝ) / 2 + 2 * α) * (W.card : ℝ) ≤ (degTo H y W : ℝ)) →
      ∃ HV : Finset (Sym2 V), HV ⊆ edgesIn H W ∧
        TriDecomp (edgesBtw H U W ∪ HV) ∧ ∀ v : V, (edeg HV v : ℝ) ≤ 2 * α * (W.card : ℝ)

theorem lemma1010K3Dense_holds : Lemma1010K3Dense := by
  intro α ρ k hα hρ _hρ1 hk hdense
  classical
  have hkR : (0:ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hsqpos : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  set g : ℝ := 18 * (k : ℝ) * Real.sqrt ρ ^ 3 with hgdef
  have hgpos : 0 < g := by rw [hgdef]; positivity
  have hg2 : g ^ 2 = 324 * (k : ℝ) ^ 2 * ρ ^ 3 := by
    rw [hgdef]
    have h : (Real.sqrt ρ ^ 3) ^ 2 = ρ ^ 3 := by
      rw [show (Real.sqrt ρ ^ 3) ^ 2 = (Real.sqrt ρ ^ 2) ^ 3 by ring, hsq]
    calc (18 * (k : ℝ) * Real.sqrt ρ ^ 3) ^ 2
        = 324 * (k:ℝ) ^ 2 * (Real.sqrt ρ ^ 3) ^ 2 := by ring
      _ = 324 * (k:ℝ) ^ 2 * ρ ^ 3 := by rw [h]
  set D : ℝ := 4 * g ^ 2 - 2 * ρ ^ 2 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, hg2]
    have h1 : 1 < 648 * (k:ℝ) ^ 2 * ρ := by
      rw [div_lt_iff₀ (by positivity)] at hdense
      linarith
    have h2 : 2 * ρ ^ 2 * 1 < 2 * ρ ^ 2 * (648 * (k:ℝ) ^ 2 * ρ) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    nlinarith only [h2]
  set C : ℝ := 2 * g / D with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set B : ℝ := max (2 * C / g) (C / α) with hBdef
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨k * (⌈B⌉₊ + 1), ?_⟩
  intro V _ H S U W hScard hloop _hHS _hUS _hWS hUW hWcard hdvd hii hiii _hiv _hv
  -- `|W|` is large
  have hWB : B ≤ (W.card : ℝ) := by
    have h1 : ((k * (⌈B⌉₊ + 1) : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hScard
    have h2 : ((⌈B⌉₊ : ℝ) + 1) ≤ (S.card : ℝ) / (k:ℝ) := by
      rw [le_div_iff₀ hkR]
      push_cast at h1
      linarith
    have h3 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    linarith
  have hWpos : 0 < (W.card : ℝ) := lt_of_lt_of_le hBpos hWB
  -- the codegree bound gives a constant bound on the number of apices at each `y ∈ W`
  have hapex : ∀ y ∈ W, (degTo H y U : ℝ) ≤ C := by
    intro y hy
    set T : Finset V := nbhdIn H y U with hT
    have hsub : ∀ x ∈ T, nbhdIn H x W ⊆ W := fun x _ => nbhdIn_subset H x W
    have hyN : ∀ x ∈ T, y ∈ nbhdIn H x W := by
      intro x hx
      rw [hT, mem_nbhdIn] at hx
      refine mem_nbhdIn.2 ⟨hy, ?_⟩
      rw [Sym2.eq_swap]
      exact hx.2
    have hsize : ∀ x ∈ T, 2 * g * (W.card : ℝ) ≤ ((nbhdIn H x W).card : ℝ) := by
      intro x hx
      have hxU : x ∈ U := (mem_nbhdIn.1 (by rw [hT] at hx; exact hx)).1
      have h1 := hii x hxU y (hyN x hx)
      have h2 : (degTo H y (nbhdIn H x W) : ℝ) ≤ ((nbhdIn H x W).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (nbhdIn_subset H y (nbhdIn H x W))
      have h3 : (degTo H x W : ℝ) = ((nbhdIn H x W).card : ℝ) := rfl
      rw [h3] at h1
      linarith
    have hcodeg : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' →
        (((nbhdIn H x W) ∩ (nbhdIn H x' W)).card : ℝ) ≤ 2 * ρ ^ 2 * (W.card : ℝ) := by
      intro x hx x' hx' hne
      have hxU : x ∈ U := (mem_nbhdIn.1 (by rw [hT] at hx; exact hx)).1
      have hx'U : x' ∈ U := (mem_nbhdIn.1 (by rw [hT] at hx'; exact hx')).1
      exact hiii x hxU x' hx'U hne
    have hmain := card_le_of_codegree W T (fun x => nbhdIn H x W) (2 * g * (W.card : ℝ))
      (2 * ρ ^ 2 * (W.card : ℝ)) (by positivity) (by positivity) hsub hsize hcodeg
    have hTcard : ((T.card : ℝ)) = (degTo H y U : ℝ) := rfl
    rw [hTcard] at hmain
    -- `t (4g² − 2ρ²) n² ≤ 2g n²`
    have hn2 : (0:ℝ) < (W.card : ℝ) ^ 2 := by positivity
    have hstep : (degTo H y U : ℝ) * D ≤ 2 * g := by
      have h := hmain
      nlinarith only [h, hn2, hWpos]
    rw [hCdef, le_div_iff₀ hDpos]
    linarith
  -- the budget fits inside the slack, and gives the final degree bound
  have hbudR : ∀ v ∈ W, 2 * (degTo H v U : ℝ) ≤ g * (W.card : ℝ) := by
    intro v hv
    have h1 := hapex v hv
    have h2 : 2 * C / g ≤ (W.card : ℝ) := le_trans (le_max_left _ _) hWB
    rw [div_le_iff₀ hgpos] at h2
    linarith
  have hfinal : ∀ v ∈ W, 2 * (degTo H v U : ℝ) ≤ 2 * α * (W.card : ℝ) := by
    intro v hv
    have h1 := hapex v hv
    have h2 : C / α ≤ (W.card : ℝ) := le_trans (le_max_right _ _) hWB
    rw [div_le_iff₀ hα] at h2
    linarith
  have hEven : ∀ x ∈ U, Even (nbhdIn H x W).card := by
    intro x hx
    obtain ⟨mm, hmm⟩ := hdvd x hx
    have h2 : (nbhdIn H x W).card = 2 * mm := hmm
    exact ⟨mm, by omega⟩
  exact dense_core hloop hUW hEven hii hbudR hfinal (by positivity)

end BKLO
