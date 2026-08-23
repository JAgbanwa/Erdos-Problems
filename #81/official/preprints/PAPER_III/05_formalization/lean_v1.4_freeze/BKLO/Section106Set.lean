/-
# BKLO Lemma 10.6 for `r = 2` on a vertex *set*: `BKLO.Lemma106K3Set`

`BKLO.Lemma106K3Set δ` (see `BKLO/Section1012Defs.lean`) is the form of BKLO Lemma 10.6 that the
proof of Lemma 10.12 consumes: the graph lives on a vertex set `S : Finset V` instead of on a
`Fintype` vertex type, and the hierarchy carried is the weak `1/k ≤ ε`.  In
`BKLO/Section1012Assembly.lean` it is a hypothesis of `BKLO.lemma1012K3'_of_inputs`.

This file discharges it, from the approximate-decomposition threshold `δ_F^η`
(`BKLO.ApproxTriDecompMinDeg δ`) alone:

* `BKLO.lemma106K3AtSet_of_fin` — the **transport**: the conclusion of Lemma 10.6, proved on a
  `Fintype` vertex type (this is what `BKLO.lemma106K3_core` produces), transported to a vertex set
  by instantiating the vertex type at the subtype `↥S` and pushing the resulting `H`, its triangle
  decomposition and its two degree bounds back along `↥S ↪ V` (`BKLO/SubtypeTransport.lean`);
* `BKLO.lemma106K3Set_of_approxTriDecomp` — `Lemma106K3Set δ` for `2/3 ≤ δ ≤ 1`, using the
  transformation step under the *weak* hierarchy `1/k ≤ ε`
  (`BKLO.transformStepK3At_of_approxTriDecomp_weak`), which is exactly what `Lemma106K3Set`
  provides and what the stronger `BKLO.Lemma106K3Res` (`1/k ≤ ε/8`) cannot supply;
* `BKLO.lemma106K3Set_of_input` — the same with BKLO Lemma 10.3 discharged by the proved
  `BKLO.lemma103K3_holds`, so that the only remaining input is `δ_F^η`.

Everything here is `sorry`-free.
-/
import BKLO.Section10TransformStepWeak
import BKLO.Section10Lemma103
import BKLO.Section1012Defs
import BKLO.Section1012Assembly

open Finset

namespace BKLO

/-- The conclusion of BKLO Lemma 10.6 (`r = 2`) at fixed parameters `(δ, γ, ε, k)`, on a `Fintype`
vertex type.  This is what `BKLO.lemma106K3_core` produces. -/
def Lemma106K3AtFin (δ γ ε : ℝ) (k : ℕ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V)) (P : Finset (Finset V)),
      n₀ ≤ Fintype.card V → (∀ e ∈ E, ¬ e.IsDiag) →
      IsKDeltaPartition k (δ + ε) P E Finset.univ →
      ∃ H : Finset (Sym2 V), H ⊆ E ∧
        TriDecomp (E \ H) ∧
        (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (Fintype.card V : ℝ)) ∧
        (∀ W ∈ P, ∀ v : V,
          (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ))

/-- The conclusion of BKLO Lemma 10.6 (`r = 2`) at fixed parameters `(δ, γ, ε, k)`, on a vertex
*set*.  This is the body of `BKLO.Lemma106K3Set`. -/
def Lemma106K3AtSet (δ γ ε : ℝ) (k : ℕ) : Prop :=
  ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (P : Finset (Finset V)),
      n₀ ≤ S.card → (∀ e ∈ E, ¬ e.IsDiag) → E ⊆ cliqueEdges S →
      IsKDeltaPartition k (δ + ε) P E S →
      ∃ H : Finset (Sym2 V), H ⊆ E ∧
        TriDecomp (E \ H) ∧
        (∀ v : V, (edeg (crossParts H P) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        (∀ W ∈ P, ∀ v : V,
          (edeg (edgesIn E W \ edgesIn H W) v : ℝ) ≤ 2 * γ * (W.card : ℝ))

/-- **The transport.**  Lemma 10.6 on a `Fintype` vertex type gives Lemma 10.6 on a vertex set:
instantiate the vertex type at the subtype `↥S` and push the conclusion back along `↥S ↪ V`. -/
theorem lemma106K3AtSet_of_fin {δ γ ε : ℝ} {k : ℕ} (hγ : 0 ≤ γ) (h : Lemma106K3AtFin δ γ ε k) :
    Lemma106K3AtSet δ γ ε k := by
  classical
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨n₀, ?_⟩
  intro V _ E S P hcard hloop hES hpart
  have hpush : pushEdges S (subEdges S E) = E := pushEdges_subEdges hES
  have hPS : ∀ W ∈ P, W ⊆ S := fun W hW => hpart.1.subset_of_mem hW
  have hcardV : Fintype.card {x // x ∈ S} = S.card := card_coe_eq S
  obtain ⟨H', hH'sub, hdec, hcross, hinside⟩ :=
    hn₀ (V := {x // x ∈ S}) (subEdges S E) (subParts S P) (by rw [hcardV]; exact hcard)
      (loopless_subEdges hloop) (isKDeltaPartition_subParts hpart)
  have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  refine ⟨pushEdges S H', ?_, ?_, ?_, ?_⟩
  · rw [← hpush]; exact pushEdges_mono hH'sub
  · have : E \ pushEdges S H' = pushEdges S (subEdges S E \ H') := by
      rw [pushEdges_sdiff, hpush]
    rw [this]
    exact hdec.push
  · intro v
    rw [crossParts_pushEdges _ P]
    by_cases hv : v ∈ S
    · have : v = ((⟨v, hv⟩ : {x // x ∈ S}) : V) := rfl
      rw [this, edeg_pushEdges]
      have := hcross ⟨v, hv⟩
      rwa [hcardV] at this
    · rw [edeg_pushEdges_eq_zero _ hv]
      simpa using mul_nonneg hγ hSnn
  · intro W hW v
    have hWS : W ⊆ S := hPS W hW
    have hWcard : (subPart S W).card = W.card := card_subPart hWS
    have hE : edgesIn E W = pushEdges S (edgesIn (subEdges S E) (subPart S W)) := by
      conv_lhs => rw [← hpush]
      rw [edgesIn_pushEdges _ W]
    have hH : edgesIn (pushEdges S H') W = pushEdges S (edgesIn H' (subPart S W)) :=
      edgesIn_pushEdges _ W
    rw [hE, hH, ← pushEdges_sdiff]
    have hWnn : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
    by_cases hv : v ∈ S
    · have hveq : v = ((⟨v, hv⟩ : {x // x ∈ S}) : V) := rfl
      rw [hveq, edeg_pushEdges]
      have := hinside (subPart S W) (mem_subParts hW) ⟨v, hv⟩
      rwa [hWcard] at this
    · rw [edeg_pushEdges_eq_zero _ hv]
      have : (0 : ℝ) ≤ 2 * γ * (W.card : ℝ) := by positivity
      simpa using this

/-- **BKLO Lemma 10.6 for `r = 2` on a vertex set**, from the approximate-decomposition threshold
`δ_F^η` and BKLO Lemma 10.3.

Compared with `BKLO.Lemma106K3Res` (the `Fintype` form) two things change, and both are handled
here: the vertex set (by `BKLO.lemma106K3AtSet_of_fin`) and the hierarchy, which is only
`1/k ≤ ε` and not `1/k ≤ ε/8` (by
`BKLO.transformStepK3At_of_approxTriDecomp_weak`). -/
theorem lemma106K3Set_of_approxTriDecomp {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (happ : ApproxTriDecompMinDeg δ) (h103 : Lemma103K3) : Lemma106K3Set δ := by
  intro γ ε k hγ hγε hε hε1 hk hkε
  have htr : TransformStepK3At δ ε k :=
    transformStepK3At_of_approxTriDecomp_weak hε hε1 hk hkε happ
  have hfin : Lemma106K3AtFin δ γ ε k :=
    lemma106K3_core hδ (lemma104K3_of_lemma103K3 h103) hγ hγε hε hε1 hk htr
  exact lemma106K3AtSet_of_fin hγ.le hfin

/-- **BKLO Lemma 10.6 for `r = 2` on a vertex set, from the single input `δ_F^η`.**  Lemma 10.3 is
discharged by the proved `BKLO.lemma103K3_holds`. -/
theorem lemma106K3Set_of_input {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ)
    (happ : ApproxTriDecompMinDeg δ) : Lemma106K3Set δ :=
  lemma106K3Set_of_approxTriDecomp hδ happ lemma103K3_holds

/-- **BKLO Lemma 10.6 for `r = 2` (the `Fintype` form, `1/k ≤ ε/8`), from the single input
`δ_F^η`**: `BKLO.lemma106K3Res_of_inputs` with Lemma 10.3 discharged by
`BKLO.lemma103K3_holds`. -/
theorem lemma106K3Res_of_input {δ : ℝ} (hδ : (2 : ℝ) / 3 ≤ δ) (hδ1 : δ ≤ 1)
    (happ : ApproxTriDecompMinDeg δ) : Lemma106K3Res δ :=
  lemma106K3Res_of_inputs hδ hδ1 happ lemma103K3_holds

/-- **BKLO Lemma 10.6 for `r = 2` on a vertex set, in the dense regime `δ = 9/10`**, from the
single input `δ_F^η`.  This is the hypothesis `h106` of `BKLO.lemma1012K3'_of_inputs`. -/
theorem lemma106K3Set_dense (happ : ApproxTriDecompMinDeg (9 / 10)) : Lemma106K3Set (9 / 10) :=
  lemma106K3Set_of_input (by norm_num) happ

/-- **BKLO Lemma 10.12 for `r = 2` (repaired), in the dense regime, from three inputs.**
`BKLO.lemma1012K3'_of_inputs` takes four: Lemma 7.2, Lemma 9.3, Lemma 10.10 and Lemma 10.6 on a
vertex set.  The last one is now discharged from the approximate-decomposition threshold `δ_F^η`,
so only the three genuinely external §7/§9/§10.2 inputs remain. -/
theorem lemma1012K3'_of_three_inputs (happ : ApproxTriDecompMinDeg (9 / 10))
    (h72 : Lemma72K3) (h93 : Lemma93K3) (h1010 : Lemma1010K3) : Lemma1012K3' (9 / 10) :=
  lemma1012K3'_of_inputs le_rfl h72 h93 h1010 (lemma106K3Set_dense happ)

end BKLO
