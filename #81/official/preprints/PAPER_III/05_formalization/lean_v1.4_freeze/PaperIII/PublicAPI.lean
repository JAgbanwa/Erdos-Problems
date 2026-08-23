/-
# Paper III — public API for downstream consumers (e.g. Paper V)

Derived interfaces around `Theorem_1_1`, kept OUT of `Theorem_1_1_Final.lean` so the final theorem's
import tree stays lean. No proof of `Theorem_1_1` is modified here; this file only exports corollaries
and re-exports existing public lemmas. There is deliberately **no** dependency on Paper V.

Contents (request AV4471, items B/C/D; item A `ofPartition` is delivered separately):
* `SplitGraph.Phi_nonneg` — `0 ≤ Φ(G)`.
* `Theorem_1_1_nat`, `Theorem_1_1_rat`, `Theorem_1_1_int6` — Archimedean corollaries of `Theorem_1_1`
  with a dominating natural / rational constant (the `int6` form is division-free).
* Re-exports of the inductive-line API (`Phi_le_erase_independent`,
  `global_bound_from_eventual_high_degree`, `Byproduct_localization_from_eventual_high_degree`,
  `Byproduct_nu3_achieved`). These do NOT close the MOQ ledger / `MREC-LIT`.

Every theorem closes with `#print axioms … = [propext, Classical.choice, Quot.sound]`.
-/
import PaperIII.Theorem_1_1_Final
import PaperIII.CanonicalTrianglePacking
import PaperIII.PaperImprovements
import PaperIII.OfPartition

namespace PaperIII

open SimpleGraph

/-! ## C. Non-negativity of `Φ` -/

/-- `Φ(G) ≥ 0` for every split graph, from `cp ≤ Φ` and `cp ≥ 0`. -/
theorem SplitGraph.Phi_nonneg (G : SplitGraph) : 0 ≤ G.Phi :=
  le_trans (Int.natCast_nonneg _) (cp_le_Phi G)

/-! ## B. Corollaries with a dominating natural / rational constant -/

/-- **Theorem 1.1, natural-constant form.** There is a *natural* `C` with
`Φ(G) ≤ n²/6 + C·n` for every split graph. Archimedean corollary: take `C = ⌈C_ℝ⌉₊`. -/
theorem Theorem_1_1_nat :
    ∃ C : ℕ, ∀ G : SplitGraph,
      ((G.Phi : ℤ) : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + (C : ℝ) * (G.n : ℝ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1
  refine ⟨⌈C⌉₊, fun G => ?_⟩
  have hn : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
  have hCle : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hmul : C * (G.n : ℝ) ≤ (⌈C⌉₊ : ℝ) * (G.n : ℝ) :=
    mul_le_mul_of_nonneg_right hCle hn
  linarith [hC G, hmul]

/-- **Theorem 1.1, rational-constant form.** Matches Paper V's `PaperIII_split_leaves`. -/
theorem Theorem_1_1_rat :
    ∃ C : ℚ, ∀ G : SplitGraph,
      (G.Phi : ℚ) ≤ (G.n : ℚ) ^ 2 / 6 + C * (G.n : ℚ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1_nat
  refine ⟨(C : ℚ), fun G => ?_⟩
  have h := hC G
  have hr : ((G.Phi : ℚ) : ℝ)
      ≤ (((G.n : ℚ) ^ 2 / 6 + (C : ℚ) * (G.n : ℚ)) : ℝ) := by
    push_cast at h ⊢
    linarith [h]
  exact_mod_cast hr

/-- **Theorem 1.1, integer division-free form.** `6·Φ(G) ≤ n² + 6·C·n` with `C : ℕ`; the most
cast-robust statement for downstream integer arithmetic. -/
theorem Theorem_1_1_int6 :
    ∃ C : ℕ, ∀ G : SplitGraph,
      6 * G.Phi ≤ (G.n : ℤ) ^ 2 + 6 * (C : ℤ) * (G.n : ℤ) := by
  obtain ⟨C, hC⟩ := Theorem_1_1_nat
  refine ⟨C, fun G => ?_⟩
  have h := hC G
  have hr : ((6 * G.Phi : ℤ) : ℝ)
      ≤ (((G.n : ℤ) ^ 2 + 6 * (C : ℤ) * (G.n : ℤ)) : ℝ) := by
    push_cast at h ⊢
    nlinarith [h]
  exact_mod_cast hr

/-! ## A. Split partition entry point (unconditional) -/

/-- **Theorem 1.1 for an externally-presented split graph.** Any finite `SimpleGraph V` carrying a
clique/independent partition `(K, I)` satisfies `Φ(H) ≤ |V|²/6 + C·|V|`, where `Φ(H) = |E| − 2ν₃(H)`.
This discharges the `hmain` hypothesis of `Theorem_1_1_of_splitPartition` with the real `Theorem_1_1`,
giving Paper V a literal-graph entry point (closes the `P3LR-LIT` gap) with no Paper V dependency. -/
theorem Theorem_1_1_of_splitPartition_uncond :
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (H : SimpleGraph V) [DecidableRel H.Adj] (K I : Finset V),
      K ∪ I = Finset.univ → Disjoint K I → H.IsClique (K : Set V) → H.IsIndepSet (I : Set V) →
      (((H.edgeFinset.card : ℤ) - 2 * (nu3 H : ℤ) : ℤ) : ℝ)
        ≤ (Fintype.card V : ℝ) ^ 2 / 6 + C * (Fintype.card V : ℝ) :=
  Theorem_1_1_of_splitPartition Theorem_1_1

/-! ## D. Re-exports for the inductive line (do NOT close MOQ / `MREC-LIT`) -/

/-- Erasing an independent vertex does not increase `Φ` (inductive step ingredient). -/
alias PublicAPI_Phi_le_erase_independent := Phi_le_erase_independent

/-- The global bound assembled from the eventual high-degree regime. -/
alias PublicAPI_global_bound_from_eventual_high_degree := global_bound_from_eventual_high_degree

/-- Localization byproduct from the eventual high-degree regime. -/
alias PublicAPI_localization_from_eventual_high_degree := Byproduct_localization_from_eventual_high_degree

/-- A concrete optimal triangle packing is achieved (`ν₃` byproduct). -/
alias PublicAPI_nu3_achieved := Byproduct_nu3_achieved

/-! ## Packaged optimality statement -/

/-- **Order-optimal with optimal leading constant (packaged).**  The clique-partition bound for split
graphs is `cp ≤ n²/6 + C·n`, and the coefficient `1/6` of the quadratic term is best possible:

1. (upper bound) there is an absolute `C` with `cp(G) ≤ n²/6 + C·n` for every split graph;
2. (forced) any such uniform `C` must satisfy `C ≥ 1/6`;
3. (attained) the complete-split family realizes `cp = n²/6 + n/6` exactly.

So `n²/6` is the sharp leading term. Assembled from `Corollary_1_2`,
`Byproduct_leading_constant_forced`, and `Byproduct_completeSplit_cp_sharp`. -/
theorem Corollary_1_2_sharp :
    (∃ C : ℝ, ∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ)) ∧
    (∀ C : ℝ, (∀ G : SplitGraph, (G.cp : ℝ) ≤ (G.n : ℝ) ^ 2 / 6 + C * (G.n : ℝ)) →
      (1 : ℝ) / 6 ≤ C) ∧
    (∀ p : ℕ, ((completeSplit p).cp : ℝ)
      = ((completeSplit p).n : ℝ) ^ 2 / 6 + ((completeSplit p).n : ℝ) / 6) :=
  ⟨Corollary_1_2, Byproduct_leading_constant_forced, Byproduct_completeSplit_cp_sharp⟩

end PaperIII
