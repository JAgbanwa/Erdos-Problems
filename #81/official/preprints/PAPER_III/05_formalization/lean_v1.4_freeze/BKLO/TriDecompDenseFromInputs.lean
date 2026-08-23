/-
# The residual `TriDecompDense`, placed inside the project's existing input structure.

`BKLO/CoverDownFromDecomp.lean` reduces the repaired §10 cover-down input `CoverDownK3Div` to
`TriDecompDense`: the triangle decomposition theorem for dense triangle-divisible graphs, in the
edge-set language of the engine.  This file shows that `TriDecompDense` is exactly what the rest of
the project already produces: it follows from the three standard external inputs of §4 together
with the §10 interface `NearOptimalDecomp`, via `BKLO.triangle_decomposition_of_inputs` and the
`BKLO/SetGraph.lean` dictionary.

So the residual left by `BKLO/CoverDownFromDecomp.lean` is not an unrelated new assumption: it is
the main theorem of the project, in edge-set form.  Together the two files say that the (repaired)
cover-down input and the theorem it is used to prove are of the same strength — which is why it
cannot be discharged from the nibble and Dirac alone.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownFromDecomp
import BKLO.Main

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-- A triangle decomposition of `setGraph S E` is an edge-disjoint triangle family covering `E`. -/
theorem exists_triFamily_of_triangleDecomposable {S : Finset V} {E : Finset (Sym2 V)}
    (hE : E ⊆ cliqueEdges S) (h : TriangleDecomposable (setGraph S E)) :
    ∃ P : Finset (Finset V), TriFamilyIn E P ∧ E ⊆ famEdges P := by
  classical
  obtain ⟨parts, hcl, huniq⟩ := h
  have hdisj : ∀ t ∈ parts, ∀ t' ∈ parts, t ≠ t' →
      Disjoint (cliqueEdges t) (cliqueEdges t') := by
    intro t ht t' ht' hne
    refine Finset.disjoint_left.2 fun e he he' => hne ?_
    have heE : e ∈ (setGraph S E).edgeFinset :=
      cliqueEdges_subset_edgeFinset (hcl t ht).1 he
    obtain ⟨t₀, _, hu⟩ := huniq e heE
    rw [hu t ⟨ht, he⟩, hu t' ⟨ht', he'⟩]
  refine ⟨parts.image (fun t => t.image Subtype.val), triFamilyIn_image_val hE hcl hdisj, ?_⟩
  have hcover : (setGraph S E).edgeFinset ⊆ parts.biUnion cliqueEdges := by
    intro e he
    obtain ⟨t, ⟨ht, het⟩, _⟩ := huniq e he
    exact Finset.mem_biUnion.2 ⟨t, ht, het⟩
  rw [famEdges_image_val, ← image_edgeFinset_setGraph hE]
  exact Finset.image_subset_image hcover

/-- **The residual of `BKLO/CoverDownFromDecomp.lean` is the project's own main theorem.**
`TriDecompDense` follows from the conclusion of §10.  (Stated from `NearOptimalConclusion`; the
form with the three §4 inputs and `NearOptimalDecomp` in front is the corollary
`BKLO.triDecompDense_of_inputs` below.) -/
theorem triDecompDense_of_nearOptimal (hNO : NearOptimalConclusion) : TriDecompDense := by
  classical
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := triangle_decomposition_of_nearOptimal hNO ε hε
  refine ⟨max n₀ 1, ?_⟩
  intro V _ S E hcard hE hdiv hdeg
  have hSpos : 0 < S.card := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right n₀ 1) hcard)
  have hne : Nonempty {x // x ∈ S} := by
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hSpos
    exact ⟨⟨v, hv⟩⟩
  have hcardS : Fintype.card {x // x ∈ S} = S.card := card_coe_eq S
  -- the degree bound, as a natural number
  set k : ℕ := ⌈(9 / 10 + ε) * (S.card : ℝ)⌉₊ with hk
  have hkdeg : ∀ a : {x // x ∈ S}, k ≤ (setGraph S E).degree a := by
    intro a
    rw [degree_setGraph hE]
    exact Nat.ceil_le.2 (hdeg (a : V) a.2)
  have hmin : (9 / 10 + ε) * (Fintype.card {x // x ∈ S} : ℝ)
      ≤ ((setGraph S E).minDegree : ℝ) := by
    have h1 : k ≤ (setGraph S E).minDegree :=
      SimpleGraph.le_minDegree_of_forall_le_degree _ k hkdeg
    have h2 : (9 / 10 + ε) * (S.card : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
    have h3 : ((k : ℕ) : ℝ) ≤ ((setGraph S E).minDegree : ℝ) := by exact_mod_cast h1
    rw [hcardS]
    linarith
  have hdivG : 3 ∣ (setGraph S E).edgeFinset.card ∧ ∀ a, Even ((setGraph S E).degree a) := by
    refine ⟨?_, fun a => ?_⟩
    · rw [card_edgeFinset_setGraph hE]; exact hdiv.2
    · rw [degree_setGraph hE]; exact hdiv.1 (a : V)
  have hcard' : n₀ ≤ Fintype.card {x // x ∈ S} := by
    rw [hcardS]; exact le_trans (le_max_left n₀ 1) hcard
  exact exists_triFamily_of_triangleDecomposable hE
    (hn₀ (setGraph S E) hcard' hdivG hmin)

/-- **`TriDecompDense` from the three §4 inputs and the §10 interface**, the original form of
`BKLO.triDecompDense_of_nearOptimal`: the inputs are used only to run `NearOptimalDecomp`. -/
theorem triDecompDense_of_inputs (hDross : FracTriangleThreshold) (hHR : FracToApprox)
    (hDirac : PerfectMatchingDirac) (hNOD : NearOptimalDecomp) : TriDecompDense :=
  triDecompDense_of_nearOptimal (hNOD hDross hHR hDirac)

/-- **The repaired cover-down input, from the project's other inputs.**  Combining
`coverDownK3Div_of_triDecompDense` with `triDecompDense_of_inputs`: the repaired §10 cover-down
interface follows from the three §4 inputs together with `NearOptimalDecomp`.  This is a statement
about the strength of the interface, not a discharge of it — `NearOptimalDecomp` is precisely what
the cover-down is used to prove. -/
theorem coverDownK3Div_of_inputs (hDross : FracTriangleThreshold) (hHR : FracToApprox)
    (hDirac : PerfectMatchingDirac) (hNOD : NearOptimalDecomp) : CoverDownK3Div :=
  coverDownK3Div_of_triDecompDense (triDecompDense_of_inputs hDross hHR hDirac hNOD)

end BKLO
