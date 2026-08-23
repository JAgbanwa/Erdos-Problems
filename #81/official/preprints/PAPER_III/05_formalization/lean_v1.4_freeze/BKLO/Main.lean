/-
# BKLO §11 — the assembly (Theorem 1.3 / 6.3 for `F = K₃`).

This file assembles the engine into the main theorem:

  every large triangle-divisible graph with `δ(G) ≥ (9/10 + ε)n` is triangle-decomposable.

The proof is the standard *absorb-then-cover* pattern, and it uses exactly the following pieces.

* **§8.1 (proved, `BKLO.AbsorberExists`)** — every loopless triangle-divisible edge set over `ℕ`
  has an absorber.  The engine needs the version with a *degeneracy bound*
  (`BKLO.SparseAbsorberExistence`), which is what makes the absorbers placeable.
* **§5 (proved, `BKLO.exists_embedding`)** — a `9`-degenerate gadget embeds into a host whose
  `9`-sets have large common neighbourhoods; `δ(G) ≥ (9/10 + ε)n` supplies exactly this.
  Iterated over the finite family of abstract absorbers this gives `BKLO.exists_placement`.
* **§10 (interface, `BKLO.NearOptimalDecomp`)** — the near-optimal decomposition obtained from the
  three external inputs by iterative absorption.

Assembly.  Fix `ε > 0`, let `C` be the bound of §10, and build, once and for all, an absorber
`Abs H` for **every** divisible graph `H` on the root set `{0, …, C-1}`.  Given `G`, §10 produces a
set `U` of at most `C` vertices; §5 places all the `Abs H` inside `G` on private sets of fresh
vertices, giving the reserved structure `A`.  Since `A` is triangle-decomposable it is divisible, so
`G - A` is divisible, and §10 covers `G - A` by edge-disjoint triangles up to a remainder `L` inside
`U`.  That remainder is divisible and is the copy of exactly one of the abstract graphs `H₀`, so
`A ∪ L = (B H₀ ∪ L) ⊎ ⋃_{H ≠ H₀} B H` is triangle-decomposable, and `E(G)` splits into the covered
part and `A ∪ L`.
-/
import BKLO.Placement
import BKLO.NearOptimal
import BKLO.Refutations
import BKLO.AbsorberExists
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Real.StarOrdered

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### §8 — the absorber existence, in the form the skeleton stated it

The skeleton's `AbsorberExistence` drops the divisibility hypothesis and is therefore false
(`not_absorberExistence`); the corrected statement over `ℕ` is `BKLO.absorber_of_triDivisible`,
proved in `BKLO/AbsorberExists.lean`. -/

/-- **Absorber existence (Lemma 8.8), as stated in the original skeleton.**  It elides the
`K₃`-divisibility hypothesis and is refuted by `not_absorberExistence`. -/
def AbsorberExistence : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : Finset (Sym2 V)),
    (∃ A : Finset (Sym2 V), IsAbsorber A H)

/-- **The interface predicate `AbsorberExistence` is false.**  As stated it drops the
`K₃`-divisibility hypothesis, and divisibility is genuinely necessary: a single edge on two
vertices has no absorber, since on two vertices the only triangle-decomposable edge set is the
empty one. -/
theorem not_absorberExistence : ¬ AbsorberExistence := fun h =>
  let ⟨A, hA⟩ := h (V := Fin 2) ({s(0, 1)} : Finset (Sym2 (Fin 2)))
  not_isAbsorber_single_edge A hA

/-! ### §11 — the assembly -/

set_option maxHeartbeats 400000 in
/-- **Main theorem (BKLO Theorem 1.3 / 6.3 for `F = K₃`; the AX2 half of Erdős #81), §11.**

From the conclusion of §10 alone: for every `ε > 0` every sufficiently large triangle-divisible
graph with `δ(G) ≥ (9/10 + ε)|V|` has a triangle decomposition.

This is the §11 assembly proper.  It used to be stated with the three classical inputs and
`NearOptimalDecomp` in front (`BKLO.triangle_decomposition_of_inputs`, which is kept below, with
its statement unchanged, as an immediate corollary); those inputs were only ever fed to the §10
interface, so the assembly is stated here from `NearOptimalConclusion` directly — which is what a
route proving §10 by other means (e.g. `BKLO/CoverDownEngineR3.lean`) supplies.
`NearOptimalConclusion` is *proved* to be satisfiable in `BKLO/NearOptimalSat.lean`
(`nearOptimalConclusion_of_target`), so the theorem below is not vacuous.
The absorbers themselves are *not* assumed: they are built over `ℕ` by
`BKLO.sparseAbsorberExistence_nine` (§8.1, proved, with the degeneracy bound `9`) and placed inside
`G` by the §5 embedding (`BKLO.exists_placement`). -/
theorem triangle_decomposition_of_nearOptimal (hNO : NearOptimalConclusion) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G := by
  classical
  intro ε hε
  obtain ⟨C, hC⟩ := hNO ε hε
  -- The abstract absorbers, chosen once and for all, for every divisible graph on `{0,…,C-1}`.
  set Hs : Finset (Finset (Sym2 ℕ)) :=
    (cliqueEdges (Finset.range C)).powerset.filter (fun H => TriDivisible H) with hHsdef
  have hHsmem : ∀ H ∈ Hs, H ⊆ cliqueEdges (Finset.range C) ∧ TriDivisible H := by
    intro H hH
    rw [hHsdef, Finset.mem_filter, Finset.mem_powerset] at hH
    exact hH
  have hHsupp : ∀ H ∈ Hs, ∀ v ∈ supp H, v < C := by
    intro H hH v hv
    obtain ⟨e, he, hve⟩ := mem_supp.1 hv
    have := (mem_cliqueEdges.1 ((hHsmem H hH).1 he)).1 v hve
    simpa using this
  have hex : ∀ H ∈ Hs, ∃ A, SparseAbsorber 9 C H A := by
    intro H hH
    refine sparseAbsorberExistence_nine C H (fun e he => (mem_cliqueEdges.1 ((hHsmem H hH).1 he)).2)
      (fun v hv => hHsupp H hH v hv) (hHsmem H hH).2
  choose! Abs hAbs using hex
  set Ktot : ℕ := ∑ H ∈ Hs, (Abs H).card with hKdef
  set Mtot : ℕ := ∑ H ∈ Hs, (supp (Abs H)).card with hMdef
  obtain ⟨n₁, hn₁⟩ := hC Ktot
  refine ⟨max n₁ (10 * (C + 2 * Mtot + 1)), ?_⟩
  intro V _ _ G _ hn hdivG hδ
  have hn1 : n₁ ≤ Fintype.card V := le_trans (le_max_left _ _) hn
  have hn2 : 10 * (C + 2 * Mtot + 1) ≤ Fintype.card V := le_trans (le_max_right _ _) hn
  -- the minimum-degree hypothesis in integer form
  have hnd : 9 * Fintype.card V ≤ 10 * G.minDegree := by
    have h0 : (0:ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
    have h1 : (9:ℝ) * (Fintype.card V : ℝ) ≤ 10 * (G.minDegree : ℝ) := by nlinarith
    exact_mod_cast h1
  -- large common neighbourhoods
  have hroom : ∀ S : Finset V, S.card ≤ 9 → C + 2 * Mtot < (commonNbrs G S).card := by
    intro S hS
    have h1 := card_commonNbrs_ge G S
    have h2 : S.card * (Fintype.card V - G.minDegree) ≤ 9 * (Fintype.card V - G.minDegree) :=
      Nat.mul_le_mul_right _ hS
    omega
  -- §10 gives the bounded set `U`
  obtain ⟨U, hUcard, hU⟩ := hn₁ G hn1 hδ
  -- extend `U` to a set `U'` of exactly `C` vertices and enumerate it
  obtain ⟨U', hUU', hU'card⟩ : ∃ t : Finset V, U ⊆ t ∧ t.card = C :=
    Finset.exists_superset_card_eq hUcard (by omega)
  obtain ⟨x₀⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  set l : List V := U'.toList with hldef
  have hlen : l.length = C := by rw [hldef, Finset.length_toList, hU'card]
  have hlnd : l.Nodup := U'.nodup_toList
  set e₀ : ℕ → V := fun i => l.getD i x₀ with he₀def
  have he₀get : ∀ i (h : i < C), e₀ i = l[i]'(by omega) := by
    intro i h
    rw [he₀def]
    exact List.getD_eq_getElem l x₀ (by omega)
  have hinj : ∀ u < C, ∀ v < C, e₀ u = e₀ v → u = v := by
    intro u hu v hv huv
    rw [he₀get u hu, he₀get v hv] at huv
    exact hlnd.getElem_inj_iff.1 huv
  have himg : (Finset.range C).image e₀ = U' := by
    ext w
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [he₀get i hi, ← Finset.mem_toList, ← hldef]
      exact List.getElem_mem _
    · intro hw
      have : w ∈ l := by rw [hldef, Finset.mem_toList]; exact hw
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem this
      exact ⟨i, by omega, by rw [he₀get i (by omega)]⟩
  -- §5 places all the abstract absorbers
  obtain ⟨B, W, hP⟩ :=
    exists_placement G C e₀ hinj U' himg.symm Hs Abs hHsupp hAbs (fun S hS => hroom S hS)
  set A : Finset (Sym2 V) := Hs.biUnion B with hAdef
  -- basic properties of the absorbing structure `A`
  have hBdisj : ∀ H₁ ∈ Hs, ∀ H₂ ∈ Hs, H₁ ≠ H₂ → Disjoint (B H₁) (B H₂) := by
    intro H₁ h₁ H₂ h₂ hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    obtain ⟨v, hv, hvW⟩ := hP.edge_meets H₁ h₁ g hg1
    rcases hP.edge_in H₂ h₂ g hg2 v hv with h | h
    · exact (Finset.disjoint_left.1 (hP.fresh_disj H₁ h₁) hvW) h
    · exact (Finset.disjoint_left.1 (hP.pairwise H₁ h₁ H₂ h₂ hne) hvW) h
  have hAsub : A ⊆ G.edgeFinset := by
    rw [hAdef]
    exact Finset.biUnion_subset.2 (fun H hH => hP.sub H hH)
  have hAcard : A.card ≤ Ktot := by
    refine le_trans (Finset.card_biUnion_le) ?_
    exact Finset.sum_le_sum (fun H hH => hP.card_le H hH)
  have hAU : Disjoint A (cliqueEdges U) := by
    rw [Finset.disjoint_left]
    intro g hg hgU
    obtain ⟨H, hH, hgH⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨v, hv, hvW⟩ := hP.edge_meets H hH g hgH
    have : v ∈ U' := hUU' ((mem_cliqueEdgesV.1 hgU).1 v hv)
    exact (Finset.disjoint_left.1 (hP.fresh_disj H hH) hvW) this
  have hAdec : TriDecomp A :=
    TriDecomp.biUnion (fun H hH => (hP.absorber H hH).2.1) hBdisj
  have hAdiv : TriDivisible A := hAdec.triDivisible
  have hGdiv : TriDivisible G.edgeFinset := triDivisible_edgeFinset G hdivG.1 hdivG.2
  have hGAdiv : TriDivisible (G.edgeFinset \ A) := TriDivisible.sdiff hAsub hGdiv hAdiv
  -- §10 covers `G - A` down to a remainder inside `U`
  obtain ⟨Pt, hPt3, hPtsub, hPtdisj, hPtleft⟩ := hU A hAsub hAcard hAU hGAdiv
  set L : Finset (Sym2 V) := (G.edgeFinset \ A) \ famEdges Pt with hLdef
  have hPtfam : famEdges Pt ⊆ G.edgeFinset \ A := by
    refine Finset.biUnion_subset.2 (fun t ht => hPtsub t ht)
  have hPtdec : TriDecomp (famEdges Pt) := ⟨Pt, hPt3, hPtdisj, rfl⟩
  have hLdiv : TriDivisible L := TriDivisible.sdiff hPtfam hGAdiv hPtdec.triDivisible
  have hLU : L ⊆ cliqueEdges U := hPtleft
  -- the remainder is the copy of one of the abstract graphs
  set H₀ : Finset (Sym2 ℕ) :=
    (cliqueEdges (Finset.range C)).filter (fun h => Sym2.map e₀ h ∈ L) with hH₀def
  have hH₀sub : H₀ ⊆ cliqueEdges (Finset.range C) := Finset.filter_subset _ _
  have hH₀supp : ∀ v ∈ supp H₀, v < C := by
    intro v hv
    obtain ⟨e, he, hve⟩ := mem_supp.1 hv
    have := (mem_cliqueEdges.1 (hH₀sub he)).1 v hve
    simpa using this
  have hH₀img : H₀.image (Sym2.map e₀) = L := by
    ext g
    constructor
    · intro hg
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hg
      exact (Finset.mem_filter.1 hh).2
    · intro hg
      have hgU' : ∀ v ∈ g, v ∈ U' := fun v hv => hUU' ((mem_cliqueEdgesV.1 (hLU hg)).1 v hv)
      have hgnd : ¬ g.IsDiag := (mem_cliqueEdgesV.1 (hLU hg)).2
      induction g using Sym2.ind with
      | _ p q =>
        have hp : p ∈ U' := hgU' p (by simp)
        have hq : q ∈ U' := hgU' q (by simp)
        rw [← himg] at hp hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
        rw [Finset.mem_range] at hi hj
        refine Finset.mem_image.2 ⟨s(i, j), Finset.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
        · refine mem_cliqueEdges.2 ⟨?_, ?_⟩
          · rintro z hz
            simp only [Sym2.mem_iff] at hz
            rcases hz with rfl | rfl <;> simp [Finset.mem_range, hi, hj]
          · simp only [Sym2.isDiag_iff_proj_eq]
            intro hij
            exact hgnd (by simp [hij])
        · simpa using hg
  have hH₀div : TriDivisible H₀ := by
    refine triDivisible_of_image (f := e₀) (fun u hu v hv huv =>
      hinj u (hH₀supp u hu) v (hH₀supp v hv) huv) ?_
    rw [hH₀img]
    exact hLdiv
  have hH₀mem : H₀ ∈ Hs := by
    rw [hHsdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hH₀sub, hH₀div⟩
  -- the absorber for `H₀` swallows the remainder
  have hAbsL : IsAbsorber (B H₀) L := by
    have := hP.absorber H₀ hH₀mem
    rwa [hH₀img] at this
  -- `A ∪ L` is triangle-decomposable
  have hsplitA : A = B H₀ ∪ (Hs.erase H₀).biUnion B := by
    rw [hAdef, ← Finset.biUnion_insert, Finset.insert_erase hH₀mem]
  have hrestdec : TriDecomp ((Hs.erase H₀).biUnion B) :=
    TriDecomp.biUnion (fun H hH => (hP.absorber H (Finset.mem_of_mem_erase hH)).2.1)
      (fun H₁ h₁ H₂ h₂ hne => hBdisj H₁ (Finset.mem_of_mem_erase h₁) H₂
        (Finset.mem_of_mem_erase h₂) hne)
  have hLrest : Disjoint L ((Hs.erase H₀).biUnion B) := by
    rw [Finset.disjoint_left]
    intro g hgL hgB
    obtain ⟨H, hH, hgH⟩ := Finset.mem_biUnion.1 hgB
    obtain ⟨v, hv, hvW⟩ := hP.edge_meets H (Finset.mem_of_mem_erase hH) g hgH
    have : v ∈ U' := hUU' ((mem_cliqueEdgesV.1 (hLU hgL)).1 v hv)
    exact (Finset.disjoint_left.1 (hP.fresh_disj H (Finset.mem_of_mem_erase hH)) hvW) this
  have hALdec : TriDecomp (A ∪ L) := by
    have hdisj : Disjoint (B H₀ ∪ L) ((Hs.erase H₀).biUnion B) := by
      refine Finset.disjoint_union_left.2 ⟨?_, hLrest⟩
      rw [Finset.disjoint_right]
      intro g hg hg0
      obtain ⟨H, hH, hgH⟩ := Finset.mem_biUnion.1 hg
      exact (Finset.disjoint_left.1 (hBdisj H₀ hH₀mem H (Finset.mem_of_mem_erase hH)
        (fun h => (Finset.mem_erase.1 hH).1 h.symm)) hg0) hgH
    have := TriDecomp.union hdisj hAbsL.2.2 hrestdec
    have heq : A ∪ L = B H₀ ∪ L ∪ (Hs.erase H₀).biUnion B := by
      rw [hsplitA, Finset.union_right_comm]
    rw [heq]
    exact this
  -- assemble
  have hsplit : G.edgeFinset = famEdges Pt ∪ (A ∪ L) := by
    ext x
    simp only [Finset.mem_union, hLdef, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inr (Or.inl hxA)
      · by_cases hxP : x ∈ famEdges Pt
        · exact Or.inl hxP
        · exact Or.inr (Or.inr ⟨⟨hx, hxA⟩, hxP⟩)
    · rintro (h | h | ⟨⟨h, -⟩, -⟩)
      · exact (Finset.mem_sdiff.1 (hPtfam h)).1
      · exact hAsub h
      · exact h
  have hfin : TriDecomp G.edgeFinset := by
    rw [hsplit]
    refine TriDecomp.union ?_ hPtdec hALdec
    refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro g hg hgA
      exact (Finset.mem_sdiff.1 (hPtfam hg)).2 hgA
    · rw [Finset.disjoint_left]
      intro g hg hgL
      exact (Finset.mem_sdiff.1 hgL).2 hg
  exact triangleDecomposable_of_triDecomp G hfin

/-- **Main theorem, from the three external inputs and the §10 interface.**  The original form of
`BKLO.triangle_decomposition_of_nearOptimal`: the three classical inputs — Dross's fractional
threshold, the Haxell–Rödl nibble, and Dirac's theorem — are used only to run the §10 interface
`NearOptimalDecomp`. -/
theorem triangle_decomposition_of_inputs
    (hDross : FracTriangleThreshold) (hHR : FracToApprox) (hDirac : PerfectMatchingDirac)
    (hNOD : NearOptimalDecomp) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_nearOptimal (hNOD hDross hHR hDirac)

end BKLO
