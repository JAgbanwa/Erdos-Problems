/-
# BKLO §11 for `F = K₃`, dense regime: the cells route

This file carries out BKLO's §11 assembly in the shape the *proved* §10 core of this project
delivers, namely with the remainder spread over the **bottom cells** of a partition sequence and
not over a single bounded core.

The three steps of §11 are:

1. reserve the §8 absorbing structure `A*` for the bottom cells;
2. run the near-optimal decomposition of §10 (here: the proved
   `BKLO.lemma1012K3'_dense_of_lemma107` fed into `BKLO.lemma_10_13_K3'`) on `E \ A*`, which
   decomposes everything except a remainder `H*` confined to the bottom cells;
3. absorb: `A* ∪ H*` is triangle-decomposable, and gluing the two edge-disjoint decompositions
   decomposes `E`.

Steps 2 and 3 are carried out here, `sorry`-free.  Step 1 — the *existence* of the cells absorber
together with the partition sequence it is built on — is isolated as the single interface
`BKLO.CellsAbsorptionK3`.  It is stated exactly in the form §11 consumes: for a large dense
triangle-divisible host `E` it produces simultaneously

* an even-degree reserved set `A ⊆ E`, and
* a partition sequence of `E \ A` with bottom cells of size at least the prescribed `m₀`,

such that `A` absorbs **every** even-degree edge set `H` inside the bottom cells of that partition
sequence (subject to the divisibility condition `3 ∣ |A ∪ H|`, which is necessary and is supplied
automatically at the point of use).

The reason the two halves of `CellsAbsorptionK3` must be bundled is BKLO's own quantifier order:
the absorber has to be reserved *before* the near-optimal decomposition is run, yet its cores are
the bottom cells of the partition sequence, so the two objects have to be produced together.

`BKLO/Section11CellsBuild.lean` builds the cells absorber itself as the edge-disjoint union, over
the cells, of per-cell bounded absorbers, and isolates precisely what is missing for
`CellsAbsorptionK3`.
-/
import BKLO.NearOptimalFaithful
import BKLO.Section1012Hier
import BKLO.Section107Core

open Finset

namespace BKLO

/-- **The §8 / §11 absorbing structure in the cells form (the interface of this route).**

For every `ε > 0`, every number of parts `k` and every prescribed bottom-cell size `m₀` there is a
threshold `n₀` such that every large dense triangle-divisible host `E ⊆ cliqueEdges S` carries

* a reserved even-degree set `A ⊆ E` (the absorber `A*` of BKLO §8), and
* a partition sequence of `E \ A` with bottom cells of size at least `m₀`,

such that `A ∪ H` is triangle-decomposable for **every** even-degree `H` confined to the bottom
cells of that partition sequence with `3 ∣ |A ∪ H|`.

This is BKLO §11's reservation step: the absorber is reserved before the near-optimal
decomposition is run, and it absorbs the remainder that §10 leaves inside the bottom cells. -/
def CellsAbsorptionK3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k m₀ : ℕ, 16 ≤ k → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + 4 * ε) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ (A : Finset (Sym2 V)) (m : ℕ) (L : List (Finset (Finset V)))
        (Pl : Finset (Finset V)),
        A ⊆ E ∧ EvenDegrees A ∧ m₀ ≤ m ∧
        PartSeq k (9 / 10 + ε) (9 / 10) ε m L Pl (E \ A) S ∧
        ∀ H : Finset (Sym2 V), H ⊆ insideParts (E \ A) (restrictParts Pl S) →
          EvenDegrees H → 3 ∣ (A ∪ H).card → TriDecomp (A ∪ H)

/-- **BKLO §11, the cells route.**  From the cells absorber and the repaired §10 Lemma 10.12,
every large dense triangle-divisible edge set decomposes into triangles.

The proof is BKLO's: reserve `A`, run the §10 iteration (`BKLO.lemma_10_13_K3'`) on `E \ A`, and
absorb the remainder, which the §10 output places inside the bottom cells of the partition
sequence. -/
theorem triDecompDense_of_cellsAbsorption (hcells : CellsAbsorptionK3)
    (h12 : Lemma1012K3' (9 / 10)) : TriDecompDense := by
  classical
  intro ε hε
  -- the working parameter: `4e ≤ ε`
  set e : ℝ := min (ε / 4) (1 / 100) with hedef
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have he3 : 4 * e ≤ ε := by
    have : e ≤ ε / 4 := min_le_left _ _
    linarith
  -- the number of parts, satisfying the hierarchy `1/k ≤ e/8`
  set k : ℕ := max 16 (⌈8 / e⌉₊ + 1) with hkdef
  have hk16 : 16 ≤ k := le_max_left _ _
  have hk0 : 0 < k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hk8 : 8 / e ≤ (k : ℝ) := by
    have h1 : 8 / e ≤ (⌈8 / e⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈8 / e⌉₊ + 1 ≤ k := le_max_right _ _
    have h3 : ((⌈8 / e⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) h2
    linarith
  have hkε : 1 / (k : ℝ) ≤ e / 8 := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]
    have := (div_le_iff₀ he).1 hk8
    linarith
  -- the §10 iteration
  obtain ⟨m₀, h10⟩ := lemma_10_13_K3' (δ := 9 / 10) (ε := e) hk0 he hkε h12
  -- the reserved cells absorber, together with the partition sequence of `E \ A`
  obtain ⟨n₁, hres⟩ := hcells e he he1 k m₀ hk16
  refine ⟨max 1 n₁, ?_⟩
  intro V _ S E hcard hES hdiv hdeg
  have hn₁ : n₁ ≤ S.card := le_trans (le_max_right _ _) hcard
  have hScard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hdeg' : ∀ v ∈ S, (9 / 10 + 4 * e) * (S.card : ℝ) ≤ (edeg E v : ℝ) := by
    intro v hv
    have := hdeg v hv
    nlinarith
  obtain ⟨A, m, L, Pl, hAE, hAev, hm₀, hps, habsorb⟩ := hres E S hn₁ hES hdiv hdeg'
  set E₁ : Finset (Sym2 V) := E \ A with hE₁def
  have hE₁E : E₁ ⊆ E := Finset.sdiff_subset
  have hE₁S : E₁ ⊆ cliqueEdges S := hE₁E.trans hES
  have hloop : ∀ f ∈ E₁, ¬ f.IsDiag := fun f hf => (mem_cliqueEdgesV.1 (hE₁S hf)).2
  have hEev : EvenDegrees E := fun v => hdiv.1 v
  have hE₁ev : EvenDegrees E₁ := evenDegrees_sdiff hAE hEev hAev
  -- the §10 output: everything is decomposed except a remainder inside the bottom cells
  obtain ⟨Hstar, hHsub, hHdec⟩ := h10 m hm₀ L Pl E₁ S hloop hE₁S hE₁ev hps
  have hHE₁ : Hstar ⊆ E₁ := hHsub.trans (insideParts_subset _ _)
  have hHev : EvenDegrees Hstar :=
    evenDegrees_of_sdiff hHE₁ hE₁ev (fun v => (hHdec.triDivisible).1 v)
  -- the remainder is edge-disjoint from the absorber
  have hHR : Disjoint A Hstar := by
    refine Finset.disjoint_left.2 fun f hfA hfH => ?_
    exact (Finset.mem_sdiff.1 (hHE₁ hfH)).2 hfA
  have hcards : (E₁ \ Hstar).card + Hstar.card + A.card = E.card := by
    have h1 : (E₁ \ Hstar).card + Hstar.card = E₁.card :=
      Finset.card_sdiff_add_card_eq_card hHE₁
    have h2 : E₁.card + A.card = E.card := Finset.card_sdiff_add_card_eq_card hAE
    omega
  have hdvd : 3 ∣ (A ∪ Hstar).card := by
    have h1 : (A ∪ Hstar).card = A.card + Hstar.card := Finset.card_union_of_disjoint hHR
    obtain ⟨a, ha⟩ := hdiv.2
    obtain ⟨b, hb⟩ := (hHdec.triDivisible).2
    exact ⟨a - b, by omega⟩
  -- absorb
  have hAbs : TriDecomp (A ∪ Hstar) := habsorb Hstar hHsub hHev hdvd
  -- and glue the two edge-disjoint decompositions
  have hsplit : (E₁ \ Hstar) ∪ (A ∪ Hstar) = E := by
    refine Finset.Subset.antisymm (fun f hf => ?_) (fun f hf => ?_)
    · rcases Finset.mem_union.1 hf with h | h
      · exact hE₁E (Finset.mem_sdiff.1 h).1
      · rcases Finset.mem_union.1 h with h' | h'
        · exact hAE h'
        · exact hE₁E (hHE₁ h')
    · by_cases hfA : f ∈ A
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hfA)
      · by_cases hfH : f ∈ Hstar
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ hfH)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hf, hfA⟩, hfH⟩)
  have hdisj2 : Disjoint (E₁ \ Hstar) (A ∪ Hstar) := by
    refine Finset.disjoint_left.2 fun f hf hf' => ?_
    rw [Finset.mem_sdiff, hE₁def, Finset.mem_sdiff] at hf
    rcases Finset.mem_union.1 hf' with h | h
    · exact hf.1.2 h
    · exact hf.2 h
  have hEdec : TriDecomp E := by
    have := TriDecomp.union hdisj2 hHdec hAbs
    rwa [hsplit] at this
  obtain ⟨P, hP3, hPd, hPfam⟩ := hEdec
  refine ⟨P, ⟨hP3, ?_, hPd⟩, ?_⟩
  · intro t ht
    rw [← hPfam]
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  · rw [hPfam]

/-- **The dense triangle-decomposition theorem on the faithful BKLO §11 cells route.**

From the approximate-decomposition threshold `δ_F^η` at `δ = 9/10` (the dense nibble,
`BKLO.ApproxTriDecompMinDeg (9/10)`) the proved §10 core of this project supplies
`BKLO.Lemma1012K3' (9/10)` (`BKLO.lemma1012K3'_dense_of_lemma107` with
`BKLO.lemma107K2_holds`); §11 then reserves the cells absorber, runs the near-optimal
decomposition on what is left, and absorbs the remainder spread over the bottom cells. -/
theorem triDecompDense_of_nibble_faithful (hcells : CellsAbsorptionK3)
    (happ : ApproxTriDecompMinDeg (9 / 10)) : TriDecompDense :=
  triDecompDense_of_cellsAbsorption hcells
    (lemma1012K3'_dense_of_lemma107 happ lemma107K2_holds)

end BKLO
