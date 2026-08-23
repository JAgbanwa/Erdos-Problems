/-
# Tools for the assembly of BKLO Lemma 10.12 (`r = 2`)

Elementary lemmas about the §10 vocabulary that the proof of Lemma 10.12 needs:

* `BKLO.crossParts_eq_inter` / `BKLO.insideParts_eq_inter` — for a subgraph `X ⊆ E`, the crossing
  (resp. inside) edges of `X` are `X ∩ crossParts E P` (resp. `X ∩ insideParts E P`); this turns all
  of the bookkeeping of the proof into Finset algebra;
* `BKLO.sum_card_parts` — the parts of an equitable partition have total size `|S|`;
* `BKLO.degTo_beforeParts_eq_sum` — degrees into `V_{<i}` split as a sum over the earlier parts;
* `BKLO.edeg_sdiff` and `BKLO.evenDegrees_sdiff` — removing an even subgraph keeps degrees even;
* a handful of monotonicity/deletion estimates for `degTo`.

Everything here is `sorry`-free.
-/
import BKLO.Section1012Defs

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Crossing and inside edges of a subgraph -/

theorem crossParts_eq_inter {E X : Finset (Sym2 V)} {P : Finset (Finset V)} (h : X ⊆ E) :
    crossParts X P = X ∩ crossParts E P := by
  ext e
  simp only [mem_crossParts, Finset.mem_inter]
  tauto_set

theorem insideParts_eq_inter {E X : Finset (Sym2 V)} {P : Finset (Finset V)} (h : X ⊆ E) :
    insideParts X P = X ∩ insideParts E P := by
  ext e
  simp only [mem_insideParts, Finset.mem_inter]
  constructor
  · rintro ⟨he, hW⟩; exact ⟨he, h he, hW⟩
  · rintro ⟨he, -, hW⟩; exact ⟨he, hW⟩

/-- Crossing edges are monotone in the graph. -/
theorem crossParts_mono {X Y : Finset (Sym2 V)} {P : Finset (Finset V)} (h : X ⊆ Y) :
    crossParts X P ⊆ crossParts Y P :=
  Finset.filter_subset_filter _ h

/-- Inside edges are monotone in the graph. -/
theorem insideParts_mono {X Y : Finset (Sym2 V)} {P : Finset (Finset V)} (h : X ⊆ Y) :
    insideParts X P ⊆ insideParts Y P :=
  Finset.filter_subset_filter _ h

/-! ### Sizes of the parts -/

theorem sum_card_parts {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) : ∑ W ∈ P, W.card = S.card := by
  have hdisj : ∀ W ∈ P, ∀ W' ∈ P, W ≠ W' → Disjoint (id W) (id W') :=
    fun W hW W' hW' hne => h.pairwise_disjoint W hW W' hW' hne
  rw [← h.cover, Finset.card_biUnion hdisj]
  rfl

/-! ### Degrees into a union of parts -/

/-- The degree into `V_{<i}` is the sum of the degrees into the earlier parts. -/
theorem degTo_beforeParts_eq_sum {k : ℕ} {P : Finset (Finset V)} {S : Finset V}
    (h : IsEquitablePartition k P S) (idx : Finset V → ℕ) (X : Finset (Sym2 V)) (y : V)
    (W : Finset V) :
    degTo X y (beforeParts P idx W) = ∑ W' ∈ P.filter (fun W' => idx W' < idx W), degTo X y W' := by
  classical
  have hnb : nbhdIn X y (beforeParts P idx W)
      = (P.filter (fun W' => idx W' < idx W)).biUnion (fun W' => nbhdIn X y W') := by
    ext z
    simp only [mem_nbhdIn, beforeParts, Finset.mem_biUnion, Finset.mem_filter, id]
    tauto
  have hdisj : ∀ W₁ ∈ P.filter (fun W' => idx W' < idx W), ∀ W₂ ∈ P.filter (fun W' => idx W' < idx W),
      W₁ ≠ W₂ → Disjoint (nbhdIn X y W₁) (nbhdIn X y W₂) := by
    intro W₁ h₁ W₂ h₂ hne
    refine Finset.disjoint_left.2 fun z hz₁ hz₂ => ?_
    have := h.pairwise_disjoint W₁ (Finset.mem_filter.1 h₁).1 W₂ (Finset.mem_filter.1 h₂).1 hne
    exact (Finset.disjoint_left.1 this) (mem_nbhdIn.1 hz₁).1 (mem_nbhdIn.1 hz₂).1
  rw [degTo, hnb, Finset.card_biUnion hdisj]
  rfl

/-- The degree of `y` into a set `W` containing it is at most its degree in `X[W]`. -/
theorem degTo_le_edeg_edgesIn_mem {X : Finset (Sym2 V)} {W : Finset V} {y : V} (hy : y ∈ W) :
    degTo X y W ≤ edeg (edgesIn X W) y := by
  classical
  have hinj : Set.InjOn (fun z => s(y, z)) (nbhdIn X y W) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hsub : (nbhdIn X y W).image (fun z => s(y, z)) ⊆ (edgesIn X W).filter (fun e => y ∈ e) := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
    rw [mem_nbhdIn] at hz
    refine Finset.mem_filter.2 ⟨mem_edgesIn.2 ⟨hz.2, ?_⟩, by simp⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hy
    · exact hz.1
  calc degTo X y W = ((nbhdIn X y W).image (fun z => s(y, z))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ edeg (edgesIn X W) y := Finset.card_le_card hsub

/-- Inside a part, the inside-part graph and the graph itself have the same neighbourhoods. -/
theorem nbhdIn_insideParts_eq {X : Finset (Sym2 V)} {P : Finset (Finset V)} {W : Finset V}
    (hW : W ∈ P) {y : V} (hy : y ∈ W) : nbhdIn (insideParts X P) y W = nbhdIn X y W := by
  ext z
  simp only [mem_nbhdIn, mem_insideParts]
  constructor
  · rintro ⟨hz, he, -⟩; exact ⟨hz, he⟩
  · rintro ⟨hz, he⟩
    refine ⟨hz, he, W, hW, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hy
    · exact hz

theorem degTo_insideParts_eq {X : Finset (Sym2 V)} {P : Finset (Finset V)} {W : Finset V}
    (hW : W ∈ P) {y : V} (hy : y ∈ W) : degTo (insideParts X P) y W = degTo X y W := by
  rw [degTo, degTo, nbhdIn_insideParts_eq hW hy]

/-- Inside a part, the inside-part graph and the graph itself have the same neighbourhoods, also
when the target set is only a subset of the part. -/
theorem nbhdIn_insideParts_eq_subset {X : Finset (Sym2 V)} {P : Finset (Finset V)} {W N : Finset V}
    (hW : W ∈ P) (hNW : N ⊆ W) {y : V} (hy : y ∈ W) :
    nbhdIn (insideParts X P) y N = nbhdIn X y N := by
  ext z
  simp only [mem_nbhdIn, mem_insideParts]
  constructor
  · rintro ⟨hz, he, -⟩; exact ⟨hz, he⟩
  · rintro ⟨hz, he⟩
    refine ⟨hz, he, W, hW, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hy
    · exact hNW hz

/-- The degree into a set is at most the degree. -/
theorem degTo_le_edeg (X : Finset (Sym2 V)) (x : V) (W : Finset V) : degTo X x W ≤ edeg X x :=
  card_filter_edge_le_edeg X x W

/-! ### Degrees of unions -/

/-- Degrees are subadditive over unions of edge sets. -/
theorem edeg_union_le_sum (A B : Finset (Sym2 V)) (v : V) :
    edeg (A ∪ B) v ≤ edeg A v + edeg B v := by
  classical
  unfold edeg
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-- Degrees add over a disjoint union of edge sets. -/
theorem edeg_union_of_disjoint {X Y : Finset (Sym2 V)} (h : Disjoint X Y) (v : V) :
    edeg (X ∪ Y) v = edeg X v + edeg Y v := by
  classical
  unfold edeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

/-- A disjoint union of even graphs is even. -/
theorem evenDegrees_union {X Y : Finset (Sym2 V)} (h : Disjoint X Y) (hX : EvenDegrees X)
    (hY : EvenDegrees Y) : EvenDegrees (X ∪ Y) := by
  intro v
  rw [edeg_union_of_disjoint h v]
  exact (hX v).add (hY v)

/-- Degrees into a set are subadditive over unions of edge sets. -/
theorem degTo_union_le (X Y : Finset (Sym2 V)) (x : V) (W : Finset V) :
    degTo (X ∪ Y) x W ≤ degTo X x W + degTo Y x W := by
  classical
  have hsub : nbhdIn (X ∪ Y) x W ⊆ nbhdIn X x W ∪ nbhdIn Y x W := by
    intro z hz
    rw [mem_nbhdIn] at hz
    rcases Finset.mem_union.1 hz.2 with h | h
    · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hz.1, h⟩)
    · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hz.1, h⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- Deleting `Y` costs `x` at most its `Y`-degree into `W`. -/
theorem degTo_le_sdiff_add (X Y : Finset (Sym2 V)) (x : V) (W : Finset V) :
    degTo X x W ≤ degTo (X \ Y) x W + degTo Y x W := by
  classical
  have hsub : nbhdIn X x W ⊆ nbhdIn (X \ Y) x W ∪ nbhdIn Y x W := by
    intro z hz
    rw [mem_nbhdIn] at hz
    by_cases hY : s(x, z) ∈ Y
    · exact Finset.mem_union_right _ (mem_nbhdIn.2 ⟨hz.1, hY⟩)
    · exact Finset.mem_union_left _ (mem_nbhdIn.2 ⟨hz.1, Finset.mem_sdiff.2 ⟨hz.2, hY⟩⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-! ### Degrees and edge deletion -/

/-- Deleting edges of `Y` from `X` costs `y` at most `edeg Y y` neighbours in any set. -/
theorem degTo_sdiff_le (X Y : Finset (Sym2 V)) (y : V) (Z : Finset V) :
    (degTo X y Z : ℝ) - (edeg Y y : ℝ) ≤ (degTo (X \ Y) y Z : ℝ) := by
  have := degTo_sdiff_ge X Y y Z
  have : (degTo X y Z : ℝ) ≤ (degTo (X \ Y) y Z : ℝ) + (edeg Y y : ℝ) := by exact_mod_cast this
  linarith

/-- The two neighbourhoods inside `W` of two vertices meet in at least
`d₁ + d₂ - |W|` vertices. -/
theorem card_inter_nbhd_ge {X Y : Finset (Sym2 V)} {x y : V} {W : Finset V} :
    ((nbhdIn X x W).card : ℝ) + ((nbhdIn Y y W).card : ℝ) - (W.card : ℝ)
      ≤ ((nbhdIn X x W ∩ nbhdIn Y y W).card : ℝ) := by
  have hcard : (nbhdIn X x W).card + (nbhdIn Y y W).card
      = (nbhdIn X x W ∪ nbhdIn Y y W).card + (nbhdIn X x W ∩ nbhdIn Y y W).card :=
    (Finset.card_union_add_card_inter _ _).symm
  have hle : (nbhdIn X x W ∪ nbhdIn Y y W).card ≤ W.card :=
    Finset.card_le_card (Finset.union_subset (nbhdIn_subset _ _ _) (nbhdIn_subset _ _ _))
  have h1 : ((nbhdIn X x W).card : ℝ) + ((nbhdIn Y y W).card : ℝ)
      = ((nbhdIn X x W ∪ nbhdIn Y y W).card : ℝ) + ((nbhdIn X x W ∩ nbhdIn Y y W).card : ℝ) := by
    exact_mod_cast hcard
  have h2 : ((nbhdIn X x W ∪ nbhdIn Y y W).card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hle
  linarith

/-- Degrees into a set are monotone in the set. -/
theorem degTo_mono_right {X : Finset (Sym2 V)} {Z Z' : Finset V} (h : Z ⊆ Z') (y : V) :
    degTo X y Z ≤ degTo X y Z' :=
  Finset.card_le_card (nbhdIn_mono_right h y)

end BKLO
