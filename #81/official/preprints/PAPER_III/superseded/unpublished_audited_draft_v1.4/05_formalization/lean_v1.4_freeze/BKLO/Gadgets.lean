/-
# The explicit finite gadgets.

Iterating the cover moves of `BKLO.Cycles` shrinks every cycle of a family to length `3`, `4` or
`5`; a triangle is decomposable on its own, and a group of `4`- and `5`-cycles whose total length is
divisible by `3` (and which contains at most three cycles) is one of

  `C₄ ⊎ C₅`,   `C₄ ⊎ C₄ ⊎ C₄`,   `C₅ ⊎ C₅ ⊎ C₅`.

For each of these three configurations we exhibit an explicit absorber, found by computer search and
verified here by `decide` on the concrete vertex set `{0, …, k-1}`; `BKLO.Transport` then moves the
gadget onto an arbitrary list of distinct vertices.  The remaining gadget, `covers_four`, is the
cover of a `4`-cycle by a `5`-cycle through two fresh vertices.
-/
import BKLO.Transport
import Mathlib.Tactic.Group

open Finset

namespace BKLO

/-! ### The concrete triangle families -/

/-- Absorber for `C₄ ⊎ C₅` on `{0,…,8}`. -/
def A45 : Finset (Finset ℕ) := {{0, 2, 4}, {2, 5, 8}, {3, 4, 6}, {3, 5, 7}}

/-- Its union with `C₄ ⊎ C₅`. -/
def AH45 : Finset (Finset ℕ) :=
  {{0, 1, 2}, {0, 3, 4}, {2, 3, 5}, {4, 5, 6}, {4, 8, 2}, {6, 7, 3}, {7, 8, 5}}

/-- Absorber for `3 · C₄` on `{0,…,11}`. -/
def A444 : Finset (Finset ℕ) :=
  {{0, 6, 9}, {1, 6, 8}, {2, 4, 11}, {2, 7, 8}, {3, 9, 11}, {4, 6, 10}}

/-- Its union with `3 · C₄`. -/
def AH444 : Finset (Finset ℕ) :=
  {{6, 7, 8}, {10, 11, 4}, {0, 1, 6}, {8, 9, 11}, {4, 7, 2}, {5, 6, 4}, {2, 3, 11}, {9, 10, 6},
   {0, 3, 9}, {1, 2, 8}}

/-- Absorber for `3 · C₅` on `{0,…,14}`. -/
def A555 : Finset (Finset ℕ) :=
  {{0, 5, 12}, {0, 6, 9}, {0, 8, 13}, {1, 8, 12}, {2, 5, 11}, {2, 6, 10}, {2, 7, 12}, {3, 7, 10},
   {3, 8, 14}, {4, 6, 8}}

/-- Its union with `3 · C₅`. -/
def AH555 : Finset (Finset ℕ) :=
  {{0, 4, 6}, {3, 4, 8}, {1, 2, 12}, {5, 6, 2}, {10, 14, 3}, {7, 8, 12}, {0, 1, 8}, {12, 13, 0},
   {5, 9, 0}, {11, 12, 5}, {2, 3, 7}, {10, 11, 2}, {6, 7, 10}, {8, 9, 6}, {13, 14, 8}}

/-- The cover of a `4`-cycle by a `5`-cycle, as a triangle family on `{0,…,5}`. -/
def T4 : Finset (Finset ℕ) := {{0, 1, 2}, {2, 3, 4}, {0, 3, 5}}

/-! ### The templates, verified by `decide` -/

theorem triDecomp_famEdges (P : Finset (Finset ℕ)) (h1 : ∀ t ∈ P, t.card = 3)
    (h2 : ∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) :
    TriDecomp (famEdges P) := ⟨P, h1, h2, rfl⟩

set_option maxRecDepth 100000

theorem gadget45_template :
    IsAbsorber (famEdges A45) (cycEdges [0, 1, 2, 3] ∪ cycEdges [4, 5, 6, 7, 8]) := by
  refine ⟨by decide +kernel, triDecomp_famEdges A45 (by decide +kernel) (by decide +kernel), ?_⟩
  have : famEdges A45 ∪ (cycEdges [0, 1, 2, 3] ∪ cycEdges [4, 5, 6, 7, 8]) = famEdges AH45 := by
    decide +kernel
  rw [this]
  exact triDecomp_famEdges AH45 (by decide +kernel) (by decide +kernel)

theorem gadget444_template :
    IsAbsorber (famEdges A444)
      (cycEdges [0, 1, 2, 3] ∪ (cycEdges [4, 5, 6, 7] ∪ cycEdges [8, 9, 10, 11])) := by
  refine ⟨by decide +kernel, triDecomp_famEdges A444 (by decide +kernel) (by decide +kernel), ?_⟩
  have : famEdges A444 ∪ (cycEdges [0, 1, 2, 3] ∪ (cycEdges [4, 5, 6, 7] ∪ cycEdges [8, 9, 10, 11]))
      = famEdges AH444 := by decide +kernel
  rw [this]
  exact triDecomp_famEdges AH444 (by decide +kernel) (by decide +kernel)

theorem gadget555_template :
    IsAbsorber (famEdges A555)
      (cycEdges [0, 1, 2, 3, 4] ∪ (cycEdges [5, 6, 7, 8, 9] ∪ cycEdges [10, 11, 12, 13, 14])) := by
  refine ⟨by decide +kernel, triDecomp_famEdges A555 (by decide +kernel) (by decide +kernel), ?_⟩
  have : famEdges A555 ∪
      (cycEdges [0, 1, 2, 3, 4] ∪ (cycEdges [5, 6, 7, 8, 9] ∪ cycEdges [10, 11, 12, 13, 14]))
      = famEdges AH555 := by decide +kernel
  rw [this]
  exact triDecomp_famEdges AH555 (by decide +kernel) (by decide +kernel)

theorem covers_four_template : Covers (cycEdges [0, 2, 4, 3, 5]) (cycEdges [0, 1, 2, 3]) := by
  refine ⟨by decide +kernel, ?_⟩
  have : cycEdges [0, 2, 4, 3, 5] ∪ cycEdges [0, 1, 2, 3] = famEdges T4 := by decide +kernel
  rw [this]
  exact triDecomp_famEdges T4 (by decide +kernel) (by decide +kernel)

/-! ### The transported gadgets

Each gadget is stated for an arbitrary list `d` of distinct vertices of the right length, split into
consecutive blocks by `take`/`drop`; the absorber it produces uses no vertices outside `d`. -/

theorem supp_A45 : supp (famEdges A45) ⊆ (List.range 9).toFinset := by decide +kernel
theorem supp_A444 : supp (famEdges A444) ⊆ (List.range 12).toFinset := by decide +kernel
theorem supp_A555 : supp (famEdges A555) ⊆ (List.range 15).toFinset := by decide +kernel

/-- **Gadget `C₄ ⊎ C₅`.** -/
theorem gadget_45 {d : List ℕ} (hnd : d.Nodup) (hlen : d.length = 9) :
    ∃ A, IsAbsorber A (cycEdges (d.take 4) ∪ cycEdges (d.drop 4)) ∧ supp A ⊆ d.toFinset := by
  obtain ⟨f, hf, hmap⟩ := exists_inj_map d hnd
  rw [hlen] at hmap
  have h1 : d.take 4 = ([0, 1, 2, 3] : List ℕ).map f := by
    rw [← hmap, ← List.map_take]; rfl
  have h2 : d.drop 4 = ([4, 5, 6, 7, 8] : List ℕ).map f := by
    rw [← hmap, ← List.map_drop]; rfl
  refine ⟨(famEdges A45).image (Sym2.map f), ?_, ?_⟩
  · have h := IsAbsorber.map hf gadget45_template
    rw [Finset.image_union, ← cycEdges_map, ← cycEdges_map, ← h1, ← h2] at h
    exact h
  · rw [supp_image_map]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    rw [List.mem_toFinset, ← hmap]
    exact List.mem_map.2 ⟨u, List.mem_toFinset.1 (supp_A45 hu), rfl⟩

/-- **Gadget `C₄ ⊎ C₄ ⊎ C₄`.** -/
theorem gadget_444 {d : List ℕ} (hnd : d.Nodup) (hlen : d.length = 12) :
    ∃ A, IsAbsorber A
        (cycEdges (d.take 4) ∪ (cycEdges ((d.drop 4).take 4) ∪ cycEdges (d.drop 8))) ∧
      supp A ⊆ d.toFinset := by
  obtain ⟨f, hf, hmap⟩ := exists_inj_map d hnd
  rw [hlen] at hmap
  have h1 : d.take 4 = ([0, 1, 2, 3] : List ℕ).map f := by
    rw [← hmap, ← List.map_take]; rfl
  have h2 : (d.drop 4).take 4 = ([4, 5, 6, 7] : List ℕ).map f := by
    rw [← hmap, ← List.map_drop, ← List.map_take]; rfl
  have h3 : d.drop 8 = ([8, 9, 10, 11] : List ℕ).map f := by
    rw [← hmap, ← List.map_drop]; rfl
  refine ⟨(famEdges A444).image (Sym2.map f), ?_, ?_⟩
  · have h := IsAbsorber.map hf gadget444_template
    rw [Finset.image_union, Finset.image_union, ← cycEdges_map, ← cycEdges_map, ← cycEdges_map,
      ← h1, ← h2, ← h3] at h
    exact h
  · rw [supp_image_map]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    rw [List.mem_toFinset, ← hmap]
    exact List.mem_map.2 ⟨u, List.mem_toFinset.1 (supp_A444 hu), rfl⟩

/-- **Gadget `C₅ ⊎ C₅ ⊎ C₅`.** -/
theorem gadget_555 {d : List ℕ} (hnd : d.Nodup) (hlen : d.length = 15) :
    ∃ A, IsAbsorber A
        (cycEdges (d.take 5) ∪ (cycEdges ((d.drop 5).take 5) ∪ cycEdges (d.drop 10))) ∧
      supp A ⊆ d.toFinset := by
  obtain ⟨f, hf, hmap⟩ := exists_inj_map d hnd
  rw [hlen] at hmap
  have h1 : d.take 5 = ([0, 1, 2, 3, 4] : List ℕ).map f := by
    rw [← hmap, ← List.map_take]; rfl
  have h2 : (d.drop 5).take 5 = ([5, 6, 7, 8, 9] : List ℕ).map f := by
    rw [← hmap, ← List.map_drop, ← List.map_take]; rfl
  have h3 : d.drop 10 = ([10, 11, 12, 13, 14] : List ℕ).map f := by
    rw [← hmap, ← List.map_drop]; rfl
  refine ⟨(famEdges A555).image (Sym2.map f), ?_, ?_⟩
  · have h := IsAbsorber.map hf gadget555_template
    rw [Finset.image_union, Finset.image_union, ← cycEdges_map, ← cycEdges_map, ← cycEdges_map,
      ← h1, ← h2, ← h3] at h
    exact h
  · rw [supp_image_map]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    rw [List.mem_toFinset, ← hmap]
    exact List.mem_map.2 ⟨u, List.mem_toFinset.1 (supp_A555 hu), rfl⟩

/-- **Four move.**  A `4`-cycle is covered by a `5`-cycle through two fresh vertices. -/
theorem covers_four {l : List ℕ} {w w' : ℕ} (hnd : l.Nodup) (h4 : l.length = 4)
    (hw : w ∉ l) (hw' : w' ∉ l) (hww : w ≠ w') :
    ∃ l' : List ℕ, l'.length = 5 ∧ l'.Nodup ∧ (∀ v ∈ l', v ∈ l ∨ v = w ∨ v = w') ∧
      Covers (cycEdges l') (cycEdges l) := by
  have hdnd : (l ++ [w, w']).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, by simp [hww], ?_⟩
    intro a ha b hb
    rcases List.mem_cons.1 hb with rfl | hb2
    · rintro rfl; exact hw ha
    rcases List.mem_cons.1 hb2 with rfl | hb3
    · rintro rfl; exact hw' ha
    · simp at hb3
  have hdlen : (l ++ [w, w']).length = 6 := by simp [h4]
  obtain ⟨f, hf, hmap⟩ := exists_inj_map _ hdnd
  rw [hdlen] at hmap
  have hl : l = ([0, 1, 2, 3] : List ℕ).map f := by
    have e1 : (l ++ [w, w']).take 4 = l := List.take_left' h4
    rw [← e1, ← hmap, ← List.map_take]; rfl
  have hww2 : ([4, 5] : List ℕ).map f = [w, w'] := by
    have e1 : (l ++ [w, w']).drop 4 = [w, w'] := List.drop_left' h4
    rw [← e1, ← hmap, ← List.map_drop]; rfl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hww2
  obtain ⟨hf4, hf5⟩ := hww2
  refine ⟨([0, 2, 4, 3, 5] : List ℕ).map f, by simp, List.Nodup.map hf (by decide +kernel), ?_, ?_⟩
  · intro v hv
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by rw [hl]; simp)
    · exact Or.inl (by rw [hl]; simp)
    · exact Or.inr (Or.inl hf4)
    · exact Or.inl (by rw [hl]; simp)
    · exact Or.inr (Or.inr hf5)
  · have h := Covers.map hf covers_four_template
    rw [← cycEdges_map, ← cycEdges_map, ← hl] at h
    exact h

/-- **Four move, explicit form.**  The `5`-cycle covering a given `4`-cycle, written out. -/
theorem covers_four_expl {a x c d w w' : ℕ} (hnd : ([a, x, c, d] : List ℕ).Nodup)
    (hw : w ∉ ([a, x, c, d] : List ℕ)) (hw' : w' ∉ ([a, x, c, d] : List ℕ)) (hww : w ≠ w') :
    Covers (cycEdges [a, c, w, d, w']) (cycEdges [a, x, c, d]) := by
  have h4 : ([a, x, c, d] : List ℕ).length = 4 := by simp
  have hdnd : (([a, x, c, d] : List ℕ) ++ [w, w']).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, by simp [hww], ?_⟩
    intro p hp q hq
    rcases List.mem_cons.1 hq with rfl | hq2
    · rintro rfl; exact hw hp
    rcases List.mem_cons.1 hq2 with rfl | hq3
    · rintro rfl; exact hw' hp
    · simp at hq3
  have hdlen : (([a, x, c, d] : List ℕ) ++ [w, w']).length = 6 := by simp
  obtain ⟨f, hf, hmap⟩ := exists_inj_map _ hdnd
  rw [hdlen] at hmap
  have hl : ([a, x, c, d] : List ℕ) = ([0, 1, 2, 3] : List ℕ).map f := by
    have e1 : (([a, x, c, d] : List ℕ) ++ [w, w']).take 4 = [a, x, c, d] := List.take_left' h4
    rw [← e1, ← hmap, ← List.map_take]; rfl
  have hww2 : ([4, 5] : List ℕ).map f = [w, w'] := by
    have e1 : (([a, x, c, d] : List ℕ) ++ [w, w']).drop 4 = [w, w'] := List.drop_left' h4
    rw [← e1, ← hmap, ← List.map_drop]; rfl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hww2
  obtain ⟨hf4, hf5⟩ := hww2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  obtain ⟨hf0, hf1, hf2, hf3⟩ := hl
  have h := Covers.map hf covers_four_template
  rw [← cycEdges_map, ← cycEdges_map] at h
  have e1 : ([0, 1, 2, 3] : List ℕ).map f = [a, x, c, d] := by
    simp only [List.map_cons, List.map_nil]
    rw [← hf0, ← hf1, ← hf2, ← hf3]
  have e2 : ([0, 2, 4, 3, 5] : List ℕ).map f = [a, c, w, d, w'] := by
    simp only [List.map_cons, List.map_nil]
    rw [← hf0, ← hf2, ← hf3, hf4, hf5]
  rwa [e1, e2] at h

end BKLO
