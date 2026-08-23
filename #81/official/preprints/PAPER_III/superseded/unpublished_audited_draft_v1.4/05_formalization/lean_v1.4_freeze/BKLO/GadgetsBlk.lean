/-
# Blocks of fresh vertices, and the gadgets placed on them, with their back-degeneracy.

The absorber recursion always relocates a family of cycles onto a *block* `blk b n` of consecutive
naturals.  Placing a gadget on such a block is a **translation** `v ↦ b + v` of the concrete
template of `BKLO.Gadgets`, and translations preserve the order of `ℕ`.  Consequently the
back-degeneracy of a placed gadget can be read off from the template by `decide`, which is what this
file does: for each of the four terminal configurations `C₄ ⊎ C₅`, `C₅ ⊎ C₄`, `3·C₄`, `3·C₅` the
union of the relocated cycles with the gadget absorbing them has back-degree at most `7` at every
vertex.
-/
import BKLO.Gadgets
import BKLO.Backdeg

open Finset

namespace BKLO

/-! ### Blocks of fresh vertices -/

/-- The block of `n` consecutive naturals starting at `b`. -/
def blk (b n : ℕ) : List ℕ := List.range' b n

@[simp] theorem blk_length (b n : ℕ) : (blk b n).length = n := by simp [blk]

theorem blk_nodup (b n : ℕ) : (blk b n).Nodup := by simp [blk, List.nodup_range']

theorem mem_blk {b n v : ℕ} : v ∈ blk b n ↔ b ≤ v ∧ v < b + n := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 h
    omega
  · intro h
    exact List.mem_range'.2 ⟨v - b, by omega, by omega⟩

theorem blk_drop (b n k : ℕ) : (blk b n).drop k = blk (b + k) (n - k) := by
  simp only [blk]
  induction k generalizing b n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.range'_succ, List.drop_succ_cons, ih]
      congr 1 <;> omega

theorem blk_take (b n k : ℕ) : (blk b n).take k = blk b (min k n) := by
  simp only [blk]
  induction k generalizing b n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.range'_succ, List.take_succ_cons, ih]
      have hm : min (k + 1) (n + 1) = min k n + 1 := by omega
      rw [hm, List.range'_succ]

/-- A block is the translate of the initial block. -/
theorem blk_eq_map (b c n : ℕ) : blk (b + c) n = (blk c n).map (b + ·) := by
  simp [blk, List.map_add_range']

/-! ### Translation of an edge set -/

/-- Translate every vertex of an edge set by `b`. -/
def shiftE (b : ℕ) (A : Finset (Sym2 ℕ)) : Finset (Sym2 ℕ) := A.image (Sym2.map (b + ·))

theorem shiftE_injective (b : ℕ) : Function.Injective (b + · : ℕ → ℕ) := by
  intro x y h
  simp only at h
  omega

theorem shiftE_union (b : ℕ) (A B : Finset (Sym2 ℕ)) :
    shiftE b (A ∪ B) = shiftE b A ∪ shiftE b B := Finset.image_union _ _

theorem cycEdges_blk (b c n : ℕ) : cycEdges (blk (b + c) n) = shiftE b (cycEdges (blk c n)) := by
  rw [blk_eq_map, cycEdges_map]
  rfl

theorem supp_shiftE_ge (b : ℕ) (A : Finset (Sym2 ℕ)) : ∀ v ∈ supp (shiftE b A), b ≤ v := by
  intro v hv
  rw [shiftE, supp_image_map] at hv
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hv
  omega

theorem touches_shiftE (b : ℕ) (A : Finset (Sym2 ℕ)) : Touches b (shiftE b A) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y => exact ⟨x, by simp, supp_shiftE_ge b A x (mem_supp.2 ⟨s(x, y), he, by simp⟩)⟩

theorem isAbsorber_shiftE {b : ℕ} {A H : Finset (Sym2 ℕ)} (h : IsAbsorber A H) :
    IsAbsorber (shiftE b A) (shiftE b H) := IsAbsorber.map (shiftE_injective b) h

/-! ### Back-degeneracy is preserved by translation -/

theorem backNbrs_shiftE_subset (b : ℕ) (A : Finset (Sym2 ℕ)) (i : ℕ) :
    backNbrs (shiftE b A) (b + i) ⊆ (backNbrs A i).image (b + ·) := by
  intro u hu
  rw [mem_backNbrs] at hu
  obtain ⟨hlt, hmem⟩ := hu
  obtain ⟨e, he, hfe⟩ := Finset.mem_image.1 hmem
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.map_pair_eq, Sym2.eq_iff] at hfe
    rcases hfe with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hyi : y = i := by omega
      subst hyi
      refine Finset.mem_image.2 ⟨x, mem_backNbrs.2 ⟨by omega, he⟩, hx⟩
    · have hxi : x = i := by omega
      subst hxi
      refine Finset.mem_image.2 ⟨y, mem_backNbrs.2 ⟨by omega, ?_⟩, hy⟩
      rwa [Sym2.eq_swap]

theorem natDegen_shiftE {d b : ℕ} {A : Finset (Sym2 ℕ)} (h : NatDegen d A) :
    NatDegen d (shiftE b A) := by
  intro v
  rcases Nat.lt_or_ge v b with hv | hv
  · rw [backNbrs_eq_empty_of_touches (touches_shiftE b A) hv]
    simp
  · obtain ⟨i, rfl⟩ : ∃ i, v = b + i := ⟨v - b, by omega⟩
    refine le_trans (Finset.card_le_card (backNbrs_shiftE_subset b A i)) ?_
    exact le_trans (Finset.card_image_le) (h i)

/-! ### The reordered `C₅ ⊎ C₄` gadget

`A45` absorbs a `4`-cycle followed by a `5`-cycle.  Relabelling its template by the cyclic shift
`i ↦ i + 5 mod 9` gives a gadget absorbing a `5`-cycle followed by a `4`-cycle, which is the second
of the two orders in which the terminal group can appear. -/

/-- Absorber for `C₅ ⊎ C₄` on `{0,…,8}`, the `5`-cycle first. -/
def A54 : Finset (Finset ℕ) := {{0, 5, 7}, {1, 4, 7}, {0, 2, 8}, {1, 3, 8}}

/-- Its union with `C₅ ⊎ C₄`. -/
def AH54 : Finset (Finset ℕ) :=
  {{5, 6, 7}, {0, 5, 8}, {1, 7, 8}, {0, 1, 2}, {0, 4, 7}, {2, 3, 8}, {1, 3, 4}}

set_option maxRecDepth 100000

theorem gadget54_template :
    IsAbsorber (famEdges A54) (cycEdges [0, 1, 2, 3, 4] ∪ cycEdges [5, 6, 7, 8]) := by
  refine ⟨by decide +kernel, triDecomp_famEdges A54 (by decide +kernel) (by decide +kernel), ?_⟩
  have : famEdges A54 ∪ (cycEdges [0, 1, 2, 3, 4] ∪ cycEdges [5, 6, 7, 8]) = famEdges AH54 := by
    decide +kernel
  rw [this]
  exact triDecomp_famEdges AH54 (by decide +kernel) (by decide +kernel)

/-! ### The four terminal templates, with their back-degeneracy -/

/-- The `C₄ ⊎ C₅` configuration together with its absorber. -/
def G45 : Finset (Sym2 ℕ) :=
  (cycEdges (blk 0 4) ∪ cycEdges (blk 4 5)) ∪ famEdges A45

/-- The `C₅ ⊎ C₄` configuration together with its absorber. -/
def G54 : Finset (Sym2 ℕ) :=
  (cycEdges (blk 0 5) ∪ cycEdges (blk 5 4)) ∪ famEdges A54

/-- The `3 · C₄` configuration together with its absorber. -/
def G444 : Finset (Sym2 ℕ) :=
  (cycEdges (blk 0 4) ∪ (cycEdges (blk 4 4) ∪ cycEdges (blk 8 4))) ∪ famEdges A444

/-- The `3 · C₅` configuration together with its absorber. -/
def G555 : Finset (Sym2 ℕ) :=
  (cycEdges (blk 0 5) ∪ (cycEdges (blk 5 5) ∪ cycEdges (blk 10 5))) ∪ famEdges A555

theorem natDegen_G45 : NatDegen 7 G45 := by
  refine natDegen_of_forall_supp ?_
  decide +kernel

theorem natDegen_G54 : NatDegen 7 G54 := by
  refine natDegen_of_forall_supp ?_
  decide +kernel

theorem natDegen_G444 : NatDegen 7 G444 := by
  refine natDegen_of_forall_supp ?_
  decide +kernel

theorem natDegen_G555 : NatDegen 7 G555 := by
  refine natDegen_of_forall_supp ?_
  decide +kernel

/-! ### The gadgets placed on a block

Each of the four terminal configurations, placed on the block starting at `b`: the gadget absorbs
the relocated cycles, uses no vertex below `b`, and the configuration together with its absorber has
back-degree at most `7` at every vertex. -/

theorem gadget_45_blk (b : ℕ) :
    ∃ A, IsAbsorber A (cycEdges (blk b 4) ∪ cycEdges (blk (b + 4) 5)) ∧ (∀ v ∈ supp A, b ≤ v) ∧
      NatDegen 7 ((cycEdges (blk b 4) ∪ cycEdges (blk (b + 4) 5)) ∪ A) := by
  have e1 : cycEdges (blk b 4) = shiftE b (cycEdges (blk 0 4)) := by
    rw [← cycEdges_blk b 0 4, Nat.add_zero]
  have e2 : cycEdges (blk (b + 4) 5) = shiftE b (cycEdges (blk 4 5)) := cycEdges_blk b 4 5
  refine ⟨shiftE b (famEdges A45), ?_, supp_shiftE_ge b _, ?_⟩
  · rw [e1, e2, ← shiftE_union]
    exact isAbsorber_shiftE gadget45_template
  · rw [e1, e2, ← shiftE_union, ← shiftE_union]
    exact natDegen_shiftE natDegen_G45

theorem gadget_54_blk (b : ℕ) :
    ∃ A, IsAbsorber A (cycEdges (blk b 5) ∪ cycEdges (blk (b + 5) 4)) ∧ (∀ v ∈ supp A, b ≤ v) ∧
      NatDegen 7 ((cycEdges (blk b 5) ∪ cycEdges (blk (b + 5) 4)) ∪ A) := by
  have e1 : cycEdges (blk b 5) = shiftE b (cycEdges (blk 0 5)) := by
    rw [← cycEdges_blk b 0 5, Nat.add_zero]
  have e2 : cycEdges (blk (b + 5) 4) = shiftE b (cycEdges (blk 5 4)) := cycEdges_blk b 5 4
  refine ⟨shiftE b (famEdges A54), ?_, supp_shiftE_ge b _, ?_⟩
  · rw [e1, e2, ← shiftE_union]
    exact isAbsorber_shiftE gadget54_template
  · rw [e1, e2, ← shiftE_union, ← shiftE_union]
    exact natDegen_shiftE natDegen_G54

theorem gadget_444_blk (b : ℕ) :
    ∃ A, IsAbsorber A
        (cycEdges (blk b 4) ∪ (cycEdges (blk (b + 4) 4) ∪ cycEdges (blk (b + 8) 4))) ∧
      (∀ v ∈ supp A, b ≤ v) ∧
      NatDegen 7 ((cycEdges (blk b 4) ∪
        (cycEdges (blk (b + 4) 4) ∪ cycEdges (blk (b + 8) 4))) ∪ A) := by
  have e1 : cycEdges (blk b 4) = shiftE b (cycEdges (blk 0 4)) := by
    rw [← cycEdges_blk b 0 4, Nat.add_zero]
  have e2 : cycEdges (blk (b + 4) 4) = shiftE b (cycEdges (blk 4 4)) := cycEdges_blk b 4 4
  have e3 : cycEdges (blk (b + 8) 4) = shiftE b (cycEdges (blk 8 4)) := cycEdges_blk b 8 4
  refine ⟨shiftE b (famEdges A444), ?_, supp_shiftE_ge b _, ?_⟩
  · rw [e1, e2, e3, ← shiftE_union, ← shiftE_union]
    exact isAbsorber_shiftE gadget444_template
  · rw [e1, e2, e3, ← shiftE_union, ← shiftE_union, ← shiftE_union]
    exact natDegen_shiftE natDegen_G444

theorem gadget_555_blk (b : ℕ) :
    ∃ A, IsAbsorber A
        (cycEdges (blk b 5) ∪ (cycEdges (blk (b + 5) 5) ∪ cycEdges (blk (b + 10) 5))) ∧
      (∀ v ∈ supp A, b ≤ v) ∧
      NatDegen 7 ((cycEdges (blk b 5) ∪
        (cycEdges (blk (b + 5) 5) ∪ cycEdges (blk (b + 10) 5))) ∪ A) := by
  have e1 : cycEdges (blk b 5) = shiftE b (cycEdges (blk 0 5)) := by
    rw [← cycEdges_blk b 0 5, Nat.add_zero]
  have e2 : cycEdges (blk (b + 5) 5) = shiftE b (cycEdges (blk 5 5)) := cycEdges_blk b 5 5
  have e3 : cycEdges (blk (b + 10) 5) = shiftE b (cycEdges (blk 10 5)) := cycEdges_blk b 10 5
  refine ⟨shiftE b (famEdges A555), ?_, supp_shiftE_ge b _, ?_⟩
  · rw [e1, e2, e3, ← shiftE_union, ← shiftE_union]
    exact isAbsorber_shiftE gadget555_template
  · rw [e1, e2, e3, ← shiftE_union, ← shiftE_union, ← shiftE_union]
    exact natDegen_shiftE natDegen_G555

end BKLO
