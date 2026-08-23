/-
# The absorber-existence predicate and its calculus.

The recursion of `BKLO.AbsorberExists` proves the statement

  `HasAbs b H` — *`H` has an absorber `A` all of whose edges reach above `b`, and none of whose
  vertices is new below `b`* —

for every family of cycles `H` living below `b`.  The two extra conditions are exactly what makes
the recursion compose:

* `Touches b A` lets an absorber built at a higher level be edge-disjoint from everything already
  constructed below `b` (`disjoint_of_touches_below`);
* the support condition `supp A ⊆ supp H ∪ [b, ∞)` propagates "everything new lives above `b`"
  through a chain of covers, which is what `AllAbove` records.
-/
import BKLO.Core
import BKLO.Expansion
import BKLO.Backdeg

open Finset

namespace BKLO

/-- Every vertex of `A` is at least `b`. -/
def AllAbove (b : ℕ) (A : Finset (Sym2 ℕ)) : Prop := ∀ v ∈ supp A, b ≤ v

/-- Every edge of `E` has an endpoint below `b`. -/
def Dips (b : ℕ) (E : Finset (Sym2 ℕ)) : Prop := ∀ e ∈ E, ∃ v ∈ e, v < b

theorem AllAbove.touches {b : ℕ} {A : Finset (Sym2 ℕ)} (h : AllAbove b A) : Touches b A := by
  intro e he
  induction e using Sym2.ind with
  | _ x y => exact ⟨x, by simp, h x (mem_supp.2 ⟨s(x, y), he, by simp⟩)⟩

theorem AllAbove.union {b : ℕ} {A B : Finset (Sym2 ℕ)} (hA : AllAbove b A) (hB : AllAbove b B) :
    AllAbove b (A ∪ B) := by
  intro v hv
  rw [supp_union, Finset.mem_union] at hv
  rcases hv with h | h
  · exact hA v h
  · exact hB v h

theorem disjoint_of_allAbove_dips {b : ℕ} {A E : Finset (Sym2 ℕ)} (hA : AllAbove b A)
    (hE : Dips b E) : Disjoint A E := by
  rw [Finset.disjoint_left]
  intro e heA heE
  obtain ⟨v, hv, hlt⟩ := hE e heE
  exact absurd (hA v (mem_supp.2 ⟨e, heA, hv⟩)) (by omega)

/-- Every finite edge set lives below some bound. -/
theorem exists_below (A : Finset (Sym2 ℕ)) (b : ℕ) : ∃ c, b ≤ c ∧ Below c A := by
  classical
  refine ⟨max b ((supp A).sup id + 1), le_max_left _ _, ?_⟩
  intro v hv
  have : v ≤ (supp A).sup id := Finset.le_sup (f := id) hv
  omega

/-- **The recursion's contract.**  `H` has an absorber whose edges all reach above `b`, which
introduces no new vertex below `b`, and which is `9`-degenerate in the order of `ℕ` (so that it can
be embedded greedily into a host graph of minimum degree `> 9n/10`). -/
def HasAbs (b : ℕ) (H : Finset (Sym2 ℕ)) : Prop :=
  ∃ A, IsAbsorber A H ∧ Touches b A ∧ (∀ v ∈ supp A, v ∈ supp H ∨ b ≤ v) ∧ NatDegen 9 A

theorem hasAbs_empty (b : ℕ) : HasAbs b (∅ : Finset (Sym2 ℕ)) :=
  ⟨∅, isAbsorber_empty, Touches.empty b, by simp, natDegen_empty 9⟩

/-- A decomposable edge set is absorbed by the empty absorber. -/
theorem hasAbs_of_triDecomp {b : ℕ} {H : Finset (Sym2 ℕ)} (h : TriDecomp H) : HasAbs b H :=
  ⟨∅, ⟨by simp, triDecomp_empty, by simpa using h⟩, Touches.empty b, by simp, natDegen_empty 9⟩

/-- **Combining absorbers of two disjoint pieces.**  The second piece is absorbed at a level above
everything the first absorber uses. -/
theorem hasAbs_union {b : ℕ} {H₁ H₂ : Finset (Sym2 ℕ)} (hB1 : Below b H₁) (hB2 : Below b H₂)
    (hd : Disjoint H₁ H₂) (h1 : HasAbs b H₁) (h2 : ∀ b', b ≤ b' → HasAbs b' H₂) :
    HasAbs b (H₁ ∪ H₂) := by
  obtain ⟨A₁, hA₁, ht₁, hs₁, hn₁⟩ := h1
  obtain ⟨c, hbc, hc⟩ := exists_below A₁ b
  obtain ⟨A₂, hA₂, ht₂, hs₂, hn₂⟩ := h2 c hbc
  refine ⟨A₁ ∪ A₂, isAbsorber_union hA₁ hA₂ (disjoint_of_touches_below ht₂ hc).symm
      (disjoint_of_touches_below ht₁ hB2) (disjoint_of_touches_below ht₂ (hB1.mono_le hbc)) hd,
    ht₁.union (ht₂.mono_le hbc), ?_, natDegen_union_split hn₁ hn₂ hc ht₂⟩
  intro v hv
  rw [supp_union, Finset.mem_union] at hv
  rw [supp_union, Finset.mem_union]
  rcases hv with h | h
  · rcases hs₁ v h with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inr h'
  · rcases hs₂ v h with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr (le_trans hbc h')

end BKLO
