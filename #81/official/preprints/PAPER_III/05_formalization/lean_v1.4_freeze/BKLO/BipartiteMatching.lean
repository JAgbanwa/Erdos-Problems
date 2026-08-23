/-
# A bipartite matching from a half-degree condition.

Hall's theorem in the form the class-respecting pairing of a link needs: two finite sets of the
same size, each vertex of either side joined to more than half of the other side, carry a perfect
matching.  The half-degree hypothesis is exactly what the two-sided grid design supplies for two
classes of one region: every vertex of `W` misses at most a quarter of every class
(`IsGridTwoSidedReservoir.classBalancedSharp`), and the reserved link keeps three quarters of every
class of its region (`linkClassGe`).

* `BKLO.exists_matching_of_half_degree` — the matching, as an injection defined on the left side.

Everything here is `sorry`-free.
-/
import Mathlib.Combinatorics.Hall.Finite

open Finset

namespace BKLO

/-- **A perfect matching from a half-degree condition.**  If `A` and `B` have the same size and
every vertex of `A` is related to more than half of `B`, and every vertex of `B` to more than half
of `A`, then `A` is matched into `B` injectively by the relation. -/
theorem exists_matching_of_half_degree {V : Type*} [DecidableEq V] {A B : Finset V}
    {r : V → V → Prop} [DecidableRel r] (hcard : A.card = B.card)
    (hA : ∀ a ∈ A, B.card < 2 * (B.filter (fun b => r a b)).card)
    (hB : ∀ b ∈ B, A.card < 2 * (A.filter (fun a => r a b)).card) :
    ∃ f : V → V, (∀ a ∈ A, f a ∈ B) ∧ (∀ a ∈ A, r a (f a)) ∧ Set.InjOn f A := by
  classical
  set t : {a // a ∈ A} → Finset V := fun a => B.filter (fun b => r a.1 b) with ht
  have hcardsub : ∀ s : Finset {a // a ∈ A}, s.card ≤ A.card := by
    intro s
    have h1 : s.card ≤ (Finset.univ : Finset {a // a ∈ A}).card := Finset.card_le_card
      (Finset.subset_univ s)
    simpa [Fintype.card_coe] using h1
  have hall : ∀ s : Finset {a // a ∈ A}, s.card ≤ (s.biUnion t).card := by
    intro s
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a₀, ha₀⟩
    · simp
    by_cases hsmall : 2 * s.card ≤ A.card
    · have h1 : t a₀ ⊆ s.biUnion t := Finset.subset_biUnion_of_mem t ha₀
      have h2 : B.card < 2 * (t a₀).card := hA a₀.1 a₀.2
      have h3 := Finset.card_le_card h1
      omega
    · have hsub : B ⊆ s.biUnion t := by
        intro b hb
        have hS : (s.image (Subtype.val)).card = s.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have hSA : s.image (Subtype.val) ⊆ A := by
          intro a ha
          obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 ha
          exact z.2
        have h2 := hB b hb
        have hne : ((s.image Subtype.val) ∩ (A.filter (fun a => r a b))).Nonempty := by
          by_contra hcon
          rw [Finset.not_nonempty_iff_eq_empty] at hcon
          have hdisj : Disjoint (s.image Subtype.val) (A.filter (fun a => r a b)) :=
            Finset.disjoint_iff_inter_eq_empty.2 hcon
          have hun : ((s.image Subtype.val) ∪ (A.filter (fun a => r a b))).card
              = (s.image Subtype.val).card + (A.filter (fun a => r a b)).card :=
            Finset.card_union_of_disjoint hdisj
          have hle : ((s.image Subtype.val) ∪ (A.filter (fun a => r a b))).card ≤ A.card :=
            Finset.card_le_card (Finset.union_subset hSA (Finset.filter_subset _ _))
          omega
        obtain ⟨a, ha⟩ := hne
        obtain ⟨haS, haf⟩ := Finset.mem_inter.1 ha
        obtain ⟨z, hzs, hza⟩ := Finset.mem_image.1 haS
        refine Finset.mem_biUnion.2 ⟨z, hzs, ?_⟩
        have hrab : r a b := (Finset.mem_filter.1 haf).2
        exact Finset.mem_filter.2 ⟨hb, by rw [hza]; exact hrab⟩
      have h1 : s.card ≤ A.card := hcardsub s
      have h2 : B.card ≤ (s.biUnion t).card := Finset.card_le_card hsub
      omega
  obtain ⟨f, hf1, hf2⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).1 hall
  refine ⟨fun a => if ha : a ∈ A then f ⟨a, ha⟩ else a, ?_, ?_, ?_⟩
  · intro a ha
    simp only [dif_pos ha]
    exact (Finset.mem_filter.1 (hf2 ⟨a, ha⟩)).1
  · intro a ha
    simp only [dif_pos ha]
    exact (Finset.mem_filter.1 (hf2 ⟨a, ha⟩)).2
  · intro a ha a' ha' heq
    simp only [Finset.mem_coe] at ha ha'
    simp only [dif_pos ha, dif_pos ha'] at heq
    exact congrArg Subtype.val (hf1 heq)

end BKLO
