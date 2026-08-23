import PaperII.CompleteSplit

/-!
# Paper II — Edge count of the complete-split graph `S_{p,q}` (ledger, S1)

Target: `|E(S_{p,q})| = C(p,2) + p*q`.

The two degree lemmas are the intended route (sum-of-degrees), but any correct proof is fine.
Clique-side vertices have degree `(p-1) + q`; independent-side vertices have degree `p`.
Sum of degrees `= p*((p-1)+q) + q*p = p*(p-1) + 2*p*q`, so `|E| = p*(p-1)/2 + p*q = C(p,2)+p*q`.
-/

open scoped BigOperators

namespace PaperII

/-- Degree of a clique-side vertex in `S_{p,q}`. -/
theorem completeSplit_degree_inl (p q : ℕ) (a : Fin p) :
    (completeSplit p q).degree (Sum.inl a) = (p - 1) + q := by
  rw [ SimpleGraph.degree ];
  rw [ show ( completeSplit p q ).neighborFinset ( Sum.inl a ) = Finset.image ( fun b : Fin p => Sum.inl b ) ( Finset.univ.erase a ) ∪ Finset.image ( fun b : Fin q => Sum.inr b ) Finset.univ from ?_ ];
  · rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
    simp +decide [ Finset.disjoint_left ];
  · ext x; simp [completeSplit];
    cases x <;> simp +decide [ csRel ];
    grind

/-- Degree of an independent-side vertex in `S_{p,q}`. -/
theorem completeSplit_degree_inr (p q : ℕ) (b : Fin q) :
    (completeSplit p q).degree (Sum.inr b) = p := by
  rw [ SimpleGraph.degree ];
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => Sum.inl ⟨ i, hi ⟩; all_goals aesop

/-- Ledger edge count: `|E(S_{p,q})| = C(p,2) + p*q`. -/
theorem completeSplit_card_edgeFinset (p q : ℕ) :
    (completeSplit p q).edgeFinset.card = p.choose 2 + p * q := by
  have h_sum_degrees : ∑ v : Fin p ⊕ Fin q, (completeSplit p q).degree v = 2 * (completeSplit p q).edgeFinset.card := by
    rw [ SimpleGraph.sum_degrees_eq_twice_card_edges ];
  simp_all +decide [ completeSplit_degree_inl, completeSplit_degree_inr ];
  rw [ Nat.c