import PaperIV.FarRounding

/-! Literal adapter from the project's mixed dual to signed edge weights.
This is the entry point for the star argument of Okechukwu, Lemma 3.1, and
its proposed retained-charge refinement. It does NOT yet sum an elimination
sequence or establish the proposed refined global fractional inequality.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def signedPrice (y : DualCover G ℚ) (e : Sym2 V) : ℚ := 1-y.price e

theorem signedPrice_le_one (y : DualCover G ℚ) (e : Sym2 V) :
    signedPrice y e ≤ 1 := by
  dsimp [signedPrice]
  linarith [y.price_nonneg e]

theorem signed_item_sum_le_one (y : DualCover G ℚ) (K : Finset V)
    (hK : K ∈ items G) : ∑ e ∈ pairs K, signedPrice y e ≤ 1 := by
  have hc := y.covers K hK
  simp only [signedPrice, sum_sub_distrib, sum_const, nsmul_eq_mul,
    mul_one, card_pairs]
  unfold gainF at hc
  linarith

theorem signed_value_eq (y : DualCover G ℚ) :
    ∑ e ∈ G.edgeFinset, signedPrice y e = (G.edgeFinset.card : ℚ)-y.value := by
  simp [signedPrice, sum_sub_distrib, DualCover.value]

theorem exists_certified_signed_cover {w : ℚ} (hw : CertifiedFractionalOptimum G w) :
    ∃ y : DualCover G ℚ, (∑ e ∈ G.edgeFinset, signedPrice y e) =
      (G.edgeFinset.card : ℚ)-w := by
  obtain ⟨_,y,_,hy⟩ := hw
  exact ⟨y,by rw [signed_value_eq,hy]⟩

/-- Maximum is taken over every vertex and every real clique in its neighborhood.
The empty clique makes the maximum nonnegative; no positivity assumption on
the individual signed prices is introduced. -/
theorem exists_maximum_signed_star [Nonempty V] (y : DualCover G ℚ) :
    ∃ v : V, ∃ C : Finset V, G.IsClique (C : Set V) ∧
      (∀ u ∈ C, G.Adj v u) ∧
      0 ≤ ∑ u ∈ C, signedPrice y s(v,u) ∧
      (∑ u ∈ C, signedPrice y s(v,u)) ≤ (C.card : ℚ) ∧
      ∀ (v' : V) (C' : Finset V), G.IsClique (C' : Set V) →
        (∀ u ∈ C', G.Adj v' u) →
        (∑ u ∈ C', signedPrice y s(v',u)) ≤ ∑ u ∈ C, signedPrice y s(v,u) := by
  classical
  let F : Finset (V × Finset V) := univ.filter (fun p =>
    G.IsClique (p.2 : Set V) ∧ ∀ u ∈ p.2, G.Adj p.1 u)
  let f : V × Finset V → ℚ := fun p => ∑ u ∈ p.2, signedPrice y s(p.1,u)
  let v0 : V := Classical.arbitrary V
  have hempty : (v0,∅) ∈ F := by simp [F]
  obtain ⟨p,hp,hmax⟩ := exists_max_image F f ⟨(v0,∅),hempty⟩
  have hp' : G.IsClique (p.2 : Set V) ∧ ∀ u ∈ p.2, G.Adj p.1 u :=
    (mem_filter.mp hp).2
  refine ⟨p.1,p.2,hp'.1,hp'.2,?_,?_,?_⟩
  · have h := hmax (v0,∅) hempty
    simpa [f] using h
  · calc
      (∑ u ∈ p.2, signedPrice y s(p.1,u)) ≤ ∑ _u ∈ p.2, (1 : ℚ) :=
        sum_le_sum (fun u _ => signedPrice_le_one y _)
      _ = (p.2.card : ℚ) := by simp
  · intro v' C' hC' hv'
    exact hmax (v',C') (by simp only [F,mem_filter,mem_univ,true_and]; exact ⟨hC',hv'⟩)

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.signed_item_sum_le_one
#print axioms PaperIV.SublinearResearch.exists_certified_signed_cover
#print axioms PaperIV.SublinearResearch.exists_maximum_signed_star
