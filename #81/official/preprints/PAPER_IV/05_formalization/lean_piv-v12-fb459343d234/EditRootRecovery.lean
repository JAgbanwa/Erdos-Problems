import RootedCliqueRecovery
import PaperIV.EditRouteLocalization

/-! Recover an actual clique of G from a clique of a nearby graph H.
The error is additive in the rooted defect s, not multiplied by sqrt(s).
All edit resources below are literal deleted edges, counted without orientation.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.RootedSimplicialDefect

theorem ordNE_le_twice_deleted {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (A : Finset (Fin n))
    (hA : H.IsClique (A : Set (Fin n))) :
    E34.ordNE G A ≤ 2 * (H.edgeFinset \ G.edgeFinset).card := by
  classical
  let f : Fin n × Fin n → Sym2 (Fin n) × Bool :=
    fun p => (s(p.1,p.2), decide (p.1 < p.2))
  have hc : E34.ordNE G A ≤
      ((H.edgeFinset \ G.edgeFinset) ×ˢ (univ : Finset Bool)).card := by
    apply card_le_card_of_injOn f
    · intro p hp
      simp only [mem_coe, E34.ordNE, mem_filter, mem_product] at hp
      have hh : H.Adj p.1 p.2 := hA hp.1.1 hp.1.2 hp.2.1
      simp only [mem_coe, mem_product, mem_sdiff, mem_univ, and_true,
        f, SimpleGraph.mem_edgeFinset]
      exact ⟨hh, hp.2.2⟩
    · intro p hp q hq hpq
      have he := congrArg Prod.fst hpq
      have ho := congrArg Prod.snd hpq
      change s(p.1,p.2) = s(q.1,q.2) at he
      change decide (p.1 < p.2) = decide (q.1 < q.2) at ho
      have ho' : (p.1 < p.2) ↔ (q.1 < q.2) := by simpa using ho
      simp only [mem_coe, mem_filter, mem_product] at hp hq
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Prod.ext h1 h2
      · have hne := hp.2.1
        rw [← h1, ← h2] at ho'
        omega
  simpa [card_product, Nat.mul_comm] using hc

theorem recover_clique_from_edit {n s : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hG : RootedDefectAt G s)
    (A : Finset (Fin n)) (hA : H.IsClique (A : Set (Fin n)))
    (u : ℚ) (hu : 0 ≤ u)
    (hedit : 2 * ((H.edgeFinset \ G.edgeFinset).card : ℚ) ≤ u^2) :
    ∃ R ⊆ A, G.IsClique (R : Set (Fin n)) ∧
      ((A \ R).card : ℚ) ≤ s + u := by
  classical
  obtain ⟨R,hRA,hR,hsq⟩ := exists_clique_additive_defect G hG A
  have hm := ordNE_le_twice_deleted G H A hA
  have hsqQ : ((A.card - R.card - s : ℕ) : ℚ)^2 ≤ u^2 := by
    have hc : ((A.card - R.card - s : ℕ) : ℚ)^2 ≤
        2 * ((H.edgeFinset \ G.edgeFinset).card : ℚ) := by
      exact_mod_cast hsq.trans hm
    exact hc.trans hedit
  have hdiff : ((A.card - R.card - s : ℕ) : ℚ) ≤ u := by
    nlinarith [sq_nonneg (((A.card - R.card - s : ℕ) : ℚ) - u)]
  have hnat : (A \ R).card ≤ (A.card - R.card - s) + s := by
    rw [card_sdiff_of_subset hRA]
    omega
  have hcast : ((A \ R).card : ℚ) ≤ ((A.card - R.card - s : ℕ) : ℚ) + s := by
    exact_mod_cast hnat
  exact ⟨R,hRA,hR,by linarith⟩

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.ordNE_le_twice_deleted
#print axioms PaperIV.SublinearResearch.recover_clique_from_edit
