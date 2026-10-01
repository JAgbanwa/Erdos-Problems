import E34.ChordalTools

/-!
Clique recovery with an additive rooted-defect loss.
This extends the dense chordal clique argument in E34.ChordalTools, rather than
using the matching bound whose error contains a factor sqrt(s+1).
The conclusion uses natural subtraction: the square is the positive part of
|D| - |C| - s. No stability or asymptotic assumption is needed.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.RootedSimplicialDefect

theorem exists_clique_additive_defect {n s : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : RootedDefectAt G s) (D : Finset (Fin n)) :
    ∃ C ⊆ D, G.IsClique (C : Set (Fin n)) ∧
      (D.card - C.card - s)^2 ≤ E34.ordNE G D := by
  classical
  induction D using Finset.strongInduction with
  | H D ih =>
    rcases D.eq_empty_or_nonempty with hD | hD
    · subst hD
      exact ⟨∅, empty_subset _, by simp, by simp⟩
    obtain ⟨v, hv, P, hPN, hPcl, hPcard⟩ :=
      hG D ∅ (empty_subset _) (by simp) (by simpa using hD)
    have hvD : v ∈ D := (mem_sdiff.mp hv).1
    obtain ⟨C', hCD, hCcl, hCb⟩ := ih (D.erase v) (erase_ssubset hvD)
    have hstep := E34.ordNE_erase_add G D v hvD
    let N := (D.erase v).filter (fun b => G.Adj v b)
    let y := ((D.erase v).filter (fun b => ¬ G.Adj v b)).card
    have hNeq : neighborsIn G D v = N := by
      ext b
      simp only [neighborsIn, N, mem_filter, mem_erase]
      constructor
      · rintro ⟨hb, ha⟩
        exact ⟨⟨fun he => G.ne_of_adj ha he.symm, hb⟩, ha⟩
      · exact fun h => ⟨h.1.2, h.2⟩
    have hNy : N.card + y = (D.erase v).card := card_filter_add_card_filter_not _
    have hDe : (D.erase v).card + 1 = D.card := card_erase_add_one hvD
    have hC'le : C'.card ≤ (D.erase v).card := card_le_card hCD
    have hNcard : N.card ≤ P.card + s := by simpa [hNeq] using hPcard
    have hvP : v ∉ P := by
      intro hp
      exact G.ne_of_adj (mem_filter.mp (hPN hp)).2 rfl
    have hPsub : insert v P ⊆ D := by
      intro b hb
      rcases mem_insert.mp hb with rfl | hb
      · exact hvD
      · exact (mem_filter.mp (hPN hb)).1
    have hPinsert : G.IsClique ((insert v P : Finset (Fin n)) : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [mem_coe, mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact (mem_filter.mp (hPN hb)).2
      · exact ((mem_filter.mp (hPN ha)).2).symm
      · exact hPcl ha hb hab
    let x := (D.erase v).card - C'.card - s
    by_cases hyx : y ≤ x
    · refine ⟨insert v P, hPsub, hPinsert, ?_⟩
      rw [card_insert_of_notMem hvP]
      have hdef : D.card - (P.card + 1) - s ≤ y := by omega
      have hsq := Nat.pow_le_pow_left (hdef.trans hyx) 2
      have hmono := E34.ordNE_mono G (erase_subset v D)
      exact hsq.trans (hCb.trans hmono)
    · refine ⟨C', hCD.trans (erase_subset v D), hCcl, ?_⟩
      have hdef : D.card - C'.card - s ≤ x + 1 := by dsimp [x]; omega
      have hsq := Nat.pow_le_pow_left hdef 2
      have hxy : x + 1 ≤ y := by omega
      change x^2 ≤ E34.ordNE G (D.erase v) at hCb
      change E34.ordNE G (D.erase v) + 2*y ≤ E34.ordNE G D at hstep
      nlinarith

theorem exists_clique_of_small_missing_mass {n s : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : RootedDefectAt G s) (D : Finset (Fin n))
    (ε : ℚ) (hε : 0 ≤ ε)
    (hm : (E34.ordNE G D : ℚ) ≤ (ε*(n : ℚ))^2) :
    ∃ C ⊆ D, G.IsClique (C : Set (Fin n)) ∧
      (D.card : ℚ) ≤ C.card + s + ε*n := by
  obtain ⟨C,hCD,hC,hb⟩ := exists_clique_additive_defect G hG D
  refine ⟨C,hCD,hC,?_⟩
  let t : ℕ := D.card-C.card-s
  have hsplit : D.card ≤ C.card+s+t := by dsimp [t]; omega
  have hsplitQ : (D.card : ℚ) ≤ C.card+s+t := by exact_mod_cast hsplit
  have hbQ : (t : ℚ)^2 ≤ E34.ordNE G D := by exact_mod_cast hb
  have hprod : 0 ≤ ε*(n : ℚ) := mul_nonneg hε (Nat.cast_nonneg n)
  have ht : (t : ℚ) ≤ ε*n := by nlinarith only [hbQ,hm,hprod]
  linarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.exists_clique_additive_defect
#print axioms PaperIV.SublinearResearch.exists_clique_of_small_missing_mass
