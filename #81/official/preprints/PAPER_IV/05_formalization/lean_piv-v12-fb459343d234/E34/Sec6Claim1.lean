import E34.NearlySimplicial

/-!
# E34 — §6 of arXiv:1902.06135, Claim 1

With `δ = ε²/256` (our Lemma 3 has constant `8`, so `8 √δ = ε/2`), let
`X = {u : p_G(u) ≤ (δ/2) n²}` and let `H = padGraph G X` be the graph equal to `G` on `Y = Xᶜ`
in which every vertex of `X` is universal.  **Claim 1**: if `G` is `ε`-far from chordal then
every chordal `F` satisfies `(δ/2) n² < editDist H F`.
-/

namespace E34

open Finset

open scoped Classical

variable {n : ℕ}

/-- `X = {u : p_G(u) ≤ (δ/2) n²}`. -/
noncomputable def lowSet (G : SimpleGraph (Fin n)) (δ : ℝ) : Finset (Fin n) :=
  univ.filter (fun u => (pG G u : ℝ) ≤ δ / 2 * (n : ℝ) ^ 2)

/-- `G` on `Xᶜ`, every vertex of `X` universal. -/
def padGraph (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (u ∈ X ∨ v ∈ X ∨ G.Adj u v)
  symm := by
    intro u v ⟨h1, h2⟩
    refine ⟨Ne.symm h1, ?_⟩
    rcases h2 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h.symm)
  loopless := ⟨fun u h => h.1 rfl⟩

/-- `G` outside `Y × Y`, `F` inside. -/
def mixGraph (G F : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := if u ∈ X ∨ v ∈ X then G.Adj u v else F.Adj u v
  symm := by
    intro u v h
    by_cases hu : u ∈ X ∨ v ∈ X
    · rw [if_pos hu] at h; rw [if_pos (Or.comm.1 hu)]; exact h.symm
    · rw [if_neg hu] at h; rw [if_neg (fun h' => hu (Or.comm.1 h'))]; exact h.symm
  loopless := ⟨fun u h => by
    by_cases hu : u ∈ X ∨ u ∈ X
    · rw [if_pos hu] at h; exact G.loopless.irrefl u h
    · rw [if_neg hu] at h; exact F.loopless.irrefl u h⟩

theorem mixGraph_adj_of_mem {G F : SimpleGraph (Fin n)} {X : Finset (Fin n)} {u : Fin n}
    (hu : u ∈ X) (v : Fin n) : (mixGraph G F X).Adj u v ↔ G.Adj u v := by
  simp only [mixGraph, hu, true_or, if_true]

theorem mixGraph_adj_of_not_mem {G F : SimpleGraph (Fin n)} {X : Finset (Fin n)} {u v : Fin n}
    (hu : u ∉ X) (hv : v ∉ X) : (mixGraph G F X).Adj u v ↔ F.Adj u v := by
  simp only [mixGraph, hu, hv, or_self, if_false]

/-- Changing edges not at `x` raises `p(x)` by at most the edit distance. -/
theorem pG_le_add_editDist (G G' : SimpleGraph (Fin n)) (x : Fin n)
    (hx : ∀ v, G'.Adj x v ↔ G.Adj x v) :
    pG G' x ≤ pG G x + AlonShapira.editDist G G' := by
  rw [editDist_eq_card]
  unfold pG
  set A := (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj x p.1 ∧ G.Adj x p.2 ∧ ¬ G.Adj p.1 p.2)
  set B := ((univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ ¬ G'.Adj p.1 p.2))
  have hsub : (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ G'.Adj x p.1 ∧ G'.Adj x p.2 ∧ ¬ G'.Adj p.1 p.2) ⊆ A ∪ B := by
    intro p hp
    simp only [mem_filter, mem_product, mem_univ, true_and, hx] at hp
    simp only [A, B, mem_union, mem_filter, mem_product, mem_univ, true_and]
    by_cases hG : G.Adj p.1 p.2
    · exact Or.inr ⟨hp.1, hG, hp.2.2.2⟩
    · exact Or.inl ⟨hp.1, hp.2.1, hp.2.2.1, hG⟩
  have hB : B.card ≤ (symmDiff G.edgeFinset G'.edgeFinset).card := by
    refine card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [B, coe_filter, mem_product, mem_univ, true_and, Set.mem_setOf_eq] at hp
      simp only [coe_symmDiff, Set.mem_symmDiff, mem_coe, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact Or.inl ⟨hp.2.1, hp.2.2⟩
    · intro p hp p' hp' he
      simp only [B, coe_filter, mem_product, mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
      simp only [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso; rw [h1, h2] at hp; exact lt_asymm hp.1 hp'.1
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hB _))

theorem editDist_mix_le (G F : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    AlonShapira.editDist G (mixGraph G F X) ≤ AlonShapira.editDist (padGraph G X) F := by
  rw [editDist_eq_card, editDist_eq_card]
  refine card_le_card ?_
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    simp only [mem_symmDiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
    by_cases hX : u ∈ X ∨ v ∈ X
    · have : (mixGraph G F X).Adj u v ↔ G.Adj u v := by simp only [mixGraph, hX, if_true]
      rw [this] at he; tauto
    · push_neg at hX
      have h1 : (mixGraph G F X).Adj u v ↔ F.Adj u v := mixGraph_adj_of_not_mem hX.1 hX.2
      have h2 : (padGraph G X).Adj u v ↔ G.Adj u v := by
        simp only [padGraph, hX.1, hX.2, false_or]
        exact ⟨fun h => h.2, fun h => ⟨G.ne_of_adj h, h⟩⟩
      rw [h1] at he; rw [h2]; exact he

/-- **Claim 1** of §6. -/
theorem sec6_claim1 (G : SimpleGraph (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε * (n : ℝ) ^ 2 ≤ (AlonShapira.editDist G F : ℝ)) :
    ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε ^ 2 / 256 / 2 * (n : ℝ) ^ 2 <
        (AlonShapira.editDist (padGraph G (lowSet G (ε ^ 2 / 256))) F : ℝ) := by
  intro F hF
  set δ := ε ^ 2 / 256 with hδ
  set X := lowSet G δ
  by_contra hcon
  push_neg at hcon
  set G' := mixGraph G F X
  have hd1 : (AlonShapira.editDist G G' : ℝ) ≤ δ / 2 * (n : ℝ) ^ 2 :=
    le_trans (by exact_mod_cast editDist_mix_le G F X) hcon
  have hY : AlonShapira.IsChordal (G'.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n))) := by
    have e : G'.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n)) =
        F.induce ((Xᶜ : Finset (Fin n)) : Set (Fin n)) := by
      ext ⟨u, hu⟩ ⟨v, hv⟩
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
      have hu' : u ∉ X := by simpa using hu
      have hv' : v ∉ X := by simpa using hv
      exact mixGraph_adj_of_not_mem hu' hv'
    rw [e]; exact hF.induce _
  have hp : ∀ x ∈ X, (pG G' x : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
    intro x hx
    have h1 := pG_le_add_editDist G G' x (fun v => mixGraph_adj_of_mem hx v)
    have h2 : (pG G x : ℝ) ≤ δ / 2 * (n : ℝ) ^ 2 := (mem_filter.1 hx).2
    have h3 : (pG G' x : ℝ) ≤ pG G x + AlonShapira.editDist G G' := by exact_mod_cast h1
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨H, hH, hdH, -⟩ := lemma3 G' X hY δ hδ0 hp
  have hsq : Real.sqrt δ = ε / 16 := by
    rw [hδ, show ε ^ 2 / 256 = (ε / 16) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [hsq] at hdH
  have htri := asEditDist_triangle G G' H
  have htri' : (AlonShapira.editDist G H : ℝ) ≤
      AlonShapira.editDist G G' + AlonShapira.editDist G' H := by exact_mod_cast htri
  have hfH := hfar H hH
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : δ / 2 < ε / 2 := by rw [hδ]; nlinarith
  nlinarith

end E34
