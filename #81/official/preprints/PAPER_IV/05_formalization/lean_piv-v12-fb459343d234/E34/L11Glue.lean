import E34.L11Subdiv

/-!
# E34 — Lemma 11: gluing the sections (the chordal graph `F`)

Given a colouring `ψ` whose colours are subtrees of `Γ`, and for every section `c` a rank
function `rk c` (a chain graph on `Lc c × Rc c`, Theorem 5(iii)), the subtree `gS u` of the
subdivided tree consists of
* the nodes of `ψ u`;
* all subdivision nodes of the edges `c → par c` with `c, par c ∈ ψ u`;
* the nodes `(c, j)` with `j ≤ rk c u` if `u ∈ Lc c`;
* the nodes `(c, j)` with `rk c u + 1 ≤ j` if `u ∈ Rc c`.

`gS_isSub`: each `gS u` is a subtree; hence `glueGraph` (the intersection graph) is chordal.
-/

namespace E34

open Finset

open scoped Classical

variable {n K : ℕ}

section Glue

variable (Γ : RTree K) (ψ : Fin n → Finset (Fin K)) (rk : Fin K → Fin n → ℕ) (B : ℕ)

/-- Membership in the glued subtree of `u`. -/
def memT (u : Fin n) : SNode K B → Prop
  | Sum.inl g => g ∈ ψ u
  | Sum.inr (c, j) => (c ∈ ψ u ∧ Γ.par c ∈ ψ u) ∨ (c ∈ ψ u ∧ Γ.par c ∉ ψ u ∧ j.val ≤ rk c u) ∨
      (c ∉ ψ u ∧ Γ.par c ∈ ψ u ∧ rk c u + 1 ≤ j.val)

/-- The glued subtree of `u`. -/
noncomputable def gS (u : Fin n) : Finset (SNode K B) := univ.filter (memT Γ ψ rk B u)

theorem mem_gS_inl (u : Fin n) (g : Fin K) : Sum.inl g ∈ gS Γ ψ rk B u ↔ g ∈ ψ u := by
  simp [gS, memT]

theorem mem_gS_inr (u : Fin n) (c : Fin K) (j : Fin (B + 1)) :
    Sum.inr (c, j) ∈ gS Γ ψ rk B u ↔ ((c ∈ ψ u ∧ Γ.par c ∈ ψ u) ∨
      (c ∈ ψ u ∧ Γ.par c ∉ ψ u ∧ j.val ≤ rk c u) ∨
      (c ∉ ψ u ∧ Γ.par c ∈ ψ u ∧ rk c u + 1 ≤ j.val)) := by
  simp only [gS, mem_filter, mem_univ, true_and]; rfl

theorem sPar_inr (c : Fin K) (j : Fin (B + 1)) :
    Γ.sPar B (Sum.inr (c, j)) = if h : j.val < B then Sum.inr (c, ⟨j.val + 1, by omega⟩)
      else Sum.inl (Γ.par c) := rfl

/-- Closure of the full and right parts under the parent map. -/
theorem sPar_mem_of_par_mem (u : Fin n) (c : Fin K) (j : Fin (B + 1))
    (hj : Sum.inr (c, j) ∈ gS Γ ψ rk B u) (hp : Γ.par c ∈ ψ u) :
    Γ.sPar B (Sum.inr (c, j)) ∈ gS Γ ψ rk B u := by
  rw [sPar_inr]
  split_ifs with hjB
  · rw [mem_gS_inr] at hj ⊢
    rcases hj with h | h | h
    · exact Or.inl h
    · exact absurd hp h.2.1
    · exact Or.inr (Or.inr ⟨h.1, h.2.1, by simp only; omega⟩)
  · rw [mem_gS_inl]; exact hp

/-- **Each glued set is a subtree** of the subdivided tree. -/
theorem gS_isSub (hB : ∀ c u, rk c u ≤ B) (u : Fin n) (hu : Γ.IsSub (ψ u)) :
    (Γ.subdiv B).IsSub ((gS Γ ψ rk B u).map (Fintype.equivFin _).toEmbedding) := by
  obtain ⟨τ, hτ⟩ := hu
  have F1 : ∀ g ∈ ψ u, g ≠ τ → Γ.par g ∈ ψ u := fun g hg hne => by
    rcases Γ.anc_step (hτ.2 g hg).1 with h | h
    · exact absurd h.symm hne
    · exact hτ.mem_of_between hg (Γ.anc_par g) h
  have F2 : ∀ g ∈ ψ u, Γ.h τ ≤ Γ.h g := fun g hg => Γ.h_le_of_anc (hτ.2 g hg).1
  have F2' : ∀ g ∈ ψ u, g ≠ τ → Γ.h τ < Γ.h g :=
    fun g hg hne => Γ.h_lt_of_anc (hτ.2 g hg).1 (Ne.symm hne)
  have F3 : ∀ c ∈ ψ u, Γ.par c ∉ ψ u → c = τ := fun c hc hp => by
    by_contra h; exact hp (F1 c hc h)
  -- the height of an inr node whose edge top is in `ψ u`
  have Hinr : ∀ (c : Fin K) (j : Fin (B + 1)), Γ.par c ∈ ψ u →
      (B + 2) * Γ.h τ < Γ.sH B (Sum.inr (c, j)) := by
    intro c j hp
    have := Nat.mul_le_mul_left (B + 2) (F2 _ hp)
    simp only [RTree.sH]; omega
  by_cases hA : Γ.par τ ∈ ψ u
  · have hτr : τ = Γ.root := by
      have h1 : Γ.Anc τ (Γ.par τ) := (hτ.2 _ hA).1
      have h2 : Γ.Anc (Γ.par τ) τ := Γ.anc_par τ
      exact (Γ.par_eq_self_iff τ).1 (Γ.anc_antisymm h1 h2)
    refine Γ.subdiv_isSub B _ (Sum.inl τ) ((mem_gS_inl Γ ψ rk B u τ).2 hτ.1) ?_
    intro a ha hat
    rcases a with g | ⟨c, j⟩
    · rw [mem_gS_inl] at ha
      have hgτ : g ≠ τ := fun h => hat (h ▸ rfl)
      have hgr : g ≠ Γ.root := hτr ▸ hgτ
      refine ⟨?_, ?_⟩
      · simp only [RTree.sPar, hgr, if_false]
        rw [mem_gS_inr]; exact Or.inl ⟨ha, F1 g ha hgτ⟩
      · simp only [RTree.sH]
        exact Nat.mul_lt_mul_of_pos_left (F2' g ha hgτ) (by omega)
    · have hp : Γ.par c ∈ ψ u := by
        have ha' := (mem_gS_inr Γ ψ rk B u c j).1 ha
        rcases ha' with h | h | h
        · exact h.2
        · exact absurd (F3 c h.1 h.2.1 ▸ hA) h.2.1
        · exact h.2.1
      exact ⟨sPar_mem_of_par_mem Γ ψ rk B u c j ha hp, by
        have := Hinr c j hp; simp only [RTree.sH] at this ⊢; omega⟩
  · have hτr : τ ≠ Γ.root := by
      intro h; apply hA; rw [h, Γ.par_root]; exact h ▸ hτ.1
    set t : SNode K B := Sum.inr (τ, ⟨rk τ u, Nat.lt_succ_of_le (hB τ u)⟩) with ht_def
    have ht : t ∈ gS Γ ψ rk B u := by
      rw [ht_def, mem_gS_inr]; exact Or.inr (Or.inl ⟨hτ.1, hA, le_refl _⟩)
    have htH : Γ.sH B t < (B + 2) * Γ.h τ := by
      have h1 := Γ.h_par τ hτr
      have : (B + 2) * (Γ.h (Γ.par τ) + 1) ≤ (B + 2) * Γ.h τ := Nat.mul_le_mul_left _ h1
      rw [Nat.mul_add, Nat.mul_one] at this
      simp only [ht_def, RTree.sH]; omega
    refine Γ.subdiv_isSub B _ t ht ?_
    intro a ha hat
    rcases a with g | ⟨c, j⟩
    · rw [mem_gS_inl] at ha
      have hgr : g ≠ Γ.root := by
        rintro rfl; exact hτr (Γ.anc_antisymm (Γ.anc_root τ) (hτ.2 _ ha).1)
      refine ⟨?_, ?_⟩
      · simp only [RTree.sPar, hgr, if_false]
        rw [mem_gS_inr]
        by_cases hpg : Γ.par g ∈ ψ u
        · exact Or.inl ⟨ha, hpg⟩
        · exact Or.inr (Or.inl ⟨ha, hpg, Nat.zero_le _⟩)
      · exact htH.trans_le (by simp only [RTree.sH]; exact Nat.mul_le_mul_left _ (F2 g ha))
    · have ha' := (mem_gS_inr Γ ψ rk B u c j).1 ha
      rcases ha' with h | h | h
      · exact ⟨sPar_mem_of_par_mem Γ ψ rk B u c j ha h.2, (htH.trans (Hinr c j h.2))⟩
      · have hcτ : c = τ := F3 c h.1 h.2.1
        subst hcτ
        have hjne : j.val ≠ rk c u := by
          intro hj; apply hat; rw [ht_def]; congr; exact Fin.ext hj
        have hjlt : j.val < rk c u := lt_of_le_of_ne h.2.2 hjne
        refine ⟨?_, ?_⟩
        · rw [sPar_inr, dif_pos (lt_of_lt_of_le hjlt (hB c u)), mem_gS_inr]
          exact Or.inr (Or.inl ⟨h.1, h.2.1, by simp only; omega⟩)
        · simp only [ht_def, RTree.sH]
          have := hB c u
          omega
      · exact ⟨sPar_mem_of_par_mem Γ ψ rk B u c j ha h.2.1, (htH.trans (Hinr c j h.2.1))⟩

/-- The intersection graph of the glued subtrees. -/
noncomputable def glueGraph : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (gS Γ ψ rk B u ∩ gS Γ ψ rk B v).Nonempty
  symm u v h := ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- **The glued graph is chordal.** -/
theorem glueGraph_chordal (hB : ∀ c u, rk c u ≤ B) (hψ : ∀ u, Γ.IsSub (ψ u)) :
    AlonShapira.IsChordal (glueGraph Γ ψ rk B) := by
  refine (Γ.subdiv B).isChordal_of_subtrees _
    (fun u => (gS Γ ψ rk B u).map (Fintype.equivFin _).toEmbedding)
    (fun u => gS_isSub Γ ψ rk B hB u (hψ u)) (fun u v huv => ?_)
  rw [← map_inter, map_nonempty]
  exact ⟨fun h => h.2, fun h => ⟨huv, h⟩⟩

end Glue

end E34
