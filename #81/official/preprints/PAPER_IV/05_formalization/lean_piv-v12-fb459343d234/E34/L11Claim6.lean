import E34.L11Glue
import E34.CycleCount

/-!
# E34 — Lemma 11, Claim 6: the glued chordal graph is close to `G`

* `switch_edge` — two disjoint subtrees whose union contains the path between them are joined
  by an edge `c → par c` of `Γ` with `c` in one and `par c` in the other.
* `claim6` — for a non-conflicting pair `uv` that is not a mismatch of any section,
  `glueGraph` and `G` agree on `uv`.
* `editDist_glue_le` — `dist(G, glueGraph) ≤ conf ψ + Σ_c chainMis_c`.
-/

namespace E34

open Finset

open scoped Classical

variable {n K : ℕ}

/-- One side of `switch_edge`. -/
theorem switch_edge_aux (Γ : RTree K) {A B : Finset (Fin K)} {tB : Fin K} (hB : Γ.IsSubAt B tB)
    (hAB : Disjoint A B) {a b : Fin K} (hb : b ∈ B)
    (hpath : pathSet Γ a b ⊆ A ∪ B) (hl : Γ.lca a b ∈ A) :
    tB ∈ B ∧ tB ∉ A ∧ Γ.par tB ∈ A ∧ Γ.par tB ∉ B := by
  set l := Γ.lca a b
  have htb : Γ.Anc tB b := (hB.2 b hb).1
  have hlb : Γ.Anc l b := Γ.lca_anc_right a b
  have htA : tB ∉ A := fun h => disjoint_left.1 hAB h hB.1
  rcases Γ.anc_chain htb hlb with h | h
  · exact absurd (hB.mem_of_between hb hlb h) (disjoint_left.1 hAB hl)
  · have hlt : l ≠ tB := fun e => htA (e ▸ hl)
    have hlp : Γ.Anc l (Γ.par tB) := (Γ.anc_step h).resolve_left hlt
    have htr : tB ≠ Γ.root := by
      intro e; apply hlt
      rw [e]; exact Γ.anc_antisymm (Γ.anc_root l) (e ▸ h)
    have hpB : Γ.par tB ∉ B := by
      intro hp
      have := Γ.anc_antisymm (hB.2 _ hp).1 (Γ.anc_par tB)
      exact htr ((Γ.par_eq_self_iff tB).1 this)
    have hpp : Γ.par tB ∈ pathSet Γ a b := by
      rw [pathSet, mem_filter]
      exact ⟨mem_univ _, (Γ.onPath_iff _ _ _).2 ⟨hlp, Or.inr (Γ.anc_trans (Γ.anc_par tB) htb)⟩⟩
    rcases mem_union.1 (hpath hpp) with h' | h'
    · exact ⟨hB.1, htA, h', hpB⟩
    · exact absurd h' hpB

/-- **Switching edge** between two disjoint subtrees covering a path. -/
theorem switch_edge (Γ : RTree K) {A B : Finset (Fin K)} (hA : Γ.IsSub A) (hB : Γ.IsSub B)
    (hAB : Disjoint A B) {a b : Fin K} (ha : a ∈ A) (hb : b ∈ B)
    (hpath : pathSet Γ a b ⊆ A ∪ B) :
    ∃ c, (c ∈ B ∧ c ∉ A ∧ Γ.par c ∈ A ∧ Γ.par c ∉ B) ∨
      (c ∈ A ∧ c ∉ B ∧ Γ.par c ∈ B ∧ Γ.par c ∉ A) := by
  have hl : Γ.lca a b ∈ A ∪ B := hpath (by
    rw [pathSet, mem_filter]
    exact ⟨mem_univ _, (Γ.onPath_iff _ _ _).2 ⟨Γ.anc_refl _, Or.inl (Γ.lca_anc_left a b)⟩⟩)
  obtain ⟨tA, hA⟩ := hA
  obtain ⟨tB, hB⟩ := hB
  rcases mem_union.1 hl with h | h
  · exact ⟨tB, Or.inl (switch_edge_aux Γ hB hAB hb hpath h)⟩
  · rw [pathSet_comm, union_comm] at hpath
    rw [Γ.lca_comm] at h
    exact ⟨tA, Or.inr (switch_edge_aux Γ hA hAB.symm ha hpath h)⟩

section Claim6

variable (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
  (ψ : Fin n → Finset (Fin K)) (rk : Fin K → Fin n → ℕ) (B : ℕ)

theorem mem_Lc (c : Fin K) (u : Fin n) : u ∈ Lc Γ ψ c ↔ c ∈ ψ u ∧ Γ.par c ∉ ψ u := by
  simp [Lc]

theorem mem_Rc (c : Fin K) (u : Fin n) : u ∈ Rc Γ ψ c ↔ c ∉ ψ u ∧ Γ.par c ∈ ψ u := by
  simp [Rc]

/-- A mismatch of the pair `(u, v)` in the section `c` (with `u` on the left). -/
def Mis (c : Fin K) (u v : Fin n) : Prop :=
  u ∈ Lc Γ ψ c ∧ v ∈ Rc Γ ψ c ∧ ¬ (G.Adj u v ↔ rk c v < rk c u)

/-- **Claim 6 of Lemma 11.** -/
theorem claim6 (hB : ∀ c u, rk c u ≤ B) (hψ : ∀ v, ψ v ∈ (pinProblem Γ x G).L v)
    {u v : Fin n} (huv : u ≠ v) (hc : (pinProblem Γ x G).compat u (ψ u) v (ψ v))
    (h1 : ∀ c, ¬ Mis Γ G ψ rk c u v) (h2 : ∀ c, ¬ Mis Γ G ψ rk c v u) :
    (glueGraph Γ ψ rk B).Adj u v ↔ G.Adj u v := by
  have hsub : ∀ w, Γ.IsSub (ψ w) ∧ x w ∈ ψ w := fun w => by
    have := hψ w
    simp only [pinProblem, mem_filter, mem_univ, true_and] at this
    exact this
  rw [pinProblem_compat_iff] at hc
  constructor
  · rintro ⟨-, z, hz⟩
    rw [mem_inter] at hz
    by_contra hG
    have hdis := hc.2 hG
    rcases z with g | ⟨c, j⟩
    · rw [mem_gS_inl, mem_gS_inl] at hz
      exact disjoint_left.1 hdis hz.1 hz.2
    · rw [mem_gS_inr, mem_gS_inr] at hz
      obtain ⟨hu, hv⟩ := hz
      have hdc : c ∈ ψ u → c ∉ ψ v := fun h => disjoint_left.1 hdis h
      have hdp : Γ.par c ∈ ψ u → Γ.par c ∉ ψ v := fun h => disjoint_left.1 hdis h
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
      · exact hdc hu.1 hv.1
      · exact hdc hu.1 hv.1
      · exact hdp hu.2 hv.2.1
      · exact hdc hu.1 hv.1
      · exact hdc hu.1 hv.1
      · apply h1 c
        refine ⟨(mem_Lc Γ ψ c u).2 ⟨hu.1, hu.2.1⟩, (mem_Rc Γ ψ c v).2 ⟨hv.1, hv.2.1⟩, ?_⟩
        intro hiff
        exact hG (hiff.2 (by omega))
      · exact hdp hu.2.1 hv.2
      · apply h2 c
        refine ⟨(mem_Lc Γ ψ c v).2 ⟨hv.1, hv.2.1⟩, (mem_Rc Γ ψ c u).2 ⟨hu.1, hu.2.1⟩, ?_⟩
        intro hiff
        exact hG (G.adj_symm (hiff.2 (by omega)))
      · exact hdp hu.2.1 hv.2.1
  · intro hG
    refine ⟨huv, ?_⟩
    have hpath := hc.1 hG
    by_cases hne : (ψ u ∩ ψ v).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [mem_inter] at hg
      exact ⟨Sum.inl g, mem_inter.2 ⟨(mem_gS_inl Γ ψ rk B u g).2 hg.1,
        (mem_gS_inl Γ ψ rk B v g).2 hg.2⟩⟩
    · rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hne
      obtain ⟨c, hcase⟩ := switch_edge Γ (hsub u).1 (hsub v).1 hne (hsub u).2 (hsub v).2 hpath
      rcases hcase with ⟨hcv, hcu, hpu, hpv⟩ | ⟨hcu, hcv, hpv, hpu⟩
      · have hlt : rk c u < rk c v := by
          by_contra hle
          exact h2 c ⟨(mem_Lc Γ ψ c v).2 ⟨hcv, hpv⟩, (mem_Rc Γ ψ c u).2 ⟨hcu, hpu⟩,
            fun hiff => hle (hiff.1 (G.adj_symm hG))⟩
        refine ⟨Sum.inr (c, ⟨rk c v, Nat.lt_succ_of_le (hB c v)⟩), mem_inter.2 ⟨?_, ?_⟩⟩
        · rw [mem_gS_inr]; exact Or.inr (Or.inr ⟨hcu, hpu, by simp only; omega⟩)
        · rw [mem_gS_inr]; exact Or.inr (Or.inl ⟨hcv, hpv, le_refl _⟩)
      · have hlt : rk c v < rk c u := by
          by_contra hle
          exact h1 c ⟨(mem_Lc Γ ψ c u).2 ⟨hcu, hpu⟩, (mem_Rc Γ ψ c v).2 ⟨hcv, hpv⟩,
            fun hiff => hle (hiff.1 hG)⟩
        refine ⟨Sum.inr (c, ⟨rk c u, Nat.lt_succ_of_le (hB c u)⟩), mem_inter.2 ⟨?_, ?_⟩⟩
        · rw [mem_gS_inr]; exact Or.inr (Or.inl ⟨hcu, hpu, le_refl _⟩)
        · rw [mem_gS_inr]; exact Or.inr (Or.inr ⟨hcv, hpv, by simp only; omega⟩)

/-- The mismatch set of the section `c`. -/
noncomputable def misSet (c : Fin K) : Finset (Fin n × Fin n) :=
  ((Lc Γ ψ c ∩ univ) ×ˢ (Rc Γ ψ c ∩ univ)).filter
    (fun p => ¬ (G.Adj p.1 p.2 ↔ rk c p.2 < rk c p.1))

theorem card_misSet (c : Fin K) :
    (misSet Γ G ψ rk c).card = chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ (rk c) := rfl

theorem mem_misSet_of_mis {c : Fin K} {u v : Fin n} (h : Mis Γ G ψ rk c u v) :
    (u, v) ∈ misSet Γ G ψ rk c := by
  obtain ⟨hu, hv, hm⟩ := h
  exact mem_filter.2 ⟨mem_product.2 ⟨mem_inter.2 ⟨hu, mem_univ _⟩, mem_inter.2 ⟨hv, mem_univ _⟩⟩, hm⟩

/-- **Distance bound** for the glued graph. -/
theorem editDist_glue_le (hB : ∀ c u, rk c u ≤ B) (hψ : ∀ v, ψ v ∈ (pinProblem Γ x G).L v) :
    AlonShapira.editDist G (glueGraph Γ ψ rk B) ≤
      (pinProblem Γ x G).conf ψ + ∑ c, chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ (rk c) := by
  rw [editDist_eq_card]
  set F := glueGraph Γ ψ rk B
  have hsub : symmDiff G.edgeFinset F.edgeFinset ⊆
      (confSet (pinProblem Γ x G) ψ ∪ univ.biUnion (fun c => misSet Γ G ψ rk c)).image
        (fun p => Sym2.mk p) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
    have hdiff : ¬ (F.Adj u v ↔ G.Adj u v) := by
      simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      tauto
    have huv : u ≠ v := by
      rintro rfl; exact hdiff (iff_of_false (F.loopless.irrefl u) (G.loopless.irrefl u))
    rw [mem_image]
    by_cases hc : (pinProblem Γ x G).compat u (ψ u) v (ψ v)
    · by_cases h1 : ∀ c, ¬ Mis Γ G ψ rk c u v
      · by_cases h2 : ∀ c, ¬ Mis Γ G ψ rk c v u
        · exact absurd (claim6 Γ x G ψ rk B hB hψ huv hc h1 h2) hdiff
        · push_neg at h2
          obtain ⟨c, hc2⟩ := h2
          exact ⟨(v, u), mem_union_right _ (mem_biUnion.2 ⟨c, mem_univ _,
            mem_misSet_of_mis Γ G ψ rk hc2⟩), Sym2.eq_swap⟩
      · push_neg at h1
        obtain ⟨c, hc1⟩ := h1
        exact ⟨(u, v), mem_union_right _ (mem_biUnion.2 ⟨c, mem_univ _,
          mem_misSet_of_mis Γ G ψ rk hc1⟩), rfl⟩
    · exact ⟨(u, v), mem_union_left _ (mem_filter.2 ⟨mem_univ _, huv, hc⟩), rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
  rw [card_confSet]
  refine Nat.add_le_add_left (card_biUnion_le.trans (le_of_eq ?_)) _
  rfl

end Claim6

end E34
