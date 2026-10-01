import E32.Transfer
import A4S1.MinDegreeAll

/-!
# E32 — low-degree deletion with edit tracking (step 2)

A vertex `v` of degree `< (1/3 − ε) n` is deleted: every order-`≤ 4` partition of `G − v` lifts to
`G` at the cost of `deg v` pieces (`lift_partition`), so the deficit drops by at least
`ε n − 1/3` (because `Q_s(n) − Q_s(n−1) = ⌊(n+s+1)/3⌋`), whereas re-inserting `v` as an exterior
vertex costs at most `n − 1` edits (`root_lift`). With `C ≥ 2/ε` this is paid by the drop.
The iteration is an induction on `n`, with the invariant `δ ≤ γ₀ n (n − N)`; a deletion from
`n = N` would give a negative deficit, contradicting Theorem C (`stable_of_minDeg`).
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic
open scoped symmDiff

/-- Every order-`≤ 4` clique partition of `G` has at least `t` pieces. -/
def LowerAt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℚ) : Prop :=
  ∀ Q : CliquePartition G, Q.OrderAtMost 4 → t ≤ (Q.size : ℚ)

variable {n : ℕ}

/-- The embedding `Fin n ↪ Fin (n+1)` missing `v`. -/
def skip (v : Fin (n + 1)) : Fin n ↪ Fin (n + 1) := ⟨v.succAbove, Fin.succAbove_right_injective⟩

@[simp] theorem skip_apply (v : Fin (n + 1)) (a : Fin n) : skip v a = v.succAbove a := rfl

theorem skip_ne (v : Fin (n + 1)) (a : Fin n) : skip v a ≠ v := Fin.succAbove_ne v a

theorem exists_skip_eq {v x : Fin (n + 1)} (h : x ≠ v) : ∃ a, skip v a = x :=
  Fin.exists_succAbove_eq h

/-- The graph `G − v`, on `Fin n`. -/
def deleteV (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) : SimpleGraph (Fin n) :=
  G.comap (skip v)

instance (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (v : Fin (n + 1)) :
    DecidableRel (deleteV G v).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj (skip v a) (skip v b)))

theorem deleteV_adj (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) (a b : Fin n) :
    (deleteV G v).Adj a b ↔ G.Adj (skip v a) (skip v b) := Iff.rfl

theorem rootedDefectAt_deleteV {s : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj]
    (v : Fin (n + 1)) (h : RootedDefectAt G s) : RootedDefectAt (deleteV G v) s :=
  A4S1.CriticalReduction.rootedDefectAt_comap G (skip v) (deleteV G v) (fun _ _ => Iff.rfl) h

/-- Lifting a partition of `G − v` to `G`. -/
theorem lift_partition (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (v : Fin (n + 1))
    (Q' : CliquePartition (deleteV G v)) (h4 : Q'.OrderAtMost 4) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ Q'.size + G.degree v := by
  classical
  have he : ∀ y, y ∉ ({v} : Finset (Fin (n + 1))) ↔ ∃ a, skip v a = y := by
    intro y
    rw [Finset.mem_singleton]
    constructor
    · intro hy; exact exists_skip_eq hy
    · rintro ⟨a, rfl⟩; exact skip_ne v a
  obtain ⟨Q0, hQ04, hQ0s⟩ := PaperIV.DefectApexStability.exists_push_partition G {v} (skip v) he
    (deleteV G v) (fun _ _ => Iff.rfl) Q' h4
  obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    G (PaperIV.DefectApexStability.avoidPart G {v})
    (PaperIV.DefectApexStability.avoidPart_le G {v}) Q0 hQ04
  rw [PaperIV.DefectApexStability.sdiff_avoidPart] at hPs
  have hT : (G.edgeFinset.filter (PaperIV.DefectApexStability.Touches {v})).card = G.degree v := by
    rw [A4S1.DefectOneAbsorbed.card_touch_singleton, SimpleGraph.card_neighborFinset_eq_degree]
  exact ⟨P, hP4, by omega⟩

theorem lift_adj_iff (v : Fin (n + 1)) (C D H : Finset (Fin n)) (a b : Fin n) :
    (defSplitGraph (C.map (skip v)) (D.map (skip v)) (insert v (H.map (skip v)))).Adj
        (skip v a) (skip v b) ↔ (defSplitGraph C D H).Adj a b := by
  simp only [defSplitGraph_adj_iff, mem_union, mem_insert, mem_map' (skip v),
    (skip v).injective.ne_iff, skip_ne, false_or]

/-- **Re-inserting the deleted vertex as an exterior vertex.** -/
theorem root_lift {s : ℕ} (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (v : Fin (n + 1))
    {C D H : Finset (Fin n)} (hR : IsDefectRoot (deleteV G v) s C D H) :
    IsDefectRoot G s (C.map (skip v)) (D.map (skip v)) (insert v (H.map (skip v))) ∧
      rootEdit G (C.map (skip v)) (D.map (skip v)) (insert v (H.map (skip v))) ≤
        rootEdit (deleteV G v) C D H + n := by
  classical
  have hvC : v ∉ C.map (skip v) := by
    intro h; obtain ⟨a, _, ha⟩ := mem_map.1 h; exact skip_ne v a ha
  have hvD : v ∉ D.map (skip v) := by
    intro h; obtain ⟨a, _, ha⟩ := mem_map.1 h; exact skip_ne v a ha
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (disjoint_map (skip v)).2 hR.disjCD
  · rw [disjoint_insert_right]; exact ⟨hvC, (disjoint_map (skip v)).2 hR.disjCH⟩
  · rw [disjoint_insert_right]; exact ⟨hvD, (disjoint_map (skip v)).2 hR.disjDH⟩
  · intro x
    by_cases hx : x = v
    · exact Or.inr (Or.inr (mem_insert.2 (Or.inl hx)))
    · obtain ⟨a, rfl⟩ := exists_skip_eq hx
      rcases hR.cover a with h | h | h
      · exact Or.inl (mem_map_of_mem _ h)
      · exact Or.inr (Or.inl (mem_map_of_mem _ h))
      · exact Or.inr (Or.inr (mem_insert_of_mem (mem_map_of_mem _ h)))
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_map.1 hy
    exact hR.clique ha hb (fun h => hxy (by rw [h]))
  · rw [card_map]; exact hR.card_def
  · rw [card_map]; exact hR.two_le
  · rw [card_insert_of_notMem (by
      intro h; obtain ⟨a, _, ha⟩ := mem_map.1 h; exact skip_ne v a ha), card_map, card_map]
    have := hR.core_le_hosts
    omega
  · -- edit tracking
    set E := defSplitGraph (C.map (skip v)) (D.map (skip v)) (insert v (H.map (skip v)))
    set E' := defSplitGraph C D H
    have hsub : G.edgeFinset ∆ E.edgeFinset ⊆
        ((deleteV G v).edgeFinset ∆ E'.edgeFinset).image (Sym2.map (skip v)) ∪
          (univ.erase v).image (fun x => s(v, x)) := by
      intro z hz
      induction z using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := by
          rcases mem_symmDiff.1 hz with ⟨h, _⟩ | ⟨h, _⟩
          · exact ((SimpleGraph.mem_edgeSet _).1 (SimpleGraph.mem_edgeFinset.1 h)).ne
          · exact ((SimpleGraph.mem_edgeSet _).1 (SimpleGraph.mem_edgeFinset.1 h)).ne
        by_cases ha : a = v
        · subst ha
          exact mem_union_right _ (mem_image.2 ⟨b, mem_erase.2 ⟨hab.symm, mem_univ _⟩, rfl⟩)
        by_cases hb : b = v
        · subst hb
          exact mem_union_right _ (mem_image.2 ⟨a, mem_erase.2 ⟨hab, mem_univ _⟩, Sym2.eq_swap⟩)
        obtain ⟨a', rfl⟩ := exists_skip_eq ha
        obtain ⟨b', rfl⟩ := exists_skip_eq hb
        refine mem_union_left _ (mem_image.2 ⟨s(a', b'), ?_, rfl⟩)
        have hG : s(skip v a', skip v b') ∈ G.edgeFinset ↔ s(a', b') ∈ (deleteV G v).edgeFinset := by
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, deleteV_adj]
        have hE : s(skip v a', skip v b') ∈ E.edgeFinset ↔ s(a', b') ∈ E'.edgeFinset := by
          simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, E, E']
          exact lift_adj_iff v C D H a' b'
        rw [mem_symmDiff] at hz ⊢
        rw [hG, hE] at hz
        exact hz
    have h1 := card_le_card hsub
    have h2 := card_union_le (((deleteV G v).edgeFinset ∆ E'.edgeFinset).image (Sym2.map (skip v)))
      ((univ.erase v).image (fun x => s(v, x)))
    have h3 := card_image_le (s := (deleteV G v).edgeFinset ∆ E'.edgeFinset) (f := Sym2.map (skip v))
    have h4 := card_image_le (s := univ.erase v) (f := fun x => s(v, x))
    have h5 : (univ.erase v).card = n := by rw [card_erase_of_mem (mem_univ _)]; simp
    unfold rootEdit PaperIV.EditMetric.editDist
    change (G.edgeFinset ∆ E.edgeFinset).card ≤ ((deleteV G v).edgeFinset ∆ E'.edgeFinset).card + n
    omega

end E32
