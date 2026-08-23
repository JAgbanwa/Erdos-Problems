/-
# Nibble — the triangle capacity of a vertex

A packing triangle through `v` uses up **two** covered graph edges at `v`, and distinct packing
triangles use disjoint edge sets.  Hence the number `t_v` of packing triangles through `v` obeys

  `2 t_v + |uncovered star at v| ≤ deg_G v`,

the *capacity* bound (`Nibble.two_mul_card_triAt_add_unDeg_le`).  This is the new input that lets
`Nibble.DenseGlobalLeftoverThird` replace the crude bound "every packing triangle carries up to
`D` witnesses" (with `D` the global maximum uncovered star) by a bound driven by the actual
uncovered-degree profile.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DenseGlobalLeftoverBelowHalf

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The star of a vertex in the edge-type hypergraph -/

/-- The hypergraph vertices (i.e. the graph edges) incident to `v`. -/
def starAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (EdgeV G) :=
  Finset.univ.filter (fun E => v ∈ E.val)

theorem mem_starAt (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} {E : EdgeV G} :
    E ∈ starAt G v ↔ v ∈ E.val := by simp [starAt]

/-- The star of `v` has `deg_G v` elements. -/
theorem card_starAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (starAt G v).card = G.degree v := by
  classical
  have hdeg : G.degree v = (G.neighborFinset v).card := rfl
  rw [hdeg]
  refine (Finset.card_bij (fun w hw => edgeE G ((SimpleGraph.mem_neighborFinset G v w).mp hw))
    ?_ ?_ ?_).symm
  · intro w hw
    exact (mem_starAt G).mpr (by simp)
  · intro w hw w' hw' heq
    have hpair := (edgeE_eq_iff G ((SimpleGraph.mem_neighborFinset G v w).mp hw)
      ((SimpleGraph.mem_neighborFinset G v w').mp hw')).mp heq
    have hmem : w ∈ ({v, w'} : Finset V) := by rw [← hpair]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · subst h
      simp at hw
    · exact h
  · intro E hE
    obtain ⟨w, hadj, rfl⟩ := exists_other_endpoint G ((mem_starAt G).mp hE)
    exact ⟨w, (SimpleGraph.mem_neighborFinset G v w).mpr hadj, rfl⟩

/-! ### The vertex set of an explicit packing triangle -/

/-- The vertex set spanned by `triE G hxy hyz hxz` is `{x, y, z}`. -/
theorem triOf_triE (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : G.Adj x z) : triOf G (triE G hxy hyz hxz) = {x, y, z} := by
  rw [triE_eq_subtype]
  exact triOf_subtype G (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)

/-- **A vertex of a packing triangle lies on exactly two of its edges.** -/
theorem card_filter_mem_of_mem_triOf (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Finset (EdgeV G)} (hT : T ∈ triangleHypergraphSub G) {v : V} (hv : v ∈ triOf G T) :
    (T.filter (fun E => v ∈ E.val)).card = 2 := by
  classical
  obtain ⟨x, y, z, hxy, hyz, hxz, rfl⟩ := exists_triE_of_mem G hT
  rw [triOf_triE] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  have hne1 : edgeE G hxy ≠ edgeE G hyz :=
    edgeE_ne_of_notMem G hxy hyz (by simp [hxy.ne, hxz.ne])
  have hne2 : edgeE G hxy ≠ edgeE G hxz :=
    edgeE_ne_of_notMem' G hxy hxz (by simp [hxy.ne', hyz.ne])
  have hne3 : edgeE G hyz ≠ edgeE G hxz :=
    edgeE_ne_of_notMem G hyz hxz (by simp [hxy.ne', hyz.ne])
  show ((({edgeE G hxy, edgeE G hyz, edgeE G hxz} : Finset (EdgeV G)).filter
    (fun E => v ∈ E.val)).card = 2)
  rw [card_filter_triple hne1 hne2 hne3]
  simp only [edgeE_val, Finset.mem_insert, Finset.mem_singleton]
  rcases hv with rfl | rfl | rfl
  · rw [if_pos (Or.inl rfl), if_neg (by simp [hxy.ne, hxz.ne]), if_pos (Or.inl rfl)]
  · rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl), if_neg (by simp [hxy.ne', hyz.ne])]
  · rw [if_neg (by simp [hxz.ne', hyz.ne']), if_pos (Or.inr rfl), if_pos (Or.inr rfl)]

/-! ### The capacity bound -/

open scoped Classical in
/-- The packing triangles through `v`. -/
noncomputable def triAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Finset (EdgeV G))) (v : V) : Finset (Finset (EdgeV G)) :=
  M.filter (fun T => v ∈ triOf G T)

theorem mem_triAt (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} {v : V} {T : Finset (EdgeV G)} :
    T ∈ triAt G M v ↔ T ∈ M ∧ v ∈ triOf G T := by
  classical
  simp [triAt]

/-- **The capacity bound.**  Each packing triangle through `v` uses two covered edges at `v`, so
`2 t_v + d_v ≤ deg_G v`. -/
theorem two_mul_card_triAt_add_unDeg_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {M : Finset (Finset (EdgeV G))} (hM : IsMatching (triangleHypergraphSub G) M) (v : V) :
    2 * (triAt G M v).card + unDeg G M v ≤ G.degree v := by
  classical
  set Cov : Finset (EdgeV G) :=
    (triAt G M v).biUnion (fun T => T.filter (fun E => v ∈ E.val)) with hCov
  have hdisj : ∀ T ∈ triAt G M v, ∀ T' ∈ triAt G M v, T ≠ T' →
      Disjoint (T.filter (fun E => v ∈ E.val)) (T'.filter (fun E => v ∈ E.val)) := by
    intro T hT T' hT' hne
    exact Finset.disjoint_filter_filter
      (hM.disjoint T (mem_triAt G |>.mp hT).1 T' (mem_triAt G |>.mp hT').1 hne)
  have hcardCov : Cov.card = 2 * (triAt G M v).card := by
    rw [hCov, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun T hT =>
      card_filter_mem_of_mem_triOf G (hM.subset (mem_triAt G |>.mp hT).1)
        (mem_triAt G |>.mp hT).2)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hdisj2 : Disjoint Cov (uncoveredAt G M v) := by
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [hCov, Finset.mem_biUnion] at hE
    obtain ⟨T, hT, hmem⟩ := hE
    exact (mem_uncoveredAt G).mp hE' |>.2 T (mem_triAt G |>.mp hT).1
      (Finset.mem_filter.mp hmem).1
  have hsub : Cov ∪ uncoveredAt G M v ⊆ starAt G v := by
    intro E hE
    rw [Finset.mem_union] at hE
    rcases hE with hE | hE
    · rw [hCov, Finset.mem_biUnion] at hE
      obtain ⟨T, -, hmem⟩ := hE
      exact (mem_starAt G).mpr (Finset.mem_filter.mp hmem).2
    · exact (mem_starAt G).mpr ((mem_uncoveredAt G).mp hE).1
  have hle : Cov.card + (uncoveredAt G M v).card ≤ (starAt G v).card := by
    rw [← Finset.card_union_of_disjoint hdisj2]
    exact Finset.card_le_card hsub
  rw [card_starAt] at hle
  rw [unDeg]
  omega

omit [DecidableEq V] in
/-- `deg_G v ≤ |V|`. -/
theorem degree_le_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ Fintype.card V := by
  have : G.degree v = (G.neighborFinset v).card := rfl
  rw [this, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

end Nibble
