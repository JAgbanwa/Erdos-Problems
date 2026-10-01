import E34.Pinned
import E34.Theorem6

/-!
# E34 — Lemma 11: the set colouring problem of pinned representations (Claim 2)

For a rooted tree `Γ` on `Fin K`, pins `x : Fin n → Fin K` and a graph `G`, `pinProblem Γ x G`
is the set colouring problem of the paper: the list of `v` consists of the subtrees of `Γ`
containing `x v`; for an edge `uv` the colours must cover the path `P_uv` from `x u` to `x v`,
for a non-edge they must be disjoint.

* `isSub_of_convex` — a non-empty path-convex set of nodes is a subtree.
* `properOn_of_pinned` — **Claim 2**: a pinned sample has a proper colouring.
* `chordal_of_pinned` — a pinned sample induces a chordal graph.
* `not_chordal_of_c4` — an induced `C₄` inside `U` makes `G[U]` non-chordal.
-/

namespace E34

open Finset

open scoped Classical

variable {n K : ℕ}

namespace RTree

variable (T : RTree K)

theorem onPath_comm (a b g : Fin K) : T.OnPath a b g ↔ T.OnPath b a g :=
  ⟨fun h S hS hb ha => h S hS ha hb, fun h S hS ha hb => h S hS hb ha⟩

/-- A non-empty path-convex set is a subtree. -/
theorem isSub_of_convex (A : Finset (Fin K)) (hne : A.Nonempty)
    (hc : ∀ a ∈ A, ∀ b ∈ A, ∀ g, T.OnPath a b g → g ∈ A) : T.IsSub A := by
  obtain ⟨t, htA, hmin⟩ := exists_min_image A (fun g => T.h g) hne
  refine ⟨t, htA, fun x hx => ?_⟩
  have hl : T.lca t x ∈ A := hc t htA x hx _ ((T.onPath_iff _ _ _).2
    ⟨T.anc_refl _, Or.inl (T.lca_anc_left t x)⟩)
  have hlt : T.lca t x = t := by
    by_contra hne'
    have := T.h_lt_of_anc (T.lca_anc_left t x) hne'
    have := hmin _ hl
    omega
  have htx : T.Anc t x := hlt ▸ T.lca_anc_right t x
  refine ⟨htx, fun y hyx hty => hc t htA x hx y ((T.onPath_iff _ _ _).2 ⟨?_, Or.inr hyx⟩)⟩
  rw [T.lca_eq_of_anc htx]; exact hty

end RTree

/-- The nodes on the path from `a` to `b`. -/
noncomputable def pathSet (Γ : RTree K) (a b : Fin K) : Finset (Fin K) :=
  univ.filter (fun g => Γ.OnPath a b g)

theorem pathSet_comm (Γ : RTree K) (a b : Fin K) : pathSet Γ a b = pathSet Γ b a := by
  ext g; simp only [pathSet, mem_filter, mem_univ, true_and]; exact Γ.onPath_comm a b g

/-- The set colouring problem of `x`-pinned representations on `Γ`. -/
noncomputable def pinProblem (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n)) :
    SetColoring n K where
  L v := univ.filter (fun A => Γ.IsSub A ∧ x v ∈ A)
  mm u v c := if G.Adj u v then pathSet Γ (x u) (x v) \ c else ∅
  MM u v c := if G.Adj u v then univ else univ \ c

theorem pinProblem_ok_iff (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (u v : Fin n) (c d : Finset (Fin K)) :
    (pinProblem Γ x G).ok u c v d ↔
      (G.Adj u v → pathSet Γ (x u) (x v) ⊆ c ∪ d) ∧ (¬ G.Adj u v → Disjoint c d) := by
  unfold SetColoring.ok pinProblem
  by_cases h : G.Adj u v
  · simp only [h, if_true, subset_univ, and_true, not_true_eq_false, IsEmpty.forall_iff,
      true_implies]
    constructor
    · intro h1 g hg
      by_cases hc : g ∈ c
      · exact mem_union_left _ hc
      · exact mem_union_right _ (h1 (mem_sdiff.2 ⟨hg, hc⟩))
    · intro h1 g hg
      rw [mem_sdiff] at hg
      rcases mem_union.1 (h1 hg.1) with h2 | h2
      · exact absurd h2 hg.2
      · exact h2
  · simp only [h, if_false, empty_subset, true_and, false_implies, not_false_eq_true,
      true_implies]
    constructor
    · intro h1
      rw [disjoint_left]
      intro g hgc hgd
      exact (mem_sdiff.1 (h1 hgd)).2 hgc
    · intro h1 g hg
      exact mem_sdiff.2 ⟨mem_univ _, fun hgc => disjoint_left.1 h1 hgc hg⟩

theorem pinProblem_compat_iff (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (u v : Fin n) (c d : Finset (Fin K)) :
    (pinProblem Γ x G).compat u c v d ↔
      (G.Adj u v → pathSet Γ (x u) (x v) ⊆ c ∪ d) ∧ (¬ G.Adj u v → Disjoint c d) := by
  unfold SetColoring.compat
  rw [pinProblem_ok_iff, pinProblem_ok_iff, pathSet_comm Γ (x v), G.adj_comm v u, union_comm d,
    disjoint_comm (a := d)]
  exact and_self_iff

theorem pinProblem_L_nonempty (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (v : Fin n) : ((pinProblem Γ x G).L v).Nonempty :=
  ⟨{x v}, mem_filter.2 ⟨mem_univ _, ⟨x v, Γ.isSubAt_singleton (x v)⟩, mem_singleton_self _⟩⟩

/-- **Claim 2 of Lemma 11**: an `x`-pinned sample has a proper colouring. -/
theorem properOn_of_pinned {Γ : RTree K} {x : Fin n → Fin K} {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} (h : PinnedOn Γ x G U) :
    ∃ φ : Fin n → Finset (Fin K), (pinProblem Γ x G).ProperOn φ U := by
  obtain ⟨K', T, ι, Tu, hpath, hsub, hadj⟩ := h
  refine ⟨fun u => univ.filter (fun g => ι g ∈ Tu u), ?_, ?_⟩
  · intro v hv
    refine mem_filter.2 ⟨mem_univ _, ?_, mem_filter.2 ⟨mem_univ _, (hsub v hv).2⟩⟩
    refine Γ.isSub_of_convex _ ⟨x v, mem_filter.2 ⟨mem_univ _, (hsub v hv).2⟩⟩ ?_
    intro a ha b hb g hg
    rw [mem_filter] at ha hb ⊢
    exact ⟨mem_univ _, hpath a b g hg _ (hsub v hv).1 ha.2 hb.2⟩
  · intro u hu v hv huv
    rw [pinProblem_compat_iff]
    constructor
    · intro hG g hg
      rw [pathSet, mem_filter] at hg
      have hT := hpath _ _ _ hg.2
      have := hT.mem_union (hsub u hu).1 (hsub v hv).1 ((hadj u hu v hv huv).1 hG)
        (hsub u hu).2 (hsub v hv).2
      rcases mem_union.1 this with h1 | h1
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h1⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h1⟩)
    · intro hG
      rw [disjoint_left]
      intro g hgu hgv
      exact hG ((hadj u hu v hv huv).2 ⟨ι g, mem_inter.2 ⟨(mem_filter.1 hgu).2,
        (mem_filter.1 hgv).2⟩⟩)

/-- A pinned sample induces a chordal graph. -/
theorem chordal_of_pinned {Γ : RTree K} {x : Fin n → Fin K} {G : SimpleGraph (Fin n)}
    {U : Finset (Fin n)} (h : PinnedOn Γ x G U) :
    AlonShapira.IsChordal (G.induce (U : Set (Fin n))) := by
  obtain ⟨K', T, ι, Tu, -, hsub, hadj⟩ := h
  let Tu' : Fin n → Finset (Fin K') := fun u => if u ∈ U then Tu u else univ
  let F : SimpleGraph (Fin n) :=
    { Adj := fun u v => u ≠ v ∧ (Tu' u ∩ Tu' v).Nonempty
      symm := fun u v h => ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩
      loopless := ⟨fun u h => h.1 rfl⟩ }
  have hF : AlonShapira.IsChordal F := by
    refine T.isChordal_of_subtrees F Tu' (fun u => ?_) (fun u v huv => ?_)
    · by_cases hu : u ∈ U
      · simp only [Tu', hu, if_true]; exact (hsub u hu).1
      · simp only [Tu', hu, if_false]; exact T.isSub_univ
    · exact ⟨fun h => h.2, fun h => ⟨huv, h⟩⟩
  refine hF.of_embedding ⟨⟨fun u => u.1, Subtype.val_injective⟩, ?_⟩
  intro u v
  simp only [Function.Embedding.coeFn_mk, SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
  show F.Adj u.1 v.1 ↔ G.Adj u.1 v.1
  have hu : u.1 ∈ U := u.2
  have hv : v.1 ∈ U := v.2
  by_cases huv : u.1 = v.1
  · rw [huv]; simp only [SimpleGraph.irrefl, iff_false]

  · simp only [F, Tu', hu, hv, if_true]
    rw [hadj u.1 hu v.1 hv huv]
    exact ⟨fun h => h.2, fun h => ⟨huv, h⟩⟩

/-- An induced `C₄` gives an embedding of `C₄` into an induced subgraph. -/
theorem c4_embedding {V : Type*} (G : SimpleGraph V) (U : Set V) {a b c d : V}
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (hac' : a ≠ c) (hbd' : b ≠ d) :
    Nonempty (SimpleGraph.cycleGraph 4 ↪g G.induce U) := by
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c := hbc.ne
  have hcd' : c ≠ d := hcd.ne
  have hda' : d ≠ a := hda.ne
  let f : Fin 4 → U := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all [f, SimpleGraph.cycleGraph_adj, G.adj_comm] <;>
      decide +kernel

/-- An induced `C₄` inside `U` makes `G[U]` non-chordal. -/
theorem not_chordal_of_c4 (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) {a b c d : Fin n}
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (hac' : a ≠ c) (hbd' : b ≠ d) :
    ¬ AlonShapira.IsChordal (G.induce (U : Set (Fin n))) := by
  intro hch
  obtain ⟨e⟩ := c4_embedding G (U : Set (Fin n)) (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb)
    (Finset.mem_coe.2 hc) (Finset.mem_coe.2 hd) hab hbc hcd hda hac hbd hac' hbd'
  exact (hch 4 _ ⟨le_refl 4, rfl⟩).false e

end E34
