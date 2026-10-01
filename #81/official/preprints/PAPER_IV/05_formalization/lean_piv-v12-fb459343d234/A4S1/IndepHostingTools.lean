import A4S1.TerminalPacking
import PaperIV.PaddedEquitableColouring
import PaperIV.MultiHostTriangleLift

/-!
# E14: neutral tools for the independent hosting constructor

* `rowGraph G H`: the graph of the edges inside the rows `H`; its edges are `inEdges G H` and its
  maximum degree is controlled by the row degrees (`maxDegree_rowGraph_add_one_le`).  This is
  what the padded equitable Vizing colouring (`PaperIV.PaddedEquitableColouring`) is applied to.
* `card_edgeFinset_le_parts`: `e(G) ≤ e(S) + e(S,H) + e(H) + Σ_{w ∈ W} deg w` when
  `V = S ∪ H ∪ W`.
* `card_inter_le_one_of`: the edge-disjointness test for two vertex sets, used for the three
  triangle families of the constructor (absorption, phase I, phase II), together with the
  three cross-family separation lemmas `abs_inter_lift`, `abs_inter_hosted`,
  `lift_inter_hosted` and the within-family lemma `abs_inter_abs`.
-/

namespace A4S1.Indep

open Finset A4S1.TerminalPacking

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The edges of `G` inside the rows `H`, as a graph on `V`. -/
def rowGraph (H : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ H ∧ y ∈ H
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance (H : Finset V) : DecidableRel (rowGraph G H).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ x ∈ H ∧ y ∈ H))

theorem edgeFinset_rowGraph (H : Finset V) : (rowGraph G H).edgeFinset = inEdges G H := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_inEdges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    rfl

theorem maxDegree_rowGraph_add_one_le (H : Finset V) (k : ℕ) (hk : 0 < k)
    (hΔ : ∀ v ∈ H, (H.filter (G.Adj v)).card + 1 ≤ k) :
    (rowGraph G H).maxDegree + 1 ≤ k := by
  have : (rowGraph G H).maxDegree ≤ k - 1 := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    by_cases hv : v ∈ H
    · have : univ.filter ((rowGraph G H).Adj v) = H.filter (G.Adj v) := by
        ext y
        simp only [mem_filter, mem_univ, true_and, rowGraph]
        tauto
      rw [this]
      have := hΔ v hv
      omega
    · have : univ.filter ((rowGraph G H).Adj v) = ∅ := by
        ext y
        simp only [mem_filter, mem_univ, true_and, rowGraph, notMem_empty, iff_false]
        tauto
      rw [this]
      simp
  omega

/-- **The edge split with exceptional vertices.** -/
theorem card_edgeFinset_le_parts (S H W : Finset V) (hSH : Disjoint S H)
    (hcov : ∀ v, v ∈ S ∨ v ∈ H ∨ v ∈ W) :
    G.edgeFinset.card ≤ (inEdges G S).card + crossCount G S H + (inEdges G H).card +
      ∑ w ∈ W, G.degree w := by
  have hsub : G.edgeFinset ⊆ inEdges G (S ∪ H) ∪ W.biUnion (fun w => G.incidenceFinset w) := by
    intro e he
    by_cases hall : ∀ v ∈ e, v ∈ S ∪ H
    · exact mem_union_left _ (mem_filter.2 ⟨he, hall⟩)
    · push_neg at hall
      obtain ⟨v, hve, hvSH⟩ := hall
      have hvW : v ∈ W := by
        rcases hcov v with h | h | h
        · exact absurd (mem_union_left _ h) hvSH
        · exact absurd (mem_union_right _ h) hvSH
        · exact h
      refine mem_union_right _ (mem_biUnion.2 ⟨v, hvW, ?_⟩)
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨SimpleGraph.mem_edgeFinset.1 he, hve⟩
  have h1 := card_le_card hsub
  have h2 := card_union_le (inEdges G (S ∪ H)) (W.biUnion fun w => G.incidenceFinset w)
  have h3 := card_biUnion_le (s := W) (t := fun w => G.incidenceFinset w)
  have h4 : ∑ w ∈ W, (G.incidenceFinset w).card = ∑ w ∈ W, G.degree w :=
    sum_congr rfl fun w _ => SimpleGraph.card_incidenceFinset_eq_degree G w
  have h5 := card_inEdges_union (G := G) hSH
  omega

omit [Fintype V] in
/-- The edge-disjointness test: two sets meet in at most one vertex if any two common vertices
coincide. -/
theorem card_inter_le_one_of {K L : Finset V}
    (h : ∀ x ∈ K, ∀ y ∈ K, x ∈ L → y ∈ L → x = y) : (K ∩ L).card ≤ 1 :=
  card_le_one.2 fun a ha b hb =>
    h a (mem_inter.1 ha).1 b (mem_inter.1 hb).1 (mem_inter.1 ha).2 (mem_inter.1 hb).2

omit [Fintype V] in
/-- An absorption triangle `{w, a, h}` and a phase-I triangle `{v} ∪ e` share at most one
vertex, unless the reserved link `a h` is a link `v h` used by the lift. -/
theorem abs_inter_lift (S H : Finset V) (hSH : Disjoint S H) {w a h v : V} {e : Sym2 V}
    (hwS : w ∉ S) (hwH : w ∉ H) (ha : a ∈ S) (hh : h ∈ H) (hv : v ∈ S) (he : ∀ z ∈ e, z ∈ H)
    (hbad : h ∈ e → a = v → False) :
    (({w, a, h} : Finset V) ∩ PaperIV.ExteriorTriangleLift.triangle v e).card ≤ 1 := by
  apply card_inter_le_one_of
  have hmemL : ∀ x, x ∈ PaperIV.ExteriorTriangleLift.triangle v e → x ∈ S ∨ x ∈ H := by
    intro x hx
    rcases PaperIV.ExteriorTriangleLift.mem_triangle.1 hx with rfl | hx
    · exact Or.inl hv
    · exact Or.inr (he x hx)
  have haL : a ∈ PaperIV.ExteriorTriangleLift.triangle v e → a = v := by
    intro hx
    rcases PaperIV.ExteriorTriangleLift.mem_triangle.1 hx with h' | hx
    · exact h'
    · exact absurd (he a hx) (disjoint_left.1 hSH ha)
  have hhL : h ∈ PaperIV.ExteriorTriangleLift.triangle v e → h ∈ e := by
    intro hx
    rcases PaperIV.ExteriorTriangleLift.mem_triangle.1 hx with h' | hx
    · exact absurd (h' ▸ hv) (disjoint_right.1 hSH hh)
    · exact hx
  intro x hx y hy hxL hyL
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl
  · rcases hmemL x hxL with h' | h' <;> contradiction
  · rcases hy with rfl | rfl | rfl
    · rcases hmemL y hyL with h' | h' <;> contradiction
    · rfl
    · exact (hbad (hhL hyL) (haL hxL)).elim
  · rcases hy with rfl | rfl | rfl
    · rcases hmemL y hyL with h' | h' <;> contradiction
    · exact (hbad (hhL hxL) (haL hyL)).elim
    · rfl

omit [Fintype V] in
/-- An absorption triangle `{w, a, h}` and a phase-II triangle `{u, u', h'}` share at most one
vertex, unless the reserved link `a h` is one of the links `u h'`, `u' h'`. -/
theorem abs_inter_hosted (S H : Finset V) (hSH : Disjoint S H) {w a h u u' h' : V}
    (hwS : w ∉ S) (hwH : w ∉ H) (ha : a ∈ S) (hh : h ∈ H) (hu : u ∈ S) (hu' : u' ∈ S)
    (hh' : h' ∈ H) (hbad : h = h' → (a = u ∨ a = u') → False) :
    (({w, a, h} : Finset V) ∩ {u, u', h'}).card ≤ 1 := by
  apply card_inter_le_one_of
  have hSH' : ∀ x, x ∈ S → x ∈ H → False := fun x h1 h2 => disjoint_left.1 hSH h1 h2
  intro x hx y hy hxL hyL
  simp only [mem_insert, mem_singleton] at hx hy hxL hyL
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | rfl
    | (rcases hxL with rfl | rfl | rfl <;> first | contradiction | exact (hwH hh').elim)
    | (rcases hyL with rfl | rfl | rfl <;> first | contradiction | exact (hwH hh').elim)
    | skip
  · rcases hyL with rfl | rfl | rfl
    · exact (hSH' _ hu hh).elim
    · exact (hSH' _ hu' hh).elim
    · rcases hxL with rfl | rfl | rfl
      · exact (hbad rfl (Or.inl rfl)).elim
      · exact (hbad rfl (Or.inr rfl)).elim
      · exact (hSH' _ ha hh').elim
  · rcases hxL with rfl | rfl | rfl
    · exact (hSH' _ hu hh).elim
    · exact (hSH' _ hu' hh).elim
    · rcases hyL with rfl | rfl | rfl
      · exact (hbad rfl (Or.inl rfl)).elim
      · exact (hbad rfl (Or.inr rfl)).elim
      · exact (hSH' _ ha hh').elim

omit [Fintype V] in
/-- A phase-I triangle `{v} ∪ e` and a phase-II triangle `{u, u', h'}` share at most one vertex,
unless `h'` lies on `e` and `v ∈ {u, u'}` (a link at `v` used twice). -/
theorem lift_inter_hosted (S H : Finset V) (hSH : Disjoint S H) {v u u' h' : V} {e : Sym2 V}
    (hv : v ∈ S) (he : ∀ z ∈ e, z ∈ H) (hu : u ∈ S) (hu' : u' ∈ S) (hh' : h' ∈ H)
    (hbad : h' ∈ e → (v = u ∨ v = u') → False) :
    (PaperIV.ExteriorTriangleLift.triangle v e ∩ {u, u', h'}).card ≤ 1 := by
  apply card_inter_le_one_of
  have hSH' : ∀ x, x ∈ S → x ∈ H → False := fun x h1 h2 => disjoint_left.1 hSH h1 h2
  -- a common vertex is `v` (then it is `u` or `u'`) or a vertex of `e` (then it is `h'`)
  have key : ∀ x, x ∈ PaperIV.ExteriorTriangleLift.triangle v e → x ∈ ({u, u', h'} : Finset V) →
      (x = v ∧ (v = u ∨ v = u')) ∨ (x ∈ e ∧ x = h') := by
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx'
    rcases PaperIV.ExteriorTriangleLift.mem_triangle.1 hx with rfl | hxe
    · rcases hx' with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl rfl⟩
      · exact Or.inl ⟨rfl, Or.inr rfl⟩
      · exact (hSH' _ hv hh').elim
    · rcases hx' with rfl | rfl | rfl
      · exact (hSH' _ hu (he _ hxe)).elim
      · exact (hSH' _ hu' (he _ hxe)).elim
      · exact Or.inr ⟨hxe, rfl⟩
  intro x hx y _ hxL hyL
  rcases key x hx hxL with ⟨rfl, hx2⟩ | ⟨hx1, rfl⟩ <;>
    rcases key y (by assumption) hyL with ⟨rfl, hy2⟩ | ⟨hy1, rfl⟩
  · rfl
  · exact (hbad hy1 hx2).elim
  · exact (hbad hx1 hy2).elim
  · rfl

omit [Fintype V] in
/-- Two absorption triangles share at most one vertex, unless they are equal. -/
theorem abs_inter_abs (S H W : Finset V) (hSH : Disjoint S H) {w a h w' a' h' : V}
    (hw : w ∈ W) (hw' : w' ∈ W) (hSW : Disjoint S W) (hHW : Disjoint H W)
    (ha : a ∈ S) (hh : h ∈ H) (ha' : a' ∈ S) (hh' : h' ∈ H)
    (hsame : w = w' → a = a' ∨ h = h' → a = a' ∧ h = h')
    (hdiff : w ≠ w' → a = a' → h = h' → False)
    (hne : ({w, a, h} : Finset V) ≠ {w', a', h'}) :
    (({w, a, h} : Finset V) ∩ {w', a', h'}).card ≤ 1 := by
  apply card_inter_le_one_of
  have hSH' : ∀ x, x ∈ S → x ∈ H → False := fun x h1 h2 => disjoint_left.1 hSH h1 h2
  have hSW' : ∀ x, x ∈ S → x ∈ W → False := fun x h1 h2 => disjoint_left.1 hSW h1 h2
  have hHW' : ∀ x, x ∈ H → x ∈ W → False := fun x h1 h2 => disjoint_left.1 hHW h1 h2
  -- the vertex of each type is determined
  have hA : a ∈ ({w', a', h'} : Finset V) → a = a' := by
    intro hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hSW' _ ha hw').elim
    · rfl
    · exact (hSH' _ ha hh').elim
  have hH : h ∈ ({w', a', h'} : Finset V) → h = h' := by
    intro hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hHW' _ hh hw').elim
    · exact (hSH' _ ha' hh).elim
    · rfl
  have hW : w ∈ ({w', a', h'} : Finset V) → w = w' := by
    intro hx; simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · rfl
    · exact (hSW' _ ha' hw).elim
    · exact (hHW' _ hh' hw).elim
  have hwa : w ≠ a := fun e => hSW' _ ha (e ▸ hw)
  have hwh : w ≠ h := fun e => hHW' _ hh (e ▸ hw)
  have hah : a ≠ h := fun e => hSH' _ ha (e ▸ hh)
  intro x hx y hy hxL hyL
  simp only [mem_insert, mem_singleton] at hx hy
  -- two distinct common vertices force equality of the triangles or a contradiction
  by_contra hxy
  have hall : w = w' ∧ a = a' ∧ h = h' → False := by
    rintro ⟨rfl, rfl, rfl⟩; exact hne rfl
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first | exact hxy rfl | skip
  · have e1 := hW hxL; have e2 := hA hyL; exact hall ⟨e1, (hsame e1 (Or.inl e2))⟩
  · have e1 := hW hxL; have e2 := hH hyL; exact hall ⟨e1, (hsame e1 (Or.inr e2))⟩
  · have e1 := hW hyL; have e2 := hA hxL; exact hall ⟨e1, (hsame e1 (Or.inl e2))⟩
  · have e1 := hA hxL; have e2 := hH hyL
    by_cases hww : w = w'
    · exact hall ⟨hww, hsame hww (Or.inl e1)⟩
    · exact hdiff hww e1 e2
  · have e1 := hW hyL; have e2 := hH hxL; exact hall ⟨e1, (hsame e1 (Or.inr e2))⟩
  · have e1 := hH hxL; have e2 := hA hyL
    by_cases hww : w = w'
    · exact hall ⟨hww, hsame hww (Or.inl e2)⟩
    · exact hdiff hww e2 e1

end A4S1.Indep
