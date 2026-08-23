import PaperII.Chordal
import PaperII.CompleteSplit
import PaperII.Dirac

/-!
# Paper II — Terminal characterization (ledger L7 = Lemma 5.1), CLIQUE-TREE-FREE

If every two nonadjacent simplicial vertices of `H` have equal open neighborhoods, then `H` is
complete-split. Proved from ONLY the Dirac-family facts in `ChordalStructure H` —
`simplicial_hereditary` (A1 heredity + A3a simplicial existence) and `two_nonadj_simplicial` (A3b) —
with NO clique tree / running-intersection (A4 removed). Follows the clique-tree-free proof in
`PATH2_terminal_characterization/L7_clique_tree_free_proof.md`.
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `H` is complete-split: isomorphic to some `S_{p,q}`. -/
def IsCompleteSplit (H : SimpleGraph V) : Prop := ∃ p q : ℕ, Nonempty (H ≃g completeSplit p q)

/-- A vertex is *universal* if it is adjacent to every other vertex. -/
def IsUniversal (H : SimpleGraph V) (v : V) : Prop := ∀ w, w ≠ v → H.Adj v w

/-- If `K` is a set of universal vertices and its complement is independent, then `H` is
complete-split. The only place a graph isomorphism is constructed. (Clique-tree-free; preserved.) -/
lemma isCompleteSplit_of_universal_indep (H : SimpleGraph V) (K : Set V)
    (hK : ∀ u ∈ K, ∀ w, w ≠ u → H.Adj u w)
    (hI : ∀ x, x ∉ K → ∀ y, y ∉ K → ¬ H.Adj x y) : IsCompleteSplit H := by
  classical
  refine ⟨Fintype.card K, Fintype.card (↥Kᶜ), ⟨?_⟩⟩
  set p := Fintype.card K
  set q := Fintype.card (↥Kᶜ)
  set e : V ≃ Fin p ⊕ Fin q :=
    (Equiv.Set.sumCompl K).symm.trans
      (Equiv.sumCongr (Fintype.equivFin ↥K) (Fintype.equivFin ↥Kᶜ)) with he
  have hmem : ∀ (a : V) (ha : a ∈ K), e a = Sum.inl (Fintype.equivFin ↥K ⟨a, ha⟩) := by
    intro a ha
    rw [he, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem ha]; rfl
  have hnmem : ∀ (a : V) (ha : a ∉ K), e a = Sum.inr (Fintype.equivFin ↥Kᶜ ⟨a, ha⟩) := by
    intro a ha
    rw [he, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem ha]; rfl
  refine ⟨e, ?_⟩
  intro a b
  by_cases ha : a ∈ K <;> by_cases hb : b ∈ K
  · rw [hmem a ha, hmem b hb, completeSplit_inl_inl]
    constructor
    · intro hij
      by_contra hab
      have hba : b = a := by by_contra h; exact hab (hK a ha b h)
      apply hij
      have h2 : e a = e b := by rw [hba]
      rw [hmem a ha, hmem b hb] at h2
      exact Sum.inl.inj h2
    · intro hab hij
      apply H.ne_of_adj hab
      apply e.injective
      rw [hmem a ha, hmem b hb, hij]
  · rw [hmem a ha, hnmem b hb]
    simp only [completeSplit_inl_inr, true_iff]
    exact hK a ha b (fun hab => hb (hab ▸ ha))
  · rw [hnmem a ha, hmem b hb]
    simp only [completeSplit_inr_inl, true_iff]
    exact (hK b hb a (fun hab => ha (hab ▸ hb))).symm
  · rw [hnmem a ha, hnmem b hb]
    simp only [completeSplit_inr_inr, false_iff]
    exact hI a ha b hb

/-! ## Clique-tree-free terminal characterization (5 lemmas) -/

/-- (0) Observation 0: a simplicial vertex's neighborhood is a clique. -/
theorem simplicial_nbhd_is_clique_separator (H : SimpleGraph V) {v : V} (hv : IsSimplicial H v) :
    H.IsClique (H.neighborSet v) := hv

/-- (†) Every simplicial vertex lies in `C = N(y)` or has open neighborhood exactly `C`
(under property (P), with `y` simplicial). -/
theorem simplicial_in_C_or_nbhd_eq_C (H : SimpleGraph V)
    (hP : ∀ a b : V, IsSimplicial H a → IsSimplicial H b → ¬ H.Adj a b →
        H.neighborSet a = H.neighborSet b)
    {y s : V} (hy : IsSimplicial H y) (hs : IsSimplicial H s) :
    s ∈ H.neighborSet y ∨ H.neighborSet s = H.neighborSet y := by
  by_cases h : H.Adj y s
  · exact Or.inl ((H.mem_neighborSet y s).2 h)
  · exact Or.inr (hP s y hs hy (fun hsy => h hsy.symm))

/-- (1) Step 1: `V ∖ C` is independent (every component of `H − C` is a singleton), `C = N(x) = N(y)`. -/
theorem components_of_minus_C_are_singletons (H : SimpleGraph V) (hchord : ChordalStructure H)
    (hP : ∀ a b : V, IsSimplicial H a → IsSimplicial H b → ¬ H.Adj a b →
        H.neighborSet a = H.neighborSet b)
    {x y : V} (hx : IsSimplicial H x) (hy : IsSimplicial H y)
    (hxy : ¬ H.Adj x y) (hC : H.neighborSet x = H.neighborSet y) :
    ∀ u v : V, u ∉ H.neighborSet x → v ∉ H.neighborSet x → ¬ H.Adj u v := by
  classical
  intro u v hu hv hadj
  -- `Cf` is the (open) neighborhood of `x` as a finset; `S = Cfᶜ` is its complement.
  set Cf : Finset V := Finset.univ.filter (fun w => w ∈ H.neighborSet x) with hCfdef
  set S : Finset V := Finset.univ.filter (fun w => w ∉ H.neighborSet x) with hSdef
  have huS : u ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩
  have hvS : v ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩
  -- `D` = component of `u` inside `S` (= the component of the edge `u-v` in `H - Cf`).
  set D : Finset V := S.filter (fun w => RReach H S u w) with hDdefeq
  have hDdef : ∀ w, w ∈ D ↔ (w ∈ S ∧ RReach H S u w) := fun w => Finset.mem_filter
  have huD : u ∈ D := (hDdef u).2 ⟨huS, Relation.ReflTransGen.refl⟩
  have hvD : v ∈ D := (hDdef v).2 ⟨hvS, Relation.ReflTransGen.single ⟨huS, hvS, hadj⟩⟩
  have huv_ne : u ≠ v := hadj.ne
  -- `Cf` is a clique (it is `N(x)`, which is a clique since `x` is simplicial).
  have hCfclique : H.IsClique (Cf : Set V) := by
    have hcoe : (Cf : Set V) = H.neighborSet x := by
      ext w; simp [hCfdef]
    rw [hcoe]; exact hx
  -- `D` avoids `Cf`.
  have hDC : ∀ d ∈ D, d ∉ Cf := by
    intro d hd
    have hdS : d ∈ S := ((hDdef d).1 hd).1
    have : d ∉ H.neighborSet x := (Finset.mem_filter.1 hdS).2
    intro hdCf; exact this ((Finset.mem_filter.1 hdCf).2)
  -- `D` is connected and separated from the rest of `H` by `Cf`.
  have hDconn : RConn H D := rconn_component H hDdef huD
  have hsep : ∀ d ∈ D, ∀ w, H.Adj d w → w ∈ Cf ∨ w ∈ D := by
    intro d hd w hadj'
    by_cases hwC : w ∈ H.neighborSet x
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hwC⟩)
    · have hwS : w ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hwC⟩
      exact Or.inr (component_sep H hDdef d hd w hwS hadj')
  -- Extract a genuinely-simplicial vertex `z` of `H` lying in `D`.
  obtain ⟨z, hzD, hzsimp⟩ :=
    exists_simplicial_in_component H (rsh_of_chordal H hchord) Cf hCfclique D hDC ⟨u, huD⟩ hDconn hsep
  have hznC : z ∉ H.neighborSet x := (Finset.mem_filter.1 ((hDdef z).1 hzD).1).2
  -- By (†), `N(z) = N(y) = N(x)`.
  have hzNy : z ∉ H.neighborSet y := by rw [← hC]; exact hznC
  have hNz : H.neighborSet z = H.neighborSet x := by
    rcases simplicial_in_C_or_nbhd_eq_C H hP hy hzsimp with h | h
    · exact absurd h hzNy
    · rw [h]; exact hC.symm
  -- But `z ∈ D` (connected, ≥ 2 vertices) has a neighbor inside `D`, contradicting `N(z) = N(x)`.
  obtain ⟨w0, hw0D, hw0ne⟩ : ∃ w0 ∈ D, w0 ≠ z := by
    by_cases hzu : z = u
    · exact ⟨v, hvD, by rw [hzu]; exact huv_ne.symm⟩
    · exact ⟨u, huD, fun h => hzu h.symm⟩
  obtain ⟨n, hnD, hzn⟩ := exists_radj_of_rreach_ne H (hDconn z hzD w0 hw0D) hw0ne.symm
  have hnnC : n ∉ H.neighborSet x := (Finset.mem_filter.1 ((hDdef n).1 hnD).1).2
  have hnNz : n ∈ H.neighborSet z := (H.mem_neighborSet z n).2 hzn
  rw [hNz] at hnNz
  exact hnnC hnNz

/-- (2) Step 2: every vertex outside `C` is simplicial with open neighborhood exactly `C`. -/
theorem complement_C_independent_and_nbhd_C (H : SimpleGraph V) (hchord : ChordalStructure H)
    (hP : ∀ a b : V, IsSimplicial H a → IsSimplicial H b → ¬ H.Adj a b →
        H.neighborSet a = H.neighborSet b)
    {x y : V} (hx : IsSimplicial H x) (hy : IsSimplicial H y)
    (hxy : ¬ H.Adj x y) (hC : H.neighborSet x = H.neighborSet y) :
    ∀ v : V, v ∉ H.neighborSet x → IsSimplicial H v ∧ H.neighborSet v = H.neighborSet x := by
  intro v hv
  have h1 := components_of_minus_C_are_singletons H hchord hP hx hy hxy hC
  -- Every neighbor of `v` lies in `N(x)` (else it would be an edge inside the complement).
  have hsub : ∀ w, H.Adj v w → w ∈ H.neighborSet x := by
    intro w hvw
    by_contra hwC
    exact h1 v w hv hwC hvw
  -- Hence `N(v) ⊆ N(x)`, a clique, so `v` is simplicial.
  have hvsimp : IsSimplicial H v := by
    intro a ha b hb hab
    have haa : a ∈ H.neighborSet x := hsub a ((H.mem_neighborSet v a).1 ha)
    have hbb : b ∈ H.neighborSet x := hsub b ((H.mem_neighborSet v b).1 hb)
    exact hx haa hbb hab
  -- `v` and `x` are nonadjacent simplicial, so by (P) they share a neighborhood.
  have hxnotC : x ∉ H.neighborSet x := by simp
  have hvx : ¬ H.Adj v x := h1 v x hv hxnotC
  exact ⟨hvsimp, hP v x hvsimp hx hvx⟩

/-- (3) Ledger L7 (Lemma 5.1). Signature unchanged; proof is now clique-tree-free. -/
theorem terminal_characterization (H : SimpleGraph V) (hchord : ChordalStructure H)
    (hH : ∀ x y : V, IsSimplicial H x → IsSimplicial H y → ¬ H.Adj x y →
        H.neighborSet x = H.neighborSet y) :
    IsCompleteSplit H := by
  classical
  by_cases hcomp : ∀ u v : V, u ≠ v → H.Adj u v
  · -- `H` is complete: take the clique side `K = univ`.
    refine isCompleteSplit_of_universal_indep H Set.univ ?_ ?_
    · exact fun u _ w hw => hcomp u w (fun h => hw h.symm)
    · exact fun a ha => absurd (Set.mem_univ a) ha
  · -- `H` is not complete: find two nonadjacent simplicial vertices.
    obtain ⟨x, y, hxy_ne, hxy, hx, hy⟩ :
        ∃ x y : V, x ≠ y ∧ ¬ H.Adj x y ∧ IsSimplicial H x ∧ IsSimplicial H y := by
      by_cases hconn : H.Connected
      · exact hchord.two_nonadj_simplicial hconn hcomp
      · have hne : Nonempty V := by
          rcases not_forall.1 hcomp with ⟨a, _⟩
          exact ⟨a⟩
        exact exists_two_nonadj_simplicial_of_not_connected H hchord hne hconn
    have hC : H.neighborSet x = H.neighborSet y := hH x y hx hy hxy
    have h1 := components_of_minus_C_are_singletons H hchord hH hx hy hxy hC
    have h2 := fun v (hv : v ∉ H.neighborSet x) =>
      complement_C_independent_and_nbhd_C H hchord hH hx hy hxy hC v hv
    refine isCompleteSplit_of_universal_indep H (H.neighborSet x) ?_ ?_
    · -- Every vertex of `C = N(x)` is universal.
      intro c hc w hwc
      by_cases hwC : w ∈ H.neighborSet x
      · exact hx hc hwC (fun h => hwc h.symm)
      · have hNw : H.neighborSet w = H.neighborSet x := (h2 w hwC).2
        have hcw : c ∈ 