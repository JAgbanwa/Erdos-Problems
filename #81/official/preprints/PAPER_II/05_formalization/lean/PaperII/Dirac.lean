import Mathlib
import PaperII.Chordal

/-!
# Paper II — Dirac-family facts from simplicial-heredity (clique-tree-free)

Auxiliary development supporting the clique-tree-free proof of the terminal characterization
(`PaperII/L7.lean`). The only chordal input used is `ChordalStructure.simplicial_hereditary`
(A1 heredity + A3a: every nonempty induced subgraph has a simplicial vertex).

We work with *relative* notions on the ambient type `V` (avoiding subtype gymnastics):

* `RSimplicial H S a` — the neighbors of `a` lying in `S` form a clique;
* `RReach H S a b` — reachability using only edges inside `S`;
* `RConn H S` — the subgraph induced on `S` is connected.

Main results:
* `rsh_of_chordal` — Dirac-1 (heredity): every nonempty `S` has a relatively-simplicial vertex;
* `rdirac2` — Dirac-2: a connected non-complete `S` has two nonadjacent relatively-simplicial
  vertices (proved by induction on `|S|`, removing a simplicial vertex, using only Dirac-1);
* `exists_simplicial_in_component` — the extraction lemma used in `L7` Step 1;
* `exists_two_nonadj_simplicial_of_not_connected` — the disconnected case of `L7` Step 3.
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Relative simpliciality: the neighbors of `a` lying inside `S` form a clique. -/
def RSimplicial (H : SimpleGraph V) (S : Finset V) (a : V) : Prop :=
  H.IsClique {b | b ∈ S ∧ H.Adj a b}

/-- One step of relative reachability inside `S`. -/
def RStep (H : SimpleGraph V) (S : Finset V) (p q : V) : Prop := p ∈ S ∧ q ∈ S ∧ H.Adj p q

/-- Relative reachability inside `S`. -/
def RReach (H : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (RStep H S) a b

/-- `S` induces a connected subgraph. -/
def RConn (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, RReach H S a b

/-
A relatively-simplicial vertex whose neighbors all lie in `S` is genuinely simplicial.
-/
theorem isSimplicial_of_rsimplicial (H : SimpleGraph V) {S : Finset V} {a : V}
    (hsub : ∀ b, H.Adj a b → b ∈ S) (h : RSimplicial H S a) : IsSimplicial H a := by
  intro b hb c hc;
  exact h ⟨ hsub b hb, hb ⟩ ⟨ hsub c hc, hc ⟩

/-
Dirac-1 (heredity): from `simplicial_hereditary`, every nonempty `S` contains a
relatively-simplicial vertex.
-/
theorem rsh_of_chordal (H : SimpleGraph V) (hchord : ChordalStructure H)
    (S : Finset V) (hne : S.Nonempty) : ∃ a ∈ S, RSimplicial H S a := by
  obtain ⟨ a, ha ⟩ := hchord.simplicial_hereditary S ( hne );
  use a.val;
  unfold IsSimplicial at ha;
  simp_all +decide [ Set.Pairwise, SimpleGraph.neighborSet ];
  intro x hx y hy hxy; specialize ha x hx.1 hx.2 y hy.1 hy.2; aesop;

/-- `RStep` is symmetric. -/
theorem rstep_symm (H : SimpleGraph V) (S : Finset V) {p q : V} (h : RStep H S p q) :
    RStep H S q p := ⟨h.2.1, h.1, h.2.2.symm⟩

/-
`RReach` is symmetric.
-/
theorem rreach_symm (H : SimpleGraph V) (S : Finset V) {a b : V} (h : RReach H S a b) :
    RReach H S b a := by
  induction h;
  · exact .refl;
  · exact .trans ( .single ( rstep_symm _ _ ‹_› ) ) ‹_›

/-
Reachability inside `S` lifts to any larger `T ⊇ S`.
-/
theorem rreach_mono (H : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) {a b : V}
    (h : RReach H S a b) : RReach H T a b := by
  convert Relation.ReflTransGen.mono _ h;
  exact fun a b h => ⟨ hST h.1, hST h.2.1, h.2.2 ⟩

/-
If `a ≠ b` are relatively reachable, then `a` has a neighbor inside `S`.
-/
theorem exists_radj_of_rreach_ne (H : SimpleGraph V) {S : Finset V} {a b : V}
    (h : RReach H S a b) (hab : a ≠ b) : ∃ n ∈ S, H.Adj a n := by
  contrapose! h;
  intro h';
  induction' h' with c hc ih;
  · contradiction;
  · cases ‹RStep H S c hc› ; aesop

/-
Shortcut lemma: reachability that may pass through a relatively-simplicial vertex `v` can be
rerouted to avoid `v` (endpoints distinct from `v`).
-/
theorem rreach_erase (H : SimpleGraph V) {S : Finset V} {v : V}
    (hv : RSimplicial H S v) {a b : V} (hab : RReach H S a b) (ha : a ≠ v) (hb : b ≠ v) :
    RReach H (S.erase v) a b := by
  -- By induction on the length of the path, we can show that if there's a path from a to b in S, then there's a path from a to b in S.erase v.
  have h_ind : ∀ c, RReach H S a c → (RReach H (S.erase v) a c) ∨ (c = v ∧ ∃ n, n ≠ v ∧ n ∈ S ∧ RReach H (S.erase v) a n ∧ H.Adj n v) := by
    intro c hc
    induction' hc with c hc ih
    generalize_proofs at *; (
    exact Or.inl ( Relation.ReflTransGen.refl ));
    rename_i h₁ h₂; rcases h₂ with ( h₂ | ⟨ rfl, n, hn, hn', hn'', hn''' ⟩ ) <;> simp_all +decide [ RStep ] ;
    · grind +locals;
    · by_cases h : hc = c <;> simp_all +decide [ RStep ];
      have := hv ( show n ∈ S ∧ H.Adj c n from ⟨ hn', hn'''.symm ⟩ ) ( show hc ∈ S ∧ H.Adj c hc from ⟨ h₁.2.1, h₁.2.2 ⟩ ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
      by_cases h : n = hc <;> simp_all +decide [ RStep ];
      exact hn''.tail ( by exact ⟨ by aesop, by aesop, this.symm ⟩ )
  generalize_proofs at *; (
  cases h_ind b hab <;> tauto)

/-
Removing a relatively-simplicial vertex from a connected `S` keeps it connected.
-/
theorem rconn_erase (H : SimpleGraph V) {S : Finset V} {v : V}
    (hv : RSimplicial H S v) (hconn : RConn H S) : RConn H (S.erase v) := by
  intro a ha b hb; exact rreach_erase H hv ( hconn a ( Finset.mem_of_mem_erase ha ) b ( Finset.mem_of_mem_erase hb ) ) ( by aesop ) ( by aesop ) ;

/-
If `a` is relatively simplicial in `S.erase v` and non-adjacent to `v`, it is relatively
simplicial in `S`.
-/
theorem rsimplicial_of_erase (H : SimpleGraph V) {S : Finset V} {v a : V}
    (h : RSimplicial H (S.erase v) a) (hav : ¬ H.Adj a v) : RSimplicial H S a := by
  intro b hb c hc; aesop;

/-
Dirac-2 from Dirac-1: a connected non-complete `S` has two nonadjacent relatively-simplicial
vertices. Proved by strong induction on `|S|`, removing a relatively-simplicial vertex.
-/
theorem rdirac2 (H : SimpleGraph V)
    (hRSH : ∀ T : Finset V, T.Nonempty → ∃ a ∈ T, RSimplicial H T a) :
    ∀ (n : ℕ) (S : Finset V), S.card = n → RConn H S →
      (¬ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b) →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬ H.Adj a b ∧ RSimplicial H S a ∧ RSimplicial H S b := by
  intro n;
  induction' n using Nat.strong_induction_on with n ih;
  intro S hS hconn hnc
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, RSimplicial H S v := hRSH S (by
  exact Finset.card_pos.mp ( hS.symm ▸ Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide ) ));
  -- Let `S' := S.erase v`. We have `RConn H S'` from `rconn_erase H hv hconn`.
  set S' := S.erase v
  have hS' : RConn H S' := by
    exact rconn_erase H hv hconn;
  by_cases hS'_complete : ∀ a ∈ S', ∀ b ∈ S', a ≠ b → H.Adj a b;
  · -- Since `S` is NOT complete, there are `p q ∈ S`, `p ≠ q`, `¬ H.Adj p q`.
    obtain ⟨p, hpS, q, hqS, hpq, hnpq⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ¬ H.Adj p q := by
      grind;
    by_cases hpv : p = v;
    · use v, hvS, q, hqS;
      simp_all +decide [ RSimplicial ];
      intro a ha b hb hab; by_cases ha' : a = v <;> by_cases hb' : b = v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
      exact hS'_complete a ( Finset.mem_erase_of_ne_of_mem ha' ha.1 ) b ( Finset.mem_erase_of_ne_of_mem hb' hb.1 ) hab;
    · by_cases hqv : q = v;
      · use p, hpS, v, hvS;
        simp_all +decide [ RSimplicial ];
        intro a ha b hb hab; specialize hS'_complete a; aesop;
      · exact False.elim ( hnpq ( hS'_complete p ( Finset.mem_erase_of_ne_of_mem hpv hpS ) q ( Finset.mem_erase_of_ne_of_mem hqv hqS ) hpq ) );
  · obtain ⟨a, haS', b, hbS', hab, hne, ha, hb⟩ : ∃ a ∈ S', ∃ b ∈ S', a ≠ b ∧ ¬H.Adj a b ∧ RSimplicial H S' a ∧ RSimplicial H S' b := by
      grind;
    by_cases hav : H.Adj a v <;> by_cases hbv : H.Adj b v;
    · exact absurd (hv ⟨ Finset.mem_of_mem_erase haS', hav.symm ⟩ ⟨ Finset.mem_of_mem_erase hbS', hbv.symm ⟩ hab) hne
    · refine ⟨ v, hvS, b, Finset.mem_of_mem_erase hbS', ?_, ?_, hv, rsimplicial_of_erase H hb hbv ⟩
      · rintro rfl; exact Finset.notMem_erase _ _ hbS'
      · rwa [ SimpleGraph.adj_comm ]
    · refine ⟨ v, hvS, a, Finset.mem_of_mem_erase haS', ?_, ?_, hv, rsimplicial_of_erase H ha hav ⟩
      · rintro rfl; exact Finset.notMem_erase _ _ haS'
      · rwa [ SimpleGraph.adj_comm ]
    · exact ⟨ a, Finset.mem_of_mem_erase haS', b, Finset.mem_of_mem_erase hbS', hab, hne, rsimplicial_of_erase H ha hav, rsimplicial_of_erase H hb hbv ⟩


/-
A connected `S` with a vertex outside a clique `K ⊆ S` has a relatively-simplicial vertex
outside `K`.
-/
theorem exists_rsimplicial_outside_clique (H : SimpleGraph V)
    (hRSH : ∀ T : Finset V, T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    {K S : Finset V} (hK : H.IsClique (K : Set V)) (hKS : K ⊆ S)
    (hne : (S \ K).Nonempty) (hconn : RConn H S) :
    ∃ z ∈ S \ K, RSimplicial H S z := by
  by_cases hcomp : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b;
  · exact Exists.elim hne fun x hx => ⟨ x, by aesop, fun a ha b hb hab => hcomp a ( by aesop ) b ( by aesop ) hab ⟩;
  · obtain ⟨ a, ha, b, hb, hab, h, ha', hb' ⟩ := rdirac2 H hRSH S.card S rfl hconn hcomp;
    by_cases haK : a ∈ K <;> by_cases hbK : b ∈ K <;> simp_all +decide;
    · exact False.elim ( h ( hK haK hbK hab ) );
    · grind +splitImp;
    · exact ⟨ a, ⟨ ha, haK ⟩, ha' ⟩;
    · exact ⟨ a, ⟨ ha, haK ⟩, ha' ⟩

/-- Reachability inside `D` lifts to `E ∪ D`. -/
theorem rreach_mono_union (H : SimpleGraph V) {D E : Finset V} {a b : V}
    (h : RReach H D a b) : RReach H (E ∪ D) a b :=
  rreach_mono H Finset.subset_union_right h

/-- If `D` is connected and every vertex of `E` has a neighbor in `D`, then `E ∪ D` is connected. -/
theorem rconn_union_of_attached (H : SimpleGraph V) {D E : Finset V}
    (hD : RConn H D) (hDne : D.Nonempty)
    (hE : ∀ c ∈ E, ∃ d ∈ D, H.Adj c d) : RConn H (E ∪ D) := by
  obtain ⟨d0, hd0⟩ := hDne
  -- every vertex of `E ∪ D` reaches `d0` inside `E ∪ D`
  have key : ∀ w ∈ E ∪ D, RReach H (E ∪ D) w d0 := by
    intro w hw
    rcases Finset.mem_union.1 hw with hwE | hwD
    · obtain ⟨d, hdD, hadj⟩ := hE w hwE
      have step : RReach H (E ∪ D) w d :=
        Relation.ReflTransGen.single
          ⟨hw, Finset.mem_union_right _ hdD, hadj⟩
      exact step.trans (rreach_mono_union H (hD d hdD d0 hd0))
    · exact rreach_mono_union H (hD w hwD d0 hd0)
  intro a ha b hb
  exact (key a ha).trans (rreach_symm H _ (key b hb))

/-
**Extraction lemma** (L7 Step 1). Given a clique `C`, a nonempty connected `D` disjoint from
`C`, separated from the rest of `H` (`hsep`), there is a genuinely-simplicial vertex of `H` inside
`D`.
-/
theorem exists_simplicial_in_component (H : SimpleGraph V)
    (hRSH : ∀ T : Finset V, T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    (C : Finset V) (hCclique : H.IsClique (C : Set V))
    (D : Finset V) (hDC : ∀ d ∈ D, d ∉ C) (hDne : D.Nonempty)
    (hDconn : RConn H D)
    (hsep : ∀ d ∈ D, ∀ w, H.Adj d w → w ∈ C ∨ w ∈ D) :
    ∃ z ∈ D, IsSimplicial H z := by
  obtain ⟨s, hs1, hs2⟩ : ∃ s ∈ D, RSimplicial H D s := by
    exact hRSH D hDne;
  -- If `s` has no `C`-neighbors (every neighbor in `D`), then `s` is genuinely simplicial by `isSimplicial_of_rsimplicial`.
  by_cases h_no_Cneighbors : ∀ b, H.Adj s b → b ∈ D;
  · exact ⟨ s, hs1, isSimplicial_of_rsimplicial H h_no_Cneighbors hs2 ⟩;
  · -- Otherwise there is a `C`-neighbor of `s` (say `x`), which is `C`-simplicial: neighbor neighbors are all in `C` (because `H` is `C`-free), so `RSimplicial H C x` implies `IsSimplicial H x`.
    obtain ⟨x, hx1, hx2⟩ : ∃ x ∈ C, H.Adj s x := by
      grind;
    -- By `rreach_mono`, `x` is relatively reachable inside `C ∪ D` from any `s' ∈ D` (if `s' = s`, `x` is directly connected; else `s'—D—s—x`).
    have hx_reachable : ∀ s' ∈ D, RReach H (C ∪ D) s' x := by
      intro s' hs';
      have hx_reachable : RReach H D s' s := by
        exact hDconn s' hs' s hs1;
      exact Relation.ReflTransGen.tail ( rreach_mono _ ( Finset.subset_union_right ) hx_reachable ) ( by exact ⟨ by aesop, by aesop, hx2 ⟩ );
    -- By `rreach_mono`, `x` is relatively reachable inside `C ∪ D` from any `s' ∈ D` (if `s' = s`, `x` is directly connected; else `s'—D—s—x`). Since `RConn H D` is true, every vertex in `D` is relatively reachable inside `D` from every other vertex in `D`, so `x` is relatively reachable inside `C ∪ D` from every vertex in `D`.
    have hx_reachable_all : ∀ s' ∈ C ∪ D, RReach H (C ∪ D) s' x := by
      intro s' hs'
      by_cases hs'_in_D : s' ∈ D;
      · exact hx_reachable s' hs'_in_D;
      · by_cases hs'_in_C : s' ∈ C <;> simp_all +decide [ Finset.mem_union ];
        by_cases hs'_eq_x : s' = x;
        · exact hs'_eq_x.symm ▸ Relation.ReflTransGen.refl;
        · exact .single ( by exact ⟨ by aesop, by aesop, hCclique hs'_in_C hx1 hs'_eq_x ⟩ );
    -- Since `x` is relatively reachable inside `C ∪ D` from every vertex in `C ∪ D`, `C ∪ D` is connected.
    have hC_union_D_connected : RConn H (C ∪ D) := by
      intro a ha b hb;
      exact Relation.ReflTransGen.trans ( hx_reachable_all a ha ) ( rreach_symm _ _ ( hx_reachable_all b hb ) );
    obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ (C ∪ D) \ C, RSimplicial H (C ∪ D) z := by
      apply exists_rsimplicial_outside_clique H hRSH hCclique (Finset.subset_union_left) (by
      grind) hC_union_D_connected;
    refine' ⟨ z, _, _ ⟩ <;> simp_all +decide [ Finset.mem_sdiff, Finset.mem_union ];
    · exact hz1.1.resolve_left hz1.2;
    · exact isSimplicial_of_rsimplicial H ( fun w hw => by cases hsep z ( by tauto ) w hw <;> aesop ) hz2

/-
`RReach` on the whole vertex set is the same as `SimpleGraph.Reachable`.
-/
theorem rreach_univ_iff (H : SimpleGraph V) {a b : V} :
    RReach H Finset.univ a b ↔ H.Reachable a b := by
  constructor;
  · intro h;
    induction h;
    · exact SimpleGraph.Reachable.refl a;
    · rename_i a b c hab hbc ih;
      exact ih.trans ( SimpleGraph.Adj.reachable hbc.2.2 );
  · rintro ⟨ p ⟩;
    induction' p with a b p ih;
    · exact Relation.ReflTransGen.refl;
    · exact .single ⟨ Finset.mem_univ _, Finset.mem_univ _, by assumption ⟩ |> Relation.ReflTransGen.trans <| by assumption;

/-
The disconnected case of Step 3: a non-connected (nonempty) chordal graph has two nonadjacent
simplicial vertices (representatives of two different components).
-/
theorem exists_two_nonadj_simplicial_of_not_connected (H : SimpleGraph V)
    (hchord : ChordalStructure H) (hne : Nonempty V) (hnconn : ¬ H.Connected) :
    ∃ a b : V, a ≠ b ∧ ¬ H.Adj a b ∧ IsSimplicial H a ∧ IsSimplicial H b := by
  have h_components : ∃ a b : V, ¬ H.Reachable a b := by
    simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
  obtain ⟨ a, b, h ⟩ := h_components; have := hchord.simplicial_hereditary; simp_all +decide [ SimpleGraph.connected_iff ] ;
  obtain ⟨ s1, hs1 ⟩ := this { v | H.Reachable a v } ⟨ a, by simp +decide ⟩
  obtain ⟨ s2, hs2 ⟩ := this { v | H.Reachable b v } ⟨ b, by simp +decide ⟩
  generalize_proofs at *; (
  refine' ⟨ s1, s2, _, _, _, _ ⟩ <;> simp_all +decide [ IsSimplicial ];
  · rintro rfl; exact h ( hs1.choose.trans hs2.choose.symm ) ;
  · intro h_adj
    have h_reachable : H.Reachable a s2 := by
      exact hs1.1.trans ( SimpleGraph.Adj.reachable h_adj )
    generalize_proofs at *; (
    exact h ( h_reachable.trans ( hs2.choose.symm ) ));
  · intro x hx y hy; have := hs1.2; simp_all +decide [ SimpleGraph.IsClique, Set.Pairwise ] ;
    exact fun hxy => this x ( hs1.1.trans ( SimpleGraph.Adj.reachable hx ) ) hx y ( hs1.1.trans ( SimpleGraph.Adj.reachable hy ) ) hy hxy;
  · intro u hu v hv huv; have := hs2.2; simp_all +decide [ SimpleGraph.IsClique, Set.Pairwise ] ;
    exact this u ( hs2.1.trans ( SimpleGraph.Adj.reachable hu ) ) hu v ( hs2.1.trans ( SimpleGraph.Adj.reachable hv ) ) hv huv)

/-
The connected component of `u` inside `S` (characterized by `hDdef`) is itself connected.
-/
theorem rconn_component (H : SimpleGraph V) {S : Finset V} {u : V} {D : Finset V}
    (hDdef : ∀ w, w ∈ D ↔ (w ∈ S ∧ RReach H S u w)) (huD : u ∈ D) : RConn H D := by
  have h_aux : ∀ w, w ∈ D → RReach H D u w := by
    intro w hw;
    induction' hDdef w |>.1 hw |>.2 with v hv ih;
    · exact Relation.ReflTransGen.refl;
    · grind +locals;
  exact fun a ha b hb => ( rreach_symm H D ( h_aux a ha ) ).trans ( h_aux b hb )

/-
The component of `u` inside `S` is separated from the rest: any `S`-neighbor of a component
vertex is again in the component.
-/