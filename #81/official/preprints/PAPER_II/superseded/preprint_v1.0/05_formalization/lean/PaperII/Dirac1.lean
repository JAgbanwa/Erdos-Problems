import PaperII.IsChordal
import PaperII.Dirac

/-!
# Paper II — Dirac-1 (A3a) from `IsChordal` (Path 2, Fase 3)

Dirac-1 (A3a): a nonempty chordal graph has a simplicial vertex (`dirac_simplicial`). Engine: in a
chordal graph every minimal vertex separator is a clique (`minimal_separator_isClique`), proven from
the standard chord definition. Fully proven (sorry-free); `dirac_simplicial` discharges the last
Dirac-family obligation for the unconditional `theorem_1_2`.
-/

open scoped BigOperators

namespace PaperII

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `a` reaches `b` **avoiding** `S`: a walk `a → b` all of whose vertices lie outside `S`. -/
def AvoidReach (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) a b

/-- `S` **separates** `a` from `b`: neither is in `S`, and there is no `S`-avoiding walk `a → b`. -/
def Separates (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ AvoidReach G S a b

/-- `S` is a **minimal** `a`–`b` separator: it separates them, and no proper subset does. -/
def IsMinimalSeparator (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  Separates G S a b ∧ ∀ T : Finset V, T ⊂ S → ¬ Separates G T a b

/-! ### Helper lemmas (private) -/

/-
`AvoidReach` is symmetric (the underlying step relation is symmetric).
-/
omit [Fintype V] [DecidableEq V] in
theorem avoidReach_symm (G : SimpleGraph V) (S : Finset V) {a b : V}
    (h : AvoidReach G S a b) : AvoidReach G S b a := by
  induction h;
  · constructor;
  · rename_i b c hb hc ih;
    exact Relation.ReflTransGen.head ⟨ hc.2.1, hc.1, hc.2.2.symm ⟩ ih

/-
`Separates` is symmetric in the two endpoints.
-/
omit [Fintype V] [DecidableEq V] in
theorem separates_symm (G : SimpleGraph V) {S : Finset V} {a b : V}
    (h : Separates G S a b) : Separates G S b a := by
  exact ⟨ h.2.1, h.1, fun h' => h.2.2 ( avoidReach_symm G S h' ) ⟩

/-
Every vertex reachable from `a` while avoiding `S` (with `a ∉ S`) is itself outside `S`.
-/
omit [Fintype V] [DecidableEq V] in
theorem avoidReach_notMem (G : SimpleGraph V) {S : Finset V} {a b : V}
    (h : AvoidReach G S a b) (ha : a ∉ S) : b ∉ S := by
  induction h <;> aesop

/-
An `S`-avoiding reach `p → q` is witnessed by an actual walk all of whose vertices are
`S`-avoidingly reachable from `p`.
-/
omit [Fintype V] [DecidableEq V] in
theorem avoidReach_walk (G : SimpleGraph V) (S : Finset V) {p q : V}
    (h : AvoidReach G S p q) :
    ∃ P : G.Walk p q, ∀ w ∈ P.support, AvoidReach G S p w := by
  induction' h with c d hcd ih;
  · refine' ⟨ SimpleGraph.Walk.nil, _ ⟩ ; simp +decide [ AvoidReach ];
    rfl;
  · obtain ⟨ P, hP ⟩ := ‹_›; use P.append ( SimpleGraph.Walk.cons ih.2.2 SimpleGraph.Walk.nil ) ; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    rintro w ( hw | rfl ) <;> [ exact hP _ hw; exact Relation.ReflTransGen.tail hcd ⟨ ih.1, ih.2.1, ih.2.2 ⟩ ]

/-
**Minimality neighbour lemma.** If `S` is a minimal `a`–`b` separator and `x ∈ S`, then `x`
has a neighbour on the `a`-side (reachable from `a` avoiding `S`).
-/
omit [Fintype V] in
theorem sep_exists_aside_nbr (G : SimpleGraph V) {S : Finset V} {a b : V}
    (hS : IsMinimalSeparator G S a b) {x : V} (hx : x ∈ S) :
    ∃ u, AvoidReach G S a u ∧ G.Adj u x := by
  -- By minimality, $S \setminus \{x\}$ is not a separator of $a$ and $b$, so there exists a path between $a$ and $b$ in $G$ that avoids $S \setminus \{x\}$.
  have h_path : AvoidReach G (S.erase x) a b := by
    have := hS.2 ( S.erase x ) ( Finset.erase_ssubset hx ) ; simp_all +decide [ Separates ] ;
    exact this ( fun _ => hS.1.1 ) ( fun _ => hS.1.2.1 );
  have h_claim : ∀ c, AvoidReach G (S.erase x) a c → (AvoidReach G S a c ∨ ∃ u, AvoidReach G S a u ∧ G.Adj u x) := by
    intro c hc
    induction' hc with c' hc' ih;
    · exact Or.inl ( Relation.ReflTransGen.refl );
    · grind +locals;
  cases h_claim b h_path <;> simp_all +decide [ IsMinimalSeparator, Separates ]

/-
A `G`-walk `x → y` all of whose vertices lie in `K` lifts to a walk in `G.induce K`, giving
reachability there.
-/
omit [Fintype V] [DecidableEq V] in
theorem reachable_induce_of_walk (G : SimpleGraph V) (K : Set V) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) :
    (G.induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction' P with x y hxy ih;
  · exact ⟨ SimpleGraph.Walk.nil ⟩;
  · rename_i p hp;
    specialize hp ( by aesop ) hy ( by aesop );
    exact SimpleGraph.Reachable.trans ( SimpleGraph.Adj.reachable <| by aesop ) hp

/-
**Geodesics are chordless.** On a shortest walk, any two adjacent support vertices are joined by
an edge of the walk.
-/
theorem geodesic_adj_imp_edge {W : Type*} {G' : SimpleGraph W} {u v : W}
    (p : G'.Walk u v) (hp : p.length = G'.dist u v)
    {s t : W} (hs : s ∈ p.support) (ht : t ∈ p.support) (hadj : G'.Adj s t) :
    s(s, t) ∈ p.edges := by
  by_contra h;
  obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ : G'.Walk u s, ∃ q₂ : G'.Walk s v, p = q₁.append q₂ := by
    grind +suggestions;
  -- If `t ∈ q₁.support`, then `q₁.takeUntil t` is a subwalk of `p` from `u` to `t`, and `q₁.dropUntil t` is a subwalk from `t` to `s`.
  by_cases ht₁ : t ∈ q₁.support;
  · obtain ⟨q₁', q₂', hq'⟩ : ∃ q₁' : G'.Walk u t, ∃ q₂' : G'.Walk t s, q₁ = q₁'.append q₂' := by
      grind +suggestions;
    simp_all +decide [ SimpleGraph.Walk.edges_append ];
    have h_dist : G'.dist u v ≤ q₁'.length + 1 + q₂.length := by
      have h_dist : G'.dist u v ≤ (q₁'.append (SimpleGraph.Walk.cons hadj.symm q₂)).length := by
        exact SimpleGraph.dist_le _;
      exact h_dist.trans ( by simp +decide [ add_assoc ] );
    have h_dist : q₂'.length ≥ 2 := by
      rcases q₂' with ( _ | ⟨ _, _, q₂' ⟩ ) <;> simp_all +decide;
    grind;
  · -- If `t ∈ q₂.support`, then `q₂.takeUntil t` is a subwalk of `p` from `s` to `t`, and `q₂.dropUntil t` is a subwalk from `t` to `v`.
    obtain ⟨q₂₁, q₂₂, hq₂⟩ : ∃ q₂₁ : G'.Walk s t, ∃ q₂₂ : G'.Walk t v, q₂ = q₂₁.append q₂₂ := by
      grind +suggestions;
    have h_dist : G'.dist u v ≤ q₁.length + 1 + q₂₂.length := by
      have h_dist : G'.dist u v ≤ (q₁.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).length + q₂₂.length := by
        have h_walk : ∃ w : G'.Walk u v, w.length = (q₁.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)).length + q₂₂.length := by
          exact ⟨ ( q₁.append ( SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil ) ).append q₂₂, by simp +decide ⟩
        exact h_walk.choose_spec ▸ SimpleGraph.dist_le _;
      exact h_dist.trans ( by simp +decide [ SimpleGraph.Walk.length_append ] );
    rcases q₂₁ with ( _ | ⟨ _, _, q₂₁ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.length ];
    linarith

/-
From a `G`-walk `x → y` staying inside `K`, extract an induced (chordless) `G`-path `x → y`
staying inside `K`.
-/
omit [Fintype V] [DecidableEq V] in
theorem exists_induced_path_of_walk (G : SimpleGraph V) (K : Set V) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) :
    ∃ Q : G.Walk x y, Q.IsPath ∧ (∀ w ∈ Q.support, w ∈ K) ∧
      (∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : (G.induce K).Walk ⟨x, hx⟩ ⟨y, hy⟩, Q.IsPath ∧ Q.length = (G.induce K).dist ⟨x, hx⟩ ⟨y, hy⟩ := by
    apply_rules [ SimpleGraph.Reachable.exists_path_of_dist ];
    convert reachable_induce_of_walk G K hx hy P hsupp using 1;
  refine' ⟨ Q.map ( SimpleGraph.Hom.comap _ _ ), _, _, _ ⟩ <;> simp_all +decide;
  · simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    exact List.Nodup.map ( fun x y => by aesop ) hQ.1;
  · intro s hs hs' t ht ht' hst
    have := geodesic_adj_imp_edge Q hQ.2 hs' ht' hst
    aesop

/-
**Cycle contradiction.** Two internally-disjoint induced `x`–`y` paths (each of length `≥ 2`,
no cross edges except through the endpoints, `x ≠ y` nonadjacent) form a chordless cycle of length
`≥ 4`, contradicting chordality.
-/
omit [Fintype V] in
theorem two_induced_paths_not_chordal (G : SimpleGraph V) (hG : IsChordal G) {x y : V}
    (P Q : G.Walk x y) (hP : P.IsPath) (hQ : Q.IsPath)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    (hPlen : 2 ≤ P.length) (hQlen : 2 ≤ Q.length)
    (hPind : ∀ s ∈ P.support, ∀ t ∈ P.support, G.Adj s t → s(s, t) ∈ P.edges)
    (hQind : ∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges)
    (hdisj : ∀ w, w ∈ P.support → w ∈ Q.support → w = x ∨ w = y)
    (hcross : ∀ s ∈ P.support, ∀ t ∈ Q.support, G.Adj s t →
        (s = x ∨ s = y) ∨ (t = x ∨ t = y)) :
    False := by
  convert hG _;
  rotate_left;
  exact x;
  exact P.append Q.reverse;
  simp +decide [ SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def ];
  refine' ⟨ _, _, _, _, _ ⟩;
  · refine' List.Nodup.append _ _ _;
    · exact hP.edges_nodup;
    · exact List.nodup_reverse.mpr ( hQ.edges_nodup );
    · intro e heP heQ;
      rcases e with ⟨ s, t ⟩;
      have h_contra : s ∈ P.support ∧ t ∈ P.support ∧ s ∈ Q.support ∧ t ∈ Q.support := by
        exact ⟨ by simpa using SimpleGraph.Walk.fst_mem_support_of_mem_edges _ heP, by simpa using SimpleGraph.Walk.snd_mem_support_of_mem_edges _ heP, by simpa using SimpleGraph.Walk.fst_mem_support_of_mem_edges _ ( List.mem_reverse.mp heQ ), by simpa using SimpleGraph.Walk.snd_mem_support_of_mem_edges _ ( List.mem_reverse.mp heQ ) ⟩;
      cases hdisj s h_contra.1 h_contra.2.2.1 <;> cases hdisj t h_contra.2.1 h_contra.2.2.2 <;> simp_all +decide;
      · exact absurd heP ( by simpa using P.edges_subset_edgeSet heP );
      · exact hnadj ( by simpa using P.edges_subset_edgeSet heP );
      · exact hnadj ( by simpa [ SimpleGraph.adj_comm ] using P.edges_subset_edgeSet heP );
      · exact absurd heP ( by simpa using P.edges_subset_edgeSet heP );
  · cases P <;> cases Q <;> simp_all +decide;
  · simp_all +decide [ SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse ];
    refine' List.Nodup.append _ _ _;
    · exact hP.support_nodup.tail;
    · exact List.nodup_reverse.mpr ( List.Nodup.sublist ( List.dropLast_sublist _ ) hQ.support_nodup );
    · simp_all +decide [ List.disjoint_left ];
      intro w hwP hwQ;
      cases hdisj w ( List.mem_of_mem_tail hwP ) ( List.mem_of_mem_dropLast hwQ ) <;> simp_all +decide;
      · cases P <;> cases Q <;> simp_all +decide [ SimpleGraph.Walk.support ];
      · have := List.mem_iff_getElem.mp hwQ;
        obtain ⟨ i, hi, hi' ⟩ := this;
        have := List.nodup_iff_injective_get.mp hQ.support_nodup;
        have := @this ⟨ i, by
          exact hi.trans_le ( by simp +decide ) ⟩ ⟨ Q.length, by
          simp +decide ⟩ ; simp_all +decide;
        grind;
  · linarith;
  · rintro z ( hz | hz ) w ( hw | hw ) hzw hzw' <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    · cases hcross z hz w hw hzw <;> aesop;
    · specialize hcross w hw z hz hzw.symm ; aesop

/-! ### Dirac helpers (private) -/

/-
An induced subgraph of a chordal graph is chordal.
-/
theorem isChordal_induce (G : SimpleGraph V) (hG : IsChordal G) (W : Set V) :
    IsChordal (G.induce W) := by
  have := @chordal_induce;
  exact this G hG ( Function.Embedding.subtype ( · ∈ W ) ) _ ( by simp +decide )

/-
A simplicial vertex of the induced subgraph on `↑T` is relatively simplicial in `T`.
-/
omit [Fintype V] [DecidableEq V] in
theorem rsimplicial_of_induce_simplicial (G : SimpleGraph V) (T : Finset V)
    (z : (T : Set V)) (hz : IsSimplicial (G.induce (T : Set V)) z) :
    RSimplicial G T z.val := by
  intro a a_in_T_and_Adj_z b b_in_T_and_Adj_z a_ne_b
  by_contra h_not_clique;
  contrapose! hz; simp_all +decide ;
  simp +decide [ IsSimplicial, Set.Pairwise ];
  exact ⟨ a, a_in_T_and_Adj_z.1, a_in_T_and_Adj_z.2, b, b_in_T_and_Adj_z.1, b_in_T_and_Adj_z.2, a_ne_b, h_not_clique ⟩

/-
A simplicial vertex of `G.induce W` whose `G`-neighbours all lie in `W` is simplicial in `G`.
-/
omit [Fintype V] [DecidableEq V] in
theorem isSimplicial_of_induce (G : SimpleGraph V) (W : Set V) (z : W)
    (hz : IsSimplicial (G.induce W) z) (hsub : ∀ w, G.Adj z.val w → w ∈ W) :
    IsSimplicial G z.val := by
  unfold IsSimplicial at *;
  intro p hp q hq hpq; have := hz ( show ⟨ p, hsub p hp ⟩ ∈ ( induce W G ).neighborSet z from by simpa [ SimpleGraph.mem_neighborSet ] using hp ) ( show ⟨ q, hsub q hq ⟩ ∈ ( induce W G ).neighborSet z from by simpa [ SimpleGraph.mem_neighborSet ] using hq ) ; aesop;

/-
`S`-avoiding reachability equals relative reachability inside the complement of `S`.
-/
theorem avoidReach_iff_rreach_compl (G : SimpleGraph V) (S : Finset V) (a b : V) :
    AvoidReach G S a b ↔ RReach G (Finset.univ \ S) a b := by
  constructor <;> intro h;
  · induction h;
    · exact Relation.ReflTransGen.refl;
    · exact Relation.ReflTransGen.tail ‹_› ( by unfold RStep; aesop );
  · convert h.mono _;
    simp +contextual [ RStep ]

/-
The complement of a nonadjacent pair `{a,b}` separates them.
-/
theorem separates_compl_pair (G : SimpleGraph V) {a b : V} (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) :
    Separates G ((Finset.univ.erase a).erase b) a b := by
  refine' ⟨ _, _, _ ⟩;
  · grind;
  · simp +decide;
  · -- By induction on the length of the path, we can show that if there is a path from a to b avoiding S, then a and b must be adjacent.
    have h_ind : ∀ c, AvoidReach G ((Finset.univ.erase a).erase b) a c → c = a := by
      intro c hc
      induction' hc with c' hc' ih;
      · rfl;
      · grind;
    exact fun h => hab ( h_ind b h ▸ rfl )

/-
From any separating set, a minimal separator exists.
-/
omit [DecidableEq V] in
theorem exists_minimal_separator (G : SimpleGraph V) {a b : V} (S₀ : Finset V)
    (h : Separates G S₀ a b) : ∃ S, IsMinimalSeparator G S a b := by
  -- By the well-ordering principle, there exists a minimal separating set S.
  obtain ⟨S, hS⟩ : ∃ S : Finset V, Separates G S a b ∧ ∀ T : Finset V, Separates G T a b → S.card ≤ T.card := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ S₀, h ⟩;
  refine' ⟨ S, hS.1, _ ⟩;
  exact fun T hT hT' => not_lt_of_ge ( hS.2 T hT' ) ( Finset.card_lt_card hT )

/-
Dirac-2, restricted form of `PaperII.rdirac2` with `hRSH` only required on subsets of `U`.
-/
set_option maxHeartbeats 1000000 in
theorem rdirac2U (H : SimpleGraph V) (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a) :
    ∀ (n : ℕ) (S : Finset V), S ⊆ U → S.card = n → RConn H S →
      (¬ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b) →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬ H.Adj a b ∧ RSimplicial H S a ∧ RSimplicial H S b := by
  intro n S hSU hSn hSconn hSnotcomplete
  induction' n using Nat.strong_induction_on with n ih generalizing S
  by_cases hScomplete : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b;
  · contradiction;
  · obtain ⟨ v, hv, hv' ⟩ := hRSH S hSU ( Finset.card_pos.mp ( by linarith [ show 0 < S.card from Nat.pos_of_ne_zero ( by aesop_cat ) ] ) );
    by_cases hS'complete : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, a ≠ b → H.Adj a b;
    · obtain ⟨ p, hp, q, hq, hpq, hpq' ⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ¬H.Adj p q := by
        grind;
      by_cases hpv : p = v <;> by_cases hqv : q = v <;> simp_all +decide only [RSimplicial];
      · contradiction;
      · use v, hv, q, hq;
        simp_all +decide [ SimpleGraph.IsClique ];
        intro a ha b hb hab; by_cases ha' : a = v <;> by_cases hb' : b = v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
      · refine' ⟨ p, hp, v, hv, hpq, hpq', _, _ ⟩ <;> simp_all +decide [ SimpleGraph.IsClique ];
        intro a ha b hb hab; by_cases ha' : a = v <;> by_cases hb' : b = v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
      · exact False.elim ( hpq' ( hS'complete p ( by aesop ) q ( by aesop ) hpq ) );
    · obtain ⟨ a, ha, b, hb, hab, hne, hadj, hsimp ⟩ := ih ( n - 1 ) ( Nat.sub_lt ( by linarith [ Finset.card_pos.mpr ⟨ v, hv ⟩ ] ) zero_lt_one ) ( S.erase v ) ( Finset.Subset.trans ( Finset.erase_subset _ _ ) hSU ) ( by rw [ Finset.card_erase_of_mem hv, hSn ] ) ( rconn_erase H hv' hSconn ) hS'complete;
      by_cases hav : H.Adj a v <;> by_cases hbv : H.Adj b v <;> simp_all +decide only [RSimplicial];
      · have := hv' ( show a ∈ { b | b ∈ S ∧ H.Adj v b } from ⟨ Finset.mem_of_mem_erase ha, hav.symm ⟩ ) ( show b ∈ { b | b ∈ S ∧ H.Adj v b } from ⟨ Finset.mem_of_mem_erase hb, hbv.symm ⟩ ) ; simp_all +decide ;
      · use b, by aesop, v, by aesop;
        simp_all +decide [ SimpleGraph.IsClique ];
        intro x hx y hy hxy; by_cases hxv : x = v <;> by_cases hyv : y = v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact hsimp ⟨ ⟨ hxv, hx.1 ⟩, hx.2 ⟩ ⟨ ⟨ hyv, hy.1 ⟩, hy.2 ⟩ hxy;
      · use a, Finset.mem_of_mem_erase ha, v, hv;
        simp_all +decide [ SimpleGraph.IsClique ];
        intro x hx y hy hxy; by_cases hxv : x = v <;> by_cases hyv : y = v <;> simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact hadj ⟨ ⟨ hxv, hx.1 ⟩, hx.2 ⟩ ⟨ ⟨ hyv, hy.1 ⟩, hy.2 ⟩ hxy;
      · simp_all +decide [ Finset.mem_erase, Set.Pairwise ];
        grind +splitImp

/-
Restricted form of `PaperII.exists_rsimplicial_outside_clique`.
-/
theorem exists_rsimplicial_outside_cliqueU (H : SimpleGraph V) (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    {K S : Finset V} (hSU : S ⊆ U) (hK : H.IsClique (K : Set V))
    (hne : (S \ K).Nonempty) (hconn : RConn H S) :
    ∃ z ∈ S \ K, RSimplicial H S z := by
  by_cases hcomp : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b;
  · obtain ⟨ z, hz ⟩ := hne;
    refine' ⟨ z, hz, _ ⟩;
    intro x hx y hy; aesop;
  · obtain ⟨ a, ha, b, hb, hab, h ⟩ := rdirac2U H U hRSH _ _ hSU rfl hconn hcomp;
    by_cases haK : a ∈ K <;> by_cases hbK : b ∈ K <;> simp_all +decide [ Finset.subset_iff ];
    · exact False.elim ( h.1 ( hK haK hbK hab ) );
    · exact ⟨ b, ⟨ hb, hbK ⟩, h.2.2 ⟩;
    · exact ⟨ a, ⟨ ha, haK ⟩, h.2.1 ⟩;
    · exact ⟨ a, ⟨ ha, haK ⟩, h.2.1 ⟩

/-
Restricted form of `PaperII.exists_simplicial_in_component`: only needs `hRSH` on subsets of
`U ⊇ C ∪ D`, and returns a genuinely simplicial vertex of `H` inside `D`.
-/
theorem exists_simplicial_in_componentU (H : SimpleGraph V) (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    (C : Finset V) (hCclique : H.IsClique (C : Set V))
    (D : Finset V) (hCDU : C ∪ D ⊆ U)
    (hDC : ∀ d ∈ D, d ∉ C) (hDne : D.Nonempty) (hDconn : RConn H D)
    (hsep : ∀ d ∈ D, ∀ w, H.Adj d w → w ∈ C ∨ w ∈ D) :
    ∃ z ∈ D, IsSimplicial H z := by
  -- By `hRSH`, we can get a relatively-simplicial `s ∈ D`.
  obtain ⟨s, hsD, hs⟩ : ∃ s ∈ D, RSimplicial H D s := by
    exact hRSH D ( Finset.subset_union_right.trans hCDU ) hDne;
  by_cases hcase : ∀ w, H.Adj s w → w ∈ D;
  · exact ⟨ s, hsD, isSimplicial_of_rsimplicial H hcase hs ⟩;
  · -- Since $s$ has a neighbor $x \in C$, we can build reachability of $x$ inside $C \cup D$ from every vertex of $C \cup D$.
    obtain ⟨x, hx⟩ : ∃ x ∈ C, H.Adj s x := by
      grind
    have hreach : ∀ a ∈ C ∪ D, RReach H (C ∪ D) a x := by
      intro a ha; by_cases haC : a ∈ C <;> simp_all +decide [ RReach ] ;
      · by_cases hax : a = x;
        · exact hax.symm ▸ Relation.ReflTransGen.refl;
        · exact .single ⟨ by aesop, by aesop, hCclique haC hx.1 hax ⟩;
      · have := hDconn a ha s hsD;
        exact this.mono ( fun p q hpq => by exact ⟨ Finset.mem_union_right _ hpq.1, Finset.mem_union_right _ hpq.2.1, hpq.2.2 ⟩ ) |> fun h => h.tail ( by exact ⟨ Finset.mem_union_right _ hsD, Finset.mem_union_left _ hx.1, hx.2 ⟩ );
    -- By `hreach`, we have `RConn H (C ∪ D)`.
    have hRConn : RConn H (C ∪ D) := by
      intro a ha b hb;
      exact Relation.ReflTransGen.trans ( hreach a ha ) ( Relation.ReflTransGen.trans ( rreach_symm _ _ ( hreach b hb ) ) ( Relation.ReflTransGen.refl ) );
    -- By `hRSH`, we can get a relatively-simplicial `z ∈ (C ∪ D) \ C`.
    obtain ⟨z, hzD, hz⟩ : ∃ z ∈ (C ∪ D) \ C, RSimplicial H (C ∪ D) z := by
      apply exists_rsimplicial_outside_cliqueU H U hRSH hCDU hCclique (by
      grind) hRConn;
    refine' ⟨ z, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact hzD.1.resolve_left hzD.2;
    · exact isSimplicial_of_rsimplicial H ( fun w hw => by cases hsep z ( hzD.1.resolve_left hzD.2 ) w hw <;> aesop ) hz

/-
**Engine.** In a chordal graph, every minimal `a`–`b` separator is a clique.
Proof: for nonadjacent `x, y ∈ S`, minimality gives neighbours of each in both
components; shortest `x→y` paths through the `a`-component and the `b`-component form an induced
cycle of length `≥ 4` with no chord, contradicting `IsChordal`.
-/
theorem minimal_separator_isClique (G : SimpleGraph V) (hG : IsChordal G)
    {S : Finset V} {a b : V} (hS : IsMinimalSeparator G S a b) :
    G.IsClique (S : Set V) := by
  by_contra h_not_clique;
  obtain ⟨x, y, hxS, hyS, hxy⟩ : ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ ¬G.Adj x y := by
    simp_all +decide [ Set.Pairwise ];
  obtain ⟨ux, haux, hadjux⟩ : ∃ ux, AvoidReach G S a ux ∧ G.Adj ux x := by
    exact sep_exists_aside_nbr G hS hxS
  obtain ⟨uy, hauy, hadjuy⟩ : ∃ uy, AvoidReach G S a uy ∧ G.Adj uy y := by
    exact sep_exists_aside_nbr G hS hyS
  obtain ⟨wx, hbwx, hadjwx⟩ : ∃ wx, AvoidReach G S b wx ∧ G.Adj wx x := by
    have := sep_exists_aside_nbr G ( show IsMinimalSeparator G S b a from by
                                      exact ⟨ separates_symm G hS.1, fun T hT hT' => hS.2 T hT ( separates_symm G hT' ) ⟩ ) hxS; aesop;
  obtain ⟨wy, hbwy, hadjwy⟩ : ∃ wy, AvoidReach G S b wy ∧ G.Adj wy y := by
    have := sep_exists_aside_nbr G ( show IsMinimalSeparator G S b a from ?_ ) hyS; tauto;
    exact ⟨ separates_symm G hS.1, fun T hT hT' => hS.2 T hT ( separates_symm G hT' ) ⟩;
  obtain ⟨Pw, hPw⟩ : ∃ Pw : G.Walk x y, ∀ w ∈ Pw.support, AvoidReach G S a w ∨ w = x ∨ w = y := by
    obtain ⟨Pw, hPw⟩ : ∃ Pw : G.Walk ux uy, ∀ w ∈ Pw.support, AvoidReach G S a w := by
      obtain ⟨Pw, hPw⟩ : ∃ Pw : G.Walk ux uy, ∀ w ∈ Pw.support, AvoidReach G S a w := by
        have h_avoidReach : AvoidReach G S ux uy := by
          exact Relation.ReflTransGen.trans ( avoidReach_symm _ _ haux ) hauy
        have := avoidReach_walk G S h_avoidReach;
        exact ⟨ this.choose, fun w hw => haux.trans ( this.choose_spec w hw ) ⟩;
      use Pw;
    use SimpleGraph.Walk.cons hadjux.symm (Pw.append (SimpleGraph.Walk.cons hadjuy SimpleGraph.Walk.nil));
    simp +zetaDelta at *;
    rintro w ( hw | rfl | rfl ) <;> [ exact Or.inl ( hPw _ hw ) ; exact Or.inl hauy; exact Or.inr ( Or.inr rfl ) ]
  obtain ⟨Qw, hQw⟩ : ∃ Qw : G.Walk x y, ∀ w ∈ Qw.support, AvoidReach G S b w ∨ w = x ∨ w = y := by
    obtain ⟨Qw, hQw⟩ : ∃ Qw : G.Walk wx wy, ∀ w ∈ Qw.support, AvoidReach G S b w := by
      have := avoidReach_walk G S hbwx;
      obtain ⟨ Qw, hQw ⟩ := this;
      obtain ⟨ Qw', hQw' ⟩ := avoidReach_walk G S hbwy;
      exact ⟨ Qw.reverse.append Qw', by aesop ⟩;
    use SimpleGraph.Walk.cons hadjwx.symm (Qw.append (SimpleGraph.Walk.cons hadjwy SimpleGraph.Walk.nil));
    simp +decide [ SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons ];
    grind;
  obtain ⟨P, hP⟩ : ∃ P : G.Walk x y, P.IsPath ∧ (∀ w ∈ P.support, AvoidReach G S a w ∨ w = x ∨ w = y) ∧ (∀ s ∈ P.support, ∀ t ∈ P.support, G.Adj s t → s(s, t) ∈ P.edges) := by
    apply exists_induced_path_of_walk G ( { w | AvoidReach G S a w ∨ w = x ∨ w = y } ) ( by aesop ) ( by aesop ) Pw ( by aesop )
  obtain ⟨Q, hQ⟩ : ∃ Q : G.Walk x y, Q.IsPath ∧ (∀ w ∈ Q.support, AvoidReach G S b w ∨ w = x ∨ w = y) ∧ (∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges) := by
    apply exists_induced_path_of_walk;
    exacts [ Or.inr <| Or.inl rfl, Or.inr <| Or.inr rfl, hQw ];
  apply two_induced_paths_not_chordal G hG P Q hP.1 hQ.1 hxy.1 hxy.2 (by
  rcases P with ( _ | ⟨ _, _, P ⟩ ) <;> simp_all +decide) (by
  rcases Q with ( _ | ⟨ _, _, Q ⟩ ) <;> simp_all +decide) hP.2.2 hQ.2.2 (by
  intro w hwP hwQ
  by_contra h_contra
  have h_avoid_a : AvoidReach G S a w := by
    exact hP.2.1 w hwP |> Or.resolve_right <| by tauto;
  have h_avoid_b : AvoidReach G S b w := by
    exact hQ.2.1 w hwQ |> Or.resolve_right <| by tauto;
  have h_avoid_ab : AvoidReach G S a b := by
    exact h_avoid_a.trans ( avoidReach_symm _ _ h_avoid_b )
  exact hS.1.2.2 h_avoid_ab) (by
  intro s hs t ht hst
  by_contra h_contra
  push_neg at h_contra
  have h_avoid : AvoidReach G S a s ∧ AvoidReach G S b t := by
    grind;
  have h_avoid : AvoidReach G S a b := by
    have h_avoid : AvoidReach G S a t := by
      grind +locals;
    have h_avoid : AvoidReach G S t b := by
      exact avoidReach_symm _ _ ( by tauto );
    exact Relation.ReflTransGen.trans ‹_› ‹_›;
  exact hS.1.2.2 h_avoid)

/-
Disconnected case of the Dirac induction: recurse into the connected component of some `a`.
-/
omit [DecidableEq V] in
theorem dirac_step_disconnected (G : SimpleGraph V)
    (hnconn : ¬ G.Connected) (hne : Nonempty V)
    (ih_ind : ∀ (W : Finset V), W.card < Fintype.card V → W.Nonempty →
        ∃ z : (↑W : Set V), IsSimplicial (G.induce (↑W : Set V)) z) :
    ∃ v : V, IsSimplicial G v := by
  rw [ SimpleGraph.connected_iff_exists_forall_reachable ] at hnconn;
  push_neg at hnconn;
  obtain ⟨ v0, hv0 ⟩ := hnconn hne.some;
  by_cases hWc : {w : V | G.Reachable hne.some w}.Finite;
  · convert ih_ind ( hWc.toFinset ) _ _;
    · constructor <;> rintro ⟨ z, hz ⟩;
      · convert ih_ind ( hWc.toFinset ) _ _;
        · exact Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ _, fun h => hv0 <| by simpa using Finset.ext_iff.mp h v0 ⟩ );
        · exact ⟨ hne.some, hWc.mem_toFinset.mpr ( SimpleGraph.Reachable.refl _ ) ⟩;
      · refine' ⟨ z, isSimplicial_of_induce G _ _ hz _ ⟩;
        intro w hw; exact hWc.mem_toFinset.mpr ( by exact SimpleGraph.Reachable.trans ( by exact z.2 |> fun h => by simpa using hWc.mem_toFinset.mp h ) ( SimpleGraph.Adj.reachable hw ) ) ;
    · exact Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ _, fun h => hv0 <| by simpa using Finset.ext_iff.mp h v0 ⟩ );
    · exact ⟨ hne.some, hWc.mem_toFinset.mpr ( SimpleGraph.Reachable.refl _ ) ⟩;
  · exact False.elim ( hWc <| Set.toFinite _ )

/-- Connected non-complete case: a minimal separator is a clique, and a component `D` of `G - S`
contains a simplicial vertex. -/
theorem dirac_step_separator (G : SimpleGraph V) (hG : IsChordal G)
    {a b : V} (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (ih_ind : ∀ (W : Finset V), W.card < Fintype.card V → W.Nonempty →
        ∃ z : (↑W : Set V), IsSimplicial (G.induce (↑W : Set V)) z) :
    ∃ v : V, IsSimplicial G v := by
  classical
  obtain ⟨S, hS⟩ := exists_minimal_separator G _ (separates_compl_pair G hab hnadj)
  obtain ⟨haS, hbS, hnr⟩ := hS.1
  have hCclique := minimal_separator_isClique G hG hS
  set Sc : Finset V := Finset.univ \ S with hSc
  set D : Finset V := Finset.univ.filter (fun w => w ∈ Sc ∧ RReach G Sc a w) with hD
  have hDdef : ∀ w, w ∈ D ↔ (w ∈ Sc ∧ RReach G Sc a w) := by
    intro w; simp [hD, Finset.mem_filter]
  have haSc : a ∈ Sc := by simp [hSc, Finset.mem_sdiff, haS]
  have haD : a ∈ D := (hDdef a).2 ⟨haSc, Relation.ReflTransGen.refl⟩
  have hDne : D.Nonempty := ⟨a, haD⟩
  have hbD : b ∉ D := by
    intro hbd
    rw [hDdef] at hbd
    exact hnr ((avoidReach_iff_rreach_compl G S a b).2 hbd.2)
  have hDconn : RConn G D := rconn_component G hDdef haD
  have hDC : ∀ d ∈ D, d ∉ S := by
    intro d hd
    have h1 := ((hDdef d).1 hd).1
    simp [hSc, Finset.mem_sdiff] at h1
    exact h1
  have hsep' : ∀ d ∈ D, ∀ w, G.Adj d w → w ∈ S ∨ w ∈ D := by
    intro d hd w hadj
    by_cases hwS : w ∈ S
    · exact Or.inl hwS
    · refine Or.inr (component_sep G hDdef d hd w ?_ hadj)
      simp [hSc, Finset.mem_sdiff, hwS]
  have hbU : b ∉ S ∪ D := by simp [Finset.mem_union, hbS, hbD]
  have hUlt : (S ∪ D).card < Fintype.card V := by
    rw [← Finset.card_univ]
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨b, Finset.mem_univ b, hbU⟩
  have hRSH : ∀ T : Finset V, T ⊆ S ∪ D → T.Nonempty → ∃ a ∈ T, RSimplicial G T a := by
    intro T hTU hTne
    have hTlt : T.card < Fintype.card V := lt_of_le_of_lt (Finset.card_le_card hTU) hUlt
    obtain ⟨z, hz⟩ := ih_ind T hTlt hTne
    refine ⟨z.val, ?_, rsimplicial_of_induce_simplicial G T z hz⟩
    have hzmem := z.property
    rwa [Finset.mem_coe] at hzmem
  obtain ⟨z, hzD, hzS⟩ := exists_simplicial_in_componentU G (S ∪ D) hRSH S hCclique D
    (Finset.Subset.refl _) hDC hDne hDconn hsep'
  exact ⟨z, hzS⟩

/-- **Dirac-1**, general (polymorphic) form, proved by strong induction on `Fintype.card`. -/
theorem dirac_gen :
    ∀ (n : ℕ) {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U),
      Fintype.card U = n → IsChordal G → Nonempty U → ∃ v : U, IsSimplicial G v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ _ G hcard hG hne
    have ih_ind : ∀ (W : Finset U), W.card < Fintype.card U → W.Nonempty →
        ∃ z : (↑W : Set U), IsSimplicial (G.induce (↑W : Set U)) z := by
      intro W hW hWne
      obtain ⟨w0, hw0⟩ := hWne
      exact ih W.card (by rw [hcard] at hW; exact hW)
        (G.induce (↑W : Set U)) (Fintype.card_coe W) (isChordal_induce G hG _) ⟨⟨w0, hw0⟩⟩
    by_cases hcomp : ∀ u w : U, u ≠ w → G.Adj u w
    · obtain ⟨v0⟩ := hne
      exact ⟨v0, fun p _ q _ hpq => hcomp p q hpq⟩
    · by_cases hconn : G.Connected
      · push_neg at hcomp
        obtain ⟨a, b, hab, hnadj⟩ := hcomp
        exact dirac_step_separator G hG hab hnadj ih_ind
      · exact dira