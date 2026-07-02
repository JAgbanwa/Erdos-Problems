import Mathlib
open scoped BigOperators
open scoped Classical
set_option maxHeartbeats 8000000
/-!
# A disproof of a uniform linear Ramsey bound from a `(2,3)`-sparsity hypothesis
This file formalises the note *"A disproof of a uniform linear Ramsey bound from a
`(2,3)`-sparsity hypothesis"*, which resolves (negatively) Erdős problem #566.
The question asks:
> Let `G` be such that any subgraph on `k` vertices has at most `2k - 3` edges.  Is it true
> that, if `H` has `m` edges and no isolated vertices, then `R(G,H) ≪ m`?
We show the answer is **no**: there is no absolute constant `C` such that
`R(G,H) ≤ C·m` for all `(2,3)`-sparse graphs `G` and all `H` with `m` edges and no isolated
vertices.  The obstruction already occurs when `G` is a path and `H = K₂` (so `m = 1`):
`R(Pₙ, K₂) = n`, which is unbounded, while the sparsity condition controls only the density
of `G`, not its number of vertices.
## Main statements
* `Erdos566.pathGraph_is23Sparse` : every path `Pₙ` is `(2,3)`-sparse (Lemma 2).
* `Erdos566.ramsey_ge_of_lt_card` : `R(A,B) ≥ |V(A)|` whenever `B` has an edge (Proposition 3),
  formalised as: no `N < |V(A)|` witnesses the Ramsey property.
* `Erdos566.ramsey_pathGraph_K2` : `R(Pₙ, K₂) = n` for `n ≥ 2` (Corollary 5).
* `Erdos566.not_proposedBound` : the proposed uniform linear Ramsey bound is false (the disproof).
-/
namespace Erdos566
open SimpleGraph
/-! ## The Ramsey number `R(G,H)` -/
/-- The set of `N` such that every red/blue colouring of the complete graph `K_N`
(encoded by its red graph `c : SimpleGraph (Fin N)`, with blue graph `cᶜ`) contains a
red copy of `G` or a blue copy of `H`. -/
def ramseySet {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : Set ℕ :=
  {N | ∀ c : SimpleGraph (Fin N), G ⊑ c ∨ H ⊑ cᶜ}
/-- The Ramsey number `R(G,H)`: the least `N` such that every red/blue colouring of `K_N`
contains a red copy of `G` or a blue copy of `H`. -/
noncomputable def Ramsey {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf (ramseySet G H)
/-! ## The `(2,3)`-sparsity condition -/
/-- A graph `G` on a finite vertex set is `(2,3)`-sparse if every subgraph `F` with at least
two vertices has at most `2·|V(F)| - 3` edges.  This is the hypothesis on `G` in the problem. -/
def Is23Sparse {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ F : G.Subgraph, 2 ≤ F.verts.ncard → F.edgeSet.ncard ≤ 2 * F.verts.ncard - 3
/-- A graph has no isolated vertices if every vertex is incident to some edge. -/
def NoIsolated {β : Type} (H : SimpleGraph β) : Prop := ∀ v : β, ∃ w, H.Adj v w
/-- The number of edges of a (finite) graph. -/
noncomputable def numEdges {β : Type} (H : SimpleGraph β) : ℕ := H.edgeSet.ncard
/-! ## Two elementary containment facts -/
/-- A copy of `G` inside a colouring of `K_N` needs at least `|V(G)|` vertices. -/
lemma card_le_of_isContained {α : Type} [Fintype α] {N : ℕ} (G : SimpleGraph α)
    (c : SimpleGraph (Fin N)) (h : G ⊑ c) : Fintype.card α ≤ N := by
  obtain ⟨f⟩ := h
  calc Fintype.card α ≤ Fintype.card (Fin N) := Fintype.card_le_of_injective f f.injective
    _ = N := by simp
/-- A graph with an edge cannot be contained in an edgeless graph. -/
lemma not_isContained_bot {β : Type} (H : SimpleGraph β) (hH : H.edgeSet.Nonempty)
    {γ : Type} : ¬ (H ⊑ (⊥ : SimpleGraph γ)) := by
  rintro ⟨f⟩
  obtain ⟨e, he⟩ := hH
  have := f.mapEdgeSet ⟨e, he⟩
  exact absurd this.2 (by simp [SimpleGraph.edgeSet_bot])
/-- `K₂` (the path on two vertices) is contained in any graph having an edge. -/
lemma K2_isContained_of_edge {β : Type} (B : SimpleGraph β) (hB : B.edgeSet.Nonempty) :
    (pathGraph 2) ⊑ B := by
  rw [pathGraph_two_eq_top]
  obtain ⟨e, he⟩ := hB
  induction e with
  | h u v =>
    have h : B.Adj u v := by rwa [SimpleGraph.mem_edgeSet] at he
    refine ⟨Hom.toCopy ⟨![u, v], ?_⟩ ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [B.symm h]
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [h.ne, h.ne']
/-- `Pₙ` embeds into the complete graph `K_n` on `n` vertices. -/
lemma pathGraph_isContained_top (n : ℕ) : (pathGraph n) ⊑ (⊤ : SimpleGraph (Fin n)) :=
  IsContained.of_le le_top
/-- The path on two vertices has an edge. -/
lemma pathGraph_two_edgeSet_nonempty : (pathGraph 2).edgeSet.Nonempty := by
  rw [pathGraph_two_eq_top]
  exact ⟨s(0, 1), by simp⟩
/-! ## Lemma 2 : paths are `(2,3)`-sparse
The key fact is that any subgraph `F` of a path has fewer edges than vertices: sending each edge
to its larger endpoint gives an injection from the edges into the vertices which misses the
smallest vertex.  This is a self-contained substitute for the forest edge bound (Lemma 1),
specialised to paths. -/
/-- The larger of the two endpoints of an edge of `Fin n` (using the linear order on `Fin n`). -/
noncomputable def topEnd (n : ℕ) : Sym2 (Fin n) → Fin n :=
  fun e => Sym2.lift ⟨fun a b => max a b, fun a b => max_comm a b⟩ e
/-- Each edge `e` of a subgraph `F` of the path `Pₙ` has a smaller endpoint `a ∈ V(F)` with
`a + 1 = topEnd e`, and `e = s(a, topEnd e)`.  In particular the larger endpoint lies in `V(F)`. -/
lemma edge_char (n : ℕ) (F : (pathGraph n).Subgraph) (e : Sym2 (Fin n)) (he : e ∈ F.edgeSet) :
    ∃ a : Fin n, a ∈ F.verts ∧ (a.val + 1 = (topEnd n e).val) ∧ (topEnd n e ∈ F.verts) ∧
      e = s(a, topEnd n e) := by
  induction e with
  | h u v =>
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    have hadj : (pathGraph n).Adj u v := F.adj_sub he
    have huv : u.val + 1 = v.val ∨ v.val + 1 = u.val := pathGraph_adj.mp hadj
    have hu : u ∈ F.verts := F.edge_vert he
    have hv : v ∈ F.verts := F.edge_vert he.symm
    rcases huv with h | h
    · have hmax : topEnd n s(u,v) = v := by
        show max u v = v; exact max_eq_right (by rw [Fin.le_def]; omega)
      refine ⟨u, hu, by rw [hmax]; exact h, by rw [hmax]; exact hv, by rw [hmax]⟩
    · have hmax : topEnd n s(u,v) = u := by
        show max u v = u; exact max_eq_left (by rw [Fin.le_def]; omega)
      refine ⟨v, hv, by rw [hmax]; exact h, by rw [hmax]; exact hu, by rw [hmax, Sym2.eq_swap]⟩
/-- Any nonempty subgraph of a path has strictly fewer edges than vertices. -/
lemma edgeSet_ncard_lt_verts_ncard (n : ℕ) (F : (pathGraph n).Subgraph) (hne : F.verts.Nonempty) :
    F.edgeSet.ncard < F.verts.ncard := by
  have hfin : F.verts.Finite := Set.toFinite _
  have hft : hfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hfin).mpr hne
  let m := hfin.toFinset.min' hft
  have hm_mem : m ∈ F.verts := (Set.Finite.mem_toFinset hfin).mp (hfin.toFinset.min'_mem hft)
  have hm_le : ∀ x ∈ F.verts, m ≤ x := fun x hx =>
    hfin.toFinset.min'_le x ((Set.Finite.mem_toFinset hfin).mpr hx)
  have hsub : F.edgeSet.ncard ≤ (F.verts \ {m}).ncard := by
    apply Set.ncard_le_ncard_of_injOn (topEnd n)
    · intro e he
      obtain ⟨a, ha_mem, ha_succ, htop_mem, he_eq⟩ := edge_char n F e he
      refine ⟨htop_mem, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hcontra
      have haltm : a < m := by rw [← hcontra, Fin.lt_def]; omega
      exact absurd (hm_le a ha_mem) (not_le.mpr haltm)
    · intro e1 he1 e2 he2 h12
      obtain ⟨a1, _, ha1, _, he1eq⟩ := edge_char n F e1 he1
      obtain ⟨a2, _, ha2, _, he2eq⟩ := edge_char n F e2 he2
      have : a1 = a2 := by apply Fin.ext; rw [h12] at ha1; omega
      rw [he1eq, he2eq, this, h12]
  rw [Set.ncard_diff_singleton_of_mem hm_mem] at hsub
  obtain ⟨w, hw⟩ := hne
  have hpos : 0 < F.verts.ncard := by
    have : F.verts.ncard ≠ 0 := by
      intro h0; rw [Set.ncard_eq_zero hfin] at h0; rw [h0] at hw; exact hw
    omega
  omega
/-- **Lemma 2.**  Every path `Pₙ` is `(2,3)`-sparse. -/
lemma pathGraph_is23Sparse (n : ℕ) : Is23Sparse (pathGraph n) := by
  intro F hcard
  have hne : F.verts.Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have := edgeSet_ncard_lt_verts_ncard n F hne
  omega
/-! ## Proposition 3 : a lower bound for the Ramsey number -/
/-- **Proposition 3.**  If `B` has an edge, then no `N < |V(A)|` lies in the Ramsey set:
the all-red colouring of `K_N` has no blue copy of `B` and too few vertices for a red copy of
`A`.  Hence `R(A,B) ≥ |V(A)|`. -/
lemma ramsey_ge_of_lt_card {α β : Type} [Fintype α] (A : SimpleGraph α) (B : SimpleGraph β)
    (hB : B.edgeSet.Nonempty) : ∀ N, N < Fintype.card α → N ∉ ramseySet A B := by
  intro N hN hmem
  rcases hmem ⊤ with h | h
  · exact absurd (card_le_of_isContained A ⊤ h) (by simpa using hN)
  · rw [show (⊤ : SimpleGraph (Fin N))ᶜ = ⊥ by simp] at h
    exact not_isContained_bot B hB h
/-! ## Corollary 5 : `R(Pₙ, K₂) = n` -/
/-- The upper-bound half of Corollary 5: `n` lies in the Ramsey set of `(Pₙ, K₂)`.
Every red/blue colouring of `K_n` either has a blue edge (a blue `K₂`) or is all red,
in which case `K_n` itself is a red `Pₙ`. -/
lemma n_mem_ramseySet_pathGraph_K2 (n : ℕ) : n ∈ ramseySet (pathGraph n) (pathGraph 2) := by
  intro c
  by_cases h : cᶜ.edgeSet.Nonempty
  · exact Or.inr (K2_isContained_of_edge cᶜ h)
  · left
    rw [Set.not_nonempty_iff_eq_empty, SimpleGraph.edgeSet_eq_empty] at h
    have hc : c = ⊤ := by simpa using congrArg (·ᶜ) h
    rw [hc]; exact pathGraph_isContained_top n
/-- **Corollary 5.**  `R(Pₙ, K₂) = n` for `n ≥ 2`.  (The hypothesis `n ≥ 2` is stated as in the
note; the proof in fact works for every `n`.) -/
lemma ramsey_pathGraph_K2 (n : ℕ) (_hn : 2 ≤ n) :
    Ramsey (pathGraph n) (pathGraph 2) = n := by
  apply le_antisymm
  · exact Nat.sInf_le (n_mem_ramseySet_pathGraph_K2 n)
  · by_contra h
    push_neg at h
    have hmem : sInf (ramseySet (pathGraph n) (pathGraph 2)) ∈
        ramseySet (pathGraph n) (pathGraph 2) :=
      Nat.sInf_mem ⟨n, n_mem_ramseySet_pathGraph_K2 n⟩
    have hcard : Fintype.card (Fin n) = n := by simp
    exact ramsey_ge_of_lt_card (pathGraph n) (pathGraph 2) pathGraph_two_edgeSet_nonempty
      _ (by rw [hcard]; exact h) hmem
/-! ## The disproof -/
/-- The proposed uniform linear Ramsey bound: there is an absolute constant `C > 0` such that
`R(G,H) ≤ C·m` for every `(2,3)`-sparse graph `G` and every graph `H` with `m` edges and no
isolated vertices (`m = numEdges H`). -/
def ProposedBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {α β : Type} [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β),
      Is23Sparse G → NoIsolated H → (Ramsey G H : ℝ) ≤ C * (numEdges H : ℝ)
/-- `K₂` has exactly one edge. -/
lemma numEdges_pathGraph_two : numEdges (pathGraph 2) = 1 := by
  unfold numEdges
  rw [pathGraph_two_eq_top, Set.ncard_eq_toFinset_card']
  decide +kernel
/-- `K₂` has no isolated vertices. -/
lemma noIsolated_pathGraph_two : NoIsolated (pathGraph 2) := by
  rw [pathGraph_two_eq_top]
  intro v
  refine ⟨if v = 0 then 1 else 0, ?_⟩
  fin_cases v <;> simp
/-- **The disproof.**  The proposed uniform linear Ramsey bound is false. -/
theorem not_proposedBound : ¬ ProposedBound := by
  rintro ⟨C, _hC, hbound⟩
  obtain ⟨n, hn2, hnC⟩ : ∃ n : ℕ, 2 ≤ n ∧ C < n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 2)
    exact ⟨n, by exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn),
      lt_of_le_of_lt (le_max_left _ _) hn⟩
  have hb := hbound (pathGraph n) (pathGraph 2) (pathGraph_is23Sparse n) noIsolated_pathGraph_two
  rw [ramsey_pathGraph_K2 n hn2, numEdges_pathGraph_two] at hb
  simp only [Nat.cast_one, mul_one] at hb
  linarith
/-! ## Theorem 4 : the counterexample for every `m`
We now formalise the full counterexample of the note: for every constant `C` and every `m ≥ 1`
there are graphs `G` (a path, hence `(2,3)`-sparse) and `H` (the matching `m·K₂`, with exactly `m`
edges and no isolated vertices) with `R(G,H) > C·m`.  The matching is `mK₂`, realised on the vertex
type `Fin m × Bool` with `(i,a)` adjacent to `(j,b)` iff `i = j` and `a ≠ b`. -/
/-- The matching `m·K₂`: `m` disjoint edges, on the vertex type `Fin m × Bool`. -/
def matchingGraph (m : ℕ) : SimpleGraph (Fin m × Bool) where
  Adj p q := p.1 = q.1 ∧ p.2 ≠ q.2
  symm := by rintro p q ⟨h1, h2⟩; exact ⟨h1.symm, (Ne.symm h2)⟩
  loopless := ⟨by rintro p ⟨_, h2⟩; exact h2 rfl⟩
/-- `mK₂` has exactly `m` edges. -/
lemma numEdges_matchingGraph (m : ℕ) : numEdges (matchingGraph m) = m := by
  unfold numEdges
  have hset : (matchingGraph m).edgeSet
      = (fun i : Fin m => s((i, false), (i, true))) '' Set.univ := by
    ext e
    induction e with
    | h p q =>
      simp only [SimpleGraph.mem_edgeSet, Set.image_univ, Set.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨p.1, ?_⟩
        obtain ⟨pi, pb⟩ := p; obtain ⟨qi, qb⟩ := q
        simp only at h1 h2 ⊢; subst h1
        fin_cases pb <;> fin_cases qb <;> simp_all [Sym2.eq_swap]
      · rintro ⟨i, hi⟩
        rw [Sym2.eq_iff] at hi
        rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          (subst h1; subst h2; exact ⟨rfl, by simp⟩)
  rw [hset, Set.ncard_image_of_injective _ (by intro a b h; simpa using h), Set.ncard_univ]
  simp
/-- `mK₂` has no isolated vertices. -/
lemma noIsolated_matchingGraph (m : ℕ) : NoIsolated (matchingGraph m) := fun v =>
  ⟨(v.1, !v.2), rfl, by simp⟩
/-- `mK₂` has an edge when `m ≥ 1`. -/
lemma matchingGraph_edgeSet_nonempty (m : ℕ) (hm : 1 ≤ m) :
    (matchingGraph m).edgeSet.Nonempty := by
  rw [← Set.ncard_pos (Set.toFinite _)]
  have := numEdges_matchingGraph m
  unfold numEdges at this
  omega
/-! ### Elementary containment facts used in the finiteness bound -/
/-- Given an edge `s(u,v)` of `D` with `pb ≠ qb`, the two vertices `ite pb v u` and `ite qb v u`
(one is `u`, the other `v`) are adjacent. -/
lemma adj_ite_of_ne {V : Type} {D : SimpleGraph V} {u v : V} (hadj : D.Adj u v)
    {pb qb : Bool} (h2 : pb ≠ qb) :
    D.Adj (if pb then v else u) (if qb then v else u) := by
  rcases pb with _ | _ <;> rcases qb with _ | _ <;> simp_all
  all_goals first | exact hadj | exact hadj.symm
/-- Extend a copy of `mK₂` by one disjoint edge to obtain a copy of `(m+1)K₂`. -/
lemma matching_extend {V : Type} (D : SimpleGraph V) (m : ℕ) (u v : V)
    (f : (matchingGraph m).Copy D) (hu : u ∉ Set.range f) (hv : v ∉ Set.range f)
    (huv : u ≠ v) (hadj : D.Adj u v) : (matchingGraph (m + 1)) ⊑ D := by
  set g : (Fin (m + 1) × Bool) → V :=
    fun p => if h : p.1.val < m then f (⟨p.1.val, h⟩, p.2) else (if p.2 then v else u) with hg
  have hhom : ∀ ⦃a b : Fin (m + 1) × Bool⦄, (matchingGraph (m + 1)).Adj a b → D.Adj (g a) (g b) := by
    rintro ⟨pi, pb⟩ ⟨qi, qb⟩ ⟨h1, h2⟩
    change pi = qi at h1; change pb ≠ qb at h2; subst h1
    rw [hg]; dsimp only
    by_cases hlt : pi.val < m
    · rw [dif_pos hlt, dif_pos hlt]; exact f.toHom.map_adj ⟨rfl, h2⟩
    · rw [dif_neg hlt, dif_neg hlt]; exact adj_ite_of_ne hadj h2
  have hinj : Function.Injective g := by
    rintro ⟨pi, pb⟩ ⟨qi, qb⟩ hpq
    rw [hg] at hpq; dsimp only at hpq
    by_cases hp : pi.val < m <;> by_cases hq : qi.val < m
    · rw [dif_pos hp, dif_pos hq] at hpq
      have h2 := f.injective hpq
      rw [Prod.mk.injEq, Fin.mk.injEq] at h2
      obtain ⟨hi, hb⟩ := h2
      subst hb; have : pi = qi := Fin.ext hi; subst this; rfl
    · exfalso; rw [dif_pos hp, dif_neg hq] at hpq
      cases qb
      · exact hu ⟨_, by simpa using hpq⟩
      · exact hv ⟨_, by simpa using hpq⟩
    · exfalso; rw [dif_neg hp, dif_pos hq] at hpq
      cases pb
      · exact hu ⟨_, by simpa using hpq.symm⟩
      · exact hv ⟨_, by simpa using hpq.symm⟩
    · rw [dif_neg hp, dif_neg hq] at hpq
      have hpeq : pi = qi := Fin.ext (by omega)
      subst hpeq
      rcases pb with _ | _ <;> rcases qb with _ | _ <;> simp_all
  exact ⟨Hom.toCopy ⟨g, fun {a b} h => hhom h⟩ hinj⟩
/-- The empty matching `0·K₂` is contained in every graph. -/
lemma empty_matching {V : Type} (D : SimpleGraph V) : (matchingGraph 0) ⊑ D := by
  refine ⟨Hom.toCopy ⟨fun p => (Fin.elim0 p.1), ?_⟩ ?_⟩
  · rintro ⟨a, _⟩; exact Fin.elim0 a
  · rintro ⟨a, _⟩; exact Fin.elim0 a
/-- `Pₙ` embeds into the complete graph on any vertex set of size at least `n`. -/
lemma pathGraph_top_of_le {V : Type} [Fintype V] (n : ℕ) (h : n ≤ Fintype.card V) :
    (pathGraph n) ⊑ (⊤ : SimpleGraph V) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using h : Fintype.card (Fin n) ≤ Fintype.card V)
  refine ⟨Hom.toCopy ⟨e, ?_⟩ e.injective⟩
  intro a b hab
  simp only [SimpleGraph.top_adj]
  exact fun hcon => (pathGraph n).ne_of_adj hab (e.injective hcon)
/-- The complement of an induced subgraph is the induced subgraph of the complement. -/
lemma compl_induce {V : Type} (c : SimpleGraph V) (s : Set V) : (c.induce s)ᶜ = cᶜ.induce s := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
  rw [Subtype.coe_ne_coe]
/-- An induced subgraph is contained in the ambient graph. -/
lemma induce_isContained {V : Type} (c : SimpleGraph V) (s : Set V) : c.induce s ⊑ c :=
  ⟨(Embedding.induce s).toCopy⟩
/-- Removing two distinct vertices decreases the vertex count by two. -/
lemma card_compl_pair {V : Type} [Fintype V] (u v : V) (huv : u ≠ v) :
    Fintype.card ↥(({u, v} : Set V)ᶜ) = Fintype.card V - 2 := by
  rw [Fintype.card_compl_set]
  congr 1
  rw [Nat.card_eq_fintype_card.symm, Nat.card_coe_set_eq, Set.ncard_pair huv]
/-- **Finiteness (Ramsey upper bound).**  In any red/blue colouring of a complete graph on at
least `n + 2m` vertices there is a red `Pₙ` or a blue `mK₂`.  Proof by induction on `m`: if the
blue graph has an edge, delete its two endpoints and recurse; otherwise everything is red and the
whole clique is a red `Pₙ`. -/
lemma ramsey_ub (n : ℕ) : ∀ (m : ℕ) (V : Type) [Fintype V] (c : SimpleGraph V),
    n + 2 * m ≤ Fintype.card V → (pathGraph n ⊑ c ∨ matchingGraph m ⊑ cᶜ) := by
  intro m
  induction m with
  | zero => intro V _ c _; exact Or.inr (empty_matching cᶜ)
  | succ k ih =>
    intro V _ c hcard
    by_cases hedge : ∃ u v, cᶜ.Adj u v
    · obtain ⟨u, v, huv⟩ := hedge
      have hne : u ≠ v := huv.ne
      have hcards : n + 2 * k ≤ Fintype.card ↥(({u, v} : Set V)ᶜ) := by
        rw [card_compl_pair u v hne]; omega
      rcases ih ↥(({u, v} : Set V)ᶜ) (c.induce (({u, v} : Set V)ᶜ)) hcards with hp | hm
      · exact Or.inl (hp.trans (induce_isContained c _))
      · right
        rw [compl_induce] at hm
        obtain ⟨f'⟩ := hm
        set f : (matchingGraph k).Copy cᶜ :=
          ⟨⟨fun x => (f' x : V), fun {a b} hab => f'.toHom.map_adj hab⟩,
            fun a b h => f'.injective (Subtype.ext h)⟩ with hf
        have hrange : ∀ x, (f x) ∈ (({u, v} : Set V)ᶜ) := fun x => (f' x).2
        apply matching_extend cᶜ k u v f
        · rintro ⟨x, hx⟩; exact (by simp : u ∉ (({u, v} : Set V)ᶜ)) (hx ▸ hrange x)
        · rintro ⟨x, hx⟩; exact (by simp : v ∉ (({u, v} : Set V)ᶜ)) (hx ▸ hrange x)
        · exact hne
        · exact huv
    · left
      push_neg at hedge
      have hc : c = ⊤ := by
        ext a b; simp only [SimpleGraph.top_adj]
        exact ⟨fun h => c.ne_of_adj h, fun h => by by_contra hcon; exact hedge a b ⟨h, hcon⟩⟩
      rw [hc]
      exact pathGraph_top_of_le n (by omega)
/-- `n + 2m` witnesses the Ramsey property for `(Pₙ, mK₂)`; in particular the Ramsey set is
nonempty (the Ramsey number is finite). -/
lemma mem_ramseySet_pathGraph_matching (n m : ℕ) :
    (n + 2 * m) ∈ ramseySet (pathGraph n) (matchingGraph m) := by
  intro c
  exact ramsey_ub n m (Fin (n + 2 * m)) c (by simp)
/-- **Lower bound for the matching counterexample.**  `R(Pₙ, mK₂) ≥ n` for `m ≥ 1`. -/
lemma ramsey_pathGraph_matching_ge (n m : ℕ) (hm : 1 ≤ m) :
    n ≤ Ramsey (pathGraph n) (matchingGraph m) := by
  by_contra h
  push_neg at h
  have hmem : sInf (ramseySet (pathGraph n) (matchingGraph m)) ∈
      ramseySet (pathGraph n) (matchingGraph m) :=
    Nat.sInf_mem ⟨n + 2 * m, mem_ramseySet_pathGraph_matching n m⟩
  have hcard : Fintype.card (Fin n) = n := by simp
  exact ramsey_ge_of_lt_card (pathGraph n) (matchingGraph m)
    (matchingGraph_edgeSet_nonempty m hm) _ (by rw [hcard]; exact h) hmem
/-- **Theorem 4.**  For every constant `C` and every `m ≥ 1` there are a `(2,3)`-sparse graph `G`
(a path) and a graph `H` (the matching `mK₂`) with exactly `m` edges and no isolated vertices such
that `R(G,H) > C·m`.  Consequently no uniform linear bound `R(G,H) ≤ C·m` can hold. -/
theorem thm4 (C : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ nn : ℕ, Is23Sparse (pathGraph nn) ∧ numEdges (matchingGraph m) = m ∧
      NoIsolated (matchingGraph m) ∧ (C * m : ℝ) < Ramsey (pathGraph nn) (matchingGraph m) := by
  obtain ⟨nn, hnn⟩ := exists_nat_gt (C * m)
  refine ⟨nn, pathGraph_is23Sparse nn, numEdges_matchingGraph m, noIsolated_matchingGraph m, ?_⟩
  have hge : (nn : ℝ) ≤ (Ramsey (pathGraph nn) (matchingGraph m) : ℝ) := by
    exact_mod_cast ramsey_pathGraph_matching_ge nn m hm
  linarith
end Erdos566
