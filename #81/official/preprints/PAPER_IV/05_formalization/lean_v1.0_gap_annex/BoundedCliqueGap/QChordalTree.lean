import BoundedCliqueGap.QPES
import BoundedCliqueGap.QTreePresentation

/-
`BoundedCliqueGap.QChordalTree` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Rung Q3 (part 3) — **every chordal graph is a tree flower**

This is the Gavril representation, formalised.  Fix a reverse perfect
elimination numbering `ord` of a chordal graph `H` (rung Q3 part 1).  The
skeleton tree has one node per vertex — node `j` is the vertex `w_j` with
`ord w_j = j` — and the clique of node `j` is `{w_j}` together with the
neighbours of `w_j` carrying smaller numbers.  So the vertex `v` occupies

  `gavSub v = {ord v} ∪ {ord u : u ∼ v, ord u > ord v}`,

the set of nodes whose clique contains `v`.  Its smallest element is `ord v`,
and the parent of node `j`,

  `gavPar j = max {ord u : u ∼ w_j, ord u < j}`,

makes `gavSub v` parent-closed above `ord v` (`gav_up`): if `v` and the
maximal back-neighbour `u*` of `w_j` are both back-neighbours of `w_j` then
they are adjacent, because back-neighbours form a clique.  Finally two vertices
are adjacent exactly when their node sets meet (`gav_adj_iff`) — that is
Gavril's theorem.

Assembling this into a `TreePresentation H` (`chordalTreePresentation`) gives

* `chordal_isTreeFlower` — every chordal graph is a presented tree flower of
  charge `|V|`, with **no hole and no territories**;
* `chordal_gap_linear_of_treeGapFull` — the interface `TreeGapFull C` bounds
  the gap of *every* chordal graph by `C·|V|`, with no family-existence
  hypothesis of any kind;
* `chordal_gap_moderate` — **unconditional**: a chordal graph with no clique on
  `32` vertices lies in the Moderate window of rung Q2 (its clique-tree
  separators exceed the one new vertex of their node by at most `29`), so its
  gap is at most `10·|V|`.
-/

namespace BoundedCliqueGap

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The clique tree of a reverse elimination numbering -/

section Gavril

variable (H : SimpleGraph V) (ord : V → ℕ)

/-- The set of clique-tree nodes whose clique contains `v`: the node of `v`
itself, and the node of every neighbour of `v` with a larger number. -/
noncomputable def gavSub (v : V) : Finset ℕ :=
  insert (ord v) ((univ.filter (fun u => H.Adj v u ∧ ord v < ord u)).image ord)

/-- The parent of node `j` in the clique tree: the largest back-neighbour of
`w_j`, or the root `0` if there is none. -/
noncomputable def gavPar (j : ℕ) : ℕ :=
  (univ.filter (fun u => ord u < j ∧ ∃ w : V, ord w = j ∧ H.Adj u w)).sup ord

variable {H ord}

lemma mem_gavSub {v : V} {j : ℕ} :
    j ∈ gavSub H ord v ↔ j = ord v ∨ ∃ u, H.Adj v u ∧ ord v < ord u ∧ ord u = j := by
  simp [gavSub, and_assoc]

lemma gavSub_rt_mem (v : V) : ord v ∈ gavSub H ord v := by
  simp [gavSub]

lemma gavSub_ge {v : V} {j : ℕ} (h : j ∈ gavSub H ord v) : ord v ≤ j := by
  rcases mem_gavSub.1 h with rfl | ⟨u, _, hlt, rfl⟩
  · exact le_rfl
  · exact hlt.le

lemma gavPar_lt {j : ℕ} (hj : 0 < j) : gavPar H ord j < j := by
  rw [gavPar]
  refine (Finset.sup_lt_iff (by simpa using hj)).2 ?_
  intro b hb
  exact (Finset.mem_filter.1 hb).2.1

lemma le_gavPar {u : V} {j : ℕ} (hu : ord u < j) {w : V} (hw : ord w = j) (huw : H.Adj u w) :
    ord u ≤ gavPar H ord j :=
  Finset.le_sup (f := ord) (Finset.mem_filter.2 ⟨mem_univ _, hu, ⟨w, hw, huw⟩⟩)

lemma gavPar_attained (hinj : Function.Injective ord) {u : V} {j : ℕ} (hu : ord u < j)
    {w : V} (hw : ord w = j) (huw : H.Adj u w) :
    ∃ z : V, ord z < j ∧ H.Adj z w ∧ ord z = gavPar H ord j := by
  set s : Finset V := univ.filter (fun x => ord x < j ∧ ∃ y : V, ord y = j ∧ H.Adj x y) with hs
  have hmem : u ∈ s := Finset.mem_filter.2 ⟨mem_univ _, hu, ⟨w, hw, huw⟩⟩
  obtain ⟨z, hz, hzeq⟩ := Finset.exists_mem_eq_sup s ⟨u, hmem⟩ ord
  obtain ⟨-, hzlt, y, hy, hzy⟩ := Finset.mem_filter.1 hz
  refine ⟨z, hzlt, ?_, ?_⟩
  · have hyw : y = w := hinj (by rw [hy, hw])
    exact hyw ▸ hzy
  · rw [gavPar, ← hs, hzeq]

/-- **The subtrees are parent-closed above their roots.** -/
lemma gav_up (hpes : RevPES H ord) {v : V} {j : ℕ} (hj : j ∈ gavSub H ord v)
    (hne : j ≠ ord v) : gavPar H ord j ∈ gavSub H ord v := by
  rcases mem_gavSub.1 hj with h | ⟨x, hvx, hlt, hxj⟩
  · exact absurd h hne
  obtain ⟨z, hzlt, hzx, hzeq⟩ := gavPar_attained hpes.inj (w := x) (by omega) hxj hvx
  rcases eq_or_ne z v with rfl | hzv
  · rw [← hzeq]
    exact gavSub_rt_mem _
  · have hadj : H.Adj v z := by
      refine hpes.down x v z hvx.symm hzx.symm ?_ ?_ (Ne.symm hzv)
      · omega
      · omega
    refine mem_gavSub.2 (Or.inr ⟨z, hadj, ?_, hzeq⟩)
    have hle := le_gavPar (u := v) (j := j) (by omega) hxj hvx
    have hne2 : ord v ≠ ord z := fun hc => hzv (hpes.inj hc.symm)
    omega

/-- **Gavril's theorem**: two vertices of a chordal graph are adjacent exactly
when their clique-tree subtrees meet. -/
theorem gav_adj_iff (hpes : RevPES H ord) (v u : V) :
    H.Adj v u ↔ v ≠ u ∧ (gavSub H ord v ∩ gavSub H ord u).Nonempty := by
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    rcases lt_trichotomy (ord v) (ord u) with hlt | heq | hgt
    · exact ⟨ord u, Finset.mem_inter.2 ⟨mem_gavSub.2 (Or.inr ⟨u, h, hlt, rfl⟩),
        gavSub_rt_mem u⟩⟩
    · exact absurd (hpes.inj heq) h.ne
    · exact ⟨ord v, Finset.mem_inter.2 ⟨gavSub_rt_mem v,
        mem_gavSub.2 (Or.inr ⟨v, h.symm, hgt, rfl⟩)⟩⟩
  · rintro ⟨hne, j, hj⟩
    obtain ⟨hjv, hju⟩ := Finset.mem_inter.1 hj
    rcases mem_gavSub.1 hjv with rfl | ⟨x, hvx, hvlt, hxj⟩
    · rcases mem_gavSub.1 hju with h | ⟨y, huy, hult, hyj⟩
      · exact absurd (hpes.inj h.symm) (Ne.symm hne)
      · have : y = v := hpes.inj hyj
        exact (this ▸ huy).symm
    · rcases mem_gavSub.1 hju with h | ⟨y, huy, hult, hyj⟩
      · have : x = u := hpes.inj (by omega)
        exact this ▸ hvx
      · have hxy : x = y := hpes.inj (by omega)
        subst hxy
        exact hpes.down x v u hvx.symm huy.symm (by omega) (by omega) hne

end Gavril

/-! ## The presentation -/

section Presentation

variable {H : SimpleGraph V} {ord : V → ℕ}

/-- The numbering `ord` as a bijection onto `Fin |V|`. -/
noncomputable def gavEquiv (hpes : RevPES H ord) : V ≃ Fin (Fintype.card V) :=
  Equiv.ofBijective (fun v => (⟨ord v, hpes.lt v⟩ : Fin (Fintype.card V)))
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => hpes.inj (by simpa [Fin.ext_iff] using h), by simp⟩)

lemma ord_gavEquiv_symm (hpes : RevPES H ord) (a : Fin (Fintype.card V)) :
    ord ((gavEquiv hpes).symm a) = (a : ℕ) := by
  have h := (gavEquiv hpes).apply_symm_apply a
  exact congrArg Fin.val h

/-- **Every chordal graph is a tree flower**: the clique tree of a reverse
perfect elimination numbering is its subtree representation.  There is no hole
and there are no territories, so the charge is exactly `|V|`. -/
noncomputable def chordalTreePresentation (hpes : RevPES H ord) : TreePresentation H where
  n := Fintype.card V
  t := 0
  m := 0
  r := Fintype.card V
  par := gavPar H ord
  rt := fun a => (a : ℕ)
  sub := fun a => gavSub H ord ((gavEquiv hpes).symm a)
  S0 := ∅
  terr := fun y => y.elim0
  sep := fun i => i.elim0
  isRep :=
    { par_lt := fun _ hj => gavPar_lt hj
      rt_mem := fun a => by
        rw [← ord_gavEquiv_symm hpes a]
        exact gavSub_rt_mem _
      rt_min := fun a j hj => by
        have := gavSub_ge hj
        rwa [ord_gavEquiv_symm hpes] at this
      up := fun a j hj hne => by
        refine gav_up hpes hj ?_
        rw [ord_gavEquiv_symm hpes]
        exact hne }
  hS0 := by simp
  hr := fun a => a.isLt
  emb := Sum.elim (gavEquiv hpes).symm (fun y => y.elim0)
  emb_inj := by
    intro a b hab
    match a, b with
    | Sum.inl a, Sum.inl b =>
      exact congrArg Sum.inl ((gavEquiv hpes).symm.injective hab)
    | Sum.inl _, Sum.inr y => exact y.elim0
    | Sum.inr x, _ => exact x.elim0
  emb_adj := by
    intro a b
    match a, b with
    | Sum.inl a, Sum.inl b =>
      rw [treeFlower_adj_inl_inl]
      simp only [Sum.elim_inl, Finset.notMem_empty, false_and, not_false_eq_true, and_true]
      rw [gav_adj_iff hpes]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun hc => h1 (by rw [hc]), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun hc => h1 ((gavEquiv hpes).symm.injective hc), h2⟩
    | Sum.inl _, Sum.inr y => exact y.elim0
    | Sum.inr x, _ => exact x.elim0
  emb_supp := by
    intro u _ _
    exact ⟨Sum.inl (gavEquiv hpes u), by simp⟩

@[simp] lemma chordalTreePresentation_sub (hpes : RevPES H ord)
    (a : Fin (chordalTreePresentation hpes).n) :
    (chordalTreePresentation hpes).sub a = gavSub H ord ((gavEquiv hpes).symm a) := rfl

@[simp] lemma chordalTreePresentation_rt (hpes : RevPES H ord)
    (a : Fin (chordalTreePresentation hpes).n) :
    (chordalTreePresentation hpes).rt a = (a : ℕ) := rfl

@[simp] lemma chordalTreePresentation_S0 (hpes : RevPES H ord) :
    (chordalTreePresentation hpes).S0 = ∅ := rfl

end Presentation

/-! ## The two master theorems -/

/-! ## The Moderate window -/

section Moderate

variable {H : SimpleGraph V} {ord : V → ℕ}

/-- The back-neighbours of a vertex, together with the vertex itself, form a
clique; so in a graph without cliques on `k+1` vertices there are fewer than
`k` of them. -/
lemma revPES_back_card_lt (hpes : RevPES H ord) {k : ℕ} (hk : H.CliqueFree (k + 1)) (v : V) :
    (univ.filter (fun u => H.Adj v u ∧ ord u < ord v)).card < k := by
  by_contra hcon
  push_neg at hcon
  set S : Finset V := univ.filter (fun u => H.Adj v u ∧ ord u < ord v) with hS
  have hvS : v ∉ S := by
    intro hv
    exact H.irrefl (Finset.mem_filter.1 hv).2.1
  have hclique : H.IsNClique (S.card + 1) (insert v S) := by
    constructor
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact (Finset.mem_filter.1 hy).2.1
      · rcases hy with rfl | hy
        · exact ((Finset.mem_filter.1 hx).2.1).symm
        · exact hpes.down v x y (Finset.mem_filter.1 hx).2.1 (Finset.mem_filter.1 hy).2.1
            (Finset.mem_filter.1 hx).2.2 (Finset.mem_filter.1 hy).2.2 hxy
    · rw [Finset.card_insert_of_notMem hvS]
  exact hk.mono (by omega) _ hclique

/-- **The clique tree of a chordal graph with no clique on `k+1` vertices has
separators of size `< k`.**  The hole of node `j` is the set of back-neighbours
of the vertex `w_j` that node `j` introduces. -/
lemma chordalTree_treeHole_card_lt (hpes : RevPES H ord) {k : ℕ}
    (hk : H.CliqueFree (k + 1)) {j : ℕ} (hj : j < Fintype.card V) :
    (treeHole (chordalTreePresentation hpes).sub (chordalTreePresentation hpes).rt
      (chordalTreePresentation hpes).S0 j).card < k := by
  classical
  set w : V := (gavEquiv hpes).symm ⟨j, hj⟩ with hw
  have hordw : ord w = j := ord_gavEquiv_symm hpes ⟨j, hj⟩
  set T := treeHole (chordalTreePresentation hpes).sub (chordalTreePresentation hpes).rt
    (chordalTreePresentation hpes).S0 j with hT
  have hsub : T.image (gavEquiv hpes).symm ⊆
      univ.filter (fun u => H.Adj w u ∧ ord u < ord w) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    rw [hT, treeHole] at ha
    simp only [chordalTreePresentation_sub, chordalTreePresentation_rt,
      chordalTreePresentation_S0, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, false_or] at ha
    obtain ⟨-, hmem, hlt⟩ := ha
    have horda : ord ((gavEquiv hpes).symm a) = (a : ℕ) := ord_gavEquiv_symm hpes a
    rcases mem_gavSub.1 hmem with heq | ⟨u, hau, hlt2, hueq⟩
    · omega
    · have huw : u = w := hpes.inj (by rw [hueq, hordw])
      subst huw
      exact Finset.mem_filter.2 ⟨mem_univ _, hau.symm, by omega⟩
  have hcard : T.card = (T.image (gavEquiv hpes).symm).card :=
    (Finset.card_image_of_injective _ (gavEquiv hpes).symm.injective).symm
  rw [hcard]
  exact lt_of_le_of_lt (Finset.card_le_card hsub) (revPES_back_card_lt hpes hk w)

end Moderate

end BoundedCliqueGap
