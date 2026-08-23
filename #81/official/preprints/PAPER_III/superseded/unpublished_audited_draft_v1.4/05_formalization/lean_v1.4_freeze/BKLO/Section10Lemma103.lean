/-
# BKLO Lemma 10.3 for `r = 2` (`F = K₃`), discharged

This file proves `BKLO.Lemma103K3` — the greedy `K_{r+1}`-factor lemma of Barber–Kühn–Lo–Osthus
(§10.1, Lemma 10.3) in the case `r = 2`, where `K_{r+1} = K₃` and the `Kᵣ`-factors are perfect
matchings supplied by Dirac's theorem (`BKLO.perfectMatchingDirac_holds`).

The argument is the paper's greedy sweep over the apices `x ∈ U`.  At each apex one takes a perfect
matching `M_x` of the *unused* part of `H[N_H(x,W)]`; the star triangles `{x} ∪ e`, `e ∈ M_x`, are
edge-disjoint, they cover **all** the edges of `H` from `x` into `W`, and the only edges they add
inside `W` are the matching edges themselves.  Dirac applies at each step because hypothesis (ii)
gives minimum degree `|N|/2 + γ|W|` in `H[N_H(x,W)]` while the already-used set has degree at most
`2 d_H(v,U) ≤ γ|W|` at every `v ∈ W` by hypothesis (iii) — the same bound that gives the conclusion
`Δ(H_V) ≤ γ|W|`.

The pieces used are the bricks already in the project:
`BKLO.perfectMatchingDirac_holds`, `BKLO.setGraph`/`BKLO.degree_setGraph`,
`BKLO.involutionMatching`, `BKLO.edeg_sdiff_ge_of_slack`,
`BKLO.triDecomp_biUnion_starTriangles`, `BKLO.edeg_biUnion_starTriangles_le_two_degTo`.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownChooserStep
import BKLO.CoverDownBudgetAccumulate
import BKLO.CoverDownGreedyExistence
import BKLO.Section10Matchings

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### A perfect matching of a neighbourhood, with its edges recorded -/

/-- **Dirac, with the partner edges recorded.**  A nonempty even vertex set `N` carrying an edge set
`A ⊆ cliqueEdges N` of minimum degree `≥ |N|/2` admits a fixed-point-free involution `f` of `N` all
of whose orbit edges `s(a, f a)` lie in `A`. -/
theorem exists_involution_adj {N : Finset V} {A : Finset (Sym2 V)}
    (hAsub : A ⊆ cliqueEdges N) (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 ≤ edeg A v) (hne : N.Nonempty) :
    ∃ f : V → V, (∀ a ∈ N, f a ∈ N) ∧ (∀ a ∈ N, f (f a) = a) ∧ (∀ a ∈ N, f a ≠ a) ∧
      (∀ a ∈ N, s(a, f a) ∈ A) := by
  classical
  haveI : Nonempty {v // v ∈ N} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hdegG : ∀ a : {v // v ∈ N}, N.card / 2 ≤ (setGraph N A).degree a := by
    intro a
    rw [degree_setGraph hAsub a]
    exact hdeg (a : V) a.2
  have hmin : N.card / 2 ≤ (setGraph N A).minDegree :=
    SimpleGraph.le_minDegree_of_forall_le_degree _ (N.card / 2) hdegG
  obtain ⟨M, hM⟩ := perfectMatchingDirac_holds (setGraph N A)
    (by rw [card_coe_eq]; exact hEven)
    (by
      rw [card_coe_eq]
      obtain ⟨m, hm⟩ := hEven
      omega)
  have hpartner : ∀ a : {v // v ∈ N}, ∃! b, M.Adj a b := fun a => hM.1 (hM.2 a)
  choose g hg huniq using hpartner
  have hginv : ∀ a, g (g a) = a := fun a => (huniq (g a) a (M.symm (hg a))).symm
  have hgadj : ∀ a, (setGraph N A).Adj a (g a) := fun a => M.adj_sub (hg a)
  have hgne : ∀ a, g a ≠ a := by
    intro a h
    have hadj := hgadj a
    rw [h] at hadj
    exact hadj.ne rfl
  refine ⟨fun v => if h : v ∈ N then ((g ⟨v, h⟩ : {v // v ∈ N}) : V) else v, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp only [dif_pos ha]; exact (g ⟨a, ha⟩).2
  · intro a ha
    simp only [dif_pos ha, dif_pos (g ⟨a, ha⟩).2]
    have h2 : (⟨((g ⟨a, ha⟩ : {v // v ∈ N}) : V), (g ⟨a, ha⟩).2⟩ : {v // v ∈ N}) = g ⟨a, ha⟩ := rfl
    rw [h2, hginv ⟨a, ha⟩]
  · intro a ha
    simp only [dif_pos ha]
    intro hcon
    exact hgne ⟨a, ha⟩ (Subtype.ext hcon)
  · intro a ha
    simp only [dif_pos ha]
    exact (hgadj ⟨a, ha⟩).2

/-- **The per-apex perfect matching, with all the data the greedy sweep needs.**  For `x ∉ N`, an
even `N` and an edge set `A ⊆ cliqueEdges N` of minimum degree `≥ |N|/2` over `N`, there is a
matching `M` of `N` avoiding `x` which is *perfect* (covers every vertex of `N`) and all of whose
edges lie in `A`. -/
theorem exists_perfect_matching_in {N : Finset V} {x : V} (hx : x ∉ N) {A : Finset (Sym2 V)}
    (hAsub : A ⊆ cliqueEdges N) (hEven : Even N.card)
    (hdeg : ∀ v ∈ N, N.card / 2 ≤ edeg A v) :
    ∃ M : Finset (Finset V), IsMatchingAvoiding M x ∧ (∀ e ∈ M, e ⊆ N) ∧
      (∀ a ∈ N, ∃ e ∈ M, a ∈ e) ∧ (∀ e ∈ M, cliqueEdges e ⊆ A) := by
  classical
  rcases N.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, ⟨by simp, by simp, by simp⟩, by simp, by simp, by simp⟩
  obtain ⟨f, hmap, hinv, hfne, hadj⟩ := exists_involution_adj hAsub hEven hdeg hne
  refine ⟨involutionMatching N f, isMatchingAvoiding_involutionMatching hmap hinv hfne hx, ?_, ?_,
    ?_⟩
  · intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ha
    · rw [Finset.mem_singleton] at hz; subst hz; exact hmap a ha
  · intro a ha
    exact ⟨{a, f a}, Finset.mem_image_of_mem _ ha, by simp⟩
  · intro e he
    rw [involutionMatching, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    intro g hg
    obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hg
    have hga : g = s(a, f a) := by
      induction g using Sym2.ind with
      | _ p q =>
        have hp := hmem p (by simp)
        have hq := hmem q (by simp)
        rw [Sym2.isDiag_iff_proj_eq] at hnd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
        rcases hp with rfl | rfl
        · rcases hq with rfl | rfl
          · exact absurd rfl hnd
          · rfl
        · rcases hq with rfl | rfl
          · rw [Sym2.eq_swap]
          · exact absurd rfl hnd
    rw [hga]
    exact hadj a ha

/-! ### Elementary bridges -/

/-- Every edge of `H` inside `S` is a clique edge of `S`, provided `H` is loopless. -/
theorem edgesIn_subset_cliqueEdges_loopless {H : Finset (Sym2 V)} (hloop : ∀ e ∈ H, ¬ e.IsDiag)
    (S : Finset V) : edgesIn H S ⊆ cliqueEdges S := by
  intro e he
  rw [mem_edgesIn] at he
  exact mem_cliqueEdgesV.2 ⟨he.2, hloop e he.1⟩

/-- The degree of `y ∈ S` into `S` is at most its edge degree in `H[S]`. -/
theorem degTo_le_edeg_edgesIn {H : Finset (Sym2 V)} {S : Finset V} {y : V} (hy : y ∈ S) :
    degTo H y S ≤ edeg (edgesIn H S) y := by
  classical
  have hinj : Set.InjOn (fun z => s(y, z)) (nbhdIn H y S) := by
    intro a _ b _ hab
    simp only [Sym2.eq_iff] at hab
    rcases hab with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  have hsub : (nbhdIn H y S).image (fun z => s(y, z))
      ⊆ (edgesIn H S).filter (fun e => y ∈ e) := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 he
    rw [mem_nbhdIn] at hz
    refine Finset.mem_filter.2 ⟨mem_edgesIn.2 ⟨hz.2, ?_⟩, by simp⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hy
    · exact hz.1
  calc degTo H y S = ((nbhdIn H y S).image (fun z => s(y, z))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ edeg (edgesIn H S) y := Finset.card_le_card hsub

/-- Every vertex of an edge of the star family at `x` over a matching inside `N` lies in
`insert x N`. -/
theorem mem_insert_of_mem_star {x : V} {M : Finset (Finset V)} {N : Finset V}
    (hMN : ∀ e ∈ M, e ⊆ N) {e : Sym2 V} (he : e ∈ famEdges (starTriangles x M)) :
    ∀ v ∈ e, v ∈ insert x N := by
  classical
  rw [famEdges, Finset.mem_biUnion] at he
  obtain ⟨t, ht, hte⟩ := he
  rw [starTriangles, Finset.mem_image] at ht
  obtain ⟨f, hf, rfl⟩ := ht
  intro v hv
  have := (mem_cliqueEdgesV.1 hte).1 v hv
  rcases Finset.mem_insert.1 this with rfl | hvf
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hMN f hf hvf)

/-! ### The budget-aware greedy sweep -/

/-- The data the greedy sweep produces at an apex `x`: a perfect matching of `N_H(x,W)` avoiding
`x`, all of whose edges are edges of `H` inside `N_H(x,W)`. -/
structure GoodMatching (H : Finset (Sym2 V)) (W : Finset V) (x : V) (M : Finset (Finset V)) :
    Prop where
  matching : IsMatchingAvoiding M x
  subset : ∀ e ∈ M, e ⊆ nbhdIn H x W
  covers : ∀ a ∈ nbhdIn H x W, ∃ e ∈ M, a ∈ e
  edges : ∀ e ∈ M, cliqueEdges e ⊆ edgesIn H (nbhdIn H x W)

/-- **The greedy sweep of Lemma 10.3, with the budget threaded as an invariant.**  Processing the
apices of `U` in turn and taking at each a perfect matching of the *unused* part of
`H[N_H(x,W)]`, one obtains matchings whose star-triangle edge sets are pairwise disjoint.  The
hypothesis needed by Dirac at each step — that the already-used set has degree `≤ d` at every
vertex of the current neighbourhood — holds automatically, because the used set is the star union
over the apices processed so far and `BKLO.edeg_biUnion_starTriangles_le_two_degTo` bounds its
degree by `2 d_H(v,U) ≤ d`. -/
theorem exists_greedy_matchings {H : Finset (Sym2 V)} {U W : Finset V} {d : ℕ}
    (hloop : ∀ e ∈ H, ¬ e.IsDiag) (hUW : Disjoint U W)
    (hEven : ∀ x ∈ U, Even (nbhdIn H x W).card)
    (hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + d ≤ edeg (edgesIn H (nbhdIn H x W)) v)
    (hbud : ∀ v ∈ W, 2 * degTo H v U ≤ d) :
    ∃ Mx : V → Finset (Finset V), (∀ x ∈ U, GoodMatching H W x (Mx x)) ∧
      (U : Set V).Pairwise (fun x y => Disjoint (famEdges (starTriangles x (Mx x)))
        (famEdges (starTriangles y (Mx y)))) := by
  classical
  suffices h : ∀ s : Finset V, s ⊆ U → ∃ Mx : V → Finset (Finset V),
      (∀ x ∈ s, GoodMatching H W x (Mx x)) ∧
      (s : Set V).Pairwise (fun x y => Disjoint (famEdges (starTriangles x (Mx x)))
        (famEdges (starTriangles y (Mx y)))) from h U (le_refl U)
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => ∅, by simp, by simp⟩
  | @insert a t ha ih =>
    intro hsub
    have haU : a ∈ U := hsub (Finset.mem_insert_self a t)
    have htU : t ⊆ U := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    obtain ⟨Mx, hgood, hpair⟩ := ih htU
    set N : Finset V := nbhdIn H a W with hNdef
    set D : Finset (Sym2 V) := t.biUnion (fun y => famEdges (starTriangles y (Mx y))) with hDdef
    have hNW : N ⊆ W := nbhdIn_subset H a W
    have haN : a ∉ N := fun hc => (Finset.disjoint_left.1 hUW haU) (hNW hc)
    -- the accumulated budget bound at every vertex of `N`
    have hbudD : ∀ v ∈ N, edeg D v ≤ d := by
      intro v hv
      have hvW : v ∈ W := hNW hv
      have hvt : ∀ y ∈ t, v ≠ y := by
        intro y hy hc
        exact (Finset.disjoint_left.1 hUW (htU hy)) (hc ▸ hvW)
      have h1 : edeg D v ≤ 2 * degTo H v t :=
        edeg_biUnion_starTriangles_le_two_degTo (fun x hx => (hgood x hx).matching) hvt
          (fun x hx e he => (hgood x hx).subset e he)
      have h2 : degTo H v t ≤ degTo H v U := Finset.card_le_card (nbhdIn_mono_right htU v)
      have h3 := hbud v hvW
      omega
    -- Dirac in the unused part of `H[N]`
    have hAsub : (edgesIn H N \ D) ⊆ cliqueEdges N :=
      Finset.sdiff_subset.trans (edgesIn_subset_cliqueEdges_loopless hloop N)
    have hdegA : ∀ v ∈ N, N.card / 2 ≤ edeg (edgesIn H N \ D) v := fun v hv =>
      edeg_sdiff_ge_of_slack (hmindeg a haU v hv) (hbudD v hv)
    obtain ⟨Ma, hMa, hMasub, hMacov, hMaedges⟩ :=
      exists_perfect_matching_in haN hAsub (hEven a haU) hdegA
    -- the new star is disjoint from everything used so far
    have hstarD : Disjoint (famEdges (starTriangles a Ma)) D := by
      refine Finset.disjoint_left.2 ?_
      intro e he heD
      rw [famEdges, Finset.mem_biUnion] at he
      obtain ⟨tri, htri, hetri⟩ := he
      rw [starTriangles, Finset.mem_image] at htri
      obtain ⟨f, hf, rfl⟩ := htri
      by_cases hae : a ∈ e
      · rw [hDdef, Finset.mem_biUnion] at heD
        obtain ⟨y, hy, hey⟩ := heD
        have hmem := mem_insert_of_mem_star (fun g hg => (hgood y hy).subset g hg) hey a hae
        rcases Finset.mem_insert.1 hmem with hay | hcon
        · exact ha (hay ▸ hy)
        · exact (Finset.disjoint_left.1 hUW haU) (nbhdIn_subset H y W hcon)
      · have hef : e ∈ cliqueEdges f := by
          obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hetri
          refine mem_cliqueEdgesV.2 ⟨?_, hnd⟩
          intro v hv
          rcases Finset.mem_insert.1 (hmem v hv) with hva | hvf
          · exact absurd (hva ▸ hv) hae
          · exact hvf
        exact (Finset.mem_sdiff.1 (hMaedges f hf hef)).2 heD
    refine ⟨Function.update Mx a Ma, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hxt
      · rw [Function.update_self]
        refine ⟨hMa, hMasub, hMacov, fun e he => ?_⟩
        exact (hMaedges e he).trans Finset.sdiff_subset
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hxt ha)]
        exact hgood x hxt
    · have hsymm : Symmetric (fun x y : V =>
          Disjoint (famEdges (starTriangles x (Function.update Mx a Ma x)))
            (famEdges (starTriangles y (Function.update Mx a Ma y)))) :=
        fun x y h => h.symm
      rw [Finset.coe_insert, Set.pairwise_insert_of_symmetric hsymm]
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hx ha),
          Function.update_of_ne (ne_of_mem_of_not_mem hy ha)]
        exact hpair hx hy hxy
      · intro b hb _
        rw [Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem hb ha)]
        exact hstarD.mono_right
          (Finset.subset_biUnion_of_mem (fun y => famEdges (starTriangles y (Mx y))) hb)

/-! ### Lemma 10.3 for `r = 2` -/

/-- **BKLO Lemma 10.3 for `r = 2` (`F = K₃`).**

Sweeping greedily over the apices `x ∈ U` and taking at each a perfect matching `M_x` of the unused
part of `H[N_H(x,W)]` (Dirac's theorem, applicable because hypothesis (ii) leaves a slack of
`γ|W|` over `|N|/2` while the used set has degree at most `2 d_H(v,U) ≤ γ|W|` by (iii)), the star
triangles `{x} ∪ e`, `e ∈ M_x`, are pairwise edge-disjoint; they cover every edge of `H` between
`U` and `W`, and the only further edges they use are the matching edges, which lie inside `W` and
form the graph `H_V` with `Δ(H_V) ≤ γ|W|`.  No largeness of `n` is needed, so the threshold is
`n₀ = 0`. -/
theorem lemma103K3_holds : Lemma103K3 := by
  intro γ k hγ _hk
  refine ⟨0, ?_⟩
  intro V _ _ H U W _hcard hloop hUW _hW hdvd hdeg hUdeg
  classical
  set d : ℕ := ⌊γ * (W.card : ℝ)⌋₊ with hddef
  have hdle : (d : ℝ) ≤ γ * (W.card : ℝ) := Nat.floor_le (by positivity)
  -- hypothesis (i): the neighbourhoods are even
  have hEven : ∀ x ∈ U, Even (nbhdIn H x W).card := by
    intro x hx
    obtain ⟨m, hm⟩ := hdvd x hx
    have h2 : (nbhdIn H x W).card = 2 * m := hm
    exact ⟨m, by omega⟩
  -- hypothesis (ii): the minimum degree of the neighbourhood graph, in `ℕ`
  have hmindeg : ∀ x ∈ U, ∀ v ∈ nbhdIn H x W,
      (nbhdIn H x W).card / 2 + d ≤ edeg (edgesIn H (nbhdIn H x W)) v := by
    intro x hx v hv
    obtain ⟨m, hm⟩ := hEven x hx
    have hhalf : (nbhdIn H x W).card / 2 = m := by omega
    have hxc : (degTo H x W : ℝ) = (m : ℝ) + (m : ℝ) := by
      have : degTo H x W = m + m := hm
      rw [this]; push_cast; ring
    have hreal := hdeg x hx v hv
    have hnat : (nbhdIn H x W).card / 2 + d ≤ degTo H v (nbhdIn H x W) := by
      have : ((m + d : ℕ) : ℝ) ≤ (degTo H v (nbhdIn H x W) : ℝ) := by
        push_cast
        rw [hxc] at hreal
        linarith
      have hcast : m + d ≤ degTo H v (nbhdIn H x W) := by exact_mod_cast this
      omega
    exact le_trans hnat (degTo_le_edeg_edgesIn hv)
  -- hypothesis (iii): the budget
  have hbud : ∀ v ∈ W, 2 * degTo H v U ≤ d := by
    intro v hv
    refine Nat.le_floor ?_
    have := hUdeg v hv
    push_cast
    linarith
  obtain ⟨Mx, hgood, hpair⟩ := exists_greedy_matchings hloop hUW hEven hmindeg hbud
  -- `H_V` is the union of the matchings, an edge set inside `W`
  have hHVsub : U.biUnion (fun x => famEdges (Mx x)) ⊆ edgesIn H W := by
    intro e he
    obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
    obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
    exact edgesIn_mono (nbhdIn_subset H x W) ((hgood x hx).edges f hf hef)
  -- the star union is exactly `H[U,W] ∪ H_V`
  have hSeq : U.biUnion (fun x => famEdges (starTriangles x (Mx x)))
      = edgesBtw H U W ∪ U.biUnion (fun x => famEdges (Mx x)) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
      obtain ⟨tri, htri, hetri⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (by rwa [starTriangles] at htri)
      obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hetri
      by_cases hxe : x ∈ e
      · refine Finset.mem_union_left _ ?_
        obtain ⟨q, rfl⟩ := Sym2.mem_iff_exists.1 hxe
        have hq : q ∈ insert x f := hmem q (by simp)
        have hqx : q ≠ x := by
          intro hc
          rw [Sym2.isDiag_iff_proj_eq] at hnd
          exact hnd hc.symm
        have hqf : q ∈ f := (Finset.mem_insert.1 hq).resolve_left hqx
        have hqN : q ∈ nbhdIn H x W := (hgood x hx).subset f hf hqf
        rw [mem_nbhdIn] at hqN
        exact Finset.mem_filter.2 ⟨hqN.2, x, hx, q, hqN.1, rfl⟩
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
        refine Finset.mem_biUnion.2 ⟨f, hf, mem_cliqueEdgesV.2 ⟨?_, hnd⟩⟩
        intro z hz
        rcases Finset.mem_insert.1 (hmem z hz) with hzx | hzf
        · exact absurd (hzx ▸ hz) hxe
        · exact hzf
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨heH, a, haU, b, hbW, rfl⟩ := Finset.mem_filter.1 he
        have hbN : b ∈ nbhdIn H a W := mem_nbhdIn.2 ⟨hbW, heH⟩
        obtain ⟨f, hf, hbf⟩ := (hgood a haU).covers b hbN
        refine Finset.mem_biUnion.2 ⟨a, haU, Finset.mem_biUnion.2
          ⟨insert a f, Finset.mem_image_of_mem _ hf, mem_cliqueEdgesV.2 ⟨?_, ?_⟩⟩⟩
        · intro z hz
          rcases Sym2.mem_iff.1 hz with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hbf
        · rw [Sym2.isDiag_iff_proj_eq]
          intro hc
          have hab : a = b := hc
          exact (Finset.disjoint_left.1 hUW haU) (by rw [hab]; exact hbW)
      · obtain ⟨x, hx, hex⟩ := Finset.mem_biUnion.1 he
        obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.1 (by rwa [famEdges] at hex)
        exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_biUnion.2
          ⟨insert x f, Finset.mem_image_of_mem _ hf,
            cliqueEdges_mono (Finset.subset_insert x f) hef⟩⟩
  refine ⟨U.biUnion (fun x => famEdges (Mx x)), hHVsub, ?_, ?_⟩
  · -- the triangle decomposition
    rw [← hSeq]
    exact triDecomp_biUnion_starTriangles (fun x hx => (hgood x hx).matching) hpair
  · -- the maximum degree bound
    intro v
    by_cases hvW : v ∈ W
    · have hvU : ∀ x ∈ U, v ≠ x := fun x hx hc => (Finset.disjoint_left.1 hUW hx) (hc ▸ hvW)
      have h1 : edeg (U.biUnion (fun x => famEdges (Mx x))) v
          ≤ edeg (U.biUnion (fun x => famEdges (starTriangles x (Mx x)))) v :=
        edeg_mono (by rw [hSeq]; exact Finset.subset_union_right) v
      have h2 := edeg_biUnion_starTriangles_le_two_degTo (H := H) (W := W)
        (fun x hx => (hgood x hx).matching) hvU (fun x hx e he => (hgood x hx).subset e he)
      have h3 := hUdeg v hvW
      have h4 : (edeg (U.biUnion (fun x => famEdges (Mx x))) v : ℝ)
          ≤ ((2 * degTo H v U : ℕ) : ℝ) := by exact_mod_cast le_trans h1 h2
      push_cast at h4
      linarith
    · have hzero : edeg (U.biUnion (fun x => famEdges (Mx x))) v = 0 := by
        unfold edeg
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        exact hvW ((mem_edgesIn.1 (hHVsub he)).2 v hve)
      rw [hzero]
      have hpos : (0 : ℝ) ≤ γ * (W.card : ℝ) := by positivity
      simpa using hpos

end BKLO
