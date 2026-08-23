/-
# Pairing one class, and pairing one link class for class.

This file supplies the two missing constructions of the class-matched one-link step
(`TWOSIDED.md` §11, items 1 and 2) in the case where the link is not perturbed:

* `BKLO.exists_involution_of_half_degree` — **Dirac inside one set**: a finite set of even size in
  which every element is related to more than half of the set carries a fixed-point-free
  involution whose pairs are related.  Unlike `BKLO.exists_matching_of_half_degree` (Hall, between
  two disjoint sets) this is the *non-bipartite* statement, and it is what pairs the corner class
  of a region — the one class of the `2h - 1` classes of a region that no class matching can send
  anywhere else.  It uses `BKLO.perfectMatchingDirac_holds`, so it costs nothing.
* `BKLO.exists_class_involution_avoiding` — the same statement at a class of a two-sided grid
  design: a class of the region of `u` is paired inside itself by edges of `F` outside `U`, as soon
  as its trace on the link has even size and the used degree inside it is small.
* `BKLO.exists_classMatched_pairing_unperturbed` — **one unperturbed link is paired class for
  class**: for any bijection `ρ` of the `h` row indices with `ρ (y u) = x u` (so that the corner
  class is matched with itself), the reserved link of `u` carries a fixed-point-free involution by
  edges of `F` outside `U` which obeys the cross-side rule `BKLO.IsCrossSideAt` at *every* vertex —
  the exceptional set is empty.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedClassMatched
import BKLO.ClassInvolution
import BKLO.DiracMatching

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Dirac inside one set -/

/-- **Dirac's threshold inside one set.**  If `T` has even size and every element of `T` is related
to more than half of `T`, then `T` carries a fixed-point-free involution all of whose pairs are
related.  This is the non-bipartite companion of `BKLO.exists_matching_of_half_degree`. -/
theorem exists_involution_of_half_degree (T : Finset V)
    (r : V → V → Prop) [DecidableRel r] (hsymm : ∀ a b, r a b → r b a)
    (heven : Even T.card)
    (hdeg : ∀ a ∈ T, T.card ≤ 2 * (T.filter (fun b => b ≠ a ∧ r a b)).card) :
    ∃ p : V → V, (∀ a ∈ T, p a ∈ T) ∧ (∀ a ∈ T, p (p a) = a) ∧ (∀ a ∈ T, p a ≠ a) ∧
      (∀ a ∈ T, r a (p a)) := by
  classical
  set G : SimpleGraph {x // x ∈ T} :=
    SimpleGraph.fromRel (fun a b : {x // x ∈ T} => r (a : V) (b : V)) with hGdef
  have hAdj : ∀ a b : {x // x ∈ T}, G.Adj a b ↔ (a ≠ b ∧ r (a : V) (b : V)) := by
    intro a b
    rw [hGdef, SimpleGraph.fromRel_adj]
    exact ⟨fun h => ⟨h.1, h.2.elim id (fun h' => hsymm _ _ h')⟩, fun h => ⟨h.1, Or.inl h.2⟩⟩
  haveI : DecidableRel G.Adj := Classical.decRel _
  have hcard : Fintype.card {x // x ∈ T} = T.card := Fintype.card_coe T
  have hEven : Even (Fintype.card {x // x ∈ T}) := by rw [hcard]; exact heven
  -- the degree of a vertex of the subtype is the count inside `T`
  have hdegree : ∀ a : {x // x ∈ T},
      G.degree a = (T.filter (fun b => b ≠ (a : V) ∧ r (a : V) b)).card := by
    intro a
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    refine Finset.card_bij (fun b _ => (b : V)) ?_ ?_ ?_
    · intro b hb
      have hb' := (hAdj a b).1 (Finset.mem_filter.1 hb).2
      exact Finset.mem_filter.2 ⟨b.2, fun hcon => hb'.1 (Subtype.ext hcon.symm), hb'.2⟩
    · intro b _ c _ hbc
      exact Subtype.ext hbc
    · intro b hb
      obtain ⟨hbT, hbne, hbr⟩ := Finset.mem_filter.1 hb
      refine ⟨⟨b, hbT⟩, ?_, rfl⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      exact (hAdj a ⟨b, hbT⟩).2 ⟨fun hcon => hbne (congrArg Subtype.val hcon.symm), hbr⟩
  have hmin : Fintype.card {x // x ∈ T} ≤ 2 * G.minDegree := by
    rcases Finset.eq_empty_or_nonempty T with rfl | hT
    · simp
    · haveI : Nonempty {x // x ∈ T} := by
        obtain ⟨z, hz⟩ := hT
        exact ⟨⟨z, hz⟩⟩
      obtain ⟨a, ha⟩ := G.exists_minimal_degree_vertex
      rw [hcard, ha, hdegree a]
      exact hdeg (a : V) a.2
  obtain ⟨M, hM⟩ := perfectMatchingDirac_holds G hEven hmin
  have hpartner : ∀ a : {x // x ∈ T}, ∃! b, M.Adj a b := fun a => hM.1 (hM.2 a)
  choose f hf huniq using fun a => hpartner a
  have hfinv : ∀ a, f (f a) = a := fun a => (huniq (f a) a (M.symm (hf a))).symm
  refine ⟨fun v => if h : v ∈ T then ((f ⟨v, h⟩ : {x // x ∈ T}) : V) else v, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [dif_pos ha]
    exact (f ⟨a, ha⟩).2
  · intro a ha
    simp only [dif_pos ha, dif_pos (f ⟨a, ha⟩).2]
    have h2 : (⟨((f ⟨a, ha⟩ : {x // x ∈ T}) : V), (f ⟨a, ha⟩).2⟩ : {x // x ∈ T}) = f ⟨a, ha⟩ := rfl
    rw [h2, hfinv ⟨a, ha⟩]
  · intro a ha hcon
    simp only [dif_pos ha] at hcon
    have hadj := (hAdj _ _).1 (M.adj_sub (hf ⟨a, ha⟩))
    have h2 : (f ⟨a, ha⟩) = (⟨a, ha⟩ : {x // x ∈ T}) := Subtype.ext hcon
    rw [h2] at hadj
    exact hadj.1 rfl
  · intro a ha
    simp only [dif_pos ha]
    exact ((hAdj _ _).1 (M.adj_sub (hf ⟨a, ha⟩))).2

/-! ### One class of a region is paired inside itself -/

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ}

/-- **A class of a two-sided grid design is paired inside itself.**  Every vertex of `W` misses at
most a quarter of a class (`IsGridTwoSidedReservoir.classBalancedSharp`), so if the trace of the
class on the link has even size and the used degree inside it is small, the trace carries a
fixed-point-free involution by edges of `F` outside `U`.  This is the companion of
`BKLO.exists_class_matching_avoiding` for the one class of a region that a class matching cannot
send anywhere else — the corner class. -/
theorem exists_class_involution_avoiding
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i : ℕ} (hi : i < gridSize ε K * gridSize ε K)
    {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hU : ∀ a ∈ C i ∩ Xu, ((C i ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (heven : Even (C i ∩ Xu).card)
    (hsize : q + 4 * m + 4 ≤ 2 * (C i ∩ Xu).card) :
    ∃ p : V → V, (∀ a ∈ C i ∩ Xu, p a ∈ C i ∩ Xu) ∧ (∀ a ∈ C i ∩ Xu, p (p a) = a) ∧
      (∀ a ∈ C i ∩ Xu, p a ≠ a) ∧
      (∀ a ∈ C i ∩ Xu, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) := by
  classical
  set T : Finset V := C i ∩ Xu with hTdef
  refine exists_involution_of_half_degree T (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U) ?_ heven ?_
  · intro a b hab
    rw [Sym2.eq_swap]
    exact hab
  · intro a ha
    show T.card ≤ 2 * (T.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card
    have haW' : a ∈ W' := hXW' (Finset.mem_inter.1 ha).2
    have hbal := hgrid.classBalancedSharp a (hW'W haW') i hi
    rw [hq i hi] at hbal
    set nb : ℕ := (nonNbrs F W' a ∩ C i).card with hnbdef
    have hbad : T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))
        ⊆ insert a ((nonNbrs F W' a ∩ C i) ∪ T.filter (fun b => s(a, b) ∈ U)) := by
      intro b hb
      obtain ⟨hbT, hbr⟩ := Finset.mem_filter.1 hb
      by_cases hba : b = a
      · exact hba ▸ Finset.mem_insert_self b _
      refine Finset.mem_insert_of_mem ?_
      by_cases hU' : s(a, b) ∈ U
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hbT, hU'⟩)
      · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨?_, (Finset.mem_inter.1 hbT).1⟩)
        refine Finset.mem_sdiff.2 ⟨hXW' (Finset.mem_inter.1 hbT).2, ?_⟩
        intro hmem
        exact hbr ⟨hba, (mem_resLink.1 hmem).2, hU'⟩
    have hcards : (T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))).card
        ≤ 1 + (nb + (T.filter (fun b => s(a, b) ∈ U)).card) := by
      refine le_trans (Finset.card_le_card hbad) ?_
      refine le_trans (Finset.card_insert_le _ _) ?_
      have := Finset.card_union_le (nonNbrs F W' a ∩ C i) (T.filter (fun b => s(a, b) ∈ U))
      omega
    have hsplit : (T.filter (fun b => b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U))).card
        + (T.filter (fun b => ¬ (b ≠ a ∧ (s(a, b) ∈ F ∧ s(a, b) ∉ U)))).card = T.card :=
      Finset.card_filter_add_card_filter_not _
    have hUa := hU a ha
    omega

/-- **Two classes of a region are paired with each other.**  `BKLO.exists_class_matching_avoiding`
matches the two traces; `BKLO.exists_swap_involution` turns the matching into a fixed-point-free
involution of their union, and the two classes are exchanged by it. -/
theorem exists_class_pair_involution_avoiding
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {i j : ℕ} (hi : i < gridSize ε K * gridSize ε K) (hj : j < gridSize ε K * gridSize ε K)
    (hij : i ≠ j) {Xu : Finset V} (hXW' : Xu ⊆ W') {U : Finset (Sym2 V)} {m q : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hcard : (C i ∩ Xu).card = (C j ∩ Xu).card)
    (hUA : ∀ a ∈ C i ∩ Xu, ((C j ∩ Xu).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (hUB : ∀ b ∈ C j ∩ Xu, ((C i ∩ Xu).filter (fun a => s(a, b) ∈ U)).card ≤ m)
    (hsize : q + 4 * m < 2 * (C i ∩ Xu).card) :
    ∃ p : V → V, (∀ a ∈ C i ∩ Xu, p a ∈ C j ∩ Xu) ∧ (∀ b ∈ C j ∩ Xu, p b ∈ C i ∩ Xu) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu), p (p z) = z) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu), p z ≠ z) ∧
      (∀ z ∈ (C i ∩ Xu) ∪ (C j ∩ Xu), s(z, p z) ∈ F ∧ s(z, p z) ∉ U) := by
  classical
  set A : Finset V := C i ∩ Xu with hAdef
  set B : Finset V := C j ∩ Xu with hBdef
  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.2 fun z hzA hzB => ?_
    exact (Finset.disjoint_left.1 (hgrid.classDisjoint i hi j hj hij))
      (Finset.mem_inter.1 hzA).1 (Finset.mem_inter.1 hzB).1
  obtain ⟨f, hmaps, hrel, hinj⟩ :=
    exists_class_matching_avoiding hgrid hW'W hi hj hXW' hq hcard hUA hUB hsize
  obtain ⟨p, hpA, hpU, hpinv, hpne, hpr⟩ :=
    exists_swap_involution hdisj hmaps hinj hcard
      (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U)
      (fun a b hab => by simp only []; rw [Sym2.eq_swap]; exact hab) hrel
  have hpAB : ∀ a ∈ A, p a ∈ B := by
    intro a ha
    rw [hpA a ha]
    exact hmaps a ha
  have himg : A.image f = B := by
    refine Finset.eq_of_subset_of_card_le (fun b hb => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact hmaps a ha
    · rw [Finset.card_image_of_injOn hinj, hcard]
  have hpBA : ∀ b ∈ B, p b ∈ A := by
    intro b hb
    have hbU : b ∈ A ∪ B := Finset.mem_union_right _ hb
    rcases Finset.mem_union.1 (hpU b hbU) with hmem | hmem
    · exact hmem
    · exfalso
      have hpb : p b ∈ A.image f := by rw [himg]; exact hmem
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hpb
      have hpa : p a = p b := by rw [hpA a ha]; exact hfa
      have h1 : p (p a) = a := hpinv a (Finset.mem_union_left _ ha)
      have h2 : p (p b) = b := hpinv b hbU
      rw [hpa, h2] at h1
      exact (Finset.disjoint_left.1 hdisj) (h1 ▸ ha) hb
  exact ⟨p, hpAB, hpBA, hpinv, hpne, hpr⟩

/-! ### One unperturbed link, paired class for class -/

/-- **An unperturbed link is paired class for class, with no leftovers.**  Let `ρ` be a permutation
of the `h` row indices with inverse `σ` sending `y u` to `x u` — so the corner class
`C (x u · h + y u)` of the region of `u`, which is a row class *and* a column class, is matched
with itself.  Then the reserved link of `u` carries a fixed-point-free involution by edges of `F`
outside `U` which obeys the cross-side rule `BKLO.IsCrossSideAt` at **every** vertex of the link:
the row class `(x u, β)` is paired with the column class `(ρ β, y u)`, and the corner class inside
itself (`BKLO.exists_class_involution_avoiding`).

This is the class-matched one-link step of `TWOSIDED.md` §11 in the unperturbed case: the leftovers
of a link come only from the perturbation. -/
theorem exists_classMatched_pairing_unperturbed
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {u : V} (hu : u ∈ W \ W') {q c : ℕ}
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hc : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u), (C i ∩ resLink R W' u).card = c)
    {ρ σ : ℕ → ℕ} (hρlt : ∀ β < gridSize ε K, ρ β < gridSize ε K)
    (hσlt : ∀ α < gridSize ε K, σ α < gridSize ε K)
    (hσρ : ∀ β < gridSize ε K, σ (ρ β) = β) (hρσ : ∀ α < gridSize ε K, ρ (σ α) = α)
    (hcorner : ρ (y u) = x u)
    {U : Finset (Sym2 V)} {m : ℕ}
    (hU : ∀ a ∈ resLink R W' u, ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ resLink R W' u).filter (fun b => s(a, b) ∈ U)).card ≤ m)
    (heven : Even c) (hsize : q + 4 * m + 4 ≤ 2 * c) :
    ∃ p : V → V, (∀ a ∈ resLink R W' u, p a ∈ resLink R W' u) ∧
      (∀ a ∈ resLink R W' u, p (p a) = a) ∧ (∀ a ∈ resLink R W' u, p a ≠ a) ∧
      (∀ a ∈ resLink R W' u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      ∀ (a : V) (α β : ℕ), α < gridSize ε K → β < gridSize ε K →
        a ∈ C (α * gridSize ε K + β) → a ∈ resLink R W' u →
        IsCrossSideAt (gridSize ε K) C x y α β u (p a) (ρ β) (σ α) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set Xu : Finset V := resLink R W' u with hXudef
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  have hXW' : Xu ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  -- the classes of the region
  set rowI : ℕ → ℕ := fun β => x u * h + β with hrowIdef
  set colI : ℕ → ℕ := fun α => α * h + y u with hcolIdef
  have hrowmem : ∀ β < h, rowI β ∈ gridIdx h (x u) (y u) := fun β hβ =>
    mem_gridIdx.2 (Or.inl ⟨β, hβ, rfl⟩)
  have hcolmem : ∀ α < h, colI α ∈ gridIdx h (x u) (y u) := fun α hα =>
    mem_gridIdx.2 (Or.inr ⟨α, hα, rfl⟩)
  have hrowlt : ∀ β < h, rowI β < h * h := fun β hβ => gridIdx_lt hxu hyu (hrowmem β hβ)
  have hcollt : ∀ α < h, colI α < h * h := fun α hα => gridIdx_lt hxu hyu (hcolmem α hα)
  have hcornereq : colI (ρ (y u)) = rowI (y u) := by
    rw [hcolIdef, hrowIdef, hcorner]
  -- the blocks
  set T : ℕ → Finset V := fun β => (C (rowI β) ∩ Xu) ∪ (C (colI (ρ β)) ∩ Xu) with hTdef
  have hTsub : ∀ β < h, T β ⊆ Xu := by
    intro β _ z hz
    rcases Finset.mem_union.1 hz with hz' | hz' <;> exact (Finset.mem_inter.1 hz').2
  -- the block of each vertex
  have hclassU : ∀ z ∈ Xu, ∃ k ∈ gridIdx h (x u) (y u), z ∈ C k := by
    intro z hz
    have : z ∈ gridRegion h C (x u) (y u) :=
      (Finset.mem_inter.1 (hgrid.linkSubset u hu hz)).2
    rw [gridRegion_eq_biUnion] at this
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.1 this
    exact ⟨k, hk, hzk⟩
  have hunion : (Finset.range h).biUnion T = Xu := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨β, hβ, hzβ⟩ := Finset.mem_biUnion.1 hz
      exact hTsub β (Finset.mem_range.1 hβ) hzβ
    · intro z hz
      obtain ⟨k, hk, hzk⟩ := hclassU z hz
      rcases mem_gridIdx.1 hk with ⟨j, hj, rfl⟩ | ⟨l, hl, rfl⟩
      · exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj,
          Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hzk, hz⟩)⟩
      · refine Finset.mem_biUnion.2 ⟨σ l, Finset.mem_range.2 (hσlt l hl), ?_⟩
        refine Finset.mem_union_right _ (Finset.mem_inter.2 ⟨?_, hz⟩)
        rwa [hcolIdef, hρσ l hl]
  -- the blocks are pairwise disjoint
  have hρinj : ∀ β < h, ∀ β' < h, ρ β = ρ β' → β = β' := by
    intro β hβ β' hβ' heq
    rw [← hσρ β hβ, ← hσρ β' hβ', heq]
  have hidxdisj : ∀ β < h, ∀ β' < h, β ≠ β' → ∀ k ∈ ({rowI β, colI (ρ β)} : Finset ℕ),
      ∀ k' ∈ ({rowI β', colI (ρ β')} : Finset ℕ), k ≠ k' := by
    intro β hβ β' hβ' hne k hk k' hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
    have hrowrow : rowI β ≠ rowI β' := by
      intro hcon
      exact hne (by simpa [hrowIdef] using hcon)
    have hcolcol : colI (ρ β) ≠ colI (ρ β') := by
      intro hcon
      have h1 : ρ β = ρ β' := by
        have := gridDigits_inj hyu hyu (by simpa [hcolIdef] using hcon)
        exact this.1
      exact hne (hρinj β hβ β' hβ' h1)
    have hrowcol : ∀ γ < h, ∀ δ < h, γ ≠ δ → rowI γ ≠ colI (ρ δ) := by
      intro γ hγ δ hδ hγδ hcon
      have h1 := gridDigits_inj hγ hyu (by simpa [hrowIdef, hcolIdef] using hcon)
      have h2 : ρ δ = ρ (y u) := by rw [hcorner]; exact h1.1.symm
      have h3 : δ = y u := hρinj δ hδ (y u) hyu h2
      exact hγδ (by rw [h1.2, h3])
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl
    · exact hrowrow
    · exact hrowcol β hβ β' hβ' hne
    · exact fun hcon => hrowcol β' hβ' β hβ (Ne.symm hne) hcon.symm
    · exact hcolcol
  have hdisj : ∀ β ∈ Finset.range h, ∀ β' ∈ Finset.range h, β ≠ β' → Disjoint (T β) (T β') := by
    intro β hβ β' hβ' hne
    rw [Finset.mem_range] at hβ hβ'
    refine Finset.disjoint_left.2 fun z hz hz' => ?_
    have hz1 : ∃ k ∈ ({rowI β, colI (ρ β)} : Finset ℕ), k < h * h ∧ z ∈ C k := by
      rcases Finset.mem_union.1 hz with hh | hh
      · exact ⟨rowI β, by simp, hrowlt β hβ, (Finset.mem_inter.1 hh).1⟩
      · exact ⟨colI (ρ β), by simp, hcollt _ (hρlt β hβ), (Finset.mem_inter.1 hh).1⟩
    have hz2 : ∃ k ∈ ({rowI β', colI (ρ β')} : Finset ℕ), k < h * h ∧ z ∈ C k := by
      rcases Finset.mem_union.1 hz' with hh | hh
      · exact ⟨rowI β', by simp, hrowlt β' hβ', (Finset.mem_inter.1 hh).1⟩
      · exact ⟨colI (ρ β'), by simp, hcollt _ (hρlt β' hβ'), (Finset.mem_inter.1 hh).1⟩
    obtain ⟨k, hk, hklt, hzk⟩ := hz1
    obtain ⟨k', hk', hk'lt, hzk'⟩ := hz2
    exact (Finset.disjoint_left.1
      (hgrid.classDisjoint k hklt k' hk'lt (hidxdisj β hβ β' hβ' hne k hk k' hk'))) hzk hzk'
  -- the used degree, in the shape the two constructions want
  have hUswap : ∀ (k l : ℕ), ∀ b ∈ C k ∩ Xu, l < h * h →
      ((C l ∩ Xu).filter (fun a => s(a, b) ∈ U)).card ≤ m := by
    intro k l b hb hl
    have hbXu : b ∈ Xu := (Finset.mem_inter.1 hb).2
    have hcong : ((C l ∩ Xu).filter (fun a => s(a, b) ∈ U))
        = ((C l ∩ Xu).filter (fun a => s(b, a) ∈ U)) := by
      refine Finset.filter_congr fun a _ => ?_
      rw [Sym2.eq_swap]
    rw [hcong]
    exact hU b hbXu l hl
  -- each block carries an involution
  have hblock : ∀ β : ℕ, ∃ pb : V → V, β < h →
      ((∀ z ∈ T β, pb z ∈ T β) ∧ (∀ z ∈ T β, pb (pb z) = z) ∧ (∀ z ∈ T β, pb z ≠ z) ∧
        (∀ z ∈ T β, s(z, pb z) ∈ F ∧ s(z, pb z) ∉ U) ∧
        (∀ z ∈ C (rowI β) ∩ Xu, pb z ∈ C (colI (ρ β)) ∩ Xu) ∧
        (∀ z ∈ C (colI (ρ β)) ∩ Xu, pb z ∈ C (rowI β) ∩ Xu)) := by
    intro β
    by_cases hβ : β < h
    swap
    · exact ⟨id, fun hcon => absurd hcon hβ⟩
    have hcardrow : (C (rowI β) ∩ Xu).card = c := hc _ (hrowmem β hβ)
    have hcardcol : (C (colI (ρ β)) ∩ Xu).card = c := hc _ (hcolmem _ (hρlt β hβ))
    by_cases hcase : β = y u
    · -- the corner class, paired inside itself
      have heqidx : colI (ρ β) = rowI β := by
        simp only [hcolIdef, hrowIdef, hcase, hcorner]
      obtain ⟨pb, hp1, hp2, hp3, hp4⟩ :=
        exists_class_involution_avoiding (i := rowI β) hgrid hW'W (hrowlt β hβ) hXW' hq
          (fun a ha => hU a (Finset.mem_inter.1 ha).2 (rowI β) (hrowlt β hβ))
          (by rw [hcardrow]; exact heven) (by rw [hcardrow]; exact hsize)
      have hTcorner : T β = C (rowI β) ∩ Xu := by
        simp only [hTdef, heqidx, Finset.union_self]
      rw [hTcorner]
      exact ⟨pb, fun _ => ⟨hp1, hp2, hp3, hp4, by rw [heqidx]; exact hp1,
        by rw [heqidx]; exact hp1⟩⟩
    · -- a row class and its column class
      have hidxne : rowI β ≠ colI (ρ β) := by
        intro hcon
        have h1 := gridDigits_inj hβ hyu (by simpa [hrowIdef, hcolIdef] using hcon)
        have h2 : ρ β = ρ (y u) := by rw [hcorner]; exact h1.1.symm
        exact hcase (by rw [h1.2])
      obtain ⟨pb, hp1, hp2, hp3, hp4, hp5⟩ :=
        exists_class_pair_involution_avoiding hgrid hW'W (hrowlt β hβ)
          (hcollt _ (hρlt β hβ)) hidxne hXW' hq (by rw [hcardrow, hcardcol])
          (fun a ha => hU a (Finset.mem_inter.1 ha).2 _ (hcollt _ (hρlt β hβ)))
          (fun b hb => hUswap _ _ b hb (hrowlt β hβ))
          (by rw [hcardrow]; omega)
      refine ⟨pb, fun _ => ⟨?_, ?_, ?_, ?_, hp1, hp2⟩⟩
      · intro z hz
        rcases Finset.mem_union.1 hz with hh | hh
        · exact Finset.mem_union_right _ (hp1 z hh)
        · exact Finset.mem_union_left _ (hp2 z hh)
      · exact hp3
      · exact hp4
      · exact hp5
  choose pb hpb using hblock
  -- glue the blocks
  obtain ⟨P, hPeq, hPmaps, hPinv, hPne, hPr⟩ :=
    exists_involution_biUnion (Finset.range h) T pb (fun a b => s(a, b) ∈ F ∧ s(a, b) ∉ U)
      hdisj
      (fun β hβ => (hpb β (Finset.mem_range.1 hβ)).1)
      (fun β hβ => (hpb β (Finset.mem_range.1 hβ)).2.1)
      (fun β hβ => (hpb β (Finset.mem_range.1 hβ)).2.2.1)
      (fun β hβ => (hpb β (Finset.mem_range.1 hβ)).2.2.2.1)
  rw [hunion] at hPmaps hPinv hPne hPr
  refine ⟨P, hPmaps, hPinv, hPne, hPr, ?_⟩
  intro a α β hα hβ hacls haXu
  -- the class of `a` is a class of the region
  obtain ⟨k, hk, hak⟩ := hclassU a haXu
  have hklt : k < h * h := gridIdx_lt hxu hyu hk
  have hαβlt : α * h + β < h * h := by
    calc α * h + β < α * h + h := by omega
      _ = (α + 1) * h := by ring
      _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
  have hkeq : k = α * h + β := by
    by_contra hcon
    exact (Finset.disjoint_left.1 (hgrid.classDisjoint k hklt _ hαβlt hcon)) hak hacls
  subst hkeq
  rcases mem_gridIdx.1 hk with ⟨j, hj, heq⟩ | ⟨l, hl, heq⟩
  · -- `a` lies in the row part
    obtain ⟨hx, hb⟩ := gridDigits_inj hβ hj heq
    have hmem : a ∈ C (rowI β) ∩ Xu := by
      refine Finset.mem_inter.2 ⟨?_, haXu⟩
      rw [hrowIdef]
      simpa [hx] using hacls
    have hPa : P a = pb β a :=
      hPeq β (Finset.mem_range.2 hβ) a (Finset.mem_union_left _ hmem)
    have := (hpb β hβ).2.2.2.2.1 a hmem
    refine Or.inl ⟨hx.symm, ?_⟩
    rw [hPa]
    exact (Finset.mem_inter.1 this).1
  · -- `a` lies in the column part
    obtain ⟨hx, hb⟩ := gridDigits_inj hβ hyu heq
    have hmem : a ∈ C (colI (ρ (σ α))) ∩ Xu := by
      refine Finset.mem_inter.2 ⟨?_, haXu⟩
      rw [hρσ α hα, hcolIdef]
      simpa [hb] using hacls
    have hPa : P a = pb (σ α) a :=
      hPeq (σ α) (Finset.mem_range.2 (hσlt α hα)) a (Finset.mem_union_right _ hmem)
    have := (hpb (σ α) (hσlt α hα)).2.2.2.2.2 a hmem
    refine Or.inr ⟨hb.symm, ?_⟩
    rw [hPa]
    exact (Finset.mem_inter.1 this).1

end BKLO
