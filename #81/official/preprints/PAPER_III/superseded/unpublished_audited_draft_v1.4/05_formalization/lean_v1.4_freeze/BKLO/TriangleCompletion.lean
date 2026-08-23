/-
# Completing a sparse reservoir to a triangle packing.

The greedy construction of `BKLO/GreedyPairCover.lean` produces a *graph* reservoir `R`: sparse
(`Δ(R) ≤ γ|S|`) and pair-covering (every pair of `S` has at least `K` common `R`-neighbours).  For
the packing route of `BKLO/PackingAbsorb.lean` the reservoir has to be the edge set of an
edge-disjoint family of triangles.

This file bridges the two.  In a host of large minimum degree every sparse subgraph `R` embeds in
the edge set of an edge-disjoint triangle family of comparable sparsity: process the edges of `R`
one at a time and complete each of them to a triangle with a fresh apex, chosen outside the
already-used neighbourhoods and outside the (few) vertices that are already carrying a large load.
The load bound is a plain double count: the triangles built so far have `3|P|` edges, so at most
`6|P|/(b-1)` vertices can have degree `≥ b-1`.

Everything here is `sorry`-free.  The two results exported are

* `BKLO.exists_triangle_completion` — the greedy completion, in arithmetic form;
* `BKLO.exists_sparse_pairCovering_packing` — a sparse pair-covering reservoir which is a
  **triangle packing**: the first two clauses of `BKLO.PackingReservoirExistence`.
-/
import BKLO.GreedyPairCover
import BKLO.PackingAbsorb

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Double counting -/

theorem card_filter_mem_edge {S : Finset V} {e : Sym2 V} (he : e ∈ cliqueEdges S) :
    (S.filter (fun v => v ∈ e)).card = 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [mem_cliqueEdgesV] at he
    obtain ⟨hmem, hnd⟩ := he
    have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
    have ha : a ∈ S := hmem a (by simp)
    have hb : b ∈ S := hmem b (by simp)
    have hset : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨ha, Or.inl rfl⟩
        · exact ⟨hb, Or.inr rfl⟩
    rw [hset, Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]

/-- **Handshake.**  The degrees of an edge set inside `S` sum to twice the number of edges. -/
theorem sum_edeg_eq_two_mul {A : Finset (Sym2 V)} {S : Finset V} (hA : A ⊆ cliqueEdges S) :
    ∑ v ∈ S, edeg A v = 2 * A.card := by
  classical
  have hrw : ∀ v : V, edeg A v = ∑ e ∈ A, if v ∈ e then 1 else 0 := by
    intro v
    rw [edeg, Finset.card_filter]
  simp only [hrw]
  rw [Finset.sum_comm]
  have hin : ∀ e ∈ A, (∑ v ∈ S, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter]
    exact card_filter_mem_edge (hA he)
  rw [Finset.sum_congr rfl hin, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### Small edge-set manipulations -/

theorem edeg_erase {R : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ R) (v : V) :
    edeg R v = edeg (R.erase e) v + (if v ∈ e then 1 else 0) := by
  classical
  have hsplit : (R.erase e).filter (fun g => v ∈ g) = (R.filter (fun g => v ∈ g)).erase e := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  by_cases hv : v ∈ e
  · have hmem : e ∈ R.filter (fun g => v ∈ g) := Finset.mem_filter.2 ⟨he, hv⟩
    rw [if_pos hv, edeg, edeg, hsplit, Finset.card_erase_of_mem hmem]
    have : 0 < (R.filter (fun g => v ∈ g)).card := Finset.card_pos.2 ⟨e, hmem⟩
    omega
  · have hmem : e ∉ R.filter (fun g => v ∈ g) := fun h => hv (Finset.mem_filter.1 h).2
    rw [if_neg hv, edeg, edeg, hsplit, Finset.erase_eq_of_notMem hmem, Nat.add_zero]

/-- The three edges of a triple of distinct vertices. -/
theorem cliqueEdges_tripleV {x y w : V} (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) :
    cliqueEdges ({x, y, w} : Finset V) = {s(x, y), s(x, w), s(y, w)} := by
  classical
  have hcard3 : ({x, y, w} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxw]),
      Finset.card_insert_of_notMem (by simp [hyw]), Finset.card_singleton]
  have hsub : ({s(x, y), s(x, w), s(y, w)} : Finset (Sym2 V)) ⊆ cliqueEdges ({x, y, w} : Finset V) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;>
      · rw [mem_cliqueEdgesV]
        refine ⟨?_, ?_⟩
        · intro u hu
          simp only [Sym2.mem_iff] at hu
          rcases hu with rfl | rfl <;> simp
        · simp [Sym2.isDiag_iff_proj_eq, hxy, hxw, hyw]
  have hc : ({s(x, y), s(x, w), s(y, w)} : Finset (Sym2 V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxw, hyw]),
      Finset.card_insert_of_notMem (by simp [hxy, hxw]),
      Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, cliqueEdges_card_three hcard3])).symm

theorem famEdges_insert (t : Finset V) (P : Finset (Finset V)) :
    famEdges (insert t P) = cliqueEdges t ∪ famEdges P := by
  simp [famEdges, Finset.biUnion_insert]

/-! ### The greedy completion -/

/-- **Greedy triangle completion (induction).**  Processing the edges of `R` one at a time, each
edge is completed to a triangle by a fresh apex; the invariant
`edeg (famEdges P) v + 2 * edeg R v ≤ b` is preserved. -/
theorem tri_complete_induction {E : Finset (Sym2 V)} {S : Finset V} {b M L : ℕ}
    (hES : E ⊆ cliqueEdges S) (hb : 2 ≤ b)
    (hL : 6 * M + (b - 1) * (2 * b) ≤ (b - 1) * L)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, ∀ W : Finset V, W.card ≤ L →
      ((nbhdIn E x S ∩ nbhdIn E y S) \ W).Nonempty) :
    ∀ N : ℕ, ∀ (R : Finset (Sym2 V)) (P : Finset (Finset V)),
      R.card ≤ N → R ⊆ E → TriFamilyIn E P → Disjoint (famEdges P) R →
      P.card + R.card ≤ M →
      (∀ v, edeg (famEdges P) v + 2 * edeg R v ≤ b) →
      ∃ P' : Finset (Finset V), TriFamilyIn E P' ∧ P ⊆ P' ∧ R ⊆ famEdges P' ∧
        P'.card ≤ M ∧ ∀ v, edeg (famEdges P') v ≤ b := by
  classical
  intro N
  induction N with
  | zero =>
    intro R P hcard hRE hP _ hM hdeg
    have hR : R = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    subst hR
    refine ⟨P, hP, Finset.Subset.refl _, by simp, by omega, fun v => ?_⟩
    have := hdeg v
    rw [edeg_empty] at this
    omega
  | succ N ih =>
    intro R P hcard hRE hP hdisj hM hdeg
    rcases R.eq_empty_or_nonempty with rfl | hne
    · refine ⟨P, hP, Finset.Subset.refl _, by simp, by omega, fun v => ?_⟩
      have := hdeg v
      rw [edeg_empty] at this
      omega
    obtain ⟨e0, he0⟩ := hne
    revert he0
    induction e0 using Sym2.ind with
    | _ x y =>
      intro he0
      -- the endpoints
      have hxyE : s(x, y) ∈ cliqueEdges S := hES (hRE he0)
      obtain ⟨hmem, hnd⟩ := mem_cliqueEdgesV.1 hxyE
      have hxy : x ≠ y := by simpa [Sym2.isDiag_iff_proj_eq] using hnd
      have hx : x ∈ S := hmem x (by simp)
      have hy : y ∈ S := hmem y (by simp)
      -- the forbidden set
      set g : V → ℕ := fun v => edeg (famEdges P) v + 2 * edeg R v with hgdef
      set W₁ : Finset V := S.filter (fun v => b - 1 ≤ g v) with hW₁
      set W : Finset V := W₁ ∪ resNbhd (famEdges P ∪ R) S x ∪ resNbhd (famEdges P ∪ R) S y with hW
      have hsum : ∑ v ∈ S, g v ≤ 6 * M := by
        have h1 : ∑ v ∈ S, g v = 2 * (famEdges P).card + 2 * (2 * R.card) := by
          rw [hgdef]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            sum_edeg_eq_two_mul (famEdges_subset_of_triFamilyIn hP |>.trans hES),
            sum_edeg_eq_two_mul (hRE.trans hES)]
        have h2 : (famEdges P).card = 3 * P.card := card_famEdges_of_triFamily hP
        rw [h1, h2]
        omega
      have hW₁card : (b - 1) * W₁.card ≤ 6 * M := by
        have h1 : (b - 1) * W₁.card ≤ ∑ v ∈ W₁, g v := by
          rw [Finset.card_eq_sum_ones, Finset.mul_sum]
          refine Finset.sum_le_sum fun v hv => ?_
          simpa using (Finset.mem_filter.1 hv).2
        have h2 : ∑ v ∈ W₁, g v ≤ ∑ v ∈ S, g v :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        omega
      have hgx : g x ≤ b := by have := hdeg x; omega
      have hgy : g y ≤ b := by have := hdeg y; omega
      have hnbx : (resNbhd (famEdges P ∪ R) S x).card ≤ b := by
        refine le_trans (card_resNbhd_le _ _ _) (le_trans (edeg_union_le _ _ _) ?_)
        have := hdeg x
        omega
      have hnby : (resNbhd (famEdges P ∪ R) S y).card ≤ b := by
        refine le_trans (card_resNbhd_le _ _ _) (le_trans (edeg_union_le _ _ _) ?_)
        have := hdeg y
        omega
      have hWcard : W.card ≤ L := by
        have hcard1 : W.card ≤ W₁.card + b + b := by
          calc W.card ≤ (W₁ ∪ resNbhd (famEdges P ∪ R) S x).card
                + (resNbhd (famEdges P ∪ R) S y).card := Finset.card_union_le _ _
            _ ≤ (W₁.card + (resNbhd (famEdges P ∪ R) S x).card)
                + (resNbhd (famEdges P ∪ R) S y).card :=
                  Nat.add_le_add_right (Finset.card_union_le _ _) _
            _ ≤ W₁.card + b + b := by omega
        have hmul : (b - 1) * W.card ≤ (b - 1) * L := by
          calc (b - 1) * W.card ≤ (b - 1) * (W₁.card + b + b) := Nat.mul_le_mul_left _ hcard1
            _ = (b - 1) * W₁.card + (b - 1) * (2 * b) := by ring
            _ ≤ 6 * M + (b - 1) * (2 * b) := by omega
            _ ≤ (b - 1) * L := hL
        exact Nat.le_of_mul_le_mul_left hmul (by omega)
      obtain ⟨w, hwmem⟩ := hcn x hx y hy W hWcard
      rw [Finset.mem_sdiff, Finset.mem_inter, mem_nbhdIn, mem_nbhdIn] at hwmem
      obtain ⟨⟨⟨hwS, hxw⟩, ⟨_, hyw⟩⟩, hwW⟩ := hwmem
      have hwW₁ : w ∉ W₁ := fun h => hwW (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hwx : s(x, w) ∉ famEdges P ∪ R := fun h =>
        hwW (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, h⟩)))
      have hwy : s(y, w) ∉ famEdges P ∪ R := fun h =>
        hwW (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, h⟩))
      have hgw : g w + 2 ≤ b := by
        have : ¬ (b - 1 ≤ g w) := fun h => hwW₁ (Finset.mem_filter.2 ⟨hwS, h⟩)
        omega
      -- the new triangle
      have hxwne : x ≠ w := by
        intro h
        subst h
        exact (mem_cliqueEdgesV.1 (hES hxw)).2 (by simp [Sym2.isDiag_iff_proj_eq])
      have hywne : y ≠ w := by
        intro h
        subst h
        exact (mem_cliqueEdgesV.1 (hES hyw)).2 (by simp [Sym2.isDiag_iff_proj_eq])
      set t : Finset V := {x, y, w} with htdef
      have htcard : t.card = 3 := by
        rw [htdef, Finset.card_insert_of_notMem (by simp [hxy, hxwne]),
          Finset.card_insert_of_notMem (by simp [hywne]), Finset.card_singleton]
      have htedges : cliqueEdges t = {s(x, y), s(x, w), s(y, w)} :=
        cliqueEdges_tripleV hxy hxwne hywne
      have htE : cliqueEdges t ⊆ E := by
        rw [htedges]
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hRE he0
        · exact hxw
        · exact hyw
      have htdisjP : Disjoint (cliqueEdges t) (famEdges P) := by
        rw [htedges]
        refine Finset.disjoint_left.2 ?_
        intro e he hP'
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hdisj) hP' he0
        · exact hwx (Finset.mem_union_left _ hP')
        · exact hwy (Finset.mem_union_left _ hP')
      have htnotP : t ∉ P := by
        intro h
        have : s(x, y) ∈ famEdges P := Finset.mem_biUnion.2 ⟨t, h, by rw [htedges]; simp⟩
        exact (Finset.disjoint_left.1 hdisj) this he0
      set P' : Finset (Finset V) := insert t P with hP'def
      have hfam : famEdges P' = cliqueEdges t ∪ famEdges P := famEdges_insert t P
      have hP'fam : TriFamilyIn E P' := by
        refine ⟨?_, ?_, ?_⟩
        · intro s hs
          rcases Finset.mem_insert.1 hs with rfl | hs
          · exact htcard
          · exact hP.1 s hs
        · intro s hs
          rcases Finset.mem_insert.1 hs with rfl | hs
          · exact htE
          · exact hP.2.1 s hs
        · intro s hs s' hs' hne
          rcases Finset.mem_insert.1 hs with rfl | hs <;>
            rcases Finset.mem_insert.1 hs' with rfl | hs'
          · exact absurd rfl hne
          · exact Finset.disjoint_of_subset_right
              (fun e he => Finset.mem_biUnion.2 ⟨s', hs', he⟩) htdisjP
          · exact (Finset.disjoint_of_subset_right
              (fun e he => Finset.mem_biUnion.2 ⟨s, hs, he⟩) htdisjP).symm
          · exact hP.2.2 s hs s' hs' hne
      -- the remaining edges
      set R' : Finset (Sym2 V) := R.erase s(x, y) with hR'def
      have hRpos : 0 < R.card := Finset.card_pos.2 ⟨_, he0⟩
      have hRerase : R'.card = R.card - 1 := by
        rw [hR'def]; exact Finset.card_erase_of_mem he0
      have hR'card : R'.card ≤ N := by omega
      have hR'E : R' ⊆ E := (Finset.erase_subset _ _).trans hRE
      have hdisj' : Disjoint (famEdges P') R' := by
        rw [hfam]
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · rw [htedges]
          refine Finset.disjoint_left.2 ?_
          intro e he heR
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl
          · exact (Finset.mem_erase.1 heR).1 rfl
          · exact hwx (Finset.mem_union_right _ (Finset.mem_of_mem_erase heR))
          · exact hwy (Finset.mem_union_right _ (Finset.mem_of_mem_erase heR))
        · exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj
      have hMcard : P'.card + R'.card ≤ M := by
        have h1 : P'.card = P.card + 1 := by
          rw [hP'def, Finset.card_insert_of_notMem htnotP]
        omega
      have hdeg' : ∀ v, edeg (famEdges P') v + 2 * edeg R' v ≤ b := by
        intro v
        have hd1 : edeg (famEdges P') v = edeg (cliqueEdges t) v + edeg (famEdges P) v := by
          rw [hfam, edeg_union_of_disjoint htdisjP]
        have hd2 : edeg (cliqueEdges t) v = if v ∈ t then 2 else 0 := edeg_cliqueEdges htcard v
        have hd3 : edeg R v = edeg R' v + (if v ∈ s(x, y) then 1 else 0) := edeg_erase he0 v
        have hdv := hdeg v
        by_cases hvt : v ∈ t
        · rw [htdef] at hvt
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvt
          rcases hvt with rfl | rfl | rfl
          · have : (v : V) ∈ s(v, y) := by simp
            rw [hd1, hd2, if_pos (by simp [htdef])]
            rw [hd3, if_pos this] at hdv
            omega
          · have : (v : V) ∈ s(x, v) := by simp
            rw [hd1, hd2, if_pos (by simp [htdef])]
            rw [hd3, if_pos this] at hdv
            omega
          · have hvne : v ∉ s(x, y) := by
              simp only [Sym2.mem_iff]
              rintro (rfl | rfl)
              · exact hxwne rfl
              · exact hywne rfl
            rw [hd1, hd2, if_pos (by simp [htdef])]
            rw [hd3, if_neg hvne] at hdv
            have hgwv : g v + 2 ≤ b := hgw
            rw [hgdef] at hgwv
            simp only at hgwv
            omega
        · rw [hd1, hd2, if_neg hvt]
          have : edeg R' v ≤ edeg R v := edeg_mono (Finset.erase_subset _ _) v
          omega
      obtain ⟨P'', hP''fam, hP'P'', hR'sub, hP''card, hP''deg⟩ :=
        ih R' P' hR'card hR'E hP'fam hdisj' hMcard hdeg'
      refine ⟨P'', hP''fam, ?_, ?_, hP''card, hP''deg⟩
      · exact (Finset.subset_insert _ _).trans hP'P''
      · intro e he
        by_cases hee : e = s(x, y)
        · subst hee
          have htP'' : t ∈ P'' := hP'P'' (Finset.mem_insert_self t P)
          exact Finset.mem_biUnion.2 ⟨t, htP'', by rw [htedges]; simp⟩
        · exact hR'sub (Finset.mem_erase.2 ⟨hee, he⟩)

/-- **Greedy triangle completion.**  A sparse subgraph of a host in which every pair of vertices
has many common neighbours outside any small exceptional set embeds into the edge set of an
edge-disjoint triangle family whose maximum degree is still at most `b`. -/
theorem exists_triangle_completion {E : Finset (Sym2 V)} {S : Finset V} {b M L : ℕ}
    (hES : E ⊆ cliqueEdges S) (hb : 2 ≤ b)
    (hL : 6 * M + (b - 1) * (2 * b) ≤ (b - 1) * L)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, ∀ W : Finset V, W.card ≤ L →
      ((nbhdIn E x S ∩ nbhdIn E y S) \ W).Nonempty)
    {R : Finset (Sym2 V)} (hRE : R ⊆ E) (hM : R.card ≤ M)
    (hRdeg : ∀ v, 2 * edeg R v ≤ b) :
    ∃ P : Finset (Finset V), TriFamilyIn E P ∧ R ⊆ famEdges P ∧
      ∀ v, edeg (famEdges P) v ≤ b := by
  classical
  obtain ⟨P, hP, _, hsub, _, hdeg⟩ :=
    tri_complete_induction hES hb hL hcn R.card R ∅ (le_refl _) hRE
      ⟨by simp, by simp, by simp⟩ (by simp [famEdges]) (by simpa using hM)
      (fun v => by simpa [famEdges, edeg_empty] using hRdeg v)
  exact ⟨P, hP, hsub, hdeg⟩

/-! ### A sparse pair-covering *triangle packing* -/

set_option maxHeartbeats 1000000 in
/-- **A sparse pair-covering reservoir which is a triangle packing** (the case of small `γ`). -/
theorem exists_sparse_pairCovering_packing_small {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1 / 20) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        (∀ v : V, (edeg (famEdges P) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges P) S e).card := by
  classical
  obtain ⟨n₁, hpc⟩ := exists_sparse_pairCovering (γ := γ / 24) (by linarith) K
  refine ⟨max n₁ (max ⌈(48 : ℝ) / γ⌉₊ 200), ?_⟩
  intro V _ E S hn hES hdeg
  set n := S.card with hndef
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : ⌈(48 : ℝ) / γ⌉₊ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : 200 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnR : (200 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn48 : (48 : ℝ) ≤ γ * (n : ℝ) := by
    have h1 : (48 : ℝ) / γ ≤ (⌈(48 : ℝ) / γ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(48 : ℝ) / γ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have h3 : (48 : ℝ) / γ ≤ (n : ℝ) := le_trans h1 h2
    have := mul_le_mul_of_nonneg_left h3 hγ.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hγ)] at this
  -- the sparse pair-covering graph reservoir
  obtain ⟨R, hRE, hRdeg, hRcov⟩ := hpc E S hn1 hES (fun v hv => by
    have := hdeg v hv
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith)
  -- the degree parameter
  set d : ℕ := ⌈γ * (n : ℝ) / 24⌉₊ with hddef
  have hd1 : 1 ≤ d := Nat.one_le_ceil_iff.2 (by positivity)
  have hdup : (d : ℝ) ≤ γ * (n : ℝ) / 24 + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hdR : ∀ v : V, edeg R v ≤ d := by
    intro v
    have h1 : (edeg R v : ℝ) ≤ γ / 24 * (n : ℝ) := hRdeg v
    have h2 : (edeg R v : ℝ) ≤ (d : ℝ) :=
      le_trans (by linarith) (Nat.le_ceil (γ * (n : ℝ) / 24))
    exact_mod_cast h2
  have h12d : (12 : ℝ) * (d : ℝ) ≤ γ * (n : ℝ) := by linarith
  have h60d : 60 * d ≤ n := by
    have : (60 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast this
  -- the arithmetic parameters of the completion
  set b : ℕ := 12 * d with hbdef
  set r : ℕ := n / 3 with hrdef
  set L : ℕ := r + 24 * d with hLdef
  have hM2 : 2 * R.card ≤ d * n := by
    have h1 : ∑ v ∈ S, edeg R v = 2 * R.card := sum_edeg_eq_two_mul (hRE.trans hES)
    have h2 : ∑ v ∈ S, edeg R v ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v _ => hdR v
    rw [Finset.sum_const, smul_eq_mul] at h2
    calc 2 * R.card = ∑ v ∈ S, edeg R v := h1.symm
      _ ≤ S.card * d := h2
      _ = d * n := by rw [← hndef]; ring
  have hr20 : 20 * d ≤ r := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have h3r : n ≤ 3 * r + 2 := by
    have := Nat.div_add_mod n 3
    have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  have hb2 : 2 ≤ b := by omega
  have hL : 6 * R.card + (b - 1) * (2 * b) ≤ (b - 1) * L := by
    have hkey : 6 * R.card ≤ (b - 1) * r := by
      have h1 : 6 * R.card ≤ 3 * (d * n) := by omega
      have h2 : 3 * (d * n) ≤ 3 * (d * (3 * r + 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3r)
      have h3 : 3 * (d * (3 * r + 2)) + r ≤ 12 * d * r := by nlinarith
      have h4 : (b - 1) * r + r = 12 * d * r := by
        have : b - 1 + 1 = b := by omega
        calc (b - 1) * r + r = (b - 1 + 1) * r := by ring
          _ = b * r := by rw [this]
          _ = 12 * d * r := by rw [hbdef]
      omega
    have hexp : (b - 1) * L = (b - 1) * r + (b - 1) * (24 * d) := by rw [hLdef]; ring
    have h2b : 2 * b = 24 * d := by rw [hbdef]; ring
    rw [hexp, h2b]
    omega
  -- every pair has many common neighbours outside a set of size `L`
  have hLreal : (L : ℝ) ≤ (n : ℝ) / 3 + 24 * (d : ℝ) := by
    have h1 : (r : ℝ) ≤ (n : ℝ) / 3 := by
      have : (3 : ℝ) * (r : ℝ) ≤ (n : ℝ) := by
        have := Nat.mul_div_le n 3
        have h3 : 3 * r ≤ n := by rw [hrdef]; omega
        exact_mod_cast h3
      linarith
    have : ((L : ℕ) : ℝ) = (r : ℝ) + 24 * (d : ℝ) := by rw [hLdef]; push_cast; ring
    rw [this]
    linarith
  have hcn : ∀ x ∈ S, ∀ y ∈ S, ∀ W : Finset V, W.card ≤ L →
      ((nbhdIn E x S ∩ nbhdIn E y S) \ W).Nonempty := by
    intro x hx y hy W hW
    have hdense := card_common_nbhd_dense hES hdeg hx hy W
    have hWR : (W.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hW
    have hdn : (24 : ℝ) * (d : ℝ) ≤ γ * (n : ℝ) + 24 := by nlinarith
    have hγn : γ * (n : ℝ) ≤ (n : ℝ) / 20 := by nlinarith
    have hpos : (0 : ℝ) < (((nbhdIn E x S ∩ nbhdIn E y S) \ W).card : ℝ) := by
      have hγ0 : (0 : ℝ) ≤ γ * (n : ℝ) := by positivity
      linarith
    have : 0 < ((nbhdIn E x S ∩ nbhdIn E y S) \ W).card := by exact_mod_cast hpos
    exact Finset.card_pos.1 this
  obtain ⟨P, hP, hRP, hPdeg⟩ :=
    exists_triangle_completion hES hb2 hL hcn hRE (le_refl _) (fun v => by
      have := hdR v
      omega)
  refine ⟨P, hP, fun v => ?_, ?_⟩
  · have h1 : (edeg (famEdges P) v : ℝ) ≤ (b : ℝ) := by exact_mod_cast hPdeg v
    have h2 : ((b : ℕ) : ℝ) = 12 * (d : ℝ) := by rw [hbdef]; push_cast; ring
    rw [h2] at h1
    linarith
  · intro e he
    exact le_trans (hRcov e he) (Finset.card_le_card (apexSet_mono hRP S e))

/-- **A sparse pair-covering reservoir which is a triangle packing.**

For every `γ > 0` and every constant `K`, every large dense host contains an edge-disjoint family
of triangles `P` whose edge set has maximum degree at most `γ|S|` and in which every pair of
vertices of `S` has at least `K` common reserved neighbours.  This is the first half of
`BKLO.PackingReservoirExistence`: the reservoir is a genuine triangle packing (hence
triangle-decomposable, of even degrees and with `3 ∣ |R|`), it is sparse, and it covers every pair
many times over. -/
theorem exists_sparse_pairCovering_packing {γ : ℝ} (hγ : 0 < γ) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        (∀ v : V, (edeg (famEdges P) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges P) S e).card := by
  obtain ⟨n₀, h⟩ := exists_sparse_pairCovering_packing_small (γ := min γ (1 / 20))
    (lt_min hγ (by norm_num)) (min_le_right _ _) K
  have hmin : min γ (1 / 20) ≤ γ := min_le_left _ _
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdeg
  have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨P, hP, hPdeg, hPcov⟩ := h E S hn hES (fun v hv => by
    have hv' := hdeg v hv
    nlinarith)
  refine ⟨P, hP, fun v => ?_, hPcov⟩
  have hv := hPdeg v
  nlinarith

end BKLO
