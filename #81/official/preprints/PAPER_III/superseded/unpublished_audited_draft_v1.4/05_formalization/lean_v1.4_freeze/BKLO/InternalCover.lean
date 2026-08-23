/-
# Covering the part-internal edges by edge-disjoint triangles (BKLO §8.1, `F = K₃`).

The construction behind the parts-confined absorber of `BKLO/AbsorberPartsInterface.lean`.

Let `E` be a host graph on `S` and let `Parts` be a family of pairwise disjoint parts of size at
most `m`.  Write `I = insideParts E Parts` for the *internal* edges of `E`, i.e. those with both
ends in one part.  We build an edge set `A ⊆ E` which

* contains every internal edge (`I ⊆ A`);
* is *exactly* triangle-decomposable (`TriDecomp A`);
* has bounded maximum degree.

The construction is greedy: the internal edges are processed one at a time, and the internal edge
`xy` (inside a part `P`) is completed to a triangle `xyz` by an *apex* `z` chosen outside `P` (so
that the two new edges `xz`, `yz` are not internal), among the common `E`-neighbours of `x` and
`y`, avoiding the vertices `z` for which `xz` or `yz` has already been used, and avoiding the
currently overloaded vertices.  The three chosen edges are new, so the triangles are edge-disjoint,
and the degree invariant `d_A(v) ≤ D₀ + 2 + 2 d_J(v)` (with `J` the set of processed internal
edges) is preserved: at the two ends of the processed edge the degree grows by `2` and `d_J` grows
by `1`, while an apex is only ever used when its current degree is at most `D₀`.

`exists_internal_triangle_cover` is the resulting statement.
-/
import BKLO.Counting

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Elementary degree computations -/

/-- The three edges of a triple. -/
theorem cliqueEdges_tripleV {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cliqueEdges ({a, b, c} : Finset V) = ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨h, hne⟩
      rcases h x (Or.inl rfl) with rfl | rfl | rfl <;>
        rcases h y (Or.inr rfl) with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        refine ⟨?_, ?_⟩ <;> simp_all <;> tauto

theorem edeg_singleton (e : Sym2 V) (v : V) :
    edeg ({e} : Finset (Sym2 V)) v = if v ∈ e then 1 else 0 := by
  classical
  by_cases h : v ∈ e <;> simp [edeg, Finset.filter_singleton, h]

theorem edeg_insert {J : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ J) (v : V) :
    edeg (insert e J) v = edeg J v + if v ∈ e then 1 else 0 := by
  classical
  have hins : insert e J = {e} ∪ J := rfl
  rw [hins, edeg_union_of_disjoint (by simpa using he), edeg_singleton, Nat.add_comm]

theorem edeg_mono' {A B : Finset (Sym2 V)} (h : A ⊆ B) (v : V) : edeg A v ≤ edeg B v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- The degree of a vertex is at most the size of its neighbourhood. -/
theorem edeg_le_card_nbhdIn {E : Finset (Sym2 V)} {S : Finset V} (hE : E ⊆ cliqueEdges S)
    (x : V) : edeg E x ≤ (nbhdIn E x S).card := by
  classical
  have hsub : E.filter (fun e => x ∈ e) ⊆ (nbhdIn E x S).image (fun z => s(x, z)) := by
    intro e he
    obtain ⟨heE, hxe⟩ := Finset.mem_filter.1 he
    have hmem := mem_cliqueEdgesV.1 (hE heE)
    induction e using Sym2.ind with
    | _ p q =>
      simp only [Sym2.mem_iff] at hxe
      have hpq : p ≠ q := by simpa [Sym2.isDiag_iff_proj_eq] using hmem.2
      rcases hxe with rfl | rfl
      · exact Finset.mem_image.2 ⟨q, mem_nbhdIn.2 ⟨hmem.1 q (by simp), heE⟩, rfl⟩
      · refine Finset.mem_image.2 ⟨p, mem_nbhdIn.2 ⟨hmem.1 p (by simp), ?_⟩, ?_⟩
        · rwa [Sym2.eq_swap]
        · rw [Sym2.eq_swap]
  calc edeg E x ≤ ((nbhdIn E x S).image (fun z => s(x, z))).card := Finset.card_le_card hsub
    _ ≤ (nbhdIn E x S).card := Finset.card_image_le

/-- Two vertices of a graph with large minimum degree have many common neighbours. -/
theorem exists_common_nbr_notMem {E : Finset (Sym2 V)} {S : Finset V} {K : ℕ}
    (hE : E ⊆ cliqueEdges S) {x y : V} {Z : Finset V} (hZ : Z.card ≤ K)
    (hxy : S.card + K < edeg E x + edeg E y) :
    ∃ z ∈ S, z ∉ Z ∧ s(x, z) ∈ E ∧ s(y, z) ∈ E := by
  classical
  set Nx := nbhdIn E x S with hNx
  set Ny := nbhdIn E y S with hNy
  have hxle : edeg E x ≤ Nx.card := edeg_le_card_nbhdIn hE x
  have hyle : edeg E y ≤ Ny.card := edeg_le_card_nbhdIn hE y
  have hunion : (Nx ∪ Ny).card ≤ S.card :=
    Finset.card_le_card (Finset.union_subset (nbhdIn_subset _ _ _) (nbhdIn_subset _ _ _))
  have hinter := Finset.card_inter_add_card_union Nx Ny
  have hne : ((Nx ∩ Ny) \ Z).Nonempty := by
    rw [← Finset.card_pos]
    have hcard : (Nx ∩ Ny).card ≤ ((Nx ∩ Ny) \ Z).card + Z.card := by
      have : Nx ∩ Ny ⊆ ((Nx ∩ Ny) \ Z) ∪ Z := by
        intro w hw
        by_cases hwZ : w ∈ Z
        · exact Finset.mem_union_right _ hwZ
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hw, hwZ⟩)
      calc (Nx ∩ Ny).card ≤ (((Nx ∩ Ny) \ Z) ∪ Z).card := Finset.card_le_card this
        _ ≤ ((Nx ∩ Ny) \ Z).card + Z.card := Finset.card_union_le _ _
    omega
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hzi, hzZ⟩ := Finset.mem_sdiff.1 hz
  obtain ⟨hzx, hzy⟩ := Finset.mem_inter.1 hzi
  rw [hNx, mem_nbhdIn] at hzx
  rw [hNy, mem_nbhdIn] at hzy
  exact ⟨z, hzx.1, hzZ, hzx.2, hzy.2⟩

/-! ### Internal edges -/

/-- An internal edge at `v` joins `v` to a vertex of its own part. -/
theorem edeg_insideParts_le {E : Finset (Sym2 V)} {S : Finset V} {Parts : Finset (Finset V)}
    {m : ℕ} (hE : E ⊆ cliqueEdges S)
    (hPd : ∀ P ∈ Parts, ∀ Q ∈ Parts, P ≠ Q → Disjoint P Q) (hPm : ∀ P ∈ Parts, P.card ≤ m)
    (v : V) : edeg (insideParts E Parts) v ≤ m - 1 := by
  classical
  by_cases hv : ∃ P ∈ Parts, v ∈ P
  · obtain ⟨P, hP, hvP⟩ := hv
    have hsub : (insideParts E Parts).filter (fun e => v ∈ e) ⊆
        (P.erase v).image (fun z => s(v, z)) := by
      intro e he
      obtain ⟨heI, hve⟩ := Finset.mem_filter.1 he
      obtain ⟨heE, Q, hQ, hQe⟩ := mem_insideParts.1 heI
      have hPQ : P = Q := by
        by_contra hne
        exact (Finset.disjoint_left.1 (hPd P hP Q hQ hne)) hvP (hQe v hve)
      subst hPQ
      have hmem := mem_cliqueEdgesV.1 (hE heE)
      induction e using Sym2.ind with
      | _ p q =>
        simp only [Sym2.mem_iff] at hve
        have hpq : p ≠ q := by simpa [Sym2.isDiag_iff_proj_eq] using hmem.2
        rcases hve with rfl | rfl
        · exact Finset.mem_image.2 ⟨q, Finset.mem_erase.2 ⟨fun h => hpq h.symm,
            hQe q (by simp)⟩, rfl⟩
        · exact Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨hpq, hQe p (by simp)⟩,
            by rw [Sym2.eq_swap]⟩
    calc edeg (insideParts E Parts) v ≤ ((P.erase v).image (fun z => s(v, z))).card :=
          Finset.card_le_card hsub
      _ ≤ (P.erase v).card := Finset.card_image_le
      _ = P.card - 1 := Finset.card_erase_of_mem hvP
      _ ≤ m - 1 := by have := hPm P hP; omega
  · push_neg at hv
    have : (insideParts E Parts).filter (fun e => v ∈ e) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun e he hve => ?_
      obtain ⟨-, Q, hQ, hQe⟩ := mem_insideParts.1 he
      exact hv Q hQ (hQe v hve)
    simp [edeg, this]

/-! ### The greedy triangle cover -/

/-- **Covering the internal edges by edge-disjoint triangles.**

`D₀` is the load threshold for apices, `ov` bounds the number of overloaded vertices, and `K`
bounds the number of vertices that a single greedy step must avoid; the hypothesis `hcn` says that
any two vertices of `S` have more than `K` common neighbours in `E`. -/
theorem exists_internal_triangle_cover {E : Finset (Sym2 V)} {S : Finset V}
    {Parts : Finset (Finset V)} {m D₀ K ov : ℕ} (hm : 1 ≤ m)
    (hE : E ⊆ cliqueEdges S)
    (hPS : ∀ P ∈ Parts, P ⊆ S)
    (hPd : ∀ P ∈ Parts, ∀ Q ∈ Parts, P ≠ Q → Disjoint P Q)
    (hPm : ∀ P ∈ Parts, P.card ≤ m)
    (hov : 6 * (insideParts E Parts).card ≤ (D₀ + 1) * ov)
    (hK : m + 2 * (D₀ + 2 * m) + ov ≤ K)
    (hcn : ∀ x ∈ S, ∀ y ∈ S, ∀ Z : Finset V, Z.card ≤ K →
      ∃ z ∈ S, z ∉ Z ∧ s(x, z) ∈ E ∧ s(y, z) ∈ E) :
    ∃ A : Finset (Sym2 V), A ⊆ E ∧ insideParts E Parts ⊆ A ∧ TriDecomp A ∧
      ∀ v : V, edeg A v ≤ D₀ + 2 * m := by
  classical
  set I : Finset (Sym2 V) := insideParts E Parts with hI
  have hIE : I ⊆ E := insideParts_subset E Parts
  have hIdeg : ∀ v : V, edeg I v ≤ m - 1 := edeg_insideParts_le hE hPd hPm
  -- the greedy induction
  have main : ∀ J : Finset (Sym2 V), J ⊆ I →
      ∃ (A : Finset (Sym2 V)) (T : Finset (Finset V)),
        A ⊆ E ∧ J ⊆ A ∧ (∀ f ∈ A, f ∈ I → f ∈ J) ∧ A.card ≤ 3 * J.card ∧
        (∀ t ∈ T, t.card = 3) ∧
        (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
        famEdges T = A ∧ (∀ v : V, edeg A v ≤ D₀ + 2 + 2 * edeg J v) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, by simp [famEdges],
        fun v => by simp [edeg]⟩
    | insert e J heJ ih =>
      intro hsub
      have heI : e ∈ I := hsub (Finset.mem_insert_self e J)
      have hJI : J ⊆ I := fun f hf => hsub (Finset.mem_insert_of_mem hf)
      obtain ⟨A, T, hAE, hJA, hAI, hAcard, hT3, hTd, hTe, hAdeg⟩ := ih hJI
      -- the edge to be covered
      obtain ⟨heE, P, hP, hPe⟩ := mem_insideParts.1 heI
      obtain ⟨x, y, rfl⟩ : ∃ x y, e = s(x, y) := by
        induction e using Sym2.ind with | _ a b => exact ⟨a, b, rfl⟩
      have hxy : x ≠ y := by
        have := (mem_cliqueEdgesV.1 (hE heE)).2
        simpa [Sym2.isDiag_iff_proj_eq] using this
      have hxP : x ∈ P := hPe x (by simp)
      have hyP : y ∈ P := hPe y (by simp)
      have hxS : x ∈ S := hPS P hP hxP
      have hyS : y ∈ S := hPS P hP hyP
      -- the forbidden vertices
      set Bad : Finset V := P ∪ S.filter (fun z => s(x, z) ∈ A) ∪
        S.filter (fun z => s(y, z) ∈ A) ∪ S.filter (fun z => D₀ < edeg A z) with hBad
      have hAdegle : ∀ v : V, edeg A v ≤ D₀ + 2 * m := by
        intro v
        have h1 := hAdeg v
        have h2 : edeg J v ≤ m - 1 := le_trans (edeg_mono' hJI v) (hIdeg v)
        omega
      have hovcard : (S.filter (fun z => D₀ < edeg A z)).card ≤ ov := by
        have hsum : ∑ v ∈ S, edeg A v = 2 * A.card :=
          sum_edeg_eq_two_mul_card (hAE.trans hE)
        have hsub2 : ∑ v ∈ S.filter (fun z => D₀ < edeg A z), edeg A v ≤ ∑ v ∈ S, edeg A v :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        have hlow0 := Finset.card_nsmul_le_sum (S.filter (fun z => D₀ < edeg A z))
          (fun v => edeg A v) (D₀ + 1) (fun v hv => (Finset.mem_filter.1 hv).2)
        simp only [smul_eq_mul] at hlow0
        have hJcard : J.card ≤ I.card := Finset.card_le_card hJI
        have hfin : (S.filter (fun z => D₀ < edeg A z)).card * (D₀ + 1) ≤ ov * (D₀ + 1) := by
          calc (S.filter (fun z => D₀ < edeg A z)).card * (D₀ + 1)
              ≤ 2 * A.card := le_trans hlow0 (by omega)
            _ ≤ 6 * I.card := by omega
            _ ≤ (D₀ + 1) * ov := hov
            _ = ov * (D₀ + 1) := Nat.mul_comm _ _
        exact Nat.le_of_mul_le_mul_right hfin (Nat.succ_pos _)
      have hBadcard : Bad.card ≤ K := by
        have h1 : (P ∪ S.filter (fun z => s(x, z) ∈ A) ∪ S.filter (fun z => s(y, z) ∈ A) ∪
            S.filter (fun z => D₀ < edeg A z)).card ≤
            P.card + (S.filter (fun z => s(x, z) ∈ A)).card +
              (S.filter (fun z => s(y, z) ∈ A)).card +
              (S.filter (fun z => D₀ < edeg A z)).card := by
          refine le_trans (Finset.card_union_le _ _) ?_
          have := Finset.card_union_le (P ∪ S.filter (fun z => s(x, z) ∈ A))
            (S.filter (fun z => s(y, z) ∈ A))
          have h2 := Finset.card_union_le P (S.filter (fun z => s(x, z) ∈ A))
          omega
        have h3 : (S.filter (fun z => s(x, z) ∈ A)).card ≤ D₀ + 2 * m :=
          le_trans (card_filter_edge_le_edeg A x S) (hAdegle x)
        have h4 : (S.filter (fun z => s(y, z) ∈ A)).card ≤ D₀ + 2 * m :=
          le_trans (card_filter_edge_le_edeg A y S) (hAdegle y)
        have h5 := hPm P hP
        rw [hBad]
        omega
      -- the apex
      obtain ⟨z, hzS, hzBad, hxz, hyz⟩ := hcn x hxS y hyS Bad hBadcard
      have hzP : z ∉ P := fun h => hzBad (by
        rw [hBad]; exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ h)))
      have hzxA : s(x, z) ∉ A := fun h => hzBad (by
        rw [hBad]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzS, h⟩))))
      have hzyA : s(y, z) ∉ A := fun h => hzBad (by
        rw [hBad]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzS, h⟩)))
      have hzload : edeg A z ≤ D₀ := by
        by_contra hlt
        exact hzBad (by
          rw [hBad]
          exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzS, by omega⟩))
      have hzx : x ≠ z := fun h => hzP (h ▸ hxP)
      have hzy : y ≠ z := fun h => hzP (h ▸ hyP)
      -- the new triangle
      set t : Finset V := {x, y, z} with ht
      have ht3 : t.card = 3 := by
        rw [ht, Finset.card_insert_of_notMem (by simp [hxy, hzx]),
          Finset.card_insert_of_notMem (by simp [hzy])]
        simp
      have htE : cliqueEdges t = ({s(x,y), s(y,z), s(x,z)} : Finset (Sym2 V)) :=
        cliqueEdges_tripleV hxy hzy hzx
      have hexy : s(x, y) ∉ A := fun h => heJ (hAI _ h heI)
      have htA : Disjoint (cliqueEdges t) A := by
        rw [htE, Finset.disjoint_left]
        intro f hf hfA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl
        exacts [hexy hfA, hzyA hfA, hzxA hfA]
      have hnotI : ∀ w : V, w ∈ P → s(w, z) ∉ I := by
        intro w hwP hmem
        obtain ⟨-, Q, hQ, hQe⟩ := mem_insideParts.1 hmem
        have hwQ : w ∈ Q := hQe w (by simp)
        have : P = Q := by
          by_contra hne
          exact (Finset.disjoint_left.1 (hPd P hP Q hQ hne)) hwP hwQ
        exact hzP (this ▸ hQe z (by simp))
      refine ⟨A ∪ cliqueEdges t, insert t T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- inside the host
        refine Finset.union_subset hAE ?_
        rw [htE]
        intro f hf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl
        exacts [heE, hyz, hxz]
      · -- contains the processed edges
        intro f hf
        rcases Finset.mem_insert.1 hf with rfl | hf
        · exact Finset.mem_union_right _ (by rw [htE]; simp)
        · exact Finset.mem_union_left _ (hJA hf)
      · -- no unprocessed internal edge has been used
        intro f hf hfI
        rcases Finset.mem_union.1 hf with hfA | hft
        · exact Finset.mem_insert_of_mem (hAI f hfA hfI)
        · rw [htE] at hft
          simp only [Finset.mem_insert, Finset.mem_singleton] at hft
          rcases hft with rfl | rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact absurd hfI (hnotI y hyP)
          · exact absurd hfI (hnotI x hxP)
      · -- edge count
        have h1 : (A ∪ cliqueEdges t).card ≤ A.card + (cliqueEdges t).card :=
          Finset.card_union_le _ _
        have h2 : (cliqueEdges t).card = 3 := cliqueEdges_card_three ht3
        rw [Finset.card_insert_of_notMem heJ]
        omega
      · -- triangles
        intro t' ht'
        rcases Finset.mem_insert.1 ht' with rfl | ht'
        · exact ht3
        · exact hT3 t' ht'
      · -- edge-disjoint triangles
        intro t₁ ht₁ t₂ ht₂ hne
        have hsubA : ∀ t' ∈ T, cliqueEdges t' ⊆ A := by
          intro t' ht'
          rw [← hTe]
          exact Finset.subset_biUnion_of_mem cliqueEdges ht'
        rcases Finset.mem_insert.1 ht₁ with rfl | ht₁ <;>
          rcases Finset.mem_insert.1 ht₂ with rfl | ht₂
        · exact absurd rfl hne
        · exact Finset.disjoint_of_subset_right (hsubA t₂ ht₂) htA
        · exact (Finset.disjoint_of_subset_right (hsubA t₁ ht₁) htA).symm
        · exact hTd t₁ ht₁ t₂ ht₂ hne
      · -- the edge sets agree
        rw [famEdges, Finset.biUnion_insert, ← famEdges, hTe, Finset.union_comm]
      · -- the degree invariant
        intro v
        rw [edeg_union_of_disjoint htA.symm, edeg_cliqueEdges ht3, edeg_insert heJ]
        have hold := hAdeg v
        have hmemt : v ∈ t ↔ (v = x ∨ v = y ∨ v = z) := by simp [ht]
        have hmeme : v ∈ s(x, y) ↔ (v = x ∨ v = y) := by simp
        by_cases hvx : v = x
        · subst hvx
          rw [if_pos (hmemt.2 (Or.inl rfl)), if_pos (hmeme.2 (Or.inl rfl))]
          omega
        · by_cases hvy : v = y
          · subst hvy
            rw [if_pos (hmemt.2 (Or.inr (Or.inl rfl))), if_pos (hmeme.2 (Or.inr rfl))]
            omega
          · by_cases hvz : v = z
            · subst hvz
              rw [if_pos (hmemt.2 (Or.inr (Or.inr rfl))), if_neg (by simp [hmeme, hvx, hvy])]
              omega
            · rw [if_neg (by simp [hmemt, hvx, hvy, hvz]), if_neg (by simp [hmeme, hvx, hvy])]
              omega
  obtain ⟨A, T, hAE, hIA, -, -, hT3, hTd, hTe, hAdeg⟩ := main I (subset_refl I)
  refine ⟨A, hAE, hIA, ⟨T, hT3, hTd, hTe⟩, fun v => ?_⟩
  have h1 := hAdeg v
  have h2 := hIdeg v
  omega

end BKLO
