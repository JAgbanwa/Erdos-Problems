/-
Copyright (c) 2026 Paper III formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paper III formalization team
-/
import Mathlib

/-!
# Dirac's theorem

A finite simple graph on at least three vertices in which every vertex has degree at least
half the number of vertices is Hamiltonian.

## Main statement

* `SimpleGraph.IsHamiltonian_of_minDegree`: if `G` is a simple graph on `V` with
  `3 ≤ Fintype.card V` and `Fintype.card V ≤ 2 * G.minDegree`, then `G.IsHamiltonian`.

## Implementation notes

The proof is the classical maximal-path / rotation–extension argument of Dirac, organised
around duplicate-free chains (`List.IsChain G.Adj`) of vertices:

* `SimpleGraph.rotationIndex_exists` — a pigeonhole step producing an index at which a
  duplicate-free chain, both of whose endpoints have all their neighbours inside the chain,
  can be rotated;
* `SimpleGraph.exists_external_edge` — a non-spanning chain has an edge leaving it;
* `SimpleGraph.hamiltonian_path_extend` — a non-spanning chain can be lengthened by one
  vertex (the analytic core of rotation–extension);
* `SimpleGraph.exists_spanning_isChain` — iterating the extension yields a spanning chain;
* `SimpleGraph.exists_spanning_closed_isChain` — a further rotation closes the spanning
  chain into a cycle;
* `SimpleGraph.exists_walk_of_chain` — a chain is realised as a walk with that support;

which are assembled into `SimpleGraph.IsHamiltonian_of_minDegree`.

## References

* G. A. Dirac, *Some theorems on abstract graphs*, Proc. London Math. Soc. (3) 2 (1952),
  69–81.
-/

namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `getLast?` of a `take (t+1)` prefix is the element at index `t`. -/
private lemma getLast?_take_succ {α : Type*} (C : List α) (t : ℕ) (ht : t < C.length) :
    (C.take (t + 1)).getLast? = some (C[t]'ht) := by
  have hlen : (C.take (t + 1)).length = t + 1 := by rw [List.length_take]; omega
  rw [List.getLast?_eq_getElem?, hlen]
  simp only [Nat.add_sub_cancel]
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem ht]

/-- **Re-rooting a cycle.** A chain that closes up (`getLast → head` is an edge) can be
rotated to end at any of its positions, remaining a chain covering the same vertices. -/
private lemma cycle_reroot {α : Type*} (R : α → α → Prop) (C : List α) (hC : C.IsChain R)
    (hclose : ∀ x ∈ C.getLast?, ∀ y ∈ C.head?, R x y)
    (t : ℕ) (ht : t < C.length) :
    ∃ Q : List α, Q.IsChain R ∧ List.Perm Q C ∧ Q.getLast? = some (C[t]'ht) ∧
      Q.length = C.length := by
  classical
  have hsplit := List.take_append_drop (t + 1) C
  rw [← hsplit] at hC
  rw [List.isChain_append] at hC
  obtain ⟨hct, hcd, _hj⟩ := hC
  refine ⟨C.drop (t + 1) ++ C.take (t + 1), ?_, ?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hcd, hct, ?_⟩
    intro x hx y hy
    rw [List.getLast?_drop] at hx
    rw [List.head?_take] at hy
    have ht1 : t + 1 ≠ 0 := by omega
    simp only [ht1, if_false] at hy
    by_cases hcase : C.length ≤ t + 1
    · simp [hcase] at hx
    · simp only [hcase, if_false] at hx
      exact hclose x hx y hy
  · have hperm : List.Perm (C.drop (t + 1) ++ C.take (t + 1))
        (C.take (t + 1) ++ C.drop (t + 1)) := List.perm_append_comm
    rwa [hsplit] at hperm
  · rw [List.getLast?_append, getLast?_take_succ C t ht]; rfl
  · rw [List.length_append, List.length_take, List.length_drop]; omega

/-- **Rotation index (pigeonhole).** For a duplicate-free chain both of whose endpoints have
all neighbours inside the chain, there is an index `j` with `head ~ L[j+1]` and `L[j] ~ last`.
(Uses `deg(head) + deg(last) ≥ |V| > length − 1`.) -/
private lemma rotationIndex_exists (H : SimpleGraph V) [DecidableRel H.Adj]
    (hδ : ∀ v, Fintype.card V ≤ 2 * H.degree v)
    (L : List V) (hnodup : L.Nodup) (hne : L ≠ [])
    (ha : ∀ w, H.Adj (L.head hne) w → w ∈ L)
    (hb : ∀ w, H.Adj (L.getLast hne) w → w ∈ L)
    (hlen2 : 2 ≤ L.length) :
    ∃ j : Fin (L.length - 1),
      H.Adj (L.head hne) (L.get ⟨j + 1, by omega⟩) ∧
        H.Adj (L.get ⟨j, by omega⟩) (L.getLast hne) := by
  classical
  set n := L.length with hn
  set a := L.head hne with hadef
  set b := L.getLast hne with hbdef
  have hncard : n ≤ Fintype.card V := by
    have h1 := List.toFinset_card_of_nodup hnodup
    have h2 := Finset.card_le_univ L.toFinset
    rw [hn]; omega
  have haget : a = L.get ⟨0, by omega⟩ := by rw [hadef, List.head_eq_getElem]; rfl
  have hbget : b = L.get ⟨n - 1, by omega⟩ := by rw [hbdef, List.getLast_eq_getElem]; rfl
  set φ : Fin (n - 1) → V := fun j => L.get ⟨j + 1, by omega⟩ with hφ
  set ψ : Fin (n - 1) → V := fun j => L.get ⟨j, by omega⟩ with hψ
  have hφinj : Function.Injective φ := by
    intro j1 j2 h; simp only [hφ] at h
    have := (List.nodup_iff_injective_get.mp hnodup) h
    simp only [Fin.mk.injEq] at this; exact Fin.ext (by omega)
  have hψinj : Function.Injective ψ := by
    intro j1 j2 h; simp only [hψ] at h
    have := (List.nodup_iff_injective_get.mp hnodup) h
    simp only [Fin.mk.injEq] at this; exact Fin.ext (by omega)
  set SA : Finset (Fin (n - 1)) := univ.filter (fun j => H.Adj a (φ j)) with hSA
  set SB : Finset (Fin (n - 1)) := univ.filter (fun j => H.Adj (ψ j) b) with hSB
  have hcardSA : SA.card = H.degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hSA,
        ← Finset.card_image_of_injOn hφinj.injOn]
    congr 1; ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hv
      obtain ⟨m, hm⟩ := List.mem_iff_get.mp (ha v hv)
      have hmlt : (m : ℕ) < n := by rw [hn]; exact m.isLt
      have hm0 : (m : ℕ) ≠ 0 := by
        intro h0
        have hva : v = a := by rw [← hm, haget]; congr 1; exact Fin.ext (by omega)
        exact H.ne_of_adj hv hva.symm
      have hφv : φ ⟨(m : ℕ) - 1, by omega⟩ = v := by
        simp only [hφ]; rw [← hm]; congr 1
        exact Fin.ext (show (m : ℕ) - 1 + 1 = (m : ℕ) by omega)
      exact ⟨⟨(m : ℕ) - 1, by omega⟩, by rw [hφv]; exact hv, hφv⟩
  have hcardSB : SB.card = H.degree b := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hSB,
        ← Finset.card_image_of_injOn hψinj.injOn]
    congr 1; ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact H.symm hj
    · intro hv
      obtain ⟨m, hm⟩ := List.mem_iff_get.mp (hb v hv)
      have hmlt : (m : ℕ) < n := by rw [hn]; exact m.isLt
      have hmn : (m : ℕ) ≠ n - 1 := by
        intro h0
        have hvb : v = b := by rw [← hm, hbget]; congr 1; exact Fin.ext (by omega)
        exact H.ne_of_adj hv hvb.symm
      have hψv : ψ ⟨(m : ℕ), by omega⟩ = v := by simp only [hψ]; rw [← hm]
      exact ⟨⟨(m : ℕ), by omega⟩, by rw [hψv]; exact H.symm hv, hψv⟩
  have hdeg : H.degree a + H.degree b ≥ Fintype.card V := by
    have := hδ a; have := hδ b; omega
  have hInter : (SA ∩ SB).Nonempty := by
    rw [← Finset.card_pos]
    have hun := Finset.card_union_add_card_inter SA SB
    have hle : (SA ∪ SB).card ≤ n - 1 := le_trans (Finset.card_le_univ _) (by simp)
    omega
  obtain ⟨j, hj⟩ := hInter
  rw [Finset.mem_inter, hSA, hSB, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hj.1.2, hj.2.2⟩

/-- **External edge.** A non-spanning duplicate-free chain whose head has all neighbours
inside it must nonetheless have an edge from some chain vertex to a vertex outside it. -/
private lemma exists_external_edge (H : SimpleGraph V) [DecidableRel H.Adj]
    (hδ : ∀ v, Fintype.card V ≤ 2 * H.degree v)
    (L : List V) (hnodup : L.Nodup) (hne : L ≠ [])
    (ha : ∀ w, H.Adj (L.head hne) w → w ∈ L)
    (hlt : L.length < Fintype.card V) :
    ∃ w, w ∉ L ∧ ∃ x, x ∈ L ∧ H.Adj x w := by
  classical
  set a := L.head hne with hadef
  have hcardL : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnodup
  have hexists : ∃ w, w ∉ L.toFinset := by
    by_contra hcon
    push_neg at hcon
    have : L.toFinset = univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [this, Finset.card_univ] at hcardL
    omega
  obtain ⟨w, hw⟩ := hexists
  rw [List.mem_toFinset] at hw
  have haL : L.head hne ∈ L := List.head_mem hne
  have hanotin : a ∉ H.neighborFinset a := by
    rw [SimpleGraph.mem_neighborFinset]; exact H.irrefl
  have hdega : H.degree a + 1 ≤ L.length := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcardL]
    have hins : insert a (H.neighborFinset a) ⊆ L.toFinset := by
      apply Finset.insert_subset (by rw [List.mem_toFinset]; exact haL)
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      rw [List.mem_toFinset]; exact ha x hx
    have := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hanotin] at this
    omega
  refine ⟨w, hw, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hsub : H.neighborFinset w ⊆ univ \ insert w L.toFinset := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      List.mem_toFinset, not_or]
    refine ⟨?_, ?_⟩
    · intro hxw; rw [hxw] at hx; exact H.irrefl hx
    · intro hxL; exact hcon x hxL (H.symm hx)
  have hdegw : H.degree w ≤ Fintype.card V - L.length - 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hcard := Finset.card_le_card hsub
    have heq := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (insert w L.toFinset))
    rw [Finset.card_univ,
        Finset.card_insert_of_notMem (by rw [List.mem_toFinset]; exact hw), hcardL] at heq
    omega
  have h1 := hδ w; have h2 := hδ a
  omega

/-- **Rotation–extension core (Dirac).** In a graph with minimum degree `≥ |V|/2`, any
duplicate-free chain that is not yet spanning can be extended by one vertex. -/
private lemma hamiltonian_path_extend (H : SimpleGraph V) [DecidableRel H.Adj]
    (hδ : ∀ v, Fintype.card V ≤ 2 * H.degree v)
    (L : List V) (hchain : L.IsChain H.Adj) (hnodup : L.Nodup)
    (hlt : L.length < Fintype.card V) :
    ∃ L' : List V, L'.IsChain H.Adj ∧ L'.Nodup ∧ L'.length = L.length + 1 := by
  classical
  rcases eq_or_ne L [] with rfl | hne
  · obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by simpa using hlt)
    exact ⟨[v0], by simp, by simp, by simp⟩
  set a := L.head hne with hadef
  set b := L.getLast hne with hbdef
  by_cases hApp : ∃ w, H.Adj b w ∧ w ∉ L
  · obtain ⟨w, hbw, hwL⟩ := hApp
    refine ⟨L ++ [w], ?_, ?_, by simp⟩
    · rw [List.isChain_append]
      refine ⟨hchain, by simp, ?_⟩
      intro y hy z hz
      rw [List.getLast?_eq_some_getLast hne] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy hz
      subst hy; subst hz; exact hbw
    · rw [List.nodup_append]
      refine ⟨hnodup, by simp, ?_⟩
      intro y hy z hz; simp only [List.mem_singleton] at hz
      subst hz; intro heq; exact hwL (heq ▸ hy)
  by_cases hPre : ∃ w, H.Adj a w ∧ w ∉ L
  · obtain ⟨w, haw, hwL⟩ := hPre
    refine ⟨w :: L, ?_, ?_, by simp⟩
    · rw [List.isChain_cons]
      refine ⟨?_, hchain⟩
      intro y hy
      rw [List.head?_eq_some_head hne] at hy
      simp only [Option.mem_some_iff] at hy
      subst hy; exact H.symm haw
    · rw [List.nodup_cons]; exact ⟨hwL, hnodup⟩
  · push_neg at hApp hPre
    obtain ⟨w, hwL, x, hxL, hxw⟩ := exists_external_edge H hδ L hnodup hne hPre hlt
    have hn2 : 2 ≤ L.length := by
      by_contra hlt2
      have hn1 : L.length = 1 := by have := List.length_pos_of_ne_nil hne; omega
      have hd0 : H.degree a = 0 := by
        by_contra hd
        have hpos : 0 < H.degree a := Nat.pos_of_ne_zero hd
        rw [← SimpleGraph.card_neighborFinset_eq_degree] at hpos
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
        rw [SimpleGraph.mem_neighborFinset] at hy
        have hyL := hPre y hy
        have hLeq : L = [a] := by
          rcases L with _ | ⟨c, tl⟩
          · simp at hn1
          · simp only [List.length_cons] at hn1
            have htl : tl = [] := List.length_eq_zero_iff.mp (by omega)
            subst htl; simp [hadef]
        rw [hLeq] at hyL; simp only [List.mem_singleton] at hyL
        subst hyL; exact H.irrefl hy
      have := hδ a; omega
    obtain ⟨j, hja, hjb⟩ := rotationIndex_exists H hδ L hnodup hne hPre hApp hn2
    set jv := (j : ℕ) with hjv
    have hjlt : jv + 1 < L.length := by have := j.isLt; omega
    set Cyc := L.take (jv + 1) ++ (L.drop (jv + 1)).reverse with hCyc
    have hLsplit := List.take_append_drop (jv + 1) L
    have hchain2 := hchain
    rw [← hLsplit, List.isChain_append] at hchain2
    obtain ⟨hct, hcd, _hjunc⟩ := hchain2
    have hflip : (fun x y : V => H.Adj y x) = H.Adj := by
      ext x y; exact H.adj_comm y x
    have hchain_rev : (L.drop (jv + 1)).reverse.IsChain H.Adj := by
      rw [List.isChain_reverse, hflip]; exact hcd
    have hCyc_chain : Cyc.IsChain H.Adj := by
      rw [hCyc, List.isChain_append]
      refine ⟨hct, hchain_rev, ?_⟩
      intro y hy z hz
      rw [getLast?_take_succ L jv (by omega)] at hy
      rw [List.head?_reverse, List.getLast?_drop] at hz
      simp only [Option.mem_some_iff] at hy
      have hnotle : ¬ L.length ≤ jv + 1 := by omega
      rw [if_neg hnotle, List.getLast?_eq_some_getLast hne] at hz
      simp only [Option.mem_some_iff] at hz
      subst hy; subst hz
      have hgg : L.get ⟨jv, by omega⟩ = L[jv] := rfl
      rw [← hgg]; exact hjb
    have hCyc_perm : List.Perm Cyc L := by
      rw [hCyc]
      have h2 := List.Perm.append_left (L.take (jv + 1)) (List.reverse_perm (L.drop (jv + 1)))
      rwa [hLsplit] at h2
    have hCyc_nodup : Cyc.Nodup := hCyc_perm.nodup_iff.mpr hnodup
    have hCyc_len : Cyc.length = L.length := hCyc_perm.length_eq
    have hclose : ∀ y ∈ Cyc.getLast?, ∀ z ∈ Cyc.head?, H.Adj y z := by
      intro y hy z hz
      rw [hCyc, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
          List.getElem?_eq_getElem hjlt] at hy
      simp only [Option.some_or, Option.mem_some_iff] at hy
      rw [hCyc, List.head?_append, List.head?_take] at hz
      have hne1 : jv + 1 ≠ 0 := by omega
      rw [if_neg hne1, List.head?_eq_some_head hne] at hz
      simp only [Option.some_or, Option.mem_some_iff] at hz
      subst hy; subst hz
      have hgg : L.get ⟨jv + 1, by omega⟩ = L[jv + 1] := rfl
      rw [← hgg]; exact H.symm hja
    have hxCyc : x ∈ Cyc := hCyc_perm.mem_iff.mpr hxL
    obtain ⟨t, ht, hCt⟩ := List.mem_iff_getElem.mp hxCyc
    obtain ⟨Q, hQchain, hQperm, hQlast, hQlen⟩ := cycle_reroot H.Adj Cyc hCyc_chain hclose t ht
    have hwQ : w ∉ Q := fun hwQ => hwL (hCyc_perm.mem_iff.mp (hQperm.mem_iff.mp hwQ))
    refine ⟨Q ++ [w], ?_, ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hQchain, by simp, ?_⟩
      intro y hy z hz
      rw [hQlast] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy hz
      subst hy; subst hz
      rw [hCt]; exact hxw
    · rw [List.nodup_append]
      refine ⟨hQperm.nodup_iff.mpr hCyc_nodup, by simp, ?_⟩
      intro y hy z hz; simp only [List.mem_singleton] at hz
      subst hz; intro heq; exact hwQ (heq ▸ hy)
    · rw [List.length_append, hQlen, hCyc_len]; simp

/-- Iterating `hamiltonian_path_extend` yields a spanning chain of length `|V|`. -/
private lemma exists_spanning_isChain (H : SimpleGraph V) [DecidableRel H.Adj]
    (hδ : ∀ v, Fintype.card V ≤ 2 * H.degree v) :
    ∃ L : List V, L.IsChain H.Adj ∧ L.Nodup ∧ L.length = Fintype.card V := by
  classical
  set N := Fintype.card V with hN
  set Pr : ℕ → Prop := fun n => ∃ L : List V, L.IsChain H.Adj ∧ L.Nodup ∧ L.length = n
    with hPr
  have hPr0 : Pr 0 := ⟨[], by simp, by simp, rfl⟩
  have hNle : Nat.findGreatest Pr N ≤ N := Nat.findGreatest_le N
  have hPrN : Pr (Nat.findGreatest Pr N) := Nat.findGreatest_spec (Nat.zero_le N) hPr0
  have hNp : Nat.findGreatest Pr N = N := by
    by_contra hne
    have hlt : Nat.findGreatest Pr N < N := lt_of_le_of_ne hNle hne
    obtain ⟨L, hc, hn, hl⟩ := hPrN
    obtain ⟨L', hc', hn', hl'⟩ := hamiltonian_path_extend H hδ L hc hn (by rw [hl]; exact hlt)
    have hPrN1 : Pr (Nat.findGreatest Pr N + 1) := ⟨L', hc', hn', by rw [hl', hl]⟩
    have := Nat.le_findGreatest (by omega : Nat.findGreatest Pr N + 1 ≤ N) hPrN1
    omega
  obtain ⟨L, a, b, c⟩ := hPrN
  exact ⟨L, a, b, c.trans hNp⟩

/-- **Closing the cycle.** A spanning duplicate-free chain can be rotated so that its two
endpoints are adjacent, giving a spanning chain that closes up into a cycle. -/
private lemma exists_spanning_closed_isChain (H : SimpleGraph V) [DecidableRel H.Adj]
    (hδ : ∀ v, Fintype.card V ≤ 2 * H.degree v) (h3 : 3 ≤ Fintype.card V) :
    ∃ (L : List V) (hne : L ≠ []), L.IsChain H.Adj ∧ L.Nodup ∧
      L.length = Fintype.card V ∧ H.Adj (L.getLast hne) (L.head hne) := by
  classical
  obtain ⟨L, hchain, hnodup, hlen⟩ := exists_spanning_isChain H hδ
  have hne : L ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen; omega
  have hmem : ∀ v, v ∈ L := by
    intro v
    by_contra hv
    have hcard : (insert v L.toFinset).card = L.length + 1 := by
      rw [Finset.card_insert_of_notMem (by rwa [List.mem_toFinset]),
          List.toFinset_card_of_nodup hnodup]
    have hle := Finset.card_le_univ (insert v L.toFinset)
    rw [hcard, hlen] at hle
    omega
  set a := L.head hne with hadef
  set b := L.getLast hne with hbdef
  have ha : ∀ w, H.Adj a w → w ∈ L := fun w _ => hmem w
  have hb : ∀ w, H.Adj b w → w ∈ L := fun w _ => hmem w
  have hn2 : 2 ≤ L.length := by rw [hlen]; omega
  obtain ⟨j, hja, hjb⟩ := rotationIndex_exists H hδ L hnodup hne ha hb hn2
  set jv := (j : ℕ) with hjv
  have hjlt : jv + 1 < L.length := by have := j.isLt; omega
  set Cyc := L.take (jv + 1) ++ (L.drop (jv + 1)).reverse with hCyc
  have hLsplit := List.take_append_drop (jv + 1) L
  have hchain2 := hchain
  rw [← hLsplit, List.isChain_append] at hchain2
  obtain ⟨hct, hcd, _hjunc⟩ := hchain2
  have hflip : (fun x y : V => H.Adj y x) = H.Adj := by
    ext x y; exact H.adj_comm y x
  have hchain_rev : (L.drop (jv + 1)).reverse.IsChain H.Adj := by
    rw [List.isChain_reverse, hflip]; exact hcd
  have hCyc_chain : Cyc.IsChain H.Adj := by
    rw [hCyc, List.isChain_append]
    refine ⟨hct, hchain_rev, ?_⟩
    intro y hy z hz
    rw [getLast?_take_succ L jv (by omega)] at hy
    rw [List.head?_reverse, List.getLast?_drop] at hz
    simp only [Option.mem_some_iff] at hy
    have hnotle : ¬ L.length ≤ jv + 1 := by omega
    rw [if_neg hnotle, List.getLast?_eq_some_getLast hne] at hz
    simp only [Option.mem_some_iff] at hz
    subst hy; subst hz
    have hgg : L.get ⟨jv, by omega⟩ = L[jv] := rfl
    rw [← hgg]; exact hjb
  have hCyc_perm : List.Perm Cyc L := by
    rw [hCyc]
    have h2 := List.Perm.append_left (L.take (jv + 1)) (List.reverse_perm (L.drop (jv + 1)))
    rwa [hLsplit] at h2
  have hCyc_nodup : Cyc.Nodup := hCyc_perm.nodup_iff.mpr hnodup
  have hCyc_len : Cyc.length = L.length := hCyc_perm.length_eq
  have hclose : ∀ y ∈ Cyc.getLast?, ∀ z ∈ Cyc.head?, H.Adj y z := by
    intro y hy z hz
    rw [hCyc, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hjlt] at hy
    simp only [Option.some_or, Option.mem_some_iff] at hy
    rw [hCyc, List.head?_append, List.head?_take] at hz
    have hne1 : jv + 1 ≠ 0 := by omega
    rw [if_neg hne1, List.head?_eq_some_head hne] at hz
    simp only [Option.some_or, Option.mem_some_iff] at hz
    subst hy; subst hz
    have hgg : L.get ⟨jv + 1, by omega⟩ = L[jv + 1] := rfl
    rw [← hgg]; exact H.symm hja
  have hCycne : Cyc ≠ [] := by
    intro h; rw [h, List.length_nil] at hCyc_len; omega
  refine ⟨Cyc, hCycne, hCyc_chain, hCyc_nodup, by rw [hCyc_len, hlen], ?_⟩
  refine hclose (Cyc.getLast hCycne) ?_ (Cyc.head hCycne) ?_
  · simp [List.getLast?_eq_some_getLast hCycne]
  · simp [List.head?_eq_some_head hCycne]

omit [Fintype V] [DecidableEq V] in
/-- A nonempty chain is realised as a walk from its head to its last vertex whose support is
the chain itself. -/
private lemma exists_walk_of_chain (H : SimpleGraph V) (L : List V) (hchain : L.IsChain H.Adj)
    (hne : L ≠ []) :
    ∃ p : H.Walk (L.head hne) (L.getLast hne), p.support = L := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil => exact ⟨Walk.nil, rfl⟩
    | cons b t' =>
      rw [List.isChain_cons] at hchain
      have hab : H.Adj a b := hchain.1 b (by simp)
      obtain ⟨q, hq⟩ := ih hchain.2 (by simp)
      refine ⟨(Walk.cons hab q).copy rfl (List.getLast_cons (by simp)).symm, ?_⟩
      rw [Walk.support_copy, Walk.support_cons, hq]

/-- **Dirac's theorem.** A finite simple graph on at least three vertices in which every
vertex has degree at least half the number of vertices is Hamiltonian: it contains a
Hamiltonian cycle. -/
theorem IsHamiltonian_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 3 ≤ Fintype.card V) (hδ : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian := by
  have hdeg : ∀ v, Fintype.card V ≤ 2 * G.degree v := by
    intro v
    exact le_trans hδ (by have := G.minDegree_le_degree v; omega)
  intro _
  obtain ⟨L, hne, hchain, hnodup, hlen, hclose⟩ := exists_spanning_closed_isChain G hdeg h
  obtain ⟨q, hq⟩ := exists_walk_of_chain G L hchain hne
  have hqlen : q.length = Fintype.card V - 1 := by
    have hs := q.length_support
    rw [hq, hlen] at hs; omega
  refine ⟨L.head hne, Walk.cons hclose.symm q.reverse, ?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, ?_⟩
    · rw [Walk.tail_cons, Walk.isPath_def, Walk.support_copy, Walk.support_reverse, hq]
      exact List.nodup_reverse.mpr hnodup
    · rw [Walk.length_cons, Walk.length_reverse, hqlen]; omega
  · rw [Walk.length_cons, Walk.length_reverse, hqlen]; omega

end SimpleGraph
