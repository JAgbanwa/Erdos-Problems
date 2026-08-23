/-
Copyright (c) 2026 Paper III contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import PaperIII.DiracHamilton

/-!
# Dirac's theorem for Hamiltonicity

This file records, in idiomatic `SimpleGraph.IsHamiltonian` vocabulary, Dirac's theorem: a
finite simple graph on at least three vertices whose minimum degree is at least half the
number of vertices is Hamiltonian.

## Main results

* `SimpleGraph.IsHamiltonian_of_minDegree`: if `3 ≤ |V|` and `|V| ≤ 2 · δ(G)`, then `G` has
  a Hamiltonian cycle, i.e. `G.IsHamiltonian`.

## Implementation notes

The proof bridges to `PaperIII.hamiltonian_ordering_of_minDegree`, which supplies the
rotation–extension core: transported to `Fin (Fintype.card V)` via `Fintype.equivFin`, the
graph acquires a bijective vertex ordering along which consecutive vertices are adjacent (a
Hamiltonian *path*).  A short pigeonhole argument on the degrees of the two endpoints closes
the path into a cyclic ordering, which is then turned into an explicit `SimpleGraph.Walk`
whose `IsHamiltonianCycle` structure witnesses `G.IsHamiltonian`.
-/

open Finset Function

namespace PaperIII.DiracBridge

variable {V : Type*}

/-- **Walk from an adjacency sequence.** Given a sequence `w : ℕ → V` with `G.Adj (w i) (w (i+1))`
for all `i + 1 < n`, every prefix of length `m + 1 ≤ n` is realised by a walk from `w 0` to
`w m` whose support is `w 0, …, w m` and whose edges are the consecutive pairs. -/
lemma exists_walk_of_adj_seq (G : SimpleGraph V) (w : ℕ → V) (n : ℕ)
    (hadj : ∀ i, i + 1 < n → G.Adj (w i) (w (i + 1))) :
    ∀ m, m + 1 ≤ n → ∃ P : G.Walk (w 0) (w m),
      P.support = (List.range (m + 1)).map w ∧
      P.edges = (List.range m).map (fun i => s(w i, w (i + 1))) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hsupp, hedg⟩ := ih (by omega)
    have hadjk : G.Adj (w k) (w (k + 1)) := hadj k (by omega)
    refine ⟨P.concat hadjk, ?_, ?_⟩
    · rw [SimpleGraph.Walk.support_concat, hsupp]
      conv_rhs => rw [List.range_succ]
      simp
    · rw [SimpleGraph.Walk.edges_concat, hedg]
      conv_rhs => rw [List.range_succ]
      simp

/-- **Cyclic ordering ⟹ Hamiltonian.** A cyclic vertex ordering `w : ℕ → V` — injective on
`{0, …, n-1}` where `n = |V|`, with `G.Adj (w i) (w (i+1))` along the path and a closing edge
`G.Adj (w (n-1)) (w 0)` — yields a Hamiltonian cycle, hence `G.IsHamiltonian`. -/
lemma isHamiltonian_of_cyclic_ordering (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card V = n) (w : ℕ → V)
    (hinj : ∀ i j, i < n → j < n → w i = w j → i = j)
    (hadj : ∀ i, i + 1 < n → G.Adj (w i) (w (i + 1)))
    (hwrap : G.Adj (w (n - 1)) (w 0)) :
    G.IsHamiltonian := by
  obtain ⟨P, hsupp, hedg⟩ := exists_walk_of_adj_seq G w n hadj (n - 1) (by omega)
  refine fun _ => ⟨w (n - 1), SimpleGraph.Walk.cons hwrap P, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def, hsupp]
      apply List.Nodup.map_on _ List.nodup_range
      intro x hx y hy hxy
      rw [List.mem_range] at hx hy
      exact hinj x y (by omega) (by omega) hxy
    · rw [hedg]
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨i, hi, hie⟩ := hmem
      rw [List.mem_range] at hi
      rw [Sym2.eq_iff] at hie
      rcases hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hinj i (n - 1) (by omega) (by omega) h1; omega
      · have e1 := hinj i 0 (by omega) (by omega) h1
        have e2 := hinj (i + 1) (n - 1) (by omega) (by omega) h2
        omega
  · rw [SimpleGraph.Walk.length_cons]
    have hlen : P.length = n - 1 := by
      have hls := P.length_support
      rw [hsupp] at hls; simp at hls; omega
    rw [hlen, hcard]; omega

/-- **Closing edge (pigeonhole).** For a vertex ordering `w` covering all of `V` (with
`n = |V|`) whose vertices each have degree `≥ n/2`, there is an index `k` with `k + 1 < n`,
`G.Adj (w 0) (w (k+1))` and `G.Adj (w k) (w (n-1))`. Rerouting through `k` closes the path
into a Hamiltonian cycle. -/
lemma exists_closing_index (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card V = n) (w : ℕ → V)
    (hinj : ∀ i j, i < n → j < n → w i = w j → i = j)
    (hsurj : ∀ v, ∃ i, i < n ∧ w i = v)
    (hdeg : ∀ v, n ≤ 2 * G.degree v) :
    ∃ k, k + 1 < n ∧ G.Adj (w 0) (w (k + 1)) ∧ G.Adj (w k) (w (n - 1)) := by
  classical
  set N := n - 1 with hN
  set A : Finset ℕ := (Finset.range N).filter (fun k => G.Adj (w 0) (w (k + 1))) with hA
  set B : Finset ℕ := (Finset.range N).filter (fun k => G.Adj (w k) (w (n - 1))) with hB
  have hinjA : Set.InjOn (fun k => w (k + 1)) ↑A := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hA, Finset.mem_filter, Finset.mem_range] at ha hb
    have := hinj (a + 1) (b + 1) (by omega) (by omega) hab; omega
  have hinjB : Set.InjOn (fun k => w k) ↑B := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hB, Finset.mem_filter, Finset.mem_range] at ha hb
    exact hinj a b (by omega) (by omega) hab
  have hcardA : G.degree (w 0) = A.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hset : G.neighborFinset (w 0) = A.image (fun k => w (k + 1)) := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, hA, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro hv
        obtain ⟨j, hj, rfl⟩ := hsurj v
        have hj0 : j ≠ 0 := by rintro rfl; exact G.irrefl hv
        exact ⟨j - 1, ⟨by omega, by rw [Nat.sub_add_cancel (by omega)]; exact hv⟩,
          by rw [Nat.sub_add_cancel (by omega)]⟩
      · rintro ⟨k, ⟨_, hadjk⟩, rfl⟩; exact hadjk
    rw [hset, Finset.card_image_of_injOn hinjA]
  have hcardB : G.degree (w (n - 1)) = B.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hset : G.neighborFinset (w (n - 1)) = B.image (fun k => w k) := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, hB, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro hv
        obtain ⟨j, hj, rfl⟩ := hsurj v
        have hjn : j ≠ n - 1 := by rintro rfl; exact G.irrefl hv
        exact ⟨j, ⟨by omega, hv.symm⟩, rfl⟩
      · rintro ⟨k, ⟨_, hadjk⟩, rfl⟩; exact hadjk.symm
    rw [hset, Finset.card_image_of_injOn hinjB]
  have hdeg0 := hdeg (w 0)
  have hdegL := hdeg (w (n - 1))
  have hAsub : A ⊆ Finset.range N := Finset.filter_subset _ _
  have hBsub : B ⊆ Finset.range N := Finset.filter_subset _ _
  have hunion : (A ∪ B).card ≤ N := by
    calc (A ∪ B).card ≤ (Finset.range N).card :=
          Finset.card_le_card (Finset.union_subset hAsub hBsub)
      _ = N := Finset.card_range N
  have hui := Finset.card_union_add_card_inter A B
  have hpos : 0 < (A ∩ B).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter, hA, hB, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
  exact ⟨k, by omega, hk.1.2, hk.2.2⟩

/-- **Path + closing edge ⟹ Hamiltonian.** From a Hamiltonian-path ordering `w` and a closing
index `k`, reroute to the cyclic ordering `w 0, …, w k, w (n-1), w (n-2), …, w (k+1)` and apply
`isHamiltonian_of_cyclic_ordering`. -/
lemma isHamiltonian_of_path_and_closing (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (n : ℕ) (hn : 3 ≤ n) (hcard : Fintype.card V = n) (w : ℕ → V)
    (hinj : ∀ i j, i < n → j < n → w i = w j → i = j)
    (hadj : ∀ i, i + 1 < n → G.Adj (w i) (w (i + 1)))
    (k : ℕ) (hk : k + 1 < n)
    (hk1 : G.Adj (w 0) (w (k + 1))) (hk2 : G.Adj (w k) (w (n - 1))) :
    G.IsHamiltonian := by
  set w' : ℕ → V := fun i => if i ≤ k then w i else w (n + k - i) with hw'
  apply isHamiltonian_of_cyclic_ordering G n hn hcard w'
  · intro i j hi hj hij
    simp only [hw'] at hij
    split_ifs at hij with hik hjk hjk
    · exact hinj i j hi hj hij
    · have := hinj i (n + k - j) (by omega) (by omega) hij; omega
    · have := hinj (n + k - i) j (by omega) (by omega) hij; omega
    · have := hinj (n + k - i) (n + k - j) (by omega) (by omega) hij; omega
  · intro i hi
    simp only [hw']
    split_ifs with hik hik1 hik1
    · exact hadj i (by omega)
    · have hik2 : i = k := by omega
      have he : n + k - (i + 1) = n - 1 := by omega
      rw [he, hik2]; exact hk2
    · omega
    · have h1 : n + k - (i + 1) + 1 = n + k - i := by omega
      have := hadj (n + k - (i + 1)) (by omega)
      rw [h1] at this; exact this.symm
  · simp only [hw']
    rw [if_neg (by omega), if_pos (by omega)]
    have he : n + k - (n - 1) = k + 1 := by omega
    rw [he]; exact hk1.symm

end PaperIII.DiracBridge

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Dirac's theorem.** A finite simple graph on at least three vertices whose minimum degree
is at least half the number of vertices is Hamiltonian. -/
theorem IsHamiltonian_of_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 3 ≤ Fintype.card V) (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    G.IsHamiltonian := by
  classical
  set n := Fintype.card V with hn
  set e := Fintype.equivFin V with he
  set H : SimpleGraph (Fin n) := G.comap e.symm with hH
  have iso : G ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        rw [hH, SimpleGraph.comap_adj, Equiv.symm_apply_apply, Equiv.symm_apply_apply] }
  have hmd : G.minDegree = H.minDegree := iso.minDegree_eq
  have hdegH : ∀ v : Fin n, n ≤ 2 * H.degree v := by
    intro v
    have h1 : H.minDegree ≤ H.degree v := H.minDegree_le_degree v
    have h2 := hδ
    rw [hmd] at h2
    omega
  obtain ⟨f, hfbij, hford⟩ :=
    PaperIII.hamiltonian_ordering_of_minDegree H (show 3 ≤ n from h) hdegH
  have hn0 : 0 < n := by omega
  set w : ℕ → V := fun i => if hi : i < n then e.symm (f ⟨i, hi⟩) else e.symm (f ⟨0, hn0⟩)
    with hw
  have hadjw : ∀ i, i + 1 < n → G.Adj (w i) (w (i + 1)) := by
    intro i hi
    have hi' : i < n := by omega
    have hHadj := hford i hi
    rw [hH, SimpleGraph.comap_adj] at hHadj
    simpa only [hw, dif_pos hi', dif_pos hi] using hHadj
  have hinjw : ∀ i j, i < n → j < n → w i = w j → i = j := by
    intro i j hi hj hij
    simp only [hw, dif_pos hi, dif_pos hj] at hij
    have hfi := hfbij.1 (e.symm.injective hij)
    simpa [Fin.ext_iff] using hfi
  have hsurjw : ∀ v, ∃ i, i < n ∧ w i = v := by
    intro v
    obtain ⟨a, ha⟩ := hfbij.2 (e v)
    refine ⟨a.1, a.2, ?_⟩
    simp only [hw, dif_pos a.2]
    have hae : (⟨a.1, a.2⟩ : Fin n) = a := rfl
    rw [hae, ha, Equiv.symm_apply_apply]
  have hdegG : ∀ v, n ≤ 2 * G.degree v := by
    intro v
    have h1 : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
    omega
  have hcard : Fintype.card V = n := hn.symm
  obtain ⟨k, hk, hk1, hk2⟩ :=
    PaperIII.DiracBridge.exists_closing_index G n h hcard w hinjw hsurjw hdegG
  exact PaperIII.DiracBridge.isHamiltonian_of_path_and_closing G n h hcard w hinjw hadjw k hk hk1 hk2

end SimpleGraph
