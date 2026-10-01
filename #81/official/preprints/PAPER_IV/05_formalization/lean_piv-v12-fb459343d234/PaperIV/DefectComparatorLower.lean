import PaperIV.DefectComparatorGraph
import PaperIV.SplitCompleteSharpLower

/-!
# The unrestricted lower bound for the defective comparator

The weight argument of the complete-split value (`-1` on each core edge, `+1` on
each link) carries over verbatim to `defSplitGraph Core Def Hosts`: a clique
meets at most one host, and if it meets a host together with at least two other
vertices then those other vertices are all *core* vertices, because a defective
vertex has no neighbour outside the hosts.  Hence every piece carries at most
one more link than it carries core edges, and summing over an arbitrary clique
partition — with **no** bound on the order of the pieces — gives

`(r+s)*h - C(r,2) ≤ #pieces`.
-/

namespace PaperIV.DefectComparatorLower

open Finset
open PaperIV.Model PaperIV.FarRounding PaperIV.SplitUniformIncidence
open PaperIV.SplitEdgeCount PaperIV.DefectComparatorGraph

variable {V : Type*} [DecidableEq V]

/-- The core edges carried by a piece. -/
def innerPartD (Core K : Finset V) : Finset (Sym2 V) :=
  (pairs K).filter fun e => e ∈ pieceEdges Core

/-- The links carried by a piece. -/
def crossPartD (Core Def Hosts K : Finset V) : Finset (Sym2 V) :=
  (pairs K).filter fun e => e ∈ crossEdges (Core ∪ Def) Hosts

theorem card_le_one_add_choose_two (c : ℕ) : c ≤ 1 + c.choose 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      omega

/-- A clique of the comparator contains at most one host. -/
theorem card_inter_hosts_le_one {Core Def Hosts K : Finset V}
    (hd : Disjoint (Core ∪ Def) Hosts)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → (defSplitGraph Core Def Hosts).Adj a b) :
    (K ∩ Hosts).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  rw [Finset.mem_inter] at ha hb
  exact not_adj_of_mem_hosts hd ha.2 hb.2 (hK a ha.1 b hb.1 hne)

/-- **The local ledger.**  A clique of the comparator carries at most one more
link than it carries core edges. -/
theorem card_crossPartD_le_one_add_innerPartD {Core Def Hosts K : Finset V}
    (hCD : Disjoint Core Def) (hDH : Disjoint Def Hosts) (hd : Disjoint (Core ∪ Def) Hosts)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → (defSplitGraph Core Def Hosts).Adj a b) :
    (crossPartD Core Def Hosts K).card ≤ 1 + (innerPartD Core K).card := by
  by_cases hhost : K ∩ Hosts = ∅
  · have : crossPartD Core Def Hosts K = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro e he
      rw [crossPartD, Finset.mem_filter, mem_crossEdges] at he
      obtain ⟨hpairs, x, -, z, hz, rfl⟩ := he
      have hzK : z ∈ K := (mem_pairs.mp hpairs).1 z (by simp)
      have : z ∈ K ∩ Hosts := Finset.mem_inter.mpr ⟨hzK, hz⟩
      rw [hhost] at this
      exact absurd this (Finset.notMem_empty z)
    rw [this]
    simp
  · obtain ⟨z, hz⟩ : ∃ z, z ∈ K ∩ Hosts := Finset.nonempty_iff_ne_empty.mpr hhost
    have hone : K ∩ Hosts = {z} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩
      intro x hx
      have hle := card_inter_hosts_le_one hd hK
      rw [Finset.card_le_one] at hle
      exact hle x hx z hz
    obtain ⟨hzK, hzH⟩ := Finset.mem_inter.mp hz
    set A : Finset V := K ∩ (Core ∪ Def) with hA
    have hAK : A ⊆ K := Finset.inter_subset_left
    have hAmem : ∀ x ∈ A, x ∈ Core ∪ Def := fun x hx => (Finset.mem_inter.mp hx).2
    have hxz : ∀ x ∈ A, x ≠ z := by
      intro x hx hEq
      exact (Finset.disjoint_left.mp hd (hAmem x hx)) (hEq ▸ hzH)
    -- the links of `K` are exactly the spokes at `z`
    have hcross : crossPartD Core Def Hosts K = A.image fun x => s(x, z) := by
      ext e
      simp only [crossPartD, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hpairs, hc⟩
        rw [mem_crossEdges] at hc
        obtain ⟨x, hx, w, hw, rfl⟩ := hc
        have hxK : x ∈ K := (mem_pairs.mp hpairs).1 x (by simp)
        have hwK : w ∈ K := (mem_pairs.mp hpairs).1 w (by simp)
        have hwz : w = z := by
          have : w ∈ K ∩ Hosts := Finset.mem_inter.mpr ⟨hwK, hw⟩
          rw [hone, Finset.mem_singleton] at this
          exact this
        exact ⟨x, Finset.mem_inter.mpr ⟨hxK, hx⟩, by rw [hwz]⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨?_, ?_⟩
        · exact mk_mem_pairs.mpr ⟨hAK hx, hzK, hxz x hx⟩
        · exact mem_crossEdges.mpr ⟨x, hAmem x hx, z, hzH, rfl⟩
    have hinj : Set.InjOn (fun x => s(x, z)) (A : Set V) := by
      intro x hx y hy hxy
      simp only [Sym2.eq_iff] at hxy
      rcases hxy with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd h1 (hxz x hx)
    have hcardcross : (crossPartD Core Def Hosts K).card = A.card := by
      rw [hcross, Finset.card_image_of_injOn hinj]
    rcases Nat.lt_or_ge A.card 2 with hsmall | hbig
    · omega
    · -- at least two non-host vertices: they are all core vertices
      have hAcore : A ⊆ Core := by
        intro x hx
        rcases Finset.mem_union.mp (hAmem x hx) with hxc | hxd
        · exact hxc
        · exfalso
          obtain ⟨y, hy, hyx⟩ :=
            (Finset.one_lt_card_iff_nontrivial.mp (by omega : 1 < A.card)).exists_ne x
          have hyA : y ∈ A := Finset.mem_coe.mp hy
          have hadj : (defSplitGraph Core Def Hosts).Adj x y :=
            hK x (hAK hx) y (hAK hyA) (Ne.symm hyx)
          have hyH : y ∈ Hosts := mem_hosts_of_adj_def hCD hDH hxd hadj
          exact (Finset.disjoint_left.mp hd (hAmem y hyA)) hyH
      have hsub : pieceEdges A ⊆ innerPartD Core K := by
        intro e he
        rw [innerPartD, Finset.mem_filter]
        refine ⟨?_, pieceEdges_mono hAcore he⟩
        have := pieceEdges_mono hAK he
        simpa [pairs, pieceEdges] using this
      have hcardinner : A.card.choose 2 ≤ (innerPartD Core K).card := by
        rw [← card_pieceEdges A]
        exact Finset.card_le_card hsub
      have := card_le_one_add_choose_two A.card
      omega

/-- **The comparator lower bound.**  Every clique partition of the comparator,
with no restriction on the order of its pieces, has at least
`(r+s)*h - C(r,2)` pieces. -/
theorem cliquePartition_size_ge_defect_baseline [Fintype V] {Core Def Hosts : Finset V}
    (hCD : Disjoint Core Def) (hDH : Disjoint Def Hosts) (hd : Disjoint (Core ∪ Def) Hosts)
    (Q : CliquePartition (defSplitGraph Core Def Hosts)) :
    (Core.card + Def.card) * Hosts.card - Core.card.choose 2 ≤ Q.size := by
  have hlocal : ∀ K ∈ Q.pieces,
      (crossPartD Core Def Hosts K).card ≤ 1 + (innerPartD Core K).card := by
    intro K hK
    exact card_crossPartD_le_one_add_innerPartD hCD hDH hd (Q.isClique K hK)
  have hsum : ∑ K ∈ Q.pieces, (crossPartD Core Def Hosts K).card ≤
      Q.size + ∑ K ∈ Q.pieces, (innerPartD Core K).card := by
    calc
      ∑ K ∈ Q.pieces, (crossPartD Core Def Hosts K).card
          ≤ ∑ K ∈ Q.pieces, (1 + (innerPartD Core K).card) :=
            Finset.sum_le_sum fun K hK => hlocal K hK
      _ = Q.size + ∑ K ∈ Q.pieces, (innerPartD Core K).card := by
        simp [CliquePartition.size, Finset.sum_add_distrib]
  have hcross : ∑ K ∈ Q.pieces, (crossPartD Core Def Hosts K).card =
      (crossEdges (Core ∪ Def) Hosts).card := by
    have hf : (graphEdges (defSplitGraph Core Def Hosts)).filter
        (fun e => e ∈ crossEdges (Core ∪ Def) Hosts) = crossEdges (Core ∪ Def) Hosts := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨crossEdges_subset_graphEdges_def hd h, h⟩⟩
    have h := PaperIV.SplitCompleteSharpLower.sum_card_filter_pairs Q
      (fun e => e ∈ crossEdges (Core ∪ Def) Hosts)
    change ∑ K ∈ Q.pieces, (crossPartD Core Def Hosts K).card =
      ((graphEdges (defSplitGraph Core Def Hosts)).filter
        (fun e => e ∈ crossEdges (Core ∪ Def) Hosts)).card at h
    rw [hf] at h
    exact h
  have hinner : ∑ K ∈ Q.pieces, (innerPartD Core K).card = (pieceEdges Core).card := by
    have hf : (graphEdges (defSplitGraph Core Def Hosts)).filter
        (fun e => e ∈ pieceEdges Core) = pieceEdges Core := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨innerEdges_subset_graphEdges_def hd h, h⟩⟩
    have h := PaperIV.SplitCompleteSharpLower.sum_card_filter_pairs Q
      (fun e => e ∈ pieceEdges Core)
    change ∑ K ∈ Q.pieces, (innerPartD Core K).card =
      ((graphEdges (defSplitGraph Core Def Hosts)).filter
        (fun e => e ∈ pieceEdges Core)).card at h
    rw [hf] at h
    exact h
  rw [hcross, hinner, card_crossEdges hd, card_pieceEdges,
    Finset.card_union_of_disjoint hCD] at hsum
  omega

end PaperIV.DefectComparatorLower
