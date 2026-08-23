/-
# Gadgets inside a single bottom cell: the connectors of the chain

The chain of BKLO §11 needs, on each boundary between two consecutive cells, two edge-disjoint
even-degree edge sets with `1` edge mod `3`, lying inside both neighbouring cores.  This file
builds them inside a single cell: two vertex-disjoint `4`-cycles.

* `BKLO.exists_adj_avoiding` — the greedy step: in a set `P` whose vertices miss at most `d`
  neighbours inside `P`, one more vertex can be joined to a small clique while avoiding a
  prescribed set;
* `BKLO.exists_two_fourCycles` — eight vertices of `P` carrying two vertex-disjoint `4`-cycles.

Everything here is `sorry`-free.
-/
import BKLO.Section10Defs
import BKLO.TransportV

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### Four-cycles -/

/-- A `4`-cycle has even degrees. -/
theorem evenDegrees_fourCycle {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    EvenDegrees ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) := by
  classical
  intro v
  have hcard2 : ({s(c, d), s(d, a)} : Finset (Sym2 V)).card = 2 :=
    Finset.card_pair (by simp; tauto)
  simp only [edeg, Finset.filter_insert, Finset.filter_singleton, Sym2.mem_iff]
  split_ifs <;>
    simp_all [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton]
  decide +kernel

/-- A `4`-cycle has four edges. -/
theorem card_fourCycle {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)).card = 4 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto), Finset.card_singleton]

/-- A `4`-cycle lies inside the clique on its four vertices. -/
theorem fourCycle_subset_cliqueEdges {a b c d : V} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d)
    (hda : d ≠ a) :
    ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) ⊆
      cliqueEdges ({a, b, c, d} : Finset V) := by
  classical
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    refine mem_cliqueEdgesV.2 ⟨?_, ?_⟩ <;>
    simp_all [Sym2.isDiag_iff_proj_eq, Sym2.mem_iff]

/-! ### The greedy step -/

/-- **One more vertex joined to a clique.**  If every vertex of `P` misses at most `d` vertices of
`P` in `F`, and `P` is larger than `|Bad| + |Y| + |Y| d`, then some vertex of `P` outside
`Bad ∪ Y` is `F`-joined to all of `Y`. -/
theorem exists_adj_avoiding {P : Finset V} {F : Finset (Sym2 V)} {d : ℕ}
    (hdeg : ∀ v ∈ P, P.card ≤ degTo F v P + d) (Bad Y : Finset V) (hYP : Y ⊆ P)
    (h : Bad.card + Y.card + Y.card * d < P.card) :
    ∃ x ∈ P, x ∉ Bad ∧ x ∉ Y ∧ ∀ y ∈ Y, s(y, x) ∈ F := by
  classical
  set Miss : Finset V := Y.biUnion (fun y => P \ nbhdIn F y P) with hMiss
  have hMisscard : Miss.card ≤ Y.card * d := by
    refine le_trans Finset.card_biUnion_le ?_
    have : ∀ y ∈ Y, (P \ nbhdIn F y P).card ≤ d := by
      intro y hy
      have h1 : (P \ nbhdIn F y P).card + (nbhdIn F y P).card = P.card :=
        Finset.card_sdiff_add_card_eq_card (nbhdIn_subset F y P)
      have h2 := hdeg y (hYP hy)
      unfold degTo at h2
      omega
    calc ∑ y ∈ Y, (P \ nbhdIn F y P).card ≤ ∑ _y ∈ Y, d := Finset.sum_le_sum this
      _ = Y.card * d := by rw [Finset.sum_const, smul_eq_mul]
  have hne : (P \ (Bad ∪ Y ∪ Miss)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (P \ (Bad ∪ Y ∪ Miss)).card ≥ P.card - (Bad ∪ Y ∪ Miss).card := by
      have := Finset.le_card_sdiff (Bad ∪ Y ∪ Miss) P
      omega
    have h2 : (Bad ∪ Y ∪ Miss).card ≤ Bad.card + Y.card + Miss.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    omega
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxP, hxnot⟩ := hx
  simp only [Finset.mem_union, not_or] at hxnot
  obtain ⟨⟨hxB, hxY⟩, hxM⟩ := hxnot
  refine ⟨x, hxP, hxB, hxY, fun y hy => ?_⟩
  have : x ∉ P \ nbhdIn F y P := fun hc => hxM (Finset.mem_biUnion.2 ⟨y, hy, hc⟩)
  rw [Finset.mem_sdiff] at this
  push_neg at this
  exact (mem_nbhdIn.1 (this hxP)).2

/-! ### Two vertex-disjoint four-cycles inside a cell -/

set_option maxHeartbeats 2000000 in
/-- **The connectors.**  In a set `P` whose vertices miss at most `d` neighbours inside `P`, and
which is larger than `|Bad| + 8 + 8d`, there are eight vertices outside `Bad` carrying two
edge-disjoint `4`-cycles of `F`. -/
theorem exists_two_fourCycles {P : Finset V} {F : Finset (Sym2 V)} {d : ℕ}
    (hdeg : ∀ v ∈ P, P.card ≤ degTo F v P + d) (Bad : Finset V)
    (hlarge : Bad.card + 8 + 8 * d < P.card) :
    ∃ (T : Finset V) (c₁ c₂ : Finset (Sym2 V)),
      T ⊆ P ∧ Disjoint T Bad ∧ T.card = 8 ∧
      c₁ ⊆ F ∧ c₂ ⊆ F ∧ c₁ ⊆ cliqueEdges T ∧ c₂ ⊆ cliqueEdges T ∧
      Disjoint c₁ c₂ ∧ EvenDegrees c₁ ∧ EvenDegrees c₂ ∧ c₁.card = 4 ∧ c₂.card = 4 := by
  classical
  -- pick eight vertices, each joined to all the previous ones
  obtain ⟨x1, h1P, h1B, -, -⟩ := exists_adj_avoiding hdeg Bad ∅ (by simp) (by simpa using by omega)
  obtain ⟨x2, h2P, h2B, h2Y, h2adj⟩ := exists_adj_avoiding hdeg Bad {x1} (by simpa using h1P) (by
    rw [Finset.card_singleton]; omega)
  have hx12 : x1 ≠ x2 := fun h => h2Y (by simp [h])
  obtain ⟨x3, h3P, h3B, h3Y, h3adj⟩ := exists_adj_avoiding hdeg Bad {x1, x2} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption) (by
    have : ({x1, x2} : Finset V).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have hd : ({x1, x2} : Finset V).card * d ≤ 2 * d := Nat.mul_le_mul_right _ this
    omega)
  have hx13 : x1 ≠ x3 := fun h => h3Y (by simp [h])
  have hx23 : x2 ≠ x3 := fun h => h3Y (by simp [h])
  obtain ⟨x4, h4P, h4B, h4Y, h4adj⟩ := exists_adj_avoiding hdeg Bad {x1, x2, x3} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> assumption) (by
    have : ({x1, x2, x3} : Finset V).card ≤ 3 :=
      le_trans (Finset.card_insert_le _ _) (by
        have := le_trans (Finset.card_insert_le x2 ({x3} : Finset V)) (by simp : ({x3} : Finset V).card + 1 ≤ 2)
        omega)
    have hd : ({x1, x2, x3} : Finset V).card * d ≤ 3 * d := Nat.mul_le_mul_right _ this
    omega)
  have hx14 : x1 ≠ x4 := fun h => h4Y (by simp [h])
  have hx24 : x2 ≠ x4 := fun h => h4Y (by simp [h])
  have hx34 : x3 ≠ x4 := fun h => h4Y (by simp [h])
  obtain ⟨x5, h5P, h5B, h5Y, h5adj⟩ := exists_adj_avoiding hdeg Bad {x1, x2, x3, x4} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by
    have hc : ({x1, x2, x3, x4} : Finset V).card ≤ 4 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      simp
    have hd : ({x1, x2, x3, x4} : Finset V).card * d ≤ 4 * d := Nat.mul_le_mul_right _ hc
    omega)
  have hx15 : x1 ≠ x5 := fun h => h5Y (by simp [h])
  have hx25 : x2 ≠ x5 := fun h => h5Y (by simp [h])
  have hx35 : x3 ≠ x5 := fun h => h5Y (by simp [h])
  have hx45 : x4 ≠ x5 := fun h => h5Y (by simp [h])
  obtain ⟨x6, h6P, h6B, h6Y, h6adj⟩ := exists_adj_avoiding hdeg Bad {x1, x2, x3, x4, x5} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption) (by
    have hc : ({x1, x2, x3, x4, x5} : Finset V).card ≤ 5 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      simp
    have hd : ({x1, x2, x3, x4, x5} : Finset V).card * d ≤ 5 * d := Nat.mul_le_mul_right _ hc
    omega)
  have hx16 : x1 ≠ x6 := fun h => h6Y (by simp [h])
  have hx26 : x2 ≠ x6 := fun h => h6Y (by simp [h])
  have hx36 : x3 ≠ x6 := fun h => h6Y (by simp [h])
  have hx46 : x4 ≠ x6 := fun h => h6Y (by simp [h])
  have hx56 : x5 ≠ x6 := fun h => h6Y (by simp [h])
  obtain ⟨x7, h7P, h7B, h7Y, h7adj⟩ := exists_adj_avoiding hdeg Bad {x1, x2, x3, x4, x5, x6} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) (by
    have hc : ({x1, x2, x3, x4, x5, x6} : Finset V).card ≤ 6 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      simp
    have hd : ({x1, x2, x3, x4, x5, x6} : Finset V).card * d ≤ 6 * d := Nat.mul_le_mul_right _ hc
    omega)
  have hx17 : x1 ≠ x7 := fun h => h7Y (by simp [h])
  have hx27 : x2 ≠ x7 := fun h => h7Y (by simp [h])
  have hx37 : x3 ≠ x7 := fun h => h7Y (by simp [h])
  have hx47 : x4 ≠ x7 := fun h => h7Y (by simp [h])
  have hx57 : x5 ≠ x7 := fun h => h7Y (by simp [h])
  have hx67 : x6 ≠ x7 := fun h => h7Y (by simp [h])
  obtain ⟨x8, h8P, h8B, h8Y, h8adj⟩ :=
    exists_adj_avoiding hdeg Bad {x1, x2, x3, x4, x5, x6, x7} (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) (by
    have hc : ({x1, x2, x3, x4, x5, x6, x7} : Finset V).card ≤ 7 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      refine Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) ?_)
      simp
    have hd : ({x1, x2, x3, x4, x5, x6, x7} : Finset V).card * d ≤ 7 * d :=
      Nat.mul_le_mul_right _ hc
    omega)
  have hx18 : x1 ≠ x8 := fun h => h8Y (by simp [h])
  have hx28 : x2 ≠ x8 := fun h => h8Y (by simp [h])
  have hx38 : x3 ≠ x8 := fun h => h8Y (by simp [h])
  have hx48 : x4 ≠ x8 := fun h => h8Y (by simp [h])
  have hx58 : x5 ≠ x8 := fun h => h8Y (by simp [h])
  have hx68 : x6 ≠ x8 := fun h => h8Y (by simp [h])
  have hx78 : x7 ≠ x8 := fun h => h8Y (by simp [h])
  -- the two cycles
  set T : Finset V := {x1, x2, x3, x4, x5, x6, x7, x8} with hT
  set c₁ : Finset (Sym2 V) := {s(x1, x2), s(x2, x3), s(x3, x4), s(x4, x1)} with hc₁
  set c₂ : Finset (Sym2 V) := {s(x5, x6), s(x6, x7), s(x7, x8), s(x8, x5)} with hc₂
  have hTP : T ⊆ P := by
    intro x hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hTB : Disjoint T Bad := by
    refine Finset.disjoint_left.2 fun x hx hxB => ?_
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1B hxB, h2B hxB, h3B hxB, h4B hxB, h5B hxB, h6B hxB, h7B hxB, h8B hxB]
  have hTcard : T.card = 8 := by
    rw [hT]
    rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx12, hx13, hx14, hx15, hx16, hx17, hx18⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx23, hx24, hx25, hx26, hx27, hx28⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx34, hx35, hx36, hx37, hx38⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx45, hx46, hx47, hx48⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx56, hx57, hx58⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
            exact ⟨hx67, hx68⟩),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_singleton]; exact hx78),
      Finset.card_singleton]
  have hc₁F : c₁ ⊆ F := by
    intro e he
    simp only [hc₁, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact h2adj x1 (by simp)
    · exact h3adj x2 (by simp)
    · exact h4adj x3 (by simp)
    · rw [Sym2.eq_swap]; exact h4adj x1 (by simp)
  have hc₂F : c₂ ⊆ F := by
    intro e he
    simp only [hc₂, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact h6adj x5 (by simp)
    · exact h7adj x6 (by simp)
    · exact h8adj x7 (by simp)
    · rw [Sym2.eq_swap]; exact h8adj x5 (by simp)
  have hsub₁ : c₁ ⊆ cliqueEdges ({x1, x2, x3, x4} : Finset V) :=
    fourCycle_subset_cliqueEdges hx12 hx23 hx34 (Ne.symm hx14)
  have hsub₂ : c₂ ⊆ cliqueEdges ({x5, x6, x7, x8} : Finset V) :=
    fourCycle_subset_cliqueEdges hx56 hx67 hx78 (Ne.symm hx58)
  have hmono : ∀ {A B : Finset V}, A ⊆ B → cliqueEdges A ⊆ cliqueEdges B := by
    intro A B hAB e he
    obtain ⟨hmem, hdiag⟩ := mem_cliqueEdgesV.1 he
    exact mem_cliqueEdgesV.2 ⟨fun x hx => hAB (hmem x hx), hdiag⟩
  have hin₁ : ({x1, x2, x3, x4} : Finset V) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inl h)))]
  have hin₂ : ({x5, x6, x7, x8} : Finset V) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [hT, Finset.mem_insert, Finset.mem_singleton]
    rcases hx with h | h | h | h
    exacts [Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))]
  refine ⟨T, c₁, c₂, hTP, hTB, hTcard, hc₁F, hc₂F,
    hsub₁.trans (hmono hin₁), hsub₂.trans (hmono hin₂), ?_,
    evenDegrees_fourCycle hx12 hx13 hx14 hx23 hx24 hx34,
    evenDegrees_fourCycle hx56 hx57 hx58 hx67 hx68 hx78,
    card_fourCycle hx12 hx13 hx14 hx23 hx24 hx34,
    card_fourCycle hx56 hx57 hx58 hx67 hx68 hx78⟩
  -- the two cycles are edge-disjoint, since their vertex sets are disjoint
  refine Finset.disjoint_left.2 fun e he₁ he₂ => ?_
  obtain ⟨hm₁, -⟩ := mem_cliqueEdgesV.1 (hsub₁ he₁)
  obtain ⟨hm₂, -⟩ := mem_cliqueEdgesV.1 (hsub₂ he₂)
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := ⟨e.out.1, by simp [Sym2.out_fst_mem]⟩
  have hA := hm₁ x hx
  have hB := hm₂ x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
  rcases hA with rfl | rfl | rfl | rfl <;> rcases hB with h | h | h | h <;>
    exact absurd h (by assumption)

end BKLO
