import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite physical `K2`/`K3`/`K4` model. -/

namespace PaperIV.Model

open Finset

inductive PieceKind where | K2 | K3 | K4 deriving DecidableEq, Repr

namespace PieceKind

def size : PieceKind → ℕ | K2 => 2 | K3 => 3 | K4 => 4
def gain : PieceKind → ℕ | K2 => 0 | K3 => 2 | K4 => 5

@[simp] theorem size_K2 : PieceKind.K2.size = 2 := rfl
@[simp] theorem size_K3 : PieceKind.K3.size = 3 := rfl
@[simp] theorem size_K4 : PieceKind.K4.size = 4 := rfl
@[simp] theorem gain_K2 : PieceKind.K2.gain = 0 := rfl
@[simp] theorem gain_K3 : PieceKind.K3.gain = 2 := rfl
@[simp] theorem gain_K4 : PieceKind.K4.gain = 5 := rfl

theorem choose_two_size (k : PieceKind) : k.size.choose 2 = k.gain + 1 := by
  cases k <;> rfl

theorem size_pos (k : PieceKind) : 0 < k.size := by cases k <;> norm_num

end PieceKind

variable {V : Type*} [DecidableEq V]

def pieceEdges (s : Finset V) : Finset (Sym2 V) :=
  s.sym2.filter fun e => ¬ e.IsDiag

@[simp] theorem mem_pieceEdges {s : Finset V} {e : Sym2 V} :
    e ∈ pieceEdges s ↔ (∀ a ∈ e, a ∈ s) ∧ ¬ e.IsDiag := by
  simp [pieceEdges, Finset.mem_sym2_iff]

theorem mem_pieceEdges_mk {s : Finset V} {a b : V} :
    s(a, b) ∈ pieceEdges s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp [mem_pieceEdges, Sym2.isDiag_iff_proj_eq]
  tauto

@[simp] theorem pieceEdges_empty : pieceEdges (∅ : Finset V) = ∅ := by simp [pieceEdges]

theorem pieceEdges_mono {s t : Finset V} (h : s ⊆ t) : pieceEdges s ⊆ pieceEdges t := by
  intro e he
  rw [mem_pieceEdges] at he ⊢
  exact ⟨fun a ha => h (he.1 a ha), he.2⟩

theorem filter_isDiag_sym2 (s : Finset V) :
    s.sym2.filter (fun e => e.IsDiag) = s.image fun a => s(a, a) := by
  ext e
  induction e with
  | _ a b =>
    simp only [mem_filter, Finset.mem_sym2_iff, Finset.mem_image, Sym2.isDiag_iff_proj_eq]
    constructor
    · rintro ⟨hmem, rfl⟩
      exact ⟨a, hmem a (by simp), rfl⟩
    · rintro ⟨c, hc, hce⟩
      rw [Sym2.eq_iff] at hce
      rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨by intro x hx; simp only [Sym2.mem_iff] at hx; rcases hx with rfl | rfl <;> exact hc,
          rfl⟩

theorem card_pieceEdges (s : Finset V) : (pieceEdges s).card = s.card.choose 2 := by
  have hsplit :
      (s.sym2.filter fun e => e.IsDiag).card + (s.sym2.filter fun e => ¬ e.IsDiag).card
        = s.sym2.card := Finset.card_filter_add_card_filter_not _
  have hdiag : (s.sym2.filter fun e => e.IsDiag).card = s.card := by
    rw [filter_isDiag_sym2, Finset.card_image_of_injective]
    intro a b hab
    simp only [Sym2.eq_iff] at hab
    tauto
  have htot : s.sym2.card = (s.card + 1).choose 2 := Finset.card_sym2 s
  have hpascal : (s.card + 1).choose 2 = s.card.choose 1 + s.card.choose 2 :=
    Nat.choose_succ_succ s.card 1
  rw [Nat.choose_one_right] at hpascal
  simp only [pieceEdges]
  omega

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def graphEdges : Finset (Sym2 V) := G.edgeFinset

omit [DecidableEq V] in
@[simp] theorem mem_graphEdges {e : Sym2 V} : e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  simp [graphEdges]

omit [DecidableEq V] in
theorem not_isDiag_of_mem_graphEdges {e : Sym2 V} (he : e ∈ graphEdges G) : ¬ e.IsDiag := by
  induction e with
  | _ a b =>
    rw [mem_graphEdges, SimpleGraph.mem_edgeSet] at he
    simpa [Sym2.isDiag_iff_proj_eq] using he.ne

structure IsPiece (s : Finset V) : Prop where
  clique : G.IsClique (s : Set V)
  kind : ∃ k : PieceKind, s.card = k.size

variable {G}

theorem IsPiece.pieceEdges_subset {s : Finset V} (h : IsPiece G s) :
    pieceEdges s ⊆ graphEdges G := by
  intro e he
  induction e with
  | _ a b =>
    rw [mem_pieceEdges_mk] at he
    obtain ⟨ha, hb, hne⟩ := he
    exact (mem_graphEdges G).mpr (h.clique (by simpa using ha) (by simpa using hb) hne)

def gainOf (s : Finset V) : ℕ :=
  if s.card = 3 then 2 else if s.card = 4 then 5 else 0

omit [DecidableEq V] [Fintype V] in
@[simp] theorem gainOf_of_card_two {s : Finset V} (h : s.card = 2) : gainOf s = 0 := by
  simp [gainOf, h]
omit [DecidableEq V] [Fintype V] in
@[simp] theorem gainOf_of_card_three {s : Finset V} (h : s.card = 3) : gainOf s = 2 := by
  simp [gainOf, h]
omit [DecidableEq V] [Fintype V] in
@[simp] theorem gainOf_of_card_four {s : Finset V} (h : s.card = 4) : gainOf s = 5 := by
  simp [gainOf, h]

omit [DecidableEq V] [Fintype V] in
theorem gainOf_kind {s : Finset V} {k : PieceKind} (h : s.card = k.size) :
    gainOf s = k.gain := by cases k <;> simp [PieceKind.size] at h <;> simp [gainOf, h]

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsPiece.card_pieceEdges_eq {s : Finset V} (h : IsPiece G s) :
    (pieceEdges s).card = gainOf s + 1 := by
  obtain ⟨k, hk⟩ := h.kind
  rw [card_pieceEdges, hk, gainOf_kind hk, PieceKind.choose_two_size]

variable (G)

structure IsPacking (P : Finset (Finset V)) : Prop where
  pieces : ∀ s ∈ P, IsPiece G s
  edgeDisjoint : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint (pieceEdges s) (pieceEdges t)

def coveredEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion pieceEdges

structure IsExactPartition (P : Finset (Finset V)) : Prop extends IsPacking G P where
  covers : coveredEdges P = graphEdges G

variable {G}

omit [Fintype V] in
@[simp] theorem mem_coveredEdges {P : Finset (Finset V)} {e : Sym2 V} :
    e ∈ coveredEdges P ↔ ∃ s ∈ P, e ∈ pieceEdges s := by simp [coveredEdges]

theorem IsPacking.coveredEdges_subset {P : Finset (Finset V)} (h : IsPacking G P) :
    coveredEdges P ⊆ graphEdges G := by
  intro e he
  rw [mem_coveredEdges] at he
  obtain ⟨s, hs, hes⟩ := he
  exact (h.pieces s hs).pieceEdges_subset hes

theorem IsExactPartition.existsUnique_piece {P : Finset (Finset V)}
    (h : IsExactPartition G P) {e : Sym2 V} (he : e ∈ graphEdges G) :
    ∃! s, s ∈ P ∧ e ∈ pieceEdges s := by
  have hmem : e ∈ coveredEdges P := by rw [h.covers]; exact he
  rw [mem_coveredEdges] at hmem
  obtain ⟨s, hs, hes⟩ := hmem
  refine ⟨s, ⟨hs, hes⟩, ?_⟩
  rintro t ⟨ht, het⟩
  by_contra hne
  exact absurd hes (Finset.disjoint_left.mp (h.edgeDisjoint t ht s hs hne) het)

def totalGain (P : Finset (Finset V)) : ℕ := ∑ s ∈ P, gainOf s

omit [DecidableEq V] [Fintype V] in
@[simp] theorem totalGain_empty : totalGain (∅ : Finset (Finset V)) = 0 := by simp [totalGain]

theorem IsExactPartition.card_add_totalGain {P : Finset (Finset V)}
    (h : IsExactPartition G P) : P.card + totalGain P = (graphEdges G).card := by
  have hcard : (coveredEdges P).card = ∑ s ∈ P, (pieceEdges s).card :=
    Finset.card_biUnion fun s hs t ht hst => h.edgeDisjoint s hs t ht hst
  have hsum : ∑ s ∈ P, (pieceEdges s).card = ∑ s ∈ P, (gainOf s + 1) :=
    Finset.sum_congr rfl fun s hs => (h.pieces s hs).card_pieceEdges_eq
  rw [← h.covers, hcard, hsum, Finset.sum_add_distrib]
  simp [totalGain, Nat.add_comm]

theorem IsExactPartition.card_eq_edges_sub_totalGain {P : Finset (Finset V)}
    (h : IsExactPartition G P) : totalGain P ≤ (graphEdges G).card ∧
      P.card = (graphEdges G).card - totalGain P := by
  have := h.card_add_totalGain
  omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem isPacking_empty : IsPacking G (∅ : Finset (Finset V)) := ⟨by simp, by simp⟩
omit [Fintype V] in
@[simp] theorem coveredEdges_empty : coveredEdges (∅ : Finset (Finset V)) = ∅ := by simp [coveredEdges]

theorem isExactPartition_empty_iff :
    IsExactPartition G (∅ : Finset (Finset V)) ↔ graphEdges G = ∅ :=
  ⟨fun h => by simpa using h.covers.symm, fun h => ⟨isPacking_empty, by simp [h]⟩⟩

end PaperIV.Model
