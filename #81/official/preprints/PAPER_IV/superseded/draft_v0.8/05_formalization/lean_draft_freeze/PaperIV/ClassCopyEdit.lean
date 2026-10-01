import PaperIV.ChordalCopy
import PaperIV.EditMetric

/-! Exact support of the edge edits caused by a class-copy step. -/

namespace PaperIV.ClassCopyEdit

open Finset
open scoped symmDiff
open PaperIV.EditMetric

variable {V : Type*} [Fintype V] [DecidableEq V]

def copiedVertices (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset V :=
  Finset.univ.filter (fun v => G.neighborFinset v = A)

def star (v : V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => v ∈ e)

def incident (C : Finset V) : Finset (Sym2 V) := C.biUnion star

def changedEdges (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Finset (Sym2 V) := G.edgeFinset ∆ (ClassCopy.graph G A B).edgeFinset

theorem card_star_le (v : V) : (star v).card ≤ Fintype.card V := by
  have hsub : star v ⊆ (Finset.univ.image fun w : V => s(v, w)) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [star, Finset.mem_filter, Finset.mem_univ, true_and,
        Sym2.mem_iff] at he
      rcases he with h | h
      · refine Finset.mem_image.mpr ⟨b, Finset.mem_univ _, ?_⟩
        simp [h]
      · refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
        simp [h]
  calc (star v).card ≤ (Finset.univ.image fun w : V => s(v, w)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

theorem card_incident_le (C : Finset V) :
    (incident C).card ≤ C.card * Fintype.card V := by
  calc (incident C).card ≤ ∑ v ∈ C, (star v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ C, Fintype.card V := Finset.sum_le_sum fun v hv => card_star_le v
    _ = C.card * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul]

/-- Every edge whose status changes under a class copy is incident with a
vertex of the copied open-neighbourhood class. -/
theorem changed_edge_has_copied_endpoint
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (e : Sym2 V)
    (he : e ∈ G.edgeFinset ∆ (ClassCopy.graph G A B).edgeFinset) :
    ∃ v : V, v ∈ e ∧ G.neighborFinset v = A := by
  induction e using Sym2.ind with
  | _ a b =>
    by_cases ha : G.neighborFinset a = A
    · exact ⟨a, by simp, ha⟩
    by_cases hb : G.neighborFinset b = A
    · exact ⟨b, by simp, hb⟩
    have hadj : (ClassCopy.graph G A B).Adj a b ↔ G.Adj a b :=
      classCopy_adj_of_neighborFinset_ne G A B ha hb
    have hmem : s(a, b) ∈ (ClassCopy.graph G A B).edgeFinset ↔
        s(a, b) ∈ G.edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
    rcases Finset.mem_symmDiff.mp he with h | h
    · exact False.elim (h.2 (hmem.mpr h.1))
    · exact False.elim (h.2 (hmem.mp h.1))

theorem changedEdges_subset_incident
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    changedEdges G A B ⊆ incident (copiedVertices G A) := by
  intro e he
  obtain ⟨v, hve, hv⟩ := changed_edge_has_copied_endpoint G A B e he
  refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
  · simp [copiedVertices, hv]
  · simp [star, hve]

theorem card_changedEdges_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (changedEdges G A B).card ≤ (copiedVertices G A).card * Fintype.card V :=
  (Finset.card_le_card (changedEdges_subset_incident G A B)).trans (card_incident_le _)

/-- A copy step involving at most one source vertex has at most `n` changed
edges.  This is the directly usable normalized one-step bound. -/
theorem card_changedEdges_le_card_of_copiedVertices_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcopy : (copiedVertices G A).card ≤ 1) :
    (changedEdges G A B).card ≤ Fintype.card V := by
  calc (changedEdges G A B).card
      ≤ (copiedVertices G A).card * Fintype.card V := card_changedEdges_le G A B
    _ ≤ 1 * Fintype.card V := Nat.mul_le_mul_right _ hcopy
    _ = Fintype.card V := one_mul _

/-- A source clone class of cardinality at most `c` changes at most `c·n`
edges.  This is the literal edit budget needed when the selector supplies a
bounded, rather than unit, source class. -/
theorem card_changedEdges_le_mul_of_copiedVertices_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (c : ℕ)
    (hcopy : (copiedVertices G A).card ≤ c) :
    (changedEdges G A B).card ≤ c * Fintype.card V := by
  calc
    (changedEdges G A B).card
        ≤ (copiedVertices G A).card * Fintype.card V := card_changedEdges_le G A B
    _ ≤ c * Fintype.card V := Nat.mul_le_mul_right _ hcopy

theorem editDist_edgeFinsets_eq_card_changedEdges
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset =
      (changedEdges G A B).card := by
  rfl

/-- The unit-class edit bound at the route's `n²` normalization. -/
theorem normalized_editDist_le_inv_of_copiedVertices_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hn : 1 ≤ Fintype.card V) (hcopy : (copiedVertices G A).card ≤ 1) :
    (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2 ≤ 1 / (Fintype.card V : ℚ) := by
  have hnq : (0 : ℚ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hcard : (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) ≤
      Fintype.card V := by
    rw [editDist_edgeFinsets_eq_card_changedEdges]
    exact_mod_cast card_changedEdges_le_card_of_copiedVertices_le_one G A B hcopy
  calc
    (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2 ≤
        (Fintype.card V : ℚ) / (Fintype.card V : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = 1 / (Fintype.card V : ℚ) := by field_simp

/-- The edit estimate at the route's `n²` normalization for a source clone
class of size at most `c`. -/
theorem normalized_editDist_le_c_div_of_copiedVertices_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (c : ℕ)
    (hn : 1 ≤ Fintype.card V) (hcopy : (copiedVertices G A).card ≤ c) :
    (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2 ≤ (c : ℚ) / (Fintype.card V : ℚ) := by
  have hnq : (0 : ℚ) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hcard : (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) ≤
      (c : ℚ) * Fintype.card V := by
    rw [editDist_edgeFinsets_eq_card_changedEdges]
    exact_mod_cast card_changedEdges_le_mul_of_copiedVertices_le G A B c hcopy
  calc
    (editDist G.edgeFinset (ClassCopy.graph G A B).edgeFinset : ℚ) /
        (Fintype.card V : ℚ) ^ 2 ≤
        ((c : ℚ) * Fintype.card V) / (Fintype.card V : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = (c : ℚ) / (Fintype.card V : ℚ) := by field_simp

end PaperIV.ClassCopyEdit
