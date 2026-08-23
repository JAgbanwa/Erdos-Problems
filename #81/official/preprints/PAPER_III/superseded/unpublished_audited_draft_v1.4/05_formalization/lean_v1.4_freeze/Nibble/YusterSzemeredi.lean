/-
# Yuster Y1 — extracting a uniform pair from a regular partition

Standalone, Mathlib-only. The first step of Y1: from a Szemerédi-regular partition `P` of `G` (few
non-uniform pairs of parts, `P.IsUniform G ε`), extract an actual `ε`-uniform pair of distinct parts.
Since the number of non-uniform ordered pairs is `≤ (#parts·(#parts-1))·ε < #parts·(#parts-1)` (for
`ε < 1`), and there are exactly `#parts·(#parts-1)` ordered pairs of distinct parts, a uniform pair
must exist.

`SimpleGraph.IsUniform G ε s t` is exactly the pair-regularity hypothesis that `triangle_counting`
and the Y3 lower bound (`triangleHypergraph_degree_lower_of_uniform_pair`) consume — this is the atom
from which the per-vertex regular pairs of Y3 are assembled.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

open Finset SimpleGraph

namespace Nibble.Yuster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `c·(c-1) = c·c - c` in `ℕ`. -/
private theorem nat_mul_pred (c : ℕ) : c * (c - 1) = c * c - c := by
  cases c with
  | zero => rfl
  | succ n => rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]

/-- **Y1 — a regular partition contains a uniform pair.** From `P.IsUniform G ε` (few non-uniform
pairs) with at least two parts and `0 < ε < 1`, there is an `ε`-uniform pair of distinct parts. -/
theorem exists_uniform_pair {ε : ℝ} {P : Finpartition (univ : Finset V)}
    (hP : P.IsUniform G ε) (hpc : 2 ≤ P.parts.card) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ s ∈ P.parts, ∃ t ∈ P.parts, s ≠ t ∧ G.IsUniform ε s t := by
  classical
  have hsub : P.nonUniforms G ε ⊆ P.parts.offDiag := Finset.filter_subset _ _
  have hoff : P.parts.offDiag.card = P.parts.card * (P.parts.card - 1) := by
    rw [Finset.offDiag_card, ← nat_mul_pred]
  have hoffpos : 0 < P.parts.offDiag.card := by
    rw [hoff]; exact Nat.mul_pos (by omega) (by omega)
  have hlt : (P.nonUniforms G ε).card < P.parts.offDiag.card := by
    have h1 : ((P.nonUniforms G ε).card : ℝ)
        ≤ ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) * ε := hP
    have h2 : ((P.nonUniforms G ε).card : ℝ) < (P.parts.offDiag.card : ℝ) := by
      rw [hoff]
      calc ((P.nonUniforms G ε).card : ℝ)
          ≤ ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) * ε := h1
        _ < ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) * 1 := by
            apply mul_lt_mul_of_pos_left hε1
            rw [← hoff]; exact_mod_cast hoffpos
        _ = ((P.parts.card * (P.parts.card - 1) : ℕ) : ℝ) := mul_one _
    exact_mod_cast h2
  have hne : (P.parts.offDiag \ P.nonUniforms G ε).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hcon
    have := Finset.card_le_card hcon
    omega
  obtain ⟨⟨s, t⟩, hst⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_offDiag] at hst
  obtain ⟨⟨hs, ht, hst_ne⟩, hnu⟩ := hst
  refine ⟨s, hs, t, ht, hst_ne, ?_⟩
  by_contra hcon
  apply hnu
  simp only [Finpartition.nonUniforms, Finset.mem_filter, Finset.mem_offDiag]
  exact ⟨⟨hs, ht, hst_ne⟩, hcon⟩

/-- **Y1 (from Szemerédi) — a graph on `≥ 2` vertices has an `ε`-uniform pair of parts.** Applies the
Szemerédi regularity lemma (`szemeredi_regularity`, with `l = 2` parts requested) and extracts a
uniform pair via `exists_uniform_pair`. The entry point that turns Mathlib's regularity lemma into the
pair-regularity atom Y3 consumes. -/
theorem exists_szemeredi_uniform_pair {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hV : 2 ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V), 2 ≤ P.parts.card ∧
      ∃ s ∈ P.parts, ∃ t ∈ P.parts, s ≠ t ∧ G.IsUniform ε s t := by
  obtain ⟨P, _hEq, hl, _hbound, hU⟩ := szemeredi_regularity G hε0 hV
  obtain ⟨s, hs, t, ht, hst, hunif⟩ := exists_uniform_pair G hU hl hε0 hε1
  exact ⟨P, hl, s, hs, t, ht, hst, hunif⟩

end Nibble.Yuster
