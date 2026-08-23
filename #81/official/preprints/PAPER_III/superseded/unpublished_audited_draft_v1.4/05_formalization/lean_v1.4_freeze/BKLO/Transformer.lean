/-
# BKLO Section 8 — transformers and absorbers (for F = K₃).

We work in an **edge-set model**: a "graph" is a `Finset (Sym2 V)` of edges.  `TriDecomp E` says the
edge set `E` splits exactly into edge-disjoint triangles.  This makes the transformer calculus of
BKLO §8 elementary:

* `TriDecomp.union` — the workhorse: an edge-disjoint union of two triangle-decomposable sets is
  triangle-decomposable (concatenate the two triangle families).
* `IsTransformer T H H'` — `T ∪ H` and `T ∪ H'` are both triangle-decomposable and `T` is disjoint
  from `H ∪ H'` (BKLO: `T[V(H∪H')]` empty; here: `T` shares no edge with `H`, `H'`).
* `Sim H H'` — `∃ T, IsTransformer T H H'` (the relation `H ∼_F H'`).
* `Sim`, `IsAbsorber` — the relation `H ∼_F H'` and absorbers.  Transitivity (Proposition 8.2) and
  the existence lemmas are the next targets.

The existence lemmas 8.4 / 8.7 / 8.8 (every `K₃`-divisible edge set has an absorber) are stated as
the roadmap holes to be filled next; they are the elementary "expansion/identification" content of
§8.1 and carry no analysis.
-/
import BKLO.Basic

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The edges of a triangle family. -/
def famEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion cliqueEdges

/-- `E` is **exactly triangle-decomposable**: an edge-disjoint family of 3-cliques whose edges are
exactly `E`.  (Cliques here are abstract 3-sets; triangle = its three `cliqueEdges`.) -/
def TriDecomp (E : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, t.card = 3) ∧
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
    famEdges P = E

/-- The empty edge set is triangle-decomposable (empty family). -/
theorem triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V)) := by
  refine ⟨∅, by simp, by simp, by simp [famEdges]⟩

/-- **Workhorse.**  An edge-disjoint union of two triangle-decomposable edge sets is
triangle-decomposable.  We union the two triangle families; edge-disjointness across the families
follows from the edge sets being disjoint. -/
theorem TriDecomp.union {E₁ E₂ : Finset (Sym2 V)} (hd : Disjoint E₁ E₂)
    (h₁ : TriDecomp E₁) (h₂ : TriDecomp E₂) : TriDecomp (E₁ ∪ E₂) := by
  classical
  obtain ⟨P₁, hc₁, hdj₁, he₁⟩ := h₁
  obtain ⟨P₂, hc₂, hdj₂, he₂⟩ := h₂
  -- edges of P₁ lie in E₁, edges of P₂ lie in E₂
  have hsub₁ : ∀ t ∈ P₁, cliqueEdges t ⊆ E₁ := by
    intro t ht; rw [← he₁]; exact Finset.subset_biUnion_of_mem cliqueEdges ht
  have hsub₂ : ∀ t ∈ P₂, cliqueEdges t ⊆ E₂ := by
    intro t ht; rw [← he₂]; exact Finset.subset_biUnion_of_mem cliqueEdges ht
  refine ⟨P₁ ∪ P₂, ?_, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · exact hc₁ t h
    · exact hc₂ t h
  · intro t ht t' ht' hne
    rcases Finset.mem_union.1 ht with h | h <;> rcases Finset.mem_union.1 ht' with h' | h'
    · exact hdj₁ t h t' h' hne
    · exact Finset.disjoint_of_subset_left (hsub₁ t h)
        (Finset.disjoint_of_subset_right (hsub₂ t' h') hd)
    · exact Finset.disjoint_of_subset_left (hsub₂ t h)
        (Finset.disjoint_of_subset_right (hsub₁ t' h') hd.symm)
    · exact hdj₂ t h t' h' hne
  · have hsplit : famEdges (P₁ ∪ P₂) = famEdges P₁ ∪ famEdges P₂ := by
      ext e; simp only [famEdges, Finset.mem_biUnion, Finset.mem_union]; aesop
    rw [hsplit, he₁, he₂]

/-- **An `(H,H')`-transformer** (BKLO §8.1).  `T` is disjoint from `H` and `H'`, and both `T ∪ H`
and `T ∪ H'` are triangle-decomposable. -/
def IsTransformer (T H H' : Finset (Sym2 V)) : Prop :=
  Disjoint T H ∧ Disjoint T H' ∧ TriDecomp (T ∪ H) ∧ TriDecomp (T ∪ H')

/-- `H ∼_F H'`: there is an `(H,H')`-transformer. -/
def Sim (H H' : Finset (Sym2 V)) : Prop := ∃ T, IsTransformer T H H'

/-- The relation is symmetric. -/
theorem sim_symm {H H' : Finset (Sym2 V)} (h : Sim H H') : Sim H' H := by
  obtain ⟨T, hTH, hTH', hd1, hd2⟩ := h
  exact ⟨T, hTH', hTH, hd2, hd1⟩

/-- An absorber for `H` is a transformer to the empty graph: `A` and `A ∪ H` both decompose. -/
def IsAbsorber (A H : Finset (Sym2 V)) : Prop :=
  Disjoint A H ∧ TriDecomp A ∧ TriDecomp (A ∪ H)

/-- **Proposition 8.2 (transitivity).**  If `T₁` transforms `(H, H')` and `T₂` transforms
`(H', H'')`, and the six cross edge-disjointness conditions hold (the edge-set analogue of BKLO's
`V(T₁) ∩ V(T₂) = V(H')`), then `T := T₁ ∪ H' ∪ T₂` transforms `(H, H'')`.  Proof: regroup and apply
the workhorse `TriDecomp.union`. -/
theorem transformer_trans {T₁ T₂ H H' H'' : Finset (Sym2 V)}
    (h₁ : IsTransformer T₁ H H') (h₂ : IsTransformer T₂ H' H'')
    (dTT : Disjoint T₁ T₂) (dHH' : Disjoint H H') (dHT₂ : Disjoint H T₂)
    (dT₁H'' : Disjoint T₁ H'') (dH'H'' : Disjoint H' H'') :
    IsTransformer (T₁ ∪ H' ∪ T₂) H H'' := by
  classical
  obtain ⟨dT₁H, dT₁H', hd1H, hd1H'⟩ := h₁
  obtain ⟨dT₂H', dT₂H'', hd2H', hd2H''⟩ := h₂
  -- disjointness of the two regrouped halves
  have dis1 : Disjoint (T₁ ∪ H) (T₂ ∪ H') :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨dTT, dT₁H'⟩,
       Finset.disjoint_union_right.mpr ⟨dHT₂, dHH'⟩⟩
  have dis2 : Disjoint (T₁ ∪ H') (T₂ ∪ H'') :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨dTT, dT₁H''⟩,
       Finset.disjoint_union_right.mpr ⟨dT₂H'.symm, dH'H''⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Disjoint (T₁ ∪ H' ∪ T₂) H
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨dT₁H, dHH'.symm⟩, dHT₂.symm⟩
  · -- Disjoint (T₁ ∪ H' ∪ T₂) H''
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨dT₁H'', dH'H''⟩, dT₂H''⟩
  · -- TriDecomp ((T₁ ∪ H' ∪ T₂) ∪ H)
    have h := TriDecomp.union dis1 hd1H hd2H'
    convert h using 1
    ext x; simp only [Finset.mem_union]; tauto
  · -- TriDecomp ((T₁ ∪ H' ∪ T₂) ∪ H'')
    have h := TriDecomp.union dis2 hd1H' hd2H''
    convert h using 1
    ext x; simp only [Finset.mem_union]; tauto

end BKLO
