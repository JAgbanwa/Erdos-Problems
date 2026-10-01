import Mathlib

/-
`BoundedCliqueGap.Defs` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
Definitional layer for the Route B triangle-packing development:
edge sets of vertex triples, triangles, edge-disjoint triangle families,
`nu3`, fractional triangle packings, their value, integral part and core.

This file is imported by `BoundedCliqueGap.lean` (statements of Tiers 1, 2, 4) and by
`BoundedCliqueGap/Krivelevich.lean` (Tier 3).
-/

namespace BoundedCliqueGap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Tier 1 — definitional layer -/

/-- The (unordered) edge pairs of a vertex 3-set. -/
def triEdges (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter fun e => ¬ e.IsDiag

omit [Fintype V] in
/-- Membership in `triEdges` unfolded. -/
lemma mem_triEdges_iff {T : Finset V} {e : Sym2 V} :
    e ∈ triEdges T ↔ ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ e = s(u, v) := by
  induction e with
  | _ a b =>
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff,
      Sym2.isDiag_iff_proj_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hd⟩
      exact ⟨a, ha, b, hb, hd, rfl⟩
    · rintro ⟨u, hu, v, hv, huv, he⟩
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hu, hv⟩, huv⟩
      · exact ⟨⟨hv, hu⟩, fun h => huv h.symm⟩

omit [Fintype V] in
lemma mk_mem_triEdges {T : Finset V} {u v : V} (hu : u ∈ T) (hv : v ∈ T)
    (huv : u ≠ v) : s(u, v) ∈ triEdges T :=
  mem_triEdges_iff.2 ⟨u, hu, v, hv, huv, rfl⟩

/-- `T` is a triangle of `G`: three vertices, pairwise adjacent. -/
def IsTriangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v

omit [Fintype V] in
/-- A triangle has at least one edge. -/
lemma IsTriangle.triEdges_nonempty {G : SimpleGraph V} {T : Finset V}
    (h : IsTriangle G T) : (triEdges T).Nonempty := by
  have h1 : 1 < T.card := by rw [h.1]; norm_num
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h1
  exact ⟨s(u, v), mk_mem_triEdges hu hv huv⟩

/-- An edge-disjoint family of triangles of `G`. -/
def IsPacking (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ T ∈ P, IsTriangle G T) ∧
  ∀ T ∈ P, ∀ T' ∈ P, T ≠ T' → Disjoint (triEdges T) (triEdges T')

/-- `nu3 G` : the maximum size of an edge-disjoint triangle family. -/
noncomputable def nu3 (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ P : Finset (Finset V), IsPacking G P ∧ P.card = n}

omit [Fintype V] in
/-- The set of packing sizes is nonempty (the empty family is a packing). -/
lemma nu3_set_nonempty (G : SimpleGraph V) :
    {n | ∃ P : Finset (Finset V), IsPacking G P ∧ P.card = n}.Nonempty :=
  ⟨0, ∅, ⟨by simp [IsPacking], by simp⟩⟩

/-- The set of packing sizes is bounded above. -/
lemma nu3_set_bddAbove (G : SimpleGraph V) :
    BddAbove {n | ∃ P : Finset (Finset V), IsPacking G P ∧ P.card = n} := by
  refine ⟨Fintype.card (Finset V), ?_⟩
  rintro n ⟨P, -, rfl⟩
  exact Finset.card_le_univ P

/-- Every packing is at most as large as `nu3`. -/
lemma card_le_nu3 {G : SimpleGraph V} {P : Finset (Finset V)} (hP : IsPacking G P) :
    P.card ≤ nu3 G :=
  le_csSup (nu3_set_bddAbove G) ⟨P, hP, rfl⟩

/-- `nu3` is attained by some packing. -/
lemma exists_packing_card_eq_nu3 (G : SimpleGraph V) :
    ∃ P : Finset (Finset V), IsPacking G P ∧ P.card = nu3 G :=
  Nat.sSup_mem (nu3_set_nonempty G) (nu3_set_bddAbove G)

/-- A fractional triangle packing of `G`. -/
structure FracPacking (G : SimpleGraph V) where
  x : Finset V → ℚ
  nonneg : ∀ T, 0 ≤ x T
  supp : ∀ T, x T ≠ 0 → IsTriangle G T
  edge_le_one : ∀ e : Sym2 V, ¬ e.IsDiag →
    ∑ T ∈ Finset.univ.filter fun T => e ∈ triEdges T ∧ x T ≠ 0, x T ≤ 1

namespace FracPacking

variable {G : SimpleGraph V}

/-- The value of a fractional packing. -/
noncomputable def value (F : FracPacking G) : ℚ :=
  ∑ T ∈ Finset.univ.filter fun T => F.x T ≠ 0, F.x T

end FracPacking

/-! ### Tier 1(a),(b) -/

end BoundedCliqueGap
