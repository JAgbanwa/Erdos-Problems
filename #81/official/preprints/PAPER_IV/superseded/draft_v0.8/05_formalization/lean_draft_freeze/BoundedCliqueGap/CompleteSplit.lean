import BoundedCliqueGap.SteinerTools

/-
`BoundedCliqueGap.CompleteSplit` — declaration-level extract of the Route B
triangle-packing development.  Only the declarations in the constant cone of
`BoundedCliqueGap.chordal_gap_linear_cliqueFree` were kept (plus the few that
the retained sources need in order to elaborate); the module documentation
below is the original one and may advertise results that were pruned away.
-/

/-
# Complete split graphs and rung C1 (the LP ceilings of `CS`)

`CS K S` is the complete split graph with clique part `K` and independent
part `S`: the `K`-part is a clique, the `S`-part is independent, and every
cross pair is adjacent.  Under the identification of `K_m` minus the edges of
a sub-clique `K_s` with `CS (Fin (m-s)) (Fin s)`, this is the *relative*
(separator-avoiding) primitive of the clique-tree programme.

* `value_le_card_of_edgeCover` — a generic LP ceiling: if every triangle of
  `G` uses an edge of a set `D`, then every fractional packing has value at
  most `|D|`.
* **C1(a)** `cs_value_le_cliqueEdges` — every triangle of `CS K S` uses a
  clique-part edge, hence `value ≤ C(|K|,2)`.
* **C1(b)** `cs_value_le_edges_third` — `value ≤ (C(|K|,2) + |K||S|)/3`.
-/

namespace BoundedCliqueGap

open Finset

/-! ## A generic LP ceiling from an edge cover of the triangles -/

/-! ## The complete split graph -/

/-- The **complete split graph** `CS K S`: `K` is a clique, `S` is independent,
all cross pairs are adjacent. -/
def CS (K S : Type*) : SimpleGraph (K ⊕ S) where
  Adj u v := u ≠ v ∧ (u.isLeft = true ∨ v.isLeft = true)
  symm := by
    rintro u v ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {K S : Type*}

@[simp] lemma CS_adj_inl_inl {a b : K} :
    (CS K S).Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b := by
  simp [CS]

@[simp] lemma CS_adj_inl_inr {a : K} {j : S} :
    (CS K S).Adj (Sum.inl a) (Sum.inr j) := by simp [CS]

@[simp] lemma CS_adj_inr_inl {a : K} {j : S} :
    (CS K S).Adj (Sum.inr j) (Sum.inl a) := by simp [CS]

@[simp] lemma CS_adj_inr_inr {i j : S} :
    ¬ (CS K S).Adj (Sum.inr i) (Sum.inr j) := by simp [CS]

section CliqueEdges

variable [Fintype K] [DecidableEq K]

/-! ## Rung C1(a) -/

end CliqueEdges

/-! ## The edge count of `CS K S`, and rung C1(b) -/

section EdgeCount

variable [Fintype K] [DecidableEq K] [Fintype S] [DecidableEq S]

end EdgeCount

end BoundedCliqueGap
