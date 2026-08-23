/-
# A3 — A counting inequality for triangle decompositions

A self-contained mini-API for triangle decompositions of an edge set (`Finset (Sym2 V)`), and the
counting inequality:

> if the edge set `X ∪ Y` decomposes into triangles, `X` and `Y` are edge-disjoint, and `Y` is
> bipartite (hence triangle-free), then `|Y| ≤ 2·|X|`.

Every triangle of the decomposition has at least one edge in `X` (a bipartite `Y` cannot contain all
three edges of a triangle), so summing over the triangles gives the bound.  This is the obstruction
behind "a low-degree reservoir cannot absorb a dense triangle-free leftover".
-/
import Mathlib

open Finset

namespace Contrib

variable {V : Type*} [DecidableEq V]

/-- The edges of a vertex set `t`: the non-loop unordered pairs inside `t`.  For a 3-set this is the
three edges of the triangle. -/
def cliqueEdges (t : Finset V) : Finset (Sym2 V) :=
  (t.sym2).filter (fun e => ¬ e.IsDiag)

theorem mem_cliqueEdges {t : Finset V} {e : Sym2 V} :
    e ∈ cliqueEdges t ↔ (∀ x ∈ e, x ∈ t) ∧ ¬ e.IsDiag := by
  simp [cliqueEdges, Finset.mem_sym2_iff]

/-- A triangle (3-set) has exactly three edges. -/
theorem cliqueEdges_card_three {t : Finset V} (h : t.card = 3) : (cliqueEdges t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h
  have h3 : cliqueEdges ({a, b, c} : Finset V) = ({s(a,b), s(b,c), s(a,c)} : Finset (Sym2 V)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_cliqueEdges, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
        Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨h, hne⟩
        rcases h x (Or.inl rfl) with rfl | rfl | rfl <;>
          rcases h y (Or.inr rfl) with rfl | rfl | rfl <;> simp_all
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          refine ⟨?_, ?_⟩ <;> simp_all <;> tauto
  rw [h3]
  rw [Finset.card_insert_of_notMem (by simp; tauto),
    Finset.card_insert_of_notMem (by simp; tauto)]
  simp

/-- The edge set of a family of triangles. -/
def famEdges (P : Finset (Finset V)) : Finset (Sym2 V) := P.biUnion cliqueEdges

/-- **Triangle decomposition of an edge set.**  A finite family of triangles, pairwise
edge-disjoint, whose edges are exactly `E`. -/
def IsTriDecomp (E : Finset (Sym2 V)) : Prop :=
  ∃ P : Finset (Finset V), (∀ t ∈ P, t.card = 3) ∧
    (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
    famEdges P = E

/-- `Y` is bipartite: its vertices admit a 2-colouring with no monochromatic edge. -/
def IsBipartite (Y : Finset (Sym2 V)) : Prop :=
  ∃ c : V → Bool, ∀ x y : V, s(x, y) ∈ Y → c x ≠ c y

/-- A bipartite edge set contains no full triangle: three pairwise-distinct colours are impossible
with two colours. -/
theorem not_cliqueEdges_subset_of_bipartite {Y : Finset (Sym2 V)} (hbip : IsBipartite Y)
    {t : Finset V} (ht : t.card = 3) : ¬ cliqueEdges t ⊆ Y := by
  obtain ⟨c, hc⟩ := hbip
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.1 ht
  intro hsub
  have mem : ∀ x y : V, x ≠ y → x ∈ ({a,b,d} : Finset V) → y ∈ ({a,b,d} : Finset V) →
      s(x,y) ∈ Y := by
    intro x y hxy hx hy
    refine hsub (mem_cliqueEdges.2 ⟨?_, ?_⟩)
    · intro z hz; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> assumption
    · simp [Sym2.isDiag_iff_proj_eq, hxy]
  have h1 := hc a b (mem a b hab (by simp) (by simp))
  have h2 := hc b d (mem b d hbd (by simp) (by simp))
  have h3 := hc a d (mem a d had (by simp) (by simp))
  -- three Booleans pairwise distinct: impossible
  revert h1 h2 h3; cases c a <;> cases c b <;> cases c d <;> decide

/-- **The counting inequality (triangle-free form).**  If `X ∪ Y` decomposes into triangles, `X`
and `Y` are edge-disjoint, and no decomposition-triangle lies entirely in `Y`, then `|Y| ≤ 2·|X|`. -/
theorem card_le_two_mul_of_triangleFree {X Y : Finset (Sym2 V)}
    (hdisj : Disjoint X Y)
    (hfree : ∀ t : Finset V, t.card = 3 → ¬ cliqueEdges t ⊆ Y)
    (hdec : IsTriDecomp (X ∪ Y)) : Y.card ≤ 2 * X.card := by
  classical
  obtain ⟨P, hcard3, hpw, hfam⟩ := hdec
  have hsub : ∀ t ∈ P, cliqueEdges t ⊆ X ∪ Y := by
    intro t ht
    rw [← hfam]
    exact Finset.subset_biUnion_of_mem cliqueEdges ht
  have hsplit : ∀ Z : Finset (Sym2 V), Z ⊆ X ∪ Y →
      Z.card = P.sum (fun t => (cliqueEdges t ∩ Z).card) := by
    intro Z hZ
    have hZeq : Z = P.biUnion (fun t => cliqueEdges t ∩ Z) := by
      refine Finset.Subset.antisymm (fun e he => ?_) ?_
      · have hmem : e ∈ famEdges P := by rw [hfam]; exact hZ he
        obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hmem
        exact Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_inter.2 ⟨het, he⟩⟩
      · exact Finset.biUnion_subset.2 fun t _ => Finset.inter_subset_right
    conv_lhs => rw [hZeq]
    exact Finset.card_biUnion fun t ht t' ht' hne =>
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hpw t ht t' ht' hne))
  have hY := hsplit Y Finset.subset_union_right
  have hX := hsplit X Finset.subset_union_left
  have hterm : ∀ t ∈ P, (cliqueEdges t ∩ Y).card ≤ 2 * (cliqueEdges t ∩ X).card := by
    intro t ht
    have h3 : (cliqueEdges t).card = 3 := cliqueEdges_card_three (hcard3 t ht)
    have hpart : (cliqueEdges t ∩ X).card + (cliqueEdges t ∩ Y).card = 3 := by
      rw [← h3, ← Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisj))]
      congr 1
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.2 (hsub t ht)
    have hle2 : (cliqueEdges t ∩ Y).card ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      have heq : cliqueEdges t ∩ Y = cliqueEdges t :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      exact hfree t (hcard3 t ht) (by rw [← heq]; exact Finset.inter_subset_right)
    omega
  calc Y.card = P.sum (fun t => (cliqueEdges t ∩ Y).card) := hY
    _ ≤ P.sum (fun t => 2 * (cliqueEdges t ∩ X).card) := Finset.sum_le_sum hterm
    _ = 2 * X.card := by rw [← Finset.mul_sum, ← hX]

/-- **The counting inequality (bipartite form).**  If `X ∪ Y` decomposes into triangles, `X` and
`Y` are edge-disjoint, and `Y` is bipartite, then `|Y| ≤ 2·|X|`. -/
theorem card_le_two_mul_of_bipartite {X Y : Finset (Sym2 V)}
    (hdisj : Disjoint X Y) (hbip : IsBipartite Y)
    (hdec : IsTriDecomp (X ∪ Y)) : Y.card ≤ 2 * X.card :=
  card_le_two_mul_of_triangleFree hdisj
    (fun t ht => not_cliqueEdges_subset_of_bipartite hbip ht) hdec

end Contrib
