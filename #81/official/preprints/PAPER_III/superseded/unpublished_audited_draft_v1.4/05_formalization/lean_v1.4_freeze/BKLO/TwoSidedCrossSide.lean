/-
# The cross-side pairing rule, and why it keeps the ledger spread.

A vertex `a` of `W'` lies in one class `C (α h + β)` of the grid, and it belongs to the reserved
link of an outer vertex `w` only if it belongs to the region of `w`'s cell — that is, only if
`x w = α` (then `a` sits in the **row part** of that region) or `y w = β` (the **column part**).
So the outer vertices that can ever pair `a` split into two families: the row-line family
`x w = α` and the column-line family `y w = β`.

The **cross-side rule** pairs `a` to the other side of the region:

* if `x w = α`, the partner of `a` is taken in a class `C (ρ h + y w)` of the *column* part;
* if `y w = β`, the partner of `a` is taken in a class `C (x w h + σ)` of the *row* part.

`BKLO.regionLoad_le_crossSide` is the point of the rule: the ledger entry of `a` at a cell `(P, Q)`
is then bounded by four counts, none of which is a ledger entry:

* `x w = α ∧ ρ w = P` — the row-line family that *chose* the row `P` for the partner; the choice is
  free, and a balanced choice makes this term the row-line family divided by `h`;
* `x w = α ∧ y w = Q` — the outer vertices of the single cell `(α, Q)`;
* `y w = β ∧ x w = P` — the outer vertices of the single cell `(P, β)`;
* `y w = β ∧ σ w = Q` — the column-line family that chose the column `Q`, again a free choice.

The two middle terms are cell fibres, which `BKLO.IsGridTwoSidedReservoir.cellFibre` already bounds;
the two outer terms are controlled by the rule itself.  Nothing here is an invariant of the sweep
that has to be *maintained*: the bound holds for whatever set `S` of earlier links, as soon as each
of them obeyed the rule.  This is what replaces the least-loaded bookkeeping — the two-sided design
gives the row part and the column part of every link exactly the same size, so a cross-side pairing
is a bipartite matching between two sides of equal size.

* `BKLO.gridDigits_inj` — a class index determines its two grid digits.
* `BKLO.IsCrossSideAt` — the rule, at one earlier outer vertex and one vertex `a` of its link.
* `BKLO.regionLoad_le_crossSide` — the four-term bound above.
* `BKLO.regionLoad_le_of_crossSide_bounds` — the ledger entry is at most `h t / 16` once the four
  terms are bounded by `h t / 64`.

Everything here is `sorry`-free.
-/
import BKLO.GridLabelling
import BKLO.TwoSidedLedgerObstruction

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- A class index determines its two grid digits. -/
theorem gridDigits_inj {h A b A' b' : ℕ} (hb : b < h) (hb' : b' < h)
    (heq : A * h + b = A' * h + b') : A = A' ∧ b = b' := by
  have h0 : 0 < h := lt_of_le_of_lt (Nat.zero_le b) hb
  have e1 : A * h + b = b + A * h := by ring
  have e2 : A' * h + b' = b' + A' * h := by ring
  rw [e1, e2] at heq
  have hmod : (b + A * h) % h = (b' + A' * h) % h := by rw [heq]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hb'] at hmod
  refine ⟨?_, hmod⟩
  have : A * h = A' * h := by omega
  exact Nat.eq_of_mul_eq_mul_right h0 this

/-- **The cross-side rule at one earlier link.**  The vertex `a` lies in the class `C (α h + β)`.
If the outer vertex `w` sees `a` through the row part of its region (`x w = α`), its pairing sends
`a` into the class `C (ρ h + y w)` of the column part; if it sees `a` through the column part
(`y w = β`), the pairing sends `a` into the class `C ((x w) h + σ)` of the row part. -/
def IsCrossSideAt (h : ℕ) (C : ℕ → Finset V) (x y : V → ℕ) (α β : ℕ) (w : V)
    (gwa : V) (ρ σ : ℕ) : Prop :=
  (x w = α ∧ gwa ∈ C (ρ * h + y w)) ∨ (y w = β ∧ gwa ∈ C (x w * h + σ))

/-- **The cross-side rule keeps the ledger of `a` spread.**  A ledger entry of `a` splits into two
cell fibres and the two free choices of the rule. -/
theorem regionLoad_le_crossSide {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V} {g : V → V → V}
    {S E : Finset V} {x y : V → ℕ} {a : V} {α β : ℕ} {ρ σ : V → ℕ} {P Q : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hρ : ∀ w ∈ S, ρ w < h) (hσ : ∀ w ∈ S, σ w < h) (hP : P < h) (hQ : Q < h)
    (hrule : ∀ w ∈ S, a ∈ X w →
      w ∈ E ∨ IsCrossSideAt h C x y α β w (g w a) (ρ w) (σ w)) :
    regionLoad h C X g S x y a P Q
      ≤ (S.filter (fun w => x w = α ∧ ρ w = P)).card
        + (S.filter (fun w => x w = α ∧ y w = Q)).card
        + ((S.filter (fun w => y w = β ∧ x w = P)).card
          + (S.filter (fun w => y w = β ∧ σ w = Q)).card) + E.card := by
  classical
  set F1 := S.filter (fun w => x w = α ∧ ρ w = P) with hF1
  set F2 := S.filter (fun w => x w = α ∧ y w = Q) with hF2
  set F3 := S.filter (fun w => y w = β ∧ x w = P) with hF3
  set F4 := S.filter (fun w => y w = β ∧ σ w = Q) with hF4
  have hsub : S.filter (fun w =>
      ¬ (x w = P ∧ y w = Q) ∧ a ∈ X w ∧ g w a ∈ gridRegion h C P Q)
      ⊆ ((F1 ∪ F2) ∪ (F3 ∪ F4)) ∪ E := by
    intro w hw
    obtain ⟨hwS, -, haX, hreg⟩ := Finset.mem_filter.1 hw
    rw [gridRegion_eq_biUnion] at hreg
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.1 hreg
    have hilt : i < h * h := gridIdx_lt hP hQ hi
    have hyw : y w < h := hylt w hwS
    have hxw : x w < h := hxlt w hwS
    -- the class of the partner is the one the rule prescribes
    have hclass : ∀ j, j < h * h → g w a ∈ C j → i = j := by
      intro j hj haj
      by_contra hne
      exact (Finset.disjoint_left.1 (hdisj i hilt j hj hne)) hai haj
    rcases hrule w hwS haX with hwE | hcross
    · exact Finset.mem_union_right _ hwE
    rcases hcross with ⟨hxα, hmem⟩ | ⟨hyβ, hmem⟩
    · have hjlt : ρ w * h + y w < h * h := by
        have := hρ w hwS
        calc ρ w * h + y w < ρ w * h + h := by omega
          _ = (ρ w + 1) * h := by ring
          _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
      have hij : i = ρ w * h + y w := hclass _ hjlt hmem
      rcases mem_gridIdx.1 hi with ⟨j, hj, hieq⟩ | ⟨l, hl, hieq⟩
      · have := gridDigits_inj hyw hj (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hxα, this.1⟩)))
      · have := gridDigits_inj hyw hQ (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hxα, this.2⟩)))
    · have hjlt : x w * h + σ w < h * h := by
        have := hσ w hwS
        calc x w * h + σ w < x w * h + h := by omega
          _ = (x w + 1) * h := by ring
          _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
      have hij : i = x w * h + σ w := hclass _ hjlt hmem
      rcases mem_gridIdx.1 hi with ⟨j, hj, hieq⟩ | ⟨l, hl, hieq⟩
      · have := gridDigits_inj (hσ w hwS) hj (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨hwS, hyβ, this.1⟩)))
      · have := gridDigits_inj (hσ w hwS) hQ (hij ▸ hieq)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hwS, hyβ, this.2⟩)))
  calc regionLoad h C X g S x y a P Q ≤ (((F1 ∪ F2) ∪ (F3 ∪ F4)) ∪ E).card :=
        Finset.card_le_card hsub
    _ ≤ ((F1 ∪ F2) ∪ (F3 ∪ F4)).card + E.card := Finset.card_union_le _ _
    _ ≤ ((F1 ∪ F2).card + (F3 ∪ F4).card) + E.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((F1.card + F2.card) + (F3.card + F4.card)) + E.card :=
        Nat.add_le_add_right
          (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)) _

/-- **The ledger stays inside its budget.**  If each of the four terms of
`BKLO.regionLoad_le_crossSide` is at most a quarter of the budget, the ledger entry is inside the
budget. -/
theorem regionLoad_le_of_crossSide_bounds {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V}
    {g : V → V → V} {S E : Finset V} {x y : V → ℕ} {a : V} {α β : ℕ} {ρ σ : V → ℕ} {P Q B : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hxlt : ∀ w ∈ S, x w < h) (hylt : ∀ w ∈ S, y w < h)
    (hρ : ∀ w ∈ S, ρ w < h) (hσ : ∀ w ∈ S, σ w < h) (hP : P < h) (hQ : Q < h)
    (hrule : ∀ w ∈ S, a ∈ X w →
      w ∈ E ∨ IsCrossSideAt h C x y α β w (g w a) (ρ w) (σ w))
    (h1 : 8 * (S.filter (fun w => x w = α ∧ ρ w = P)).card ≤ B)
    (h2 : 8 * (S.filter (fun w => x w = α ∧ y w = Q)).card ≤ B)
    (h3 : 8 * (S.filter (fun w => y w = β ∧ x w = P)).card ≤ B)
    (h4 : 8 * (S.filter (fun w => y w = β ∧ σ w = Q)).card ≤ B)
    (h5 : 8 * E.card ≤ B) :
    regionLoad h C X g S x y a P Q ≤ B := by
  have := regionLoad_le_crossSide (C := C) (X := X) (g := g) (S := S) (E := E) (x := x) (y := y)
    (a := a) (α := α) (β := β) (ρ := ρ) (σ := σ) (P := P) (Q := Q) hdisj hxlt hylt hρ hσ hP hQ
    hrule
  omega


/-! ### A shift function balanced on every cell -/

/-- **A balanced shift.**  Every finite set carries a function to `[h]` which is balanced on every
cell of a labelling: the vertices of a cell are distributed over the `h` values evenly, up to one.
This is the free coordinate the cross-side rule uses, and it needs no probability: enumerate each
cell and read the index modulo `h`. -/
theorem exists_cell_balanced_shift (D : Finset V) (x y : V → ℕ) {h : ℕ} (hh : 0 < h) :
    ∃ φ : V → ℕ, (∀ w, φ w < h) ∧
      ∀ p q j : ℕ, (D.filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card
        ≤ (D.filter (fun w => x w = p ∧ y w = q)).card / h + 1 := by
  classical
  have H : ∀ pq : ℕ × ℕ, ∃ f : V → ℕ,
      (∀ w ∈ D.filter (fun w => x w = pq.1 ∧ y w = pq.2),
        f w < (D.filter (fun w => x w = pq.1 ∧ y w = pq.2)).card) ∧
      ∀ v ∈ D.filter (fun w => x w = pq.1 ∧ y w = pq.2),
        ∀ w ∈ D.filter (fun w => x w = pq.1 ∧ y w = pq.2), f v = f w → v = w := by
    intro pq
    set s : Finset V := D.filter (fun w => x w = pq.1 ∧ y w = pq.2) with hs
    refine ⟨fun w => if hw : w ∈ s then ((s.equivFin ⟨w, hw⟩ : Fin s.card) : ℕ) else 0, ?_, ?_⟩
    · intro w hw
      simp only [dif_pos hw]
      exact (s.equivFin ⟨w, hw⟩).2
    · intro v hv w hw hvw
      simp only [dif_pos hv, dif_pos hw] at hvw
      have h1 : s.equivFin ⟨v, hv⟩ = s.equivFin ⟨w, hw⟩ := Fin.ext hvw
      exact congrArg Subtype.val (s.equivFin.injective h1)
  choose f hf1 hf2 using H
  refine ⟨fun w => f (x w, y w) w % h, fun w => Nat.mod_lt _ hh, ?_⟩
  intro p q j
  refine le_trans (Finset.card_le_card_of_injOn (fun w => f (p, q) w) ?_ ?_)
    (card_filter_mod_le_grid _ h j)
  · intro w hw
    obtain ⟨hwD, hwx, hwy, hwφ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hw)
    have hws : w ∈ D.filter (fun v => x v = (p, q).1 ∧ y v = (p, q).2) :=
      Finset.mem_filter.2 ⟨hwD, hwx, hwy⟩
    have hwφ' : f (x w, y w) w % h = j := hwφ
    rw [hwx, hwy] at hwφ'
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 (hf1 (p, q) w hws), hwφ'⟩)
  · intro v hv w hw hvw
    obtain ⟨hvD, hvx, hvy, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
    obtain ⟨hwD, hwx, hwy, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hw)
    exact hf2 (p, q) v (Finset.mem_filter.2 ⟨hvD, hvx, hvy⟩) w
      (Finset.mem_filter.2 ⟨hwD, hwx, hwy⟩) hvw

omit [DecidableEq V] in
/-- A shift balanced on every cell is balanced on every row of the labelling. -/
theorem card_row_shift_le {D : Finset V} {x y φ : V → ℕ} {h : ℕ}
    (hy : ∀ w ∈ D, y w < h)
    (hcell : ∀ p q j : ℕ, (D.filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card
      ≤ (D.filter (fun w => x w = p ∧ y w = q)).card / h + 1) (p j : ℕ) :
    (D.filter (fun w => x w = p ∧ φ w = j)).card
      ≤ (D.filter (fun w => x w = p)).card / h + h := by
  classical
  have hfib : (D.filter (fun w => x w = p ∧ φ w = j)).card
      = ∑ q ∈ Finset.range h,
        ((D.filter (fun w => x w = p ∧ φ w = j)).filter (fun w => y w = q)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro w hw
    exact Finset.mem_coe.2 (Finset.mem_range.2 (hy w (Finset.mem_filter.1 hw).1))
  have hfib' : (D.filter (fun w => x w = p)).card
      = ∑ q ∈ Finset.range h, ((D.filter (fun w => x w = p)).filter (fun w => y w = q)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro w hw
    exact Finset.mem_coe.2 (Finset.mem_range.2 (hy w (Finset.mem_filter.1 hw).1))
  have heq1 : ∀ q : ℕ, ((D.filter (fun w => x w = p ∧ φ w = j)).filter (fun w => y w = q))
      = D.filter (fun w => x w = p ∧ y w = q ∧ φ w = j) := by
    intro q; ext w; simp only [Finset.mem_filter]; tauto
  have heq2 : ∀ q : ℕ, ((D.filter (fun w => x w = p)).filter (fun w => y w = q))
      = D.filter (fun w => x w = p ∧ y w = q) := by
    intro q; ext w; simp only [Finset.mem_filter]; tauto
  have hsum : ∑ q ∈ Finset.range h, (D.filter (fun w => x w = p ∧ y w = q)).card / h
      ≤ (∑ q ∈ Finset.range h, (D.filter (fun w => x w = p ∧ y w = q)).card) / h := by
    classical
    induction (Finset.range h) using Finset.induction with
    | empty => simp
    | insert q s hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq]
      exact le_trans (Nat.add_le_add_left ih _) (Nat.add_div_le_add_div _ _ _)
  calc (D.filter (fun w => x w = p ∧ φ w = j)).card
      = ∑ q ∈ Finset.range h, (D.filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card := by
        rw [hfib]; exact Finset.sum_congr rfl fun q _ => by rw [heq1 q]
    _ ≤ ∑ q ∈ Finset.range h, ((D.filter (fun w => x w = p ∧ y w = q)).card / h + 1) :=
        Finset.sum_le_sum fun q _ => hcell p q j
    _ = (∑ q ∈ Finset.range h, (D.filter (fun w => x w = p ∧ y w = q)).card / h) + h := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ (∑ q ∈ Finset.range h, (D.filter (fun w => x w = p ∧ y w = q)).card) / h + h :=
        Nat.add_le_add_right hsum _
    _ = (D.filter (fun w => x w = p)).card / h + h := by
        rw [hfib']
        exact congrArg (fun z => z / h + h) (Finset.sum_congr rfl fun q _ => by rw [heq2 q]).symm

omit [DecidableEq V] in
/-- A shift balanced on every cell is balanced on every column of the labelling. -/
theorem card_col_shift_le {D : Finset V} {x y φ : V → ℕ} {h : ℕ}
    (hx : ∀ w ∈ D, x w < h)
    (hcell : ∀ p q j : ℕ, (D.filter (fun w => x w = p ∧ y w = q ∧ φ w = j)).card
      ≤ (D.filter (fun w => x w = p ∧ y w = q)).card / h + 1) (q j : ℕ) :
    (D.filter (fun w => y w = q ∧ φ w = j)).card
      ≤ (D.filter (fun w => y w = q)).card / h + h := by
  classical
  have hcell' : ∀ p' q' j' : ℕ, (D.filter (fun w => y w = p' ∧ x w = q' ∧ φ w = j')).card
      ≤ (D.filter (fun w => y w = p' ∧ x w = q')).card / h + 1 := by
    intro p' q' j'
    have e1 : D.filter (fun w => y w = p' ∧ x w = q' ∧ φ w = j')
        = D.filter (fun w => x w = q' ∧ y w = p' ∧ φ w = j') := by
      ext w; simp only [Finset.mem_filter]; tauto
    have e2 : D.filter (fun w => y w = p' ∧ x w = q') = D.filter (fun w => x w = q' ∧ y w = p') := by
      ext w; simp only [Finset.mem_filter]; tauto
    rw [e1, e2]; exact hcell q' p' j'
  exact card_row_shift_le (x := y) (y := x) hx hcell' q j

end BKLO
