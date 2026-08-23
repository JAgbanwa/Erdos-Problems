/-
# The balanced-fibre clause: the repair the counted merge needs

`BKLO/AX2CountedMergeCaps.lean` locates the exact place where the one-link step
`BKLO.RoutedSweepInvCellCountWide6hStep` runs out of room.  The counted clause of
`BKLO.RoutedSweepInvCellCount` *caps* each routing fibre at `5 K² t + 1` but says nothing about how
the fibres of one place are shared out, and `BKLO.pool_blocking_affordable` shows that a history
admitted by the invariant can spend its whole budget emptying every fibre of every place the plan
offers one chosen link.  At that link the merge has no routing index left, its forced leftovers all
have to go into the foreign plan, and the concentrated demand they make there exceeds every ceiling
the leftover ledger admits (`BKLO.line_local_foreign_demand_exceeds_ceiling`).

This file is the repair, stated and proved in the abstract, so that it can be dropped into the
invariant.  The extra clause is that the fibres of a place are *balanced* against the plan's claim
on it:

```
BKLO.FibreBalanced h S L Pc rt  :=  ∀ a P, h · excRouteCount S Pc a (rt · a) P
                                      ≤ |{w ∈ S : a ∈ L w}| + (h - 1)
```

— no index of a place carries more than the average of the plan's claim on that place, up to one.
Three facts make it the right clause:

* `BKLO.fibreBalanced_empty` — the empty sweep is balanced, so the induction starts;
* `BKLO.exists_least_loaded_index` and `BKLO.fibreBalanced_insert_of_least_loaded` — a new link that
  routes each of its planned leftovers at a **least-loaded** index keeps the clause, so the
  induction steps.  The rule costs the merge nothing: a least-loaded index always exists;
* `BKLO.excRouteCount_le_of_fibreBalanced` — under the clause, *every* index of *every* place is
  usable, as soon as the plan's claim on the place along the relevant line is at most `B h`.  The
  cell-balanced plans of the development are far below that: `BKLO.planned_row_line_card_lt` bounds
  the claim by `(5 K² t + 1) h`, and the plans actually built by
  `BKLO.exists_cell_balanced_plan_of_resized` and
  `BKLO.exists_cell_balanced_plan_of_resized_in_link` sit at a small fraction of the cell ceiling.

With `BKLO.excRouteCount_le_of_fibreBalanced` in place of one-index-per-place
(`BKLO.exists_free_routing_index`), the two sides of a forced pair have *matching* free indices —
indeed all of them — so the merge may choose the class of every foreign partner freely and spread
its foreign demand into the window `BKLO.spread_foreign_allotment_fits` describes.  That is exactly
what the counted invariant as stated cannot guarantee.

Everything here is `sorry`-free.  It is stated for arbitrary `h`, `S`, `L`, `Pc`, `rt`, so adding
the clause to `BKLO.RoutedSweepInvCellCount` and re-running the chain
`BKLO.excLedgerSpread_of_routedSweepInvCellCountWide` →
`BKLO.twoSidedUsedClassMatchedResized6hPairing_of_cell_step_countWide` →
`BKLO.triangle_decomposition_of_inputs_and_cell_step_countWide` is all that stands between it and
the merge; the chain uses only the clauses it already has, so the strengthened invariant still
pays the same ledger.
-/
import BKLO.AX2CountedMergeCaps

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The clause -/

/-- **The fibres of a place are balanced against the plan's claim on it.**  No routing index of a
place carries more than the average, up to one, of the links at which the plan claims that place.
This is the clause `BKLO.RoutedSweepInvCellCount` is missing: it caps the fibres but never balances
them. -/
def FibreBalanced (h : ℕ) (S : Finset V) (L Pc : V → Finset V) (rt : V → V → ℕ) : Prop :=
  ∀ (a : V) (P : ℕ), h * excRouteCount S Pc a (fun w => rt w a) P
    ≤ (S.filter (fun w => a ∈ L w)).card + (h - 1)

/-- The empty sweep is balanced. -/
theorem fibreBalanced_empty (h : ℕ) (L Pc : V → Finset V) (rt : V → V → ℕ) :
    FibreBalanced h (∅ : Finset V) L Pc rt := by
  intro a P
  simp [excRouteCount]

/-! ### What the clause buys: every index is usable -/

/-- **Under the balanced clause every routing index of a place is free.**  If the plan claims the
place at no more than `B h` links of the relevant line, then no fibre of the place carries more
than `B`, so the new link may route it at *any* index and stay inside the cap `B + 1`.  This is the
statement `BKLO.exists_free_routing_index` cannot give: there, one index is all that is
guaranteed. -/
theorem excRouteCount_le_of_fibreBalanced {h B : ℕ} {S : Finset V} {L Pc : V → Finset V}
    {rt : V → V → ℕ} (hh : 0 < h) (hbal : FibreBalanced h S L Pc rt) {a : V}
    (hload : (S.filter (fun w => a ∈ L w)).card ≤ B * h) (P : ℕ) :
    excRouteCount S Pc a (fun w => rt w a) P ≤ B := by
  have h1 := hbal a P
  by_contra hcon
  push_neg at hcon
  have h2 : (B + 1) * h ≤ excRouteCount S Pc a (fun w => rt w a) P * h :=
    Nat.mul_le_mul_right _ hcon
  have h3 : excRouteCount S Pc a (fun w => rt w a) P * h
      = h * excRouteCount S Pc a (fun w => rt w a) P := Nat.mul_comm _ _
  have h4 : (B + 1) * h = B * h + h := by ring
  omega

/-! ### The clause is maintained by the least-loaded rule -/

/-- **A least-loaded routing index always exists.**  Some index carries no more than the average of
the links at which the place is a cross-routed leftover. -/
theorem exists_least_loaded_index {h : ℕ} {S : Finset V} {Pc : V → Finset V} {rt : V → V → ℕ}
    (hh : 0 < h) (a : V) (hrt : ∀ w ∈ S, rt w a < h) :
    ∃ P < h, h * excRouteCount S Pc a (fun w => rt w a) P
      ≤ (S.filter (fun w => a ∈ Pc w)).card := by
  classical
  have hsum : ∑ P ∈ Finset.range h, excRouteCount S Pc a (fun w => rt w a) P
      = (S.filter (fun w => a ∈ Pc w)).card := by
    simp only [excRouteCount, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro w hw
    by_cases hwa : a ∈ Pc w
    · rw [Finset.sum_eq_single (rt w a)]
      · simp [hwa]
      · intro P _ hne
        simp [Ne.symm hne]
      · intro hmem
        exact absurd (Finset.mem_range.2 (hrt w hw)) hmem
    · simp [hwa]
  by_contra hcon
  push_neg at hcon
  have hlow : ∀ P ∈ Finset.range h,
      (S.filter (fun w => a ∈ Pc w)).card + 1
        ≤ h * excRouteCount S Pc a (fun w => rt w a) P := by
    intro P hP
    exact hcon P (Finset.mem_range.1 hP)
  have h1 : ((S.filter (fun w => a ∈ Pc w)).card + 1) * h
      ≤ ∑ P ∈ Finset.range h, h * excRouteCount S Pc a (fun w => rt w a) P := by
    calc ((S.filter (fun w => a ∈ Pc w)).card + 1) * h
        = ∑ _P ∈ Finset.range h, ((S.filter (fun w => a ∈ Pc w)).card + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlow
  have h2 : ∑ P ∈ Finset.range h, h * excRouteCount S Pc a (fun w => rt w a) P
      = h * (S.filter (fun w => a ∈ Pc w)).card := by
    rw [← Finset.mul_sum, hsum]
  rw [h2] at h1
  have h3 : ((S.filter (fun w => a ∈ Pc w)).card + 1) * h
      = h * (S.filter (fun w => a ∈ Pc w)).card + h := by ring
  omega

/-- **Inserting a link that routes at a least-loaded index keeps the clause.**  The new link adds
one unit to the fibre it uses and one unit to the plan's claim on the place it routes, and the
least-loaded choice is exactly what makes the first affordable. -/
theorem fibreBalanced_insert_of_least_loaded {h : ℕ} {S : Finset V} {L Pc : V → Finset V}
    {rt : V → V → ℕ} {u : V} (huS : u ∉ S)
    (hbal : FibreBalanced h S L Pc rt) (hPcL : Pc u ⊆ L u)
    (hchoice : ∀ a ∈ Pc u, h * excRouteCount S Pc a (fun w => rt w a) (rt u a)
      ≤ (S.filter (fun w => a ∈ L w)).card) :
    FibreBalanced h (insert u S) L Pc rt := by
  classical
  intro a P
  -- the claim of the plan can only grow
  have hloadmono : (S.filter (fun w => a ∈ L w)).card
      ≤ ((insert u S).filter (fun w => a ∈ L w)).card :=
    Finset.card_le_card (fun w hw => by
      obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
      exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hwS, hwa⟩)
  by_cases hcase : a ∈ Pc u ∧ rt u a = P
  · obtain ⟨hau, hrtu⟩ := hcase
    -- the fibre grows by exactly one, and so does the claim
    have hfil : (insert u S).filter (fun w => a ∈ Pc w ∧ rt w a = P)
        = insert u (S.filter (fun w => a ∈ Pc w ∧ rt w a = P)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw | hw, hp⟩
        · exact Or.inl hw
        · exact Or.inr ⟨hw, hp⟩
      · rintro (rfl | ⟨hw, hp⟩)
        · exact ⟨Or.inl rfl, hau, hrtu⟩
        · exact ⟨Or.inr hw, hp⟩
    have hnot : u ∉ S.filter (fun w => a ∈ Pc w ∧ rt w a = P) := fun hcon =>
      huS (Finset.mem_filter.1 hcon).1
    have hcount : excRouteCount (insert u S) Pc a (fun w => rt w a) P
        = excRouteCount S Pc a (fun w => rt w a) P + 1 := by
      simp only [excRouteCount]
      rw [hfil, Finset.card_insert_of_notMem hnot]
    have hfilL : (insert u S).filter (fun w => a ∈ L w)
        = insert u (S.filter (fun w => a ∈ L w)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw | hw, hp⟩
        · exact Or.inl hw
        · exact Or.inr ⟨hw, hp⟩
      · rintro (rfl | ⟨hw, hp⟩)
        · exact ⟨Or.inl rfl, hPcL hau⟩
        · exact ⟨Or.inr hw, hp⟩
    have hnotL : u ∉ S.filter (fun w => a ∈ L w) := fun hcon =>
      huS (Finset.mem_filter.1 hcon).1
    have hloadins : ((insert u S).filter (fun w => a ∈ L w)).card
        = (S.filter (fun w => a ∈ L w)).card + 1 := by
      rw [hfilL, Finset.card_insert_of_notMem hnotL]
    have hch := hchoice a hau
    rw [hrtu] at hch
    rw [hcount, hloadins]
    have : h * (excRouteCount S Pc a (fun w => rt w a) P + 1)
        = h * excRouteCount S Pc a (fun w => rt w a) P + h := by ring
    omega
  · -- the fibre does not grow
    have hsub : (insert u S).filter (fun w => a ∈ Pc w ∧ rt w a = P)
        ⊆ S.filter (fun w => a ∈ Pc w ∧ rt w a = P) := by
      intro w hw
      obtain ⟨hwS, hp⟩ := Finset.mem_filter.1 hw
      rcases Finset.mem_insert.1 hwS with rfl | hwS
      · exact absurd hp hcase
      · exact Finset.mem_filter.2 ⟨hwS, hp⟩
    have hcount : excRouteCount (insert u S) Pc a (fun w => rt w a) P
        ≤ excRouteCount S Pc a (fun w => rt w a) P :=
      Finset.card_le_card hsub
    have h1 := hbal a P
    have h2 : h * excRouteCount (insert u S) Pc a (fun w => rt w a) P
        ≤ h * excRouteCount S Pc a (fun w => rt w a) P := Nat.mul_le_mul_left _ hcount
    omega

end BKLO
