import PaperIV.RD09FiniteAveraging
import PaperIV.EquitableEdgeColouring

/-!
# E14, step 2: RD09 phase I — choosing the root of every colour class by finite averaging

Let the edges `E` of the rows be properly coloured by a finite group `ι` (every colour class a
matching), and let `root : V → ι` label the core vertices.  For a shift `g ∈ ι`, the core vertex
`v` hosts the colour class `root v · g⁻¹` and lifts those of its edges `e` with `ok v e`
(both ends of `e` joined to `v` by usable links) to triangles `{v} ∪ e`:

  `liftAt col root ok g v = { e ∈ E : ok v e ∧ col e = root v · g⁻¹ }`.

`exists_shift_lift_ge`: some shift lifts at least the average,

  `|E| · c' ≤ |ι| · Σ_{v ∈ S} |liftAt g v|`,

whenever every `e ∈ E` has at least `c'` core vertices `v` with `ok v e`.  The proof is the exact
double count of `PaperIV.RD09FiniteAveraging.sum_shiftCost_eq` (every class–root incidence is
met by exactly one translation), applied to the incidence weight
`gain j r = Σ_{v ∈ S, root v = r} |{e ∈ E : ok v e, col e = j}|`.
No injectivity is needed for the count; it is used later only to separate the hosts.
-/

namespace A4S1.Indep

open Finset PaperIV.ColourClasses

variable {V : Type*} [DecidableEq V] {ι : Type*} [Group ι] [Fintype ι] [DecidableEq ι]

/-- The edges lifted at the core vertex `v` by the shift `g`. -/
def liftAt (E : Finset (Sym2 V)) (col : Sym2 V → ι) (root : V → ι)
    (ok : V → Sym2 V → Prop) [∀ v e, Decidable (ok v e)] (g : ι) (v : V) : Finset (Sym2 V) :=
  E.filter fun e => ok v e ∧ col e = root v * g⁻¹

/-- The class–root incidence weight. -/
def phaseOneGain (S : Finset V) (E : Finset (Sym2 V)) (col : Sym2 V → ι) (root : V → ι)
    (ok : V → Sym2 V → Prop) [∀ v e, Decidable (ok v e)] (j r : ι) : ℕ :=
  ∑ v ∈ S, if root v = r then (E.filter fun e => ok v e ∧ col e = j).card else 0

variable (S : Finset V) (E : Finset (Sym2 V)) (col : Sym2 V → ι) (root : V → ι)
  (ok : V → Sym2 V → Prop) [∀ v e, Decidable (ok v e)]

omit [DecidableEq V] in
/-- One translation: the incidences met by the shift `g` are exactly the lifted edges. -/
theorem shiftCost_phaseOneGain (g : ι) :
    PaperIV.RD09FiniteAveraging.shiftCost (phaseOneGain S E col root ok) g =
      ∑ v ∈ S, (liftAt E col root ok g v).card := by
  classical
  unfold PaperIV.RD09FiniteAveraging.shiftCost phaseOneGain
  rw [Finset.sum_comm]
  refine sum_congr rfl fun v _ => ?_
  have : ∀ j : ι, (if root v = j * g then (E.filter fun e => ok v e ∧ col e = j).card else 0) =
      (if root v * g⁻¹ = j then (E.filter fun e => ok v e ∧ col e = j).card else 0) := by
    intro j
    have hiff : root v = j * g ↔ root v * g⁻¹ = j := by
      constructor
      · intro h; rw [h, mul_inv_cancel_right]
      · intro h; rw [← h, inv_mul_cancel_right]
    by_cases h : root v = j * g
    · rw [if_pos h, if_pos (hiff.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]
  rw [Fintype.sum_congr _ _ this, Fintype.sum_ite_eq]
  rfl

omit [Group ι] in
/-- All translations together: every pair `(v, e)` with `ok v e` is counted once. -/
theorem sum_phaseOneGain :
    ∑ j : ι, ∑ r : ι, phaseOneGain S E col root ok j r =
      ∑ e ∈ E, (S.filter fun v => ok v e).card := by
  classical
  unfold phaseOneGain
  have h1 : ∀ j : ι, ∑ r : ι, (∑ v ∈ S, if root v = r then
      (E.filter fun e => ok v e ∧ col e = j).card else 0) =
      ∑ v ∈ S, (E.filter fun e => ok v e ∧ col e = j).card := by
    intro j
    rw [Finset.sum_comm]
    refine sum_congr rfl fun v _ => ?_
    rw [Fintype.sum_ite_eq]
  rw [Fintype.sum_congr _ _ h1, Finset.sum_comm]
  have h2 : ∀ v ∈ S, ∑ j : ι, (E.filter fun e => ok v e ∧ col e = j).card =
      (E.filter fun e => ok v e).card := by
    intro v _
    have := PaperIV.EquitableEdgeColouring.sum_card_colourClass_univ (E.filter fun e => ok v e)
      col
    rw [← this]
    refine Fintype.sum_congr _ _ fun j => ?_
    unfold colourClass
    rw [filter_filter]
  rw [sum_congr rfl h2]
  simp only [card_filter]
  rw [Finset.sum_comm]

/-- **Phase I by finite averaging.** Some shift lifts at least the average number of edges. -/
theorem exists_shift_lift_ge (c' : ℕ) (hc' : ∀ e ∈ E, c' ≤ (S.filter fun v => ok v e).card) :
    ∃ g : ι, E.card * c' ≤ Fintype.card ι * ∑ v ∈ S, (liftAt E col root ok g v).card := by
  classical
  set total := ∑ j : ι, ∑ r : ι, phaseOneGain S E col root ok j r with htotal
  have hsum := PaperIV.RD09FiniteAveraging.sum_shiftCost_eq (phaseOneGain S E col root ok)
  have hlow : E.card * c' ≤ total := by
    rw [htotal, sum_phaseOneGain]
    calc E.card * c' = ∑ _e ∈ E, c' := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hc'
  obtain ⟨g, -, hg⟩ := Finset.exists_le_of_sum_le (s := (univ : Finset ι)) univ_nonempty
    (f := fun _ => total)
    (g := fun g => Fintype.card ι * PaperIV.RD09FiniteAveraging.shiftCost
      (phaseOneGain S E col root ok) g)
    (by rw [← Finset.mul_sum, hsum, sum_const, card_univ, smul_eq_mul])
  refine ⟨g, hlow.trans ?_⟩
  rw [← shiftCost_phaseOneGain]
  exact hg

omit [Fintype ι] in
/-- The lifted edges at `v` lie in one colour class. -/
theorem liftAt_subset_class (g : ι) (v : V) :
    liftAt E col root ok g v ⊆ colourClass E col (root v * g⁻¹) := by
  intro e he
  rw [liftAt, mem_filter] at he
  exact mem_colourClass.2 ⟨he.1, he.2.2⟩

omit [Fintype ι] [DecidableEq V] in
/-- Distinct roots lift disjoint edge sets. -/
theorem liftAt_disjoint (g : ι) {v v' : V} (hvv : root v ≠ root v') :
    Disjoint (liftAt E col root ok g v) (liftAt E col root ok g v') := by
  rw [disjoint_left]
  intro e he he'
  rw [liftAt, mem_filter] at he he'
  apply hvv
  have := he.2.2.symm.trans he'.2.2
  exact mul_right_cancel this

end A4S1.Indep
