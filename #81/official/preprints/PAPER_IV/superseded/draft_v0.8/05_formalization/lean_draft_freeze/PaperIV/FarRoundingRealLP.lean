import PaperIV.FarRounding
import PaperIV.FiniteLPDuality

/-!
# Literal finite matrix for the normalized mixed packing LP

Rows are literal graph edges and columns are literal `K₃`/`K₄` items.  This
module contains no rationality assertion: it is the real finite-matrix side of
M02.
-/

namespace PaperIV.FarRoundingRealLP

open Finset
open PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev EdgeIdx := {e : Sym2 V // e ∈ G.edgeFinset}
abbrev ItemIdx := {K : Finset V // K ∈ items G}

/-- Objective-normalized edge/item incidence. -/
noncomputable def incidence (e : EdgeIdx G) (K : ItemIdx G) : ℝ :=
  if e.1 ∈ pairs K.1 then 1 / gainF ℝ K.1 else 0

/-- The same finite matrix over the rationals.  Its only nonzero entries are
`1/2` and `1/5`, according to whether the column is a `K3` or a `K4`. -/
def incidenceQ (e : EdgeIdx G) (K : ItemIdx G) : ℚ :=
  if e.1 ∈ pairs K.1 then 1 / gainF ℚ K.1 else 0

lemma incidence_eq_ratCast (e : EdgeIdx G) (K : ItemIdx G) :
    incidence G e K = (incidenceQ G e K : ℝ) := by
  unfold incidence incidenceQ gainF
  by_cases h : e.1 ∈ pairs K.1
  · simp [h]
  · simp [h]

lemma gain_pos (K : ItemIdx G) : 0 < gainF ℝ K.1 := by
  rcases (mem_items.mp K.2).2 with h3 | h4
  · norm_num [gainF, h3, Nat.choose]
  · norm_num [gainF, h4, Nat.choose]

lemma incidence_nonneg (e : EdgeIdx G) (K : ItemIdx G) : 0 ≤ incidence G e K := by
  unfold incidence
  split_ifs
  · exact one_div_nonneg.2 (gain_pos G K).le
  · exact le_rfl

/-- Every nonempty mixed-item column has a strictly positive incidence entry.
This is the nondegeneracy hypothesis required by finite LP duality. -/
lemma exists_incidence_pos (K : ItemIdx G) : ∃ e : EdgeIdx G, 0 < incidence G e K := by
  have hitem : IsItem G K.1 := mem_items.mp K.2
  have hcard : 0 < (pairs K.1).card := by
    rw [card_pairs_of_isItem hitem]
    rcases hitem.2 with h3 | h4
    · norm_num [gainOf, h3, Nat.choose]
    · norm_num [gainOf, h4, Nat.choose]
  obtain ⟨e, he⟩ := Finset.card_pos.mp hcard
  have heG : e ∈ G.edgeFinset := pairs_subset_edgeFinset hitem he
  refine ⟨⟨e, heG⟩, ?_⟩
  simpa [incidence, he] using one_div_pos.mpr (gain_pos G K)

/-- Convert a gain-weighted packing coordinate into the unit-objective mass
of its item column. -/
noncomputable def normalizedMass (x : FracPacking G ℝ) (K : ItemIdx G) : ℝ :=
  gainF ℝ K.1 * x.weight K.1

lemma normalizedMass_nonneg (x : FracPacking G ℝ) (K : ItemIdx G) :
    0 ≤ normalizedMass G x K :=
  mul_nonneg (gain_pos G K).le (x.weight_nonneg K.1)

/-- One normalized matrix entry times its mass is exactly the original edge
load contribution. -/
lemma incidence_mul_normalizedMass (x : FracPacking G ℝ) (e : EdgeIdx G) (K : ItemIdx G) :
    incidence G e K * normalizedMass G x K =
      if e.1 ∈ pairs K.1 then x.weight K.1 else 0 := by
  unfold incidence normalizedMass
  by_cases h : e.1 ∈ pairs K.1
  · simp only [if_pos h]
    have hne : gainF ℝ K.1 ≠ 0 := (gain_pos G K).ne'
    field_simp [hne]
  · simp [h]

/-- A literal real fractional packing becomes feasible for the normalized
finite matrix. -/
theorem normalizedMass_feasible (x : FracPacking G ℝ) (e : EdgeIdx G) :
    ∑ K : ItemIdx G, incidence G e K * normalizedMass G x K ≤ 1 := by
  calc
    ∑ K : ItemIdx G, incidence G e K * normalizedMass G x K =
        ∑ K : ItemIdx G, (if e.1 ∈ pairs K.1 then x.weight K.1 else 0) :=
      Finset.sum_congr rfl (fun K _ => incidence_mul_normalizedMass G x e K)
    _ = ∑ K ∈ items G, (if e.1 ∈ pairs K then x.weight K else 0) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach (items G) (fun K => if e.1 ∈ pairs K then x.weight K else 0))
    _ ≤ 1 := x.capacity e.1 e.2

/-- The unit objective of the finite matrix is literally the original
gain-weighted mixed-packing value. -/
theorem sum_normalizedMass_eq_value (x : FracPacking G ℝ) :
    ∑ K : ItemIdx G, normalizedMass G x K = x.value := by
  exact Finset.sum_attach (items G) (fun K => gainF ℝ K * x.weight K)

/-- Recover a gain-weighted real packing from a feasible vector of normalized
item masses. -/
noncomputable def packingOfNormalized (w : ItemIdx G → ℝ)
    (hw0 : ∀ K, 0 ≤ w K)
    (hwcap : ∀ e : EdgeIdx G, ∑ K, incidence G e K * w K ≤ 1) :
    FracPacking G ℝ where
  weight K := if h : K ∈ items G then w ⟨K, h⟩ / gainF ℝ K else 0
  weight_nonneg K := by
    split_ifs with h
    · exact div_nonneg (hw0 _) (gain_pos G ⟨K, h⟩).le
    · exact le_rfl
  capacity e he := by
    change (∑ K ∈ items G,
      (if e ∈ pairs K then (if h : K ∈ items G then w ⟨K, h⟩ / gainF ℝ K else 0) else 0)) ≤ 1
    calc
      (∑ K ∈ items G,
        (if e ∈ pairs K then (if h : K ∈ items G then w ⟨K, h⟩ / gainF ℝ K else 0) else 0)) =
          ∑ K : ItemIdx G, incidence G ⟨e, he⟩ K * w K := by
        rw [← Finset.sum_attach]
        apply Finset.sum_congr rfl
        intro K _
        unfold incidence
        by_cases h : e ∈ pairs K.1
        · simp [K.2, h, div_eq_mul_inv]
          ring
        · simp [K.2, h]
      _ ≤ 1 := hwcap ⟨e, he⟩

theorem packingOfNormalized_value (w : ItemIdx G → ℝ)
    (hw0 : ∀ K, 0 ≤ w K)
    (hwcap : ∀ e : EdgeIdx G, ∑ K, incidence G e K * w K ≤ 1) :
    (packingOfNormalized G w hw0 hwcap).value = ∑ K, w K := by
  unfold packingOfNormalized FracPacking.value
  calc
    (∑ K ∈ items G, gainF ℝ K *
      (if h : K ∈ items G then w ⟨K, h⟩ / gainF ℝ K else 0)) =
        ∑ K : ItemIdx G, gainF ℝ K.1 * (w K / gainF ℝ K.1) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro K _
      simp [K.2]
    _ = ∑ K : ItemIdx G, w K := by
      apply Finset.sum_congr rfl
      intro K _
      have hne : gainF ℝ K.1 ≠ 0 := (gain_pos G K).ne'
      field_simp [hne]

/-- The literal mixed `K₃/K₄` fractional LP has an attained optimum over the
reals.  This closes the analytic/maximization half of M02; it deliberately
does not claim that the optimum has rational coordinates. -/
theorem exists_real_optimal_packing :
    ∃ x : FracPacking G ℝ, ∀ z : FracPacking G ℝ, z.value ≤ x.value := by
  obtain ⟨w, hw0, hwcap, hwmax⟩ :=
    FiniteLP.covering_packing_primal_optimum (incidence G) (fun _ : EdgeIdx G => 1)
      (fun e K => incidence_nonneg G e K) (fun _ => by norm_num)
      (fun K => exists_incidence_pos G K)
  let x : FracPacking G ℝ := packingOfNormalized G w hw0 hwcap
  refine ⟨x, ?_⟩
  intro z
  have hz0 : ∀ K : ItemIdx G, 0 ≤ normalizedMass G z K :=
    fun K => normalizedMass_nonneg G z K
  have hzcap : ∀ e : EdgeIdx G,
      ∑ K, incidence G e K * normalizedMass G z K ≤ 1 :=
    fun e => normalizedMass_feasible G z e
  have hmax := hwmax (fun K => normalizedMass G z K) hz0 hzcap
  calc
    z.value = ∑ K, normalizedMass G z K := (sum_normalizedMass_eq_value G z).symm
    _ ≤ ∑ K, w K := hmax
    _ = x.value := (packingOfNormalized_value G w hw0 hwcap).symm

/-- A real fractional packing attains the mixed LP optimum. -/
def IsRealOptimal (x : FracPacking G ℝ) : Prop :=
  ∀ z : FracPacking G ℝ, z.value ≤ x.value

theorem packing_gain_le_of_realOptimal {x : FracPacking G ℝ} (hx : IsRealOptimal G x)
    (P : Packing G) : (P.gain : ℝ) ≤ x.value := by
  have h := hx (P.toFrac (F := ℝ))
  rwa [Packing.toFrac_value] at h

theorem exists_realOptimal : ∃ x : FracPacking G ℝ, IsRealOptimal G x := by
  obtain ⟨x, hx⟩ := exists_real_optimal_packing G
  exact ⟨x, hx⟩

end PaperIV.FarRoundingRealLP
