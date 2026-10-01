import PaperIV.PatternPoolGeometry
import PaperIV.RC01CleanFiber
import PaperIV.RC01Candidates
import PaperIV.PartitionBridge

/-!
# RC01: regular counting in the physical `t^3` / `t^4` scale

`PatternPoolGeometry` proves the lower counting lemma in its natural form.
The cleaned RC01 gate consumes the same estimate with the physical pair scale
`D = t^2` already exposed.  This file is the small, but important, typed
adapter between those two statements.

No rounding statement is assumed here.  The only input is the literal
regularity certificate and density lower bounds on the three or six pairs.
-/

namespace PaperIV.RC01RegularVolume

open PaperIV.PatternCounting
open PaperIV.PatternPoolGeometry
open PaperIV.RegularityFormat
open PaperIV.RC01Candidates
open PaperIV.RC01CleanFiber
open PaperIV.PartitionBridge
open PaperIV.FarRounding

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The cubic reference volume required by the cleaned `K3` gate follows
directly from the regular counting lemma. -/
theorem k3_budget_volume_of_regular {δ d₀ u : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 ≤ u)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK3, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK3, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ)
      ≤ (1 + u) * patCount G V patK3 := by
  have hcount := patCount_K3_ge hδ hd₀ R V hV hVne hgood hdens
  have hnonneg : 0 ≤ patCount G V patK3 := by
    rw [patCount_eq_card]
    positivity
  calc
    (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ)
        = (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 3 := by ring
    _ ≤ patCount G V patK3 := hcount
    _ ≤ (1 + u) * patCount G V patK3 := by
      nlinarith [mul_nonneg hu hnonneg]

/-- The quartic reference volume required by the cleaned `K4` gate follows
directly from the regular counting lemma. -/
theorem k4_budget_volume_of_regular {δ d₀ u : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 ≤ u)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK4, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK4, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2
      ≤ (1 + u) * patCount G V patK4 := by
  have hcount := patCount_K4_ge hδ hd₀ R V hV hVne hgood hdens
  have hnonneg : 0 ≤ patCount G V patK4 := by
    rw [patCount_eq_card]
    positivity
  calc
    (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2
        = (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 4 := by ring
    _ ≤ patCount G V patK4 := hcount
    _ ≤ (1 + u) * patCount G V patK4 := by
      nlinarith [mul_nonneg hu hnonneg]

/-- Positivity of the literal `K3` reference count in the non-vacuous
counting regime. -/
theorem patCount_K3_pos_of_regular {δ d₀ : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hcoef : 0 < d₀ ^ 3 - 3 * δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK3, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK3, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    0 < patCount G V patK3 := by
  have hcount := patCount_K3_ge hδ hd₀ R V hV hVne hgood hdens
  have hsize : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
  exact lt_of_lt_of_le (mul_pos hcoef (pow_pos hsize 3)) hcount

/-- Positivity of the literal `K4` reference count in the non-vacuous
counting regime. -/
theorem patCount_K4_pos_of_regular {δ d₀ : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hcoef : 0 < d₀ ^ 6 - 6 * δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts)
    (hVne : ∀ e ∈ patK4, V e.1 ≠ V e.2)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK4, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    0 < patCount G V patK4 := by
  have hcount := patCount_K4_ge hδ hd₀ R V hV hVne hgood hdens
  have hsize : (0 : ℚ) < R.size := by exact_mod_cast R.size_pos
  exact lt_of_lt_of_le (mul_pos hcoef (pow_pos hsize 4)) hcount

/-! ## From indexed transversal copies to the coordinate-free profile fibre -/

/-- The reduced pattern represented by an indexed family of regularity parts. -/
noncomputable def regularPattern {ι : Type*} [Fintype ι]
    (V : ι → Finset α) : Finset (Option (Finset α)) :=
  Finset.univ.image (fun i => some (V i))

/-- A transversal copy has exactly the coordinate-free profile represented by
its indexed family of parts. -/
theorem image_partOf_piece_eq_regularPattern {ι : Type*}
    [Fintype ι] [DecidableEq ι] {δ : ℚ}
    (R : EqualRegularity G δ) (V : ι → Finset α)
    (hV : ∀ i, V i ∈ R.parts) {F : Finset (ι × ι)} {φ : ι → α}
    (hφ : φ ∈ transversal G V F) :
    (piece φ).image (partOf R) = regularPattern V := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨i, hi⟩ := mem_piece.1 ha
    have hpart := partOf_eq_some R (hV i) ((mem_transversal.1 hφ).1 i)
    rw [← hi, hpart]
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  · intro hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    refine Finset.mem_image.2 ⟨φ i, apply_mem_piece φ i, ?_⟩
    exact partOf_eq_some R (hV i) ((mem_transversal.1 hφ).1 i)

/-- Distinct indexed parts give a reduced pattern with exactly the expected
number of vertices. -/
theorem card_regularPattern {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Finset α) (hVne : Function.Injective V) :
    (regularPattern V).card = Fintype.card ι := by
  classical
  rw [regularPattern, Finset.card_image_of_injective, Finset.card_univ]
  intro i j hij
  exact hVne (Option.some.inj hij)

/-- Literal `K3` transversal candidates are contained in the coordinate-free
profile fibre used by the cleaned RC01 gate. -/
theorem candidates_K3_subset_profileFiber {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V) :
    candidates G V patK3 ⊆ profileFiber G (partOf R) (regularPattern V) := by
  intro K hK
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (fun h => hij (hVne h))
  refine mem_profileFiber.2 ⟨mem_items.2 (candidates_K3_isItem hdisj hK), ?_, ?_⟩
  · exact image_partOf_piece_eq_regularPattern R V hV hφ
  · rw [card_piece hdisj (mem_transversal.1 hφ).1,
      card_regularPattern V hVne]

/-- Literal `K4` transversal candidates are contained in the coordinate-free
profile fibre used by the cleaned RC01 gate. -/
theorem candidates_K4_subset_profileFiber {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V) :
    candidates G V patK4 ⊆ profileFiber G (partOf R) (regularPattern V) := by
  intro K hK
  obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hK
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (fun h => hij (hVne h))
  refine mem_profileFiber.2 ⟨mem_items.2 (candidates_K4_isItem hdisj hK), ?_, ?_⟩
  · exact image_partOf_piece_eq_regularPattern R V hV hφ
  · rw [card_piece hdisj (mem_transversal.1 hφ).1,
      card_regularPattern V hVne]

/-- The regular `K3` count is a genuine lower reference volume for the
coordinate-free profile fibre. -/
theorem patCount_K3_le_profileFiber {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V) :
    patCount G V patK3
      ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) := by
  have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (fun h => hij (hVne h))
  have hcard := Finset.card_le_card (candidates_K3_subset_profileFiber R V hV hVne)
  have hcast : ((candidates G V patK3).card : ℚ)
      ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) := by
    exact_mod_cast hcard
  rwa [card_candidates_eq_patCount hdisj] at hcast

/-- The regular `K4` count is a genuine lower reference volume for the
coordinate-free profile fibre. -/
theorem patCount_K4_le_profileFiber {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V) :
    patCount G V patK4
      ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) := by
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (fun h => hij (hVne h))
  have hcard := Finset.card_le_card (candidates_K4_subset_profileFiber R V hV hVne)
  have hcast : ((candidates G V patK4).card : ℚ)
      ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) := by
    exact_mod_cast hcard
  rwa [card_candidates_eq_patCount hdisj] at hcast

/-- The three volume obligations of the cleaned `K3` gate, bundled for one
literal regular triple with `vol = patCount`. -/
theorem exists_k3_regular_reference {δ d₀ u : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 ≤ u)
    (hcoef : 0 < d₀ ^ 3 - 3 * δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V)
    (hgood : ∀ e ∈ patK3, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK3, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    ∃ vol : ℚ,
      0 < vol ∧
      vol ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) ∧
      (d₀ ^ 3 - 3 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ)
        ≤ (1 + u) * vol := by
  refine ⟨patCount G V patK3,
    patCount_K3_pos_of_regular hδ hd₀ hcoef R V hV
      (fun e he hEq => patK3_ne e he (hVne hEq)) hgood hdens,
    patCount_K3_le_profileFiber R V hV hVne, ?_⟩
  exact k3_budget_volume_of_regular hδ hd₀ hu R V hV
    (fun e he hEq => patK3_ne e he (hVne hEq)) hgood hdens

/-- The three volume obligations of the cleaned `K4` gate, bundled for one
literal regular quadruple with `vol = patCount`. -/
theorem exists_k4_regular_reference {δ d₀ u : ℚ}
    (hδ : 0 ≤ δ) (hd₀ : 0 ≤ d₀) (hu : 0 ≤ u)
    (hcoef : 0 < d₀ ^ 6 - 6 * δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVne : Function.Injective V)
    (hgood : ∀ e ∈ patK4, (V e.1, V e.2) ∉ R.bad)
    (hdens : ∀ e ∈ patK4, d₀ ≤ G.edgeDensity (V e.1) (V e.2)) :
    ∃ vol : ℚ,
      0 < vol ∧
      vol ≤ ((profileFiber G (partOf R) (regularPattern V)).card : ℚ) ∧
      (d₀ ^ 6 - 6 * δ) * (R.size : ℚ) ^ 2 * (R.size : ℚ) ^ 2
        ≤ (1 + u) * vol := by
  refine ⟨patCount G V patK4,
    patCount_K4_pos_of_regular hδ hd₀ hcoef R V hV
      (fun e he hEq => patK4_ne e he (hVne hEq)) hgood hdens,
    patCount_K4_le_profileFiber R V hV hVne, ?_⟩
  exact k4_budget_volume_of_regular hδ hd₀ hu R V hV
    (fun e he hEq => patK4_ne e he (hVne hEq)) hgood hdens

end PaperIV.RC01RegularVolume
