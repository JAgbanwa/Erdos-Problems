/-
# Nibble — the weighted nibble for *spread* fractional matchings

The library's nibble `Nibble.nibbleTheoremMostCeil_holds` consumes a *near-regular* hypergraph.  A
hypergraph carrying a perfect fractional matching need not be near-regular at all.  This file
bridges the two in the regime where the fractional matching is **spread**, i.e. no single hyperedge
carries more than a small constant weight `δ`:

> for every `β > 0` there are `δ, γ, η > 0` such that every `3`-uniform hypergraph of codegree `≤ 1`
> carrying a fractional matching with all weights `≤ δ`, supported on a vertex set `R` missing at
> most an `η`-fraction of the vertices and covering every vertex of `R` to level at least `1 - γ`,
> has a matching covering all but a `β`-fraction of *all* the vertices.

The bridge is *deterministic*: the Beck–Fiala rounding `Nibble.BeckFiala.exists_rounding` turns the
fractional selection `y = D·w` (whose fractional degree is `≈ D` at every vertex of `R` and `0`
elsewhere) into an integral subhypergraph `S ⊆ H` whose degrees are all within `3` of that profile —
i.e. a nearly `D`-regular subhypergraph on `R` with codegree `≤ 1`, which is precisely the nibble's
input once `D` is large.

* `Nibble.IsSpreadFracMatchingOn` — a fractional matching with weights `≤ δ`, supported on `R` and
  covering every vertex of `R` to level in `[1-γ, 1]`.
* `Nibble.exists_nearRegular_sub_of_spread` — the Beck–Fiala regularization step.
* `Nibble.exists_matching_of_spread` — the weighted nibble for spread fractional matchings.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.BeckFiala
import Nibble.TightNibble

open Finset Hypergraph

namespace Nibble

/-- A **spread fractional matching, near-perfect on `R`**: nonnegative weights bounded by `δ`,
under which every vertex has total weight at most `1` and every vertex of `R` has total weight at
least `1 - γ`. -/
def IsSpreadFracMatchingOn {V : Type} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (w : Finset V → ℝ) (δ γ : ℝ) (R : Finset V) : Prop :=
  (∀ t ∈ H, 0 ≤ w t ∧ w t ≤ δ) ∧ (∀ x : V, ∑ t ∈ H.filter (fun t => x ∈ t), w t ≤ 1) ∧
    ∀ x ∈ R, 1 - γ ≤ ∑ t ∈ H.filter (fun t => x ∈ t), w t

/-- **Beck–Fiala regularization.**  If `H` carries a fractional matching with all weights at most
`1/D` covering every vertex to level at most `1` and every vertex of `R` to level at least `1 - γ`,
then `H` has a subhypergraph whose degrees lie in `[(1-γ)D - r, D + r]` on `R` and are at most
`D + r` everywhere. -/
theorem exists_nearRegular_sub_of_spread {V : Type} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (w : Finset V → ℝ) (R : Finset V) (D r : ℕ) (γ : ℝ) (hD : 0 < D)
    (hunif : IsUniform H r) (hw : IsSpreadFracMatchingOn H w (1 / (D : ℝ)) γ R) :
    ∃ S ⊆ H, (∀ x ∈ R, (1 - γ) * (D : ℝ) - r ≤ (degree S x : ℝ)) ∧
      (∀ x : V, (degree S x : ℝ) ≤ (D : ℝ) + r) := by
  classical
  obtain ⟨hwb, hwle, hwsum⟩ := hw
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  set y : Finset V → ℝ := fun t => (D : ℝ) * w t with hydef
  have hy0 : ∀ t ∈ H, 0 ≤ y t := fun t ht => mul_nonneg hDR.le (hwb t ht).1
  have hy1 : ∀ t ∈ H, y t ≤ 1 := by
    intro t ht
    have h := (hwb t ht).2
    rw [hydef]
    calc (D : ℝ) * w t ≤ (D : ℝ) * (1 / (D : ℝ)) := mul_le_mul_of_nonneg_left h hDR.le
      _ = 1 := by field_simp
  have hk : ∀ t ∈ H, t.card ≤ r := fun t ht => le_of_eq (hunif t ht)
  obtain ⟨S, hSH, -, -, hbound⟩ := BeckFiala.exists_rounding r H hk y hy0 hy1
  have hfrac : ∀ x : V, ∑ t ∈ H.filter (fun t => x ∈ t), y t
      = (D : ℝ) * ∑ t ∈ H.filter (fun t => x ∈ t), w t := by
    intro x; rw [hydef, ← Finset.mul_sum]
  have hdeg : ∀ x : V, ((S.filter (fun t => x ∈ t)).card : ℝ) = (degree S x : ℝ) := by
    intro x; simp [degree]
  refine ⟨S, hSH, ?_, ?_⟩
  · intro x hx
    have h := (abs_le.mp (hbound x)).1
    rw [hfrac x, hdeg x] at h
    have hprod : (D : ℝ) * (1 - γ) ≤ (D : ℝ) * ∑ t ∈ H.filter (fun t => x ∈ t), w t :=
      mul_le_mul_of_nonneg_left (hwsum x hx) hDR.le
    nlinarith [hprod]
  · intro x
    have h := (abs_le.mp (hbound x)).2
    rw [hfrac x, hdeg x] at h
    have hprod2 : (D : ℝ) * ∑ t ∈ H.filter (fun t => x ∈ t), w t ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (hwle x) hDR.le
    nlinarith [hprod2]

/-- **The weighted nibble for spread fractional matchings.**  For every `r ≥ 2` and `β > 0` there
are `δ, γ, η > 0` such that every `r`-uniform hypergraph with codegree at most `1` carrying a
fractional
matching with all weights at most `δ`, covering every vertex to level at most `1` and every vertex
of a set `R` whose complement has at most `η|V|` vertices to level at least `1 - γ`, has a matching
covering all but a `β`-fraction of the vertices. -/
theorem exists_matching_of_spread (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V]
        (H : Finset (Finset V)) (w : Finset V → ℝ) (R : Finset V),
      IsUniform H r → (∀ x y : V, x ≠ y → (codegree H x y : ℝ) ≤ 1) →
      IsSpreadFracMatchingOn H w δ γ R →
      ((Finset.univ \ R).card : ℝ) ≤ η * (Fintype.card V : ℝ) →
      ∃ M : Finset (Finset V), IsMatching H M ∧
        (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, hmain⟩ := nibbleTheoremMostCeil_holds r hr β hβ
  set K : ℕ := ⌈(2 * (r : ℝ) + 2) / μ⌉₊ with hKdef
  set D : ℕ := max ⌈d₀⌉₊ K + 1 with hDdef
  have hDpos : 0 < D := Nat.succ_pos _
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hd₀D : d₀ ≤ (D : ℝ) := by
    have h1 : (⌈d₀⌉₊ : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : ⌈d₀⌉₊ ≤ D)
    exact le_trans (Nat.le_ceil _) h1
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hμD : 2 * (r : ℝ) + 2 ≤ μ * (D : ℝ) := by
    have h1 : ((2 * (r : ℝ) + 2) / μ) ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil _
    have h2 : (K : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : K ≤ D)
    have h3 : ((2 * (r : ℝ) + 2) / μ) ≤ (D : ℝ) := le_trans h1 h2
    rw [div_le_iff₀ hμ] at h3
    linarith
  refine ⟨1 / (D : ℝ), by positivity, μ / 2, by positivity, η, hη, ?_⟩
  intro V _ _ H w R hunif hcod hw hRsmall
  obtain ⟨S, hSH, hSdegR, hSceil⟩ :=
    exists_nearRegular_sub_of_spread H w R D r (μ / 2) hDpos hunif hw
  have hSunif : IsUniform S r := fun t ht => hunif t (hSH ht)
  have hceil : ∀ x : V, (degree S x : ℝ) ≤ (1 + μ) * (D : ℝ) := by
    intro x
    have h := hSceil x
    nlinarith [hμD, hμ.le, hDR.le]
  have hdegR : ∀ x ∈ R, (1 - μ) * (D : ℝ) ≤ (degree S x : ℝ) ∧
      (degree S x : ℝ) ≤ (1 + μ) * (D : ℝ) := by
    intro x hx
    refine ⟨?_, hceil x⟩
    have hlow := hSdegR x hx
    nlinarith [hμD, hμ.le, hDR.le]
  have hreg : NearlyRegularMost S (D : ℝ) μ η := by
    refine ⟨Finset.univ \ R, hRsmall, fun v hv => ?_⟩
    have hvR : v ∈ R := by
      by_contra hcon
      exact hv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hcon⟩)
    exact hdegR v hvR
  have hScod : CodegreeBounded S (μ * (D : ℝ)) := by
    intro x y hxy
    have hmono : codegree S x y ≤ codegree H x y :=
      Finset.card_le_card (Finset.filter_subset_filter _ hSH)
    have h1 : (codegree S x y : ℝ) ≤ (codegree H x y : ℝ) := by exact_mod_cast hmono
    have h2 := hcod x y hxy
    linarith
  obtain ⟨M, hM, hMcard⟩ := hmain S (D : ℝ) hDR hd₀D hSunif hreg hScod hceil
  exact ⟨M, ⟨Finset.Subset.trans hM.subset hSH, hM.disjoint⟩, by simpa using hMcard⟩

end Nibble
