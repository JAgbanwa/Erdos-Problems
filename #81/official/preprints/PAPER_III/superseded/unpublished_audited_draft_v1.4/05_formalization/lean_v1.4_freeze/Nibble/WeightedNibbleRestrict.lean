/-
# Nibble — the weighted nibble on a sub-region of the vertex set

`Nibble.fracNibble_weightedCodegree` asks the fractional matching to be near-perfect at all but an
`η`-fraction of *all* vertices.  Frequently the interesting weight lives on a small part `R` of the
vertex set, the remaining vertices carrying no weight at all — and then the global `η`-condition is
unusable.  This file removes it by transporting the whole statement to the subtype `↥R`:

* `Nibble.fracNibble_weightedCodegree_on` — if every edge of `H` lies inside `R` and the fractional
  matching is near-perfect at all but an `η`-fraction of the vertices **of `R`**, then `H` has a
  matching of size at least `(1-β)∑w`.  Vertices outside `R` are unconstrained, and there is still
  no hypothesis on the degrees or codegrees of `H`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WeightedSpreadNibble

open Finset Hypergraph

namespace Nibble

/-- **The weighted nibble localised to a region `R` of the vertex set.**  Only the vertices of `R`
— those that the hypergraph actually uses — have to be nearly saturated by `w`. -/
theorem fracNibble_weightedCodegree_on (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (R Exc : Finset W),
        IsUniform H r →
        (∀ T ∈ H, T ⊆ R) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ v : W, v ∈ R → v ∉ Exc → 1 - γ ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (R.card : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((R.card : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ, hγ, η, hη, hmain⟩ := fracNibble_weightedCodegree r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H w R Exc hunif hsubR hwnn hvle hvge hExc hcod
  haveI : Fintype {x : W // x ∈ R} := FinsetCoe.fintype R
  set em : {x : W // x ∈ R} ↪ W := Function.Embedding.subtype (fun x => x ∈ R) with hem
  set proj : Finset W → Finset {x : W // x ∈ R} := fun T => T.subtype (fun x => x ∈ R) with hproj
  set H' : Finset (Finset {x : W // x ∈ R}) := H.image proj with hH'
  set w' : Finset {x : W // x ∈ R} → ℝ := fun T' => w (T'.map em) with hw'
  -- the projection is a bijection between `H` and `H'`
  have hmap : ∀ T ∈ H, (proj T).map em = T := by
    intro T hT
    exact Finset.subtype_map_of_mem (fun x hx => hsubR T hT hx)
  have hinjOn : Set.InjOn proj ↑H := by
    intro T hT T' hT' heq
    rw [← hmap T hT, ← hmap T' hT', heq]
  have hw'proj : ∀ T ∈ H, w' (proj T) = w T := by
    intro T hT; rw [hw']; simp only; rw [hmap T hT]
  -- membership in `H'`
  have hmemH' : ∀ T' ∈ H', (T'.map em) ∈ H ∧ T' = proj (T'.map em) := by
    intro T' hT'
    rw [hH', Finset.mem_image] at hT'
    obtain ⟨T, hT, rfl⟩ := hT'
    rw [hmap T hT]
    exact ⟨hT, rfl⟩
  -- uniformity is preserved
  have hunif' : IsUniform H' r := by
    intro T' hT'
    obtain ⟨hmemT, hTeq⟩ := hmemH' T' hT'
    have h1 : (T'.map em).card = T'.card := Finset.card_map em
    rw [← h1]
    exact hunif _ hmemT
  -- the vertex sums agree
  have hfilter : ∀ (Q : Finset W → Prop) [DecidablePred Q],
      H'.filter (fun T' => Q (T'.map em)) = (H.filter Q).image proj := by
    intro Q _
    rw [hH', Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro T hT
    rw [hmap T hT]
  have hsumfilter : ∀ (Q : Finset W → Prop) [DecidablePred Q],
      ∑ T' ∈ H'.filter (fun T' => Q (T'.map em)), w' T' = ∑ T ∈ H.filter Q, w T := by
    intro Q _
    rw [hfilter Q, Finset.sum_image (fun a ha b hb h => hinjOn (Finset.mem_coe.mpr
      (Finset.mem_filter.mp ha).1) (Finset.mem_coe.mpr (Finset.mem_filter.mp hb).1) h)]
    exact Finset.sum_congr rfl (fun T hT => hw'proj T (Finset.mem_filter.mp hT).1)
  have hvle' : ∀ v : {x : W // x ∈ R},
      ∑ T' ∈ H'.filter (fun T' => v ∈ T'), w' T' ≤ 1 := by
    intro v
    have heq : H'.filter (fun T' => v ∈ T') = H'.filter (fun T' => (v : W) ∈ T'.map em) := by
      refine Finset.filter_congr ?_
      intro T' _
      simp [hem]
    rw [heq, hsumfilter (fun T => (v : W) ∈ T)]
    exact hvle (v : W)
  set Exc' : Finset {x : W // x ∈ R} := Exc.subtype (fun x => x ∈ R) with hExc'
  have hvge' : ∀ v : {x : W // x ∈ R}, v ∉ Exc' →
      1 - γ ≤ ∑ T' ∈ H'.filter (fun T' => v ∈ T'), w' T' := by
    intro v hv
    have hvExc : (v : W) ∉ Exc := by
      intro hcon
      exact hv (Finset.mem_subtype.mpr hcon)
    have heq : H'.filter (fun T' => v ∈ T') = H'.filter (fun T' => (v : W) ∈ T'.map em) := by
      refine Finset.filter_congr ?_
      intro T' _
      simp [hem]
    rw [heq, hsumfilter (fun T => (v : W) ∈ T)]
    exact hvge (v : W) v.2 hvExc
  have hcod' : ∀ x z : {x : W // x ∈ R}, x ≠ z →
      ∑ T' ∈ H'.filter (fun T' => x ∈ T' ∧ z ∈ T'), w' T' ≤ γ := by
    intro x z hxz
    have hxz' : (x : W) ≠ (z : W) := fun h => hxz (Subtype.ext h)
    have heq : H'.filter (fun T' => x ∈ T' ∧ z ∈ T')
        = H'.filter (fun T' => (x : W) ∈ T'.map em ∧ (z : W) ∈ T'.map em) := by
      refine Finset.filter_congr ?_
      intro T' _
      simp [hem]
    rw [heq, hsumfilter (fun T => (x : W) ∈ T ∧ (z : W) ∈ T)]
    exact hcod (x : W) (z : W) hxz'
  have hExccard : (Exc'.card : ℝ) ≤ η * (Fintype.card {x : W // x ∈ R} : ℝ) := by
    have h1 : Exc'.card ≤ Exc.card := by
      have h2 : (Exc'.map em) ⊆ Exc := by
        intro a ha
        rw [Finset.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact Finset.mem_subtype.mp hb
      have h3 : (Exc'.map em).card = Exc'.card := Finset.card_map em
      rw [← h3]
      exact Finset.card_le_card h2
    have h4 : (Fintype.card {x : W // x ∈ R} : ℝ) = (R.card : ℝ) := by
      rw [Fintype.card_coe]
    rw [h4]
    exact le_trans (by exact_mod_cast h1) hExc
  have hwnn' : ∀ T' : Finset {x : W // x ∈ R}, 0 ≤ w' T' := fun T' => hwnn _
  obtain ⟨M', hM', hM'cover, hM'card⟩ := hmain H' w' Exc' hunif' hwnn' hvle' hvge' hExccard hcod'
  -- transport the matching back
  refine ⟨M'.image (fun T' => T'.map em), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨T', hT', rfl⟩ := hT
    exact (hmemH' T' (hM'.subset hT')).1
  · intro e he f hf hef
    rw [Finset.mem_image] at he hf
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨f', hf', rfl⟩ := hf
    have hne : e' ≠ f' := fun h => hef (by rw [h])
    exact (Finset.disjoint_map em).mpr (hM'.disjoint e' he' f' hf' hne)
  · have hcard : (M'.image (fun T' => T'.map em)).card = M'.card :=
      Finset.card_image_of_injective _ (Finset.map_injective em)
    have hRcard : (Fintype.card {x : W // x ∈ R} : ℝ) = (R.card : ℝ) := by rw [Fintype.card_coe]
    rw [hcard, ← hRcard]
    exact hM'cover
  · have hcard : (M'.image (fun T' => T'.map em)).card = M'.card :=
      Finset.card_image_of_injective _ (Finset.map_injective em)
    have hsum : ∑ T' ∈ H', w' T' = ∑ T ∈ H, w T := by
      rw [hH', Finset.sum_image (fun a ha b hb h => hinjOn ha hb h)]
      exact Finset.sum_congr rfl (fun T hT => hw'proj T hT)
    rw [hcard, ← hsum]
    exact hM'card

/-- **The weighted nibble at an arbitrary load level `c`.**  The fractional matching no longer has
to saturate the vertices: it suffices that all loads `∑_{T ∋ v} w T` lie in `[(1-γ)c, c]` for a
common level `c ∈ (0, 1]` (outside an `η`-fraction exceptional set of `R`), the weighted codegrees
being at most `γc`.  Rescaling `w` by `1/c` turns this into
`Nibble.fracNibble_weightedCodegree_on`, and the conclusion only improves because `c ≤ 1`. -/
theorem fracNibble_weightedCodegree_on_scaled (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (R Exc : Finset W) (c : ℝ),
        0 < c → c ≤ 1 →
        IsUniform H r →
        (∀ T ∈ H, T ⊆ R) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ c) →
        (∀ v : W, v ∈ R → v ∉ Exc → (1 - γ) * c ≤ ∑ T ∈ H.filter (fun T => v ∈ T), w T) →
        (Exc.card : ℝ) ≤ η * (R.card : ℝ) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ * c) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((R.card : ℝ) / r) ≤ (M.card : ℝ) ∧
          (1 - β) * (∑ T ∈ H, w T) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ, hγ, η, hη, hmain⟩ := fracNibble_weightedCodegree_on r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H w R Exc c hc hc1 hunif hsubR hwnn hvle hvge hExc hcod
  -- rescale the weighting to load level `1`
  set w' : Finset W → ℝ := fun T => w T / c with hw'
  have hdiv : ∀ (A : Finset (Finset W)), ∑ T ∈ A, w' T = (∑ T ∈ A, w T) / c := by
    intro A; rw [hw', ← Finset.sum_div]
  obtain ⟨M, hM, hMcover, hMcard⟩ := hmain H w' R Exc hunif hsubR (fun T => by
      rw [hw']; exact div_nonneg (hwnn T) hc.le)
    (fun v => by
      rw [hdiv, div_le_one hc]
      exact hvle v)
    (fun v hvR hvE => by
      rw [hdiv, le_div_iff₀ hc]
      exact hvge v hvR hvE)
    hExc
    (fun x z hxz => by
      rw [hdiv, div_le_iff₀ hc]
      exact hcod x z hxz)
  refine ⟨M, hM, hMcover, ?_⟩
  rw [hdiv] at hMcard
  have hnn : 0 ≤ ∑ T ∈ H, w T := Finset.sum_nonneg (fun T _ => hwnn T)
  rcases le_or_gt β 1 with h1 | h1
  · have hmono : (∑ T ∈ H, w T) ≤ (∑ T ∈ H, w T) / c := by
      rw [le_div_iff₀ hc]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hmono (by linarith)) hMcard
  · have hle0 : (1 - β) * (∑ T ∈ H, w T) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
    exact le_trans hle0 (Nat.cast_nonneg _)

end Nibble
