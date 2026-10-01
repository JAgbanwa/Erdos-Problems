import PaperIV.TrianglePairingDefs

/-!
# RC01: the quantitative side of the triangle pairing

Everything the reduction needs about the merged system `pairFam H₃` with the coupling weight
`pairWeight H₃ w t`, where `t = ∑_{T ∈ H₃} w T` is the total triangle mass:

* `pairWeight_nonneg` — the merged weight is a weight;
* `pairs_load_le`, `pairs_load_ge` — the merged load at a resource is the triangle load, up to
  the absolute error `3/t`.  In particular merging **does not increase** any load, so the
  capacity hypothesis of the nibble survives, and it decreases it by at most `3/t`, so the
  near-perfect hypothesis survives as well;
* `pairs_mass_ge`, `pairs_mass_le` — the merged mass is `t/2` up to `3/2`; each merged
  hyperedge is unfolded back into **two** triples, which is what restores the factor;
* `pairs_codeg_le` — the merged weighted codegree exceeds the triangle weighted codegree by at
  most `1/t`.

The constant `3` is `3 = |S|`: the `w`-mass of the triples meeting a fixed triple `S` is at
most the sum of the three loads at its resources (`mass_meeting_le`).
-/

namespace PaperIV.TrianglePairingSums

open Finset
open PaperIV.TrianglePairingDefs

variable {W : Type*} [DecidableEq W]

/-! ## 1. Reindexing the pair domain -/

/-- Summing over resource-disjoint ordered pairs is an iterated sum. -/
theorem sum_dom_eq (A B : Finset (Finset W)) (f : Finset W × Finset W → ℝ) :
    ∑ q ∈ (A ×ˢ B).filter (fun q => Disjoint q.1 q.2), f q
      = ∑ S ∈ A, ∑ S' ∈ B.filter (fun S' => Disjoint S S'), f (S, S') := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun S _ => by rw [Finset.sum_filter]

/-- Filtering the pair domain by properties of the two coordinates. -/
theorem pairDom_filter_both (H₃ : Finset (Finset W)) (p q : Finset W → Prop)
    [DecidablePred p] [DecidablePred q] :
    (pairDom H₃).filter (fun r => p r.1 ∧ q r.2)
      = ((H₃.filter p) ×ˢ (H₃.filter q)).filter (fun r => Disjoint r.1 r.2) := by
  classical
  ext r
  simp only [pairDom, Finset.mem_filter, Finset.mem_product]
  tauto

/-- The coupling sum with both coordinates constrained, as an iterated sum. -/
theorem sum_pairY_both (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ)
    (p q : Finset W → Prop) [DecidablePred p] [DecidablePred q] :
    ∑ r ∈ (pairDom H₃).filter (fun r => p r.1 ∧ q r.2), pairY w t r
      = ∑ S ∈ H₃.filter p, ∑ S' ∈ (H₃.filter q).filter (fun S' => Disjoint S S'),
          w S * w S' / t := by
  classical
  rw [pairDom_filter_both, sum_dom_eq]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => rfl

/-- A product upper bound for the coupling sum. -/
theorem sum_pairY_both_le (H₃ : Finset (Finset W)) (w : Finset W → ℝ) {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 < t) (p q : Finset W → Prop)
    [DecidablePred p] [DecidablePred q] :
    ∑ r ∈ (pairDom H₃).filter (fun r => p r.1 ∧ q r.2), pairY w t r
      ≤ (∑ S ∈ H₃.filter p, w S) * (∑ S' ∈ H₃.filter q, w S') / t := by
  classical
  rw [sum_pairY_both]
  have hsplit : (∑ S ∈ H₃.filter p, w S) * (∑ S' ∈ H₃.filter q, w S') / t
      = ∑ S ∈ H₃.filter p, ∑ S' ∈ H₃.filter q, w S * w S' / t := by
    rw [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun S _ => by rw [Finset.sum_div]
  rw [hsplit]
  refine Finset.sum_le_sum fun S _ => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro S' _ _
  exact div_nonneg (mul_nonneg (hw _) (hw _)) ht.le

/-- The coupling sum with only the first coordinate constrained. -/
theorem sum_pairY_fst (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ)
    (p : Finset W → Prop) [DecidablePred p] :
    ∑ r ∈ (pairDom H₃).filter (fun r => p r.1), pairY w t r
      = ∑ S ∈ H₃.filter p, w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t := by
  classical
  have hset : (pairDom H₃).filter (fun r => p r.1)
      = ((H₃.filter p) ×ˢ H₃).filter (fun r => Disjoint r.1 r.2) := by
    ext r
    simp only [pairDom, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hset, sum_dom_eq]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun S' _ => rfl

/-- The total coupling sum, as an iterated sum. -/
theorem sum_pairY_total (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ) :
    ∑ q ∈ pairDom H₃, pairY w t q
      = ∑ S ∈ H₃, w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t := by
  classical
  have hset : pairDom H₃ = (H₃ ×ˢ H₃).filter (fun r => Disjoint r.1 r.2) := rfl
  rw [hset, sum_dom_eq]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun S' _ => rfl

/-! ## 2. From the ordered domain to the merged family -/

/-- **The fibre identity.**  Summing the merged weight over merged sets satisfying a property
is summing the coupling over ordered disjoint pairs whose union satisfies it — halved, because
the domain is ordered. -/
theorem sum_pairWeight_filter (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ)
    (p : Finset W → Prop) [DecidablePred p] :
    ∑ P ∈ (pairFam H₃).filter p, pairWeight H₃ w t P
      = (∑ q ∈ (pairDom H₃).filter (fun q => p (q.1 ∪ q.2)), pairY w t q) / 2 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
      (s := (pairDom H₃).filter (fun q => p (q.1 ∪ q.2)))
      (t := (pairFam H₃).filter p) (g := fun q => q.1 ∪ q.2)
      (fun q hq => by
        rw [Finset.mem_filter] at hq ⊢
        exact ⟨mem_pairFam.2 ⟨q, hq.1, rfl⟩, hq.2⟩)
      (pairY w t),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finset.mem_filter] at hP
  rw [pairWeight]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, rfl⟩; exact ⟨⟨hq, hP.2⟩, rfl⟩
  · rintro ⟨⟨hq, -⟩, rfl⟩; exact ⟨hq, rfl⟩

/-- The total merged mass, in terms of the coupling. -/
theorem sum_pairWeight_total (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ) :
    ∑ P ∈ pairFam H₃, pairWeight H₃ w t P = (∑ q ∈ pairDom H₃, pairY w t q) / 2 := by
  classical
  have h1 : ∑ P ∈ pairFam H₃, pairWeight H₃ w t P
      = ∑ P ∈ (pairFam H₃).filter (fun _ => True), pairWeight H₃ w t P := by
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
  have h2 : ∑ P ∈ (pairFam H₃).filter (fun _ => True), pairWeight H₃ w t P
      = (∑ q ∈ (pairDom H₃).filter (fun _ => True), pairY w t q) / 2 :=
    sum_pairWeight_filter H₃ w t (fun _ => True)
  rw [h1, h2, Finset.filter_true_of_mem (fun _ _ => trivial)]

/-- **The swap symmetry.**  A resource of a merged set lies in exactly one of its two halves,
and swapping the halves is an involution of the domain preserving the coupling. -/
theorem sum_pairY_mem_union (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ) (v : W) :
    ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2), pairY w t q
      = 2 * ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q := by
  classical
  have hsplit : (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2)
      = (pairDom H₃).filter (fun q => v ∈ q.1) ∪ (pairDom H₃).filter (fun q => v ∈ q.2) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro q _
    simp [Finset.mem_union]
  have hdisj : Disjoint ((pairDom H₃).filter (fun q => v ∈ q.1))
      ((pairDom H₃).filter (fun q => v ∈ q.2)) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.mem_filter] at hq hq'
    exact (Finset.disjoint_left.1 (mem_pairDom.1 hq.1).2.2) hq.2 hq'.2
  have hswap : ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.2), pairY w t q
      = ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q := by
    refine Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1))
      ?_ ?_ ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      obtain ⟨h1, h2, hd⟩ := mem_pairDom.1 hq.1
      exact ⟨mem_pairDom.2 ⟨h2, h1, hd.symm⟩, hq.2⟩
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      obtain ⟨h1, h2, hd⟩ := mem_pairDom.1 hq.1
      exact ⟨mem_pairDom.2 ⟨h2, h1, hd.symm⟩, hq.2⟩
    · intro q _; rfl
    · intro q _; rfl
    · intro q _
      rw [pairY, pairY]
      ring
  rw [hsplit, Finset.sum_union hdisj, hswap]
  ring

/-! ## 3. The mass of the triples meeting a fixed triple -/

/-- **The absolute constant of the construction.**  With loads at most one, the `w`-mass of the
triples meeting a fixed triple `S` is at most `|S| = 3`. -/
theorem mass_meeting_le {H₃ : Finset (Finset W)} {w : Finset W → ℝ}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) (hw : ∀ T, 0 ≤ w T)
    (hload : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1)
    {S : Finset W} (hS : S ∈ H₃) :
    ∑ S' ∈ H₃.filter (fun S' => ¬ Disjoint S S'), w S' ≤ 3 := by
  classical
  have hswap : ∑ v ∈ S, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T
      = ∑ T ∈ H₃, ∑ v ∈ S.filter (fun v => v ∈ T), w T := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  have hstep : ∀ T ∈ H₃.filter (fun S' => ¬ Disjoint S S'),
      w T ≤ ∑ v ∈ S.filter (fun v => v ∈ T), w T := by
    intro T hT
    obtain ⟨a, haS, haT⟩ := Finset.not_disjoint_iff.1 (Finset.mem_filter.1 hT).2
    have hsub : ({a} : Finset W) ⊆ S.filter (fun v => v ∈ T) := by
      intro b hb
      rw [Finset.mem_singleton] at hb
      subst hb
      exact Finset.mem_filter.2 ⟨haS, haT⟩
    calc w T = ∑ _v ∈ ({a} : Finset W), w T := by rw [Finset.sum_singleton]
      _ ≤ ∑ _v ∈ S.filter (fun v => v ∈ T), w T :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hw T)
  calc ∑ S' ∈ H₃.filter (fun S' => ¬ Disjoint S S'), w S'
      ≤ ∑ T ∈ H₃.filter (fun S' => ¬ Disjoint S S'), ∑ v ∈ S.filter (fun v => v ∈ T), w T :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ T ∈ H₃, ∑ v ∈ S.filter (fun v => v ∈ T), w T := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro T _ _
        exact Finset.sum_nonneg fun _ _ => hw T
    _ = ∑ v ∈ S, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T := hswap.symm
    _ ≤ ∑ _v ∈ S, (1 : ℝ) := Finset.sum_le_sum fun v _ => hload v
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = 3 := by rw [h3 _ hS]; norm_num

/-- The mass of the triples disjoint from a fixed triple is at least `t - 3`. -/
theorem mass_disjoint_ge {H₃ : Finset (Finset W)} {w : Finset W → ℝ}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) (hw : ∀ T, 0 ≤ w T)
    (hload : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1)
    {S : Finset W} (hS : S ∈ H₃) :
    (∑ T ∈ H₃, w T) - 3 ≤ ∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S' := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not H₃ (fun S' => Disjoint S S') w
  have hmeet := mass_meeting_le h3 hw hload hS
  linarith

/-- And at most the total mass. -/
theorem mass_disjoint_le {H₃ : Finset (Finset W)} {w : Finset W → ℝ} (hw : ∀ T, 0 ≤ w T)
    {S : Finset W} :
    ∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S' ≤ ∑ T ∈ H₃, w T :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun T _ _ => hw T)

/-! ## 4. The merged weight: nonnegativity, loads, mass, codegree -/

theorem pairWeight_nonneg {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 ≤ t) (P : Finset W) : 0 ≤ pairWeight H₃ w t P := by
  classical
  rw [pairWeight]
  have hnn : 0 ≤ ∑ q ∈ (pairDom H₃).filter (fun q => q.1 ∪ q.2 = P), pairY w t q := by
    refine Finset.sum_nonneg fun q _ => ?_
    rw [pairY]
    exact div_nonneg (mul_nonneg (hw _) (hw _)) ht
  linarith

/-- **Merging does not increase loads.** -/
theorem pairs_load_le {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 < t) (htot : ∑ T ∈ H₃, w T ≤ t) (v : W) :
    ∑ P ∈ (pairFam H₃).filter (fun P => v ∈ P), pairWeight H₃ w t P
      ≤ ∑ T ∈ H₃.filter (fun T => v ∈ T), w T := by
  classical
  have e1 : ∑ P ∈ (pairFam H₃).filter (fun P => v ∈ P), pairWeight H₃ w t P
      = (∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2), pairY w t q) / 2 :=
    sum_pairWeight_filter H₃ w t (fun P => v ∈ P)
  have e2 : ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2), pairY w t q
      = 2 * ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q :=
    sum_pairY_mem_union H₃ w t v
  have e3 : ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q
      = ∑ S ∈ H₃.filter (fun T => v ∈ T),
          w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t :=
    sum_pairY_fst H₃ w t (fun T => v ∈ T)
  have hterm : ∀ S ∈ H₃.filter (fun T => v ∈ T),
      w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t ≤ w S := by
    intro S _
    have h1 : (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') ≤ t :=
      le_trans (mass_disjoint_le hw) htot
    have h2 : (0 : ℝ) ≤ ∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S' :=
      Finset.sum_nonneg fun T _ => hw T
    rw [div_le_iff₀ ht]
    nlinarith [hw S]
  have hsum := Finset.sum_le_sum hterm
  rw [e1, e2, e3]
  linarith

/-- **Merging decreases a load by at most `3/t`.** -/
theorem pairs_load_ge {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) (hw : ∀ T, 0 ≤ w T) (ht : 0 < t)
    (ht' : t ≤ ∑ T ∈ H₃, w T)
    (hload : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1) (v : W) :
    (∑ T ∈ H₃.filter (fun T => v ∈ T), w T) - 3 / t
      ≤ ∑ P ∈ (pairFam H₃).filter (fun P => v ∈ P), pairWeight H₃ w t P := by
  classical
  have e1 : ∑ P ∈ (pairFam H₃).filter (fun P => v ∈ P), pairWeight H₃ w t P
      = (∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2), pairY w t q) / 2 :=
    sum_pairWeight_filter H₃ w t (fun P => v ∈ P)
  have e2 : ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1 ∪ q.2), pairY w t q
      = 2 * ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q :=
    sum_pairY_mem_union H₃ w t v
  have e3 : ∑ q ∈ (pairDom H₃).filter (fun q => v ∈ q.1), pairY w t q
      = ∑ S ∈ H₃.filter (fun T => v ∈ T),
          w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t :=
    sum_pairY_fst H₃ w t (fun T => v ∈ T)
  have hterm : ∀ S ∈ H₃.filter (fun T => v ∈ T),
      w S * (t - 3) / t
        ≤ w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t := by
    intro S hS
    have hS' : S ∈ H₃ := (Finset.mem_filter.1 hS).1
    have hD := mass_disjoint_ge h3 hw hload hS'
    have hnum : w S * (t - 3) ≤ w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') := by
      nlinarith [hw S]
    exact div_le_div_of_nonneg_right hnum ht.le
  have hsum := Finset.sum_le_sum hterm
  have hfac : ∑ S ∈ H₃.filter (fun T => v ∈ T), w S * (t - 3) / t
      = (∑ S ∈ H₃.filter (fun T => v ∈ T), w S) * (t - 3) / t := by
    rw [Finset.sum_mul, Finset.sum_div]
  set L : ℝ := ∑ S ∈ H₃.filter (fun T => v ∈ T), w S with hL
  have hLle : L ≤ 1 := hload v
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun T _ => hw T
  have hkey : L - 3 / t ≤ L * (t - 3) / t := by
    have hexp : L * (t - 3) / t - (L - 3 / t) = (3 - 3 * L) / t := by
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ (3 - 3 * L) / t := div_nonneg (by linarith) ht.le
    linarith
  rw [e1, e2, e3]
  rw [hfac] at hsum
  linarith

/-- **The merged mass is at least half the triangle mass, up to `3/2`.** -/
theorem pairs_mass_ge {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) (hw : ∀ T, 0 ≤ w T) (ht : 0 < t)
    (hteq : t = ∑ T ∈ H₃, w T)
    (hload : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1) :
    (t - 3) / 2 ≤ ∑ P ∈ pairFam H₃, pairWeight H₃ w t P := by
  classical
  have hterm : ∀ S ∈ H₃, w S * (t - 3) / t
      ≤ w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t := by
    intro S hS
    have hD := mass_disjoint_ge h3 hw hload hS
    rw [← hteq] at hD
    have hnum : w S * (t - 3) ≤ w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') := by
      nlinarith [hw S]
    exact div_le_div_of_nonneg_right hnum ht.le
  have hsum := Finset.sum_le_sum hterm
  have hfac : ∑ S ∈ H₃, w S * (t - 3) / t = t * (t - 3) / t := by
    rw [← Finset.sum_div, ← Finset.sum_mul, ← hteq]
  have hsimp : t * (t - 3) / t = t - 3 := by
    field_simp
  rw [sum_pairWeight_total, sum_pairY_total]
  rw [hfac, hsimp] at hsum
  linarith

/-- And at most half the triangle mass. -/
theorem pairs_mass_le {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 < t) (hteq : t = ∑ T ∈ H₃, w T) :
    ∑ P ∈ pairFam H₃, pairWeight H₃ w t P ≤ t / 2 := by
  classical
  have hterm : ∀ S ∈ H₃,
      w S * (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') / t ≤ w S := by
    intro S _
    have h1 : (∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S') ≤ t := by
      rw [hteq]; exact mass_disjoint_le hw
    have h2 : (0 : ℝ) ≤ ∑ S' ∈ H₃.filter (fun S' => Disjoint S S'), w S' :=
      Finset.sum_nonneg fun T _ => hw T
    rw [div_le_iff₀ ht]
    nlinarith [hw S]
  have hsum := Finset.sum_le_sum hterm
  rw [sum_pairWeight_total, sum_pairY_total]
  rw [← hteq] at hsum
  linarith

/-- **The merged weighted codegree exceeds the triangle one by at most `1/t`.** -/
theorem pairs_codeg_le {H₃ : Finset (Finset W)} {w : Finset W → ℝ} {t : ℝ}
    (hw : ∀ T, 0 ≤ w T) (ht : 0 < t) (hteq : t = ∑ T ∈ H₃, w T)
    (hload : ∀ v : W, ∑ T ∈ H₃.filter (fun T => v ∈ T), w T ≤ 1) (x z : W) :
    ∑ P ∈ (pairFam H₃).filter (fun P => x ∈ P ∧ z ∈ P), pairWeight H₃ w t P
      ≤ (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T) + 1 / t := by
  classical
  have e1 : ∑ P ∈ (pairFam H₃).filter (fun P => x ∈ P ∧ z ∈ P), pairWeight H₃ w t P
      = (∑ q ∈ (pairDom H₃).filter (fun q => x ∈ q.1 ∪ q.2 ∧ z ∈ q.1 ∪ q.2),
          pairY w t q) / 2 :=
    sum_pairWeight_filter H₃ w t (fun P => x ∈ P ∧ z ∈ P)
  -- the four ways two resources can sit in a merged set
  set A1 := (pairDom H₃).filter (fun r => (fun T => x ∈ T ∧ z ∈ T) r.1 ∧ (fun _ => True) r.2)
    with hA1
  set A2 := (pairDom H₃).filter (fun r => (fun _ => True) r.1 ∧ (fun T => x ∈ T ∧ z ∈ T) r.2)
    with hA2
  set A3 := (pairDom H₃).filter (fun r => (fun T => x ∈ T) r.1 ∧ (fun T => z ∈ T) r.2) with hA3
  set A4 := (pairDom H₃).filter (fun r => (fun T => z ∈ T) r.1 ∧ (fun T => x ∈ T) r.2) with hA4
  have hsub : (pairDom H₃).filter (fun q => x ∈ q.1 ∪ q.2 ∧ z ∈ q.1 ∪ q.2)
      ⊆ A1 ∪ A2 ∪ A3 ∪ A4 := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqd, hx, hz⟩ := hq
    rw [Finset.mem_union] at hx hz
    simp only [hA1, hA2, hA3, hA4, Finset.mem_union, Finset.mem_filter]
    rcases hx with hx | hx <;> rcases hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl ⟨hqd, ⟨hx, hz⟩, trivial⟩))
    · exact Or.inl (Or.inr ⟨hqd, hx, hz⟩)
    · exact Or.inr ⟨hqd, hz, hx⟩
    · exact Or.inl (Or.inl (Or.inr ⟨hqd, trivial, ⟨hx, hz⟩⟩))
  have hnn : ∀ q, 0 ≤ pairY w t q := by
    intro q
    rw [pairY]
    exact div_nonneg (mul_nonneg (hw _) (hw _)) ht.le
  have hunion : ∀ s s' : Finset (Finset W × Finset W),
      ∑ q ∈ s ∪ s', pairY w t q ≤ (∑ q ∈ s, pairY w t q) + ∑ q ∈ s', pairY w t q := by
    intro s s'
    have h := Finset.sum_union_inter (s₁ := s) (s₂ := s') (f := pairY w t)
    have h2 : (0 : ℝ) ≤ ∑ q ∈ s ∩ s', pairY w t q := Finset.sum_nonneg fun q _ => hnn q
    linarith
  have hstep : ∑ q ∈ (pairDom H₃).filter (fun q => x ∈ q.1 ∪ q.2 ∧ z ∈ q.1 ∪ q.2), pairY w t q
      ≤ ((∑ q ∈ A1, pairY w t q) + ∑ q ∈ A2, pairY w t q)
        + (∑ q ∈ A3, pairY w t q) + ∑ q ∈ A4, pairY w t q := by
    calc ∑ q ∈ (pairDom H₃).filter (fun q => x ∈ q.1 ∪ q.2 ∧ z ∈ q.1 ∪ q.2), pairY w t q
        ≤ ∑ q ∈ A1 ∪ A2 ∪ A3 ∪ A4, pairY w t q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hnn q)
      _ ≤ (∑ q ∈ A1 ∪ A2 ∪ A3, pairY w t q) + ∑ q ∈ A4, pairY w t q := hunion _ _
      _ ≤ ((∑ q ∈ A1 ∪ A2, pairY w t q) + ∑ q ∈ A3, pairY w t q) + ∑ q ∈ A4, pairY w t q := by
          have := hunion (A1 ∪ A2) A3
          linarith
      _ ≤ ((∑ q ∈ A1, pairY w t q) + ∑ q ∈ A2, pairY w t q)
            + (∑ q ∈ A3, pairY w t q) + ∑ q ∈ A4, pairY w t q := by
          have := hunion A1 A2
          linarith
  -- the four bounds
  have hcodnn : (0 : ℝ) ≤ ∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T :=
    Finset.sum_nonneg fun T _ => hw T
  have htrue : H₃.filter (fun _ => True) = H₃ := Finset.filter_true_of_mem (fun _ _ => trivial)
  have hb1 : ∑ q ∈ A1, pairY w t q ≤ ∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
    have := sum_pairY_both_le H₃ w hw ht (fun T => x ∈ T ∧ z ∈ T) (fun _ => True)
    rw [htrue, ← hteq] at this
    calc ∑ q ∈ A1, pairY w t q
        ≤ (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T) * t / t := this
      _ = ∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T := by field_simp
  have hb2 : ∑ q ∈ A2, pairY w t q ≤ ∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
    have := sum_pairY_both_le H₃ w hw ht (fun _ => True) (fun T => x ∈ T ∧ z ∈ T)
    rw [htrue, ← hteq] at this
    calc ∑ q ∈ A2, pairY w t q
        ≤ t * (∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T) / t := this
      _ = ∑ T ∈ H₃.filter (fun T => x ∈ T ∧ z ∈ T), w T := by field_simp
  have hb3 : ∑ q ∈ A3, pairY w t q ≤ 1 / t := by
    have := sum_pairY_both_le H₃ w hw ht (fun T => x ∈ T) (fun T => z ∈ T)
    refine le_trans this ?_
    have hx := hload x
    have hz := hload z
    have hxnn : (0 : ℝ) ≤ ∑ T ∈ H₃.filter (fun T => x ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    have hznn : (0 : ℝ) ≤ ∑ T ∈ H₃.filter (fun T => z ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  have hb4 : ∑ q ∈ A4, pairY w t q ≤ 1 / t := by
    have := sum_pairY_both_le H₃ w hw ht (fun T => z ∈ T) (fun T => x ∈ T)
    refine le_trans this ?_
    have hx := hload x
    have hz := hload z
    have hxnn : (0 : ℝ) ≤ ∑ T ∈ H₃.filter (fun T => x ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    have hznn : (0 : ℝ) ≤ ∑ T ∈ H₃.filter (fun T => z ∈ T), w T :=
      Finset.sum_nonneg fun T _ => hw T
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  rw [e1]
  linarith

end PaperIV.TrianglePairingSums

