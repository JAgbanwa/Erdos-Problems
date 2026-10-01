import PaperIV.NibblePort

/-!
# RC01: the triangle-pairing construction (definitions)

The two-rank obstruction of `PaperIV.JointTypedNibbleGate` is that `jointSupports` carries
hyperedges of size `3` **and** of size `6`, while Paper III's nibble is `r`-uniform.  The two
escapes ruled out there are *arm splitting* (`additive_shortcut_fails`) and *padding a triple
with fresh private resources* (`no_faithful_padding_of_capacity`,
`private_padding_forces_exceptional`).

This module sets up a third route, which is blocked by neither obstruction: **pair two
resource-disjoint triples into a single `6`-set of real resources**.  No resource is invented,
the capacity used per triangle is exactly `3` (so the capacity count of
`faithful_padding_capacity` is satisfied with equality, not doubled), and nothing is
pre-allocated to an arm.

* `pairDom H₃` — the ordered pairs of resource-disjoint hyperedges of `H₃`;
* `pairFam H₃` — their unions: a **`6`-uniform** family on the *same* resource universe;
* `pairY w t q = w q.1 * w q.2 / t` — the product coupling, `t` the total triangle mass;
* `pairWeight H₃ w t P` — the weight induced on a `6`-set, summed over all the ways it splits
  into two disjoint triples (and halved, because the domain is ordered);
* `bigFam`, `bigWeight` — the `6`-uniform system `H₄ ∪ pairFam H₃` fed to the nibble.

The quantitative facts are in `PaperIV.TrianglePairingSums`, the matching bookkeeping in
`PaperIV.TrianglePairingSplit`, and the reduction theorem in `PaperIV.TrianglePairingNibble`.
-/

namespace PaperIV.TrianglePairingDefs

open Finset

variable {W : Type*} [DecidableEq W]

/-- The ordered pairs of resource-disjoint hyperedges of `H₃`. -/
def pairDom (H₃ : Finset (Finset W)) : Finset (Finset W × Finset W) :=
  (H₃ ×ˢ H₃).filter (fun q => Disjoint q.1 q.2)

/-- The family of `6`-sets obtained by merging two resource-disjoint triples. -/
def pairFam (H₃ : Finset (Finset W)) : Finset (Finset W) :=
  (pairDom H₃).image (fun q => q.1 ∪ q.2)

/-- The product coupling on ordered disjoint pairs, normalized by the total triangle mass. -/
noncomputable def pairY (w : Finset W → ℝ) (t : ℝ) (q : Finset W × Finset W) : ℝ :=
  w q.1 * w q.2 / t

/-- The weight induced on a merged `6`-set: the coupling summed over all its splittings into
two disjoint triples, halved because `pairDom` is ordered. -/
noncomputable def pairWeight (H₃ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ)
    (P : Finset W) : ℝ :=
  (∑ q ∈ (pairDom H₃).filter (fun q => q.1 ∪ q.2 = P), pairY w t q) / 2

/-- The `6`-uniform system that the single-rank nibble is run on. -/
def bigFam (H₃ H₄ : Finset (Finset W)) : Finset (Finset W) := H₄ ∪ pairFam H₃

/-- Its weight: the original `K₄` weight on `H₄`, the merged weight on the pairs. -/
noncomputable def bigWeight (H₃ H₄ : Finset (Finset W)) (w : Finset W → ℝ) (t : ℝ)
    (P : Finset W) : ℝ :=
  if P ∈ H₄ then w P else pairWeight H₃ w t P

theorem mem_pairDom {H₃ : Finset (Finset W)} {q : Finset W × Finset W} :
    q ∈ pairDom H₃ ↔ q.1 ∈ H₃ ∧ q.2 ∈ H₃ ∧ Disjoint q.1 q.2 := by
  classical
  simp only [pairDom, Finset.mem_filter, Finset.mem_product]
  tauto

theorem mem_pairFam {H₃ : Finset (Finset W)} {P : Finset W} :
    P ∈ pairFam H₃ ↔ ∃ q ∈ pairDom H₃, q.1 ∪ q.2 = P := by
  simp only [pairFam, Finset.mem_image]

/-- A merged set of two disjoint triples has `6` resources. -/
theorem card_eq_six_of_mem_pairFam {H₃ : Finset (Finset W)}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) {P : Finset W} (hP : P ∈ pairFam H₃) :
    P.card = 6 := by
  obtain ⟨q, hq, rfl⟩ := mem_pairFam.1 hP
  obtain ⟨h1, h2, hd⟩ := mem_pairDom.1 hq
  rw [Finset.card_union_of_disjoint hd, h3 _ h1, h3 _ h2]

/-- `bigFam` is `6`-uniform. -/
theorem bigFam_uniform {H₃ H₄ : Finset (Finset W)}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3)
    (h4 : NibblePort.Hypergraph.IsUniform H₄ 6) :
    NibblePort.Hypergraph.IsUniform (bigFam H₃ H₄) 6 := by
  intro P hP
  rcases Finset.mem_union.1 hP with h | h
  · exact h4 _ h
  · exact card_eq_six_of_mem_pairFam h3 h

/-- The two halves of a merged set are distinct: they are disjoint and nonempty. -/
theorem fst_ne_snd_of_mem_pairDom {H₃ : Finset (Finset W)}
    (h3 : NibblePort.Hypergraph.IsUniform H₃ 3) {q : Finset W × Finset W}
    (hq : q ∈ pairDom H₃) : q.1 ≠ q.2 := by
  obtain ⟨h1, h2, hd⟩ := mem_pairDom.1 hq
  intro heq
  have hne : q.1.Nonempty := by
    rw [← Finset.card_pos, h3 _ h1]; omega
  obtain ⟨v, hv⟩ := hne
  have hv2 : v ∈ q.2 := by rwa [← heq]
  exact (Finset.disjoint_left.1 hd) hv hv2

end PaperIV.TrianglePairingDefs

