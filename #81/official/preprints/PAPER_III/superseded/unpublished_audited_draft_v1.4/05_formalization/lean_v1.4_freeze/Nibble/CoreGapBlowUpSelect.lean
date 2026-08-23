/-
# Nibble — the **general** blow-up theorem `ν₃(H[q]) ≥ q²·ν₃*(H) − ε·|V(H[q])|²`

`Nibble/CoreGapBlowUpGap.lean` proved the blow-up gap theorem for a host `H` whose triangle
hypergraph is *near-regular*.  The reduced cluster graph of a Szemerédi partition carries no such
regularity, so that hypothesis has to go.  This file removes it.

The mechanism is a **weighted selection inside the blow-up**.  Let `w` be a fractional triangle
packing of `H` of value close to `ν₃*(H)` and put `m t = ⌊q·w t⌋`.  Inside the `q`-blow-up we keep,
above each triangle `t = {a,b,c}` of `H`, exactly those blown-up triangles `{(a,i),(b,j),(c,k)}`
whose *phase* `(i+j+k) mod q` is smaller than `m t`.  The phase is a symmetric function of the
triple, and fixing any two of the three coordinates leaves the phase a bijection of the third, so:

* the kept family has exactly `m t · q²` triangles above `t` (`Nibble.AX1.card_selTri_fiber`), hence
  `(∑_t m t)·q²` in total (`Nibble.AX1.card_selTri`);
* every edge `{(a,i),(b,j)}` of the blow-up lies in exactly `∑_{t ⊇ {a,b}} m t ≤ q` kept triangles
  (`Nibble.AX1.card_selTri_fiber_edge`, `Nibble.AX1.degree_selHyp`).

So the kept family is a `3`-uniform hypergraph of codegree `≤ 1` whose degrees are bounded by `q`,
and the **deficiency-aware padded nibble** `Nibble.Pad.exists_matching_defic` — which needs no
regularity at all — turns it into a matching of size at least `|K|/q − ε|E(H[q])|`, that is at
least `q²·(∑_t w t) − o(q²)`.

* `Nibble.AX1.nu3_blowUp_ge_general` — the general blow-up theorem: for every `ε > 0` and every host
  `H` there is a `q₀` such that `ν₃(H[q]) ≥ q²·ν₃*(H) − ε·|V(H[q])|²` for all `q ≥ q₀`.
* `Nibble.AX1.nu3star_sub_nu3_blowUp_le_general` — the same statement in gap form.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlowUp
import Nibble.CoreGapBlowUpGap
import Nibble.PadRounding
import Nibble.YusterSubBridge
import Nibble.YusterSubDegreeChar

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Counting residues -/

/-- The residues below `m` are `m` in number. -/
theorem card_fin_lt {q m : ℕ} (hm : m ≤ q) :
    #((univ : Finset (Fin q)).filter (fun y : Fin q => y.val < m)) = m := by
  classical
  have himg : ((univ : Finset (Fin q)).filter (fun y : Fin q => y.val < m)).image Fin.val
      = Finset.range m := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, lt_of_lt_of_le hx hm⟩, hx, rfl⟩
  have := congrArg Finset.card himg
  rwa [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at this

/-- **A shifted residue window has the expected size.**  For every constant `C`, exactly `m` of the
`q` values of `k` satisfy `(C + k) mod q < m`. -/
theorem card_shift {q : ℕ} (hq : 0 < q) {m : ℕ} (C : ℕ) (hm : m ≤ q) :
    #((univ : Finset (Fin q)).filter (fun k : Fin q => (C + k.val) % q < m)) = m := by
  classical
  set f : Fin q → Fin q := fun k => ⟨(C + k.val) % q, Nat.mod_lt _ hq⟩ with hf
  have hinj : Function.Injective f := by
    intro k k' h
    have h' : (C + k.val) % q = (C + k'.val) % q := congrArg Fin.val h
    have h2 : k.val % q = k'.val % q := Nat.ModEq.add_left_cancel' C h'
    have hk := Nat.mod_eq_of_lt k.isLt
    have hk' := Nat.mod_eq_of_lt k'.isLt
    exact Fin.ext (by omega)
  have hcard : #((univ : Finset (Fin q)).filter (fun k : Fin q => (f k).val < m))
      = #((univ : Finset (Fin q)).filter (fun y : Fin q => y.val < m)) := by
    apply Finset.card_bij (fun k _ => f k)
    · intro k hk; simpa using (Finset.mem_filter.mp hk).2
    · intro a _ b _ h; exact hinj h
    · intro b hb
      obtain ⟨a, ha⟩ := (Finite.injective_iff_bijective.mp hinj).2 b
      exact ⟨a, by simp [Finset.mem_filter, ha, (Finset.mem_filter.mp hb).2], ha⟩
  rw [card_fin_lt hm] at hcard
  simpa using hcard

/-- **The phase window on triples.**  Exactly `m·q²` of the `q³` triples `(i,j,k)` satisfy
`(i+j+k) mod q < m`. -/
theorem card_shift_triple {q : ℕ} (hq : 0 < q) {m : ℕ} (hm : m ≤ q) :
    #((univ : Finset (Fin q × Fin q × Fin q)).filter
      (fun p => (p.1.val + p.2.1.val + p.2.2.val) % q < m)) = m * q ^ 2 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ i : Fin q, ∑ jk : Fin q × Fin q,
      (if (i.val + jk.1.val + jk.2.val) % q < m then 1 else 0) = m * q := by
    intro i
    rw [Fintype.sum_prod_type]
    have h2 : ∀ j : Fin q, ∑ k : Fin q,
        (if (i.val + j.val + k.val) % q < m then 1 else 0) = m := by
      intro j
      rw [← Finset.card_filter]
      exact card_shift hq (i.val + j.val) hm
    rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-! ### The phase of a blown-up triangle -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The **phase** of a set of blow-up vertices: the sum of the fibre coordinates, mod `q`. -/
def phase {q : ℕ} (t' : Finset (W × Fin q)) : ℕ := (∑ p ∈ t', (p.2 : ℕ)) % q

omit [Fintype W] in
/-- The phase of an explicit blown-up triangle. -/
theorem phase_triple {q : ℕ} {a b c : W} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j k : Fin q) :
    phase ({(a, i), (b, j), (c, k)} : Finset (W × Fin q))
      = (i.val + j.val + k.val) % q := by
  classical
  unfold phase
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  congr 1
  simp
  omega

/-- The **selected sub-family** of triangles of the blow-up: those whose phase falls in the window
prescribed by the multiplicity `m` of the triangle below them. -/
def selTri (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) (m : Finset W → ℕ) :
    Finset (Finset (W × Fin q)) :=
  ((blowUp H q).cliqueFinset 3).filter (fun t' => phase t' < m (t'.image Prod.fst))

theorem selTri_subset (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) (m : Finset W → ℕ) :
    selTri H q m ⊆ (blowUp H q).cliqueFinset 3 := Finset.filter_subset _ _

/-! ### The fibres of the projection, as explicit images -/

omit [Fintype W] in
/-- Blown-up triples with distinct base vertices are determined by their fibre coordinates. -/
theorem blowUp_triple_injective {q : ℕ} {a b c : W} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective
      (fun p : Fin q × Fin q × Fin q => ({(a, p.1), (b, p.2.1), (c, p.2.2)} : Finset (W × Fin q))) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only at h
  have h1 : ((a, i) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
    rw [← h]; simp
  have h2 : ((b, j) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
    rw [← h]; simp
  have h3 : ((c, k) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2 h3
  have e1 : i = i' := by
    rcases h1 with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hab
    · exact absurd h hac
  have e2 : j = j' := by
    rcases h2 with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h.symm hab
    · exact h
    · exact absurd h hbc
  have e3 : k = k' := by
    rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm hac
    · exact absurd h.symm hbc
    · exact h
  simp [e1, e2, e3]

/-- **The fibre of the projection over a triangle, explicitly.** -/
theorem blowUp_fiber_eq_image (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ht : H.IsNClique 3 ({a, b, c} : Finset W)) :
    ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = ({a, b, c} : Finset W))
      = (univ : Finset (Fin q × Fin q × Fin q)).image
          (fun p => ({(a, p.1), (b, p.2.1), (c, p.2.2)} : Finset (W × Fin q))) := by
  classical
  have hAab : H.Adj a b := ht.1 (by simp) (by simp) hab
  have hAac : H.Adj a c := ht.1 (by simp) (by simp) hac
  have hAbc : H.Adj b c := ht.1 (by simp) (by simp) hbc
  ext t'
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · rintro ⟨hcl, himg⟩
    have hax : ∃ x ∈ t', x.1 = a := by
      have : a ∈ t'.image Prod.fst := by rw [himg]; simp
      simpa [Finset.mem_image] using this
    have hbx : ∃ x ∈ t', x.1 = b := by
      have : b ∈ t'.image Prod.fst := by rw [himg]; simp
      simpa [Finset.mem_image] using this
    have hcx : ∃ x ∈ t', x.1 = c := by
      have : c ∈ t'.image Prod.fst := by rw [himg]; simp
      simpa [Finset.mem_image] using this
    obtain ⟨x, hx, hxa⟩ := hax
    obtain ⟨y, hy, hyb⟩ := hbx
    obtain ⟨z, hz, hzc⟩ := hcx
    have hxy : x ≠ y := fun h => hab (by rw [← hxa, ← hyb, h])
    have hxz : x ≠ z := fun h => hac (by rw [← hxa, ← hzc, h])
    have hyz : y ≠ z := fun h => hbc (by rw [← hyb, ← hzc, h])
    have hsub : ({x, y, z} : Finset (W × Fin q)) ⊆ t' := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hcard : #({x, y, z} : Finset (W × Fin q)) = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    have heq : ({x, y, z} : Finset (W × Fin q)) = t' :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcl.card_eq, hcard])
    have ex : ((a, x.2) : W × Fin q) = x := by rw [Prod.ext_iff]; exact ⟨hxa.symm, rfl⟩
    have ey : ((b, y.2) : W × Fin q) = y := by rw [Prod.ext_iff]; exact ⟨hyb.symm, rfl⟩
    have ez : ((c, z.2) : W × Fin q) = z := by rw [Prod.ext_iff]; exact ⟨hzc.symm, rfl⟩
    refine ⟨(x.2, y.2, z.2), ?_⟩
    rw [← heq]
    simp only
    rw [ex, ey, ez]
  · rintro ⟨⟨i, j, k⟩, rfl⟩
    constructor
    · constructor
      · intro u hu v hv huv
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
          Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          simp_all [blowUp_adj, hAab.symm, hAac.symm, hAbc.symm]
      · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    · simp

/-- **The fibre of the projection over a triangle through a fixed blow-up edge, explicitly.** -/
theorem blowUp_fiber_edge_eq_image (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ht : H.IsNClique 3 ({a, b, c} : Finset W))
    (i j : Fin q) :
    ((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = ({a, b, c} : Finset W) ∧
        ({(a, i), (b, j)} : Finset (W × Fin q)) ⊆ t')
      = (univ : Finset (Fin q)).image
          (fun k => ({(a, i), (b, j), (c, k)} : Finset (W × Fin q))) := by
  classical
  rw [← Finset.filter_filter]
  rw [blowUp_fiber_eq_image H q hab hac hbc ht]
  ext t'
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨i', j', k'⟩, rfl⟩, hsub⟩
    have hi : ((a, i) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) :=
      hsub (by simp)
    have hj : ((b, j) : W × Fin q) ∈ ({(a, i'), (b, j'), (c, k')} : Finset (W × Fin q)) :=
      hsub (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hi hj
    have e1 : i = i' := by
      rcases hi with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hab
      · exact absurd h hac
    have e2 : j = j' := by
      rcases hj with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hab
      · exact h
      · exact absurd h hbc
    exact ⟨k', by rw [e1, e2]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨(i, j, k), rfl⟩, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp

/-! ### The size of the selected family and its degrees -/

/-- **The selected family has `m t · q²` triangles above the triangle `t`.** -/
theorem card_selTri_fiber (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (m : Finset W → ℕ) {t : Finset W} (ht : H.IsNClique 3 t) (hmt : m t ≤ q) :
    #((selTri H q m).filter (fun t' => t'.image Prod.fst = t)) = m t * q ^ 2 := by
  classical
  have h1 : (selTri H q m).filter (fun t' => t'.image Prod.fst = t)
      = (((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t)).filter
          (fun t' => phase t' < m t) := by
    unfold selTri
    ext t'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, hB⟩, hC⟩
      exact ⟨⟨hA, hC⟩, by rw [hC] at hB; exact hB⟩
    · rintro ⟨⟨hA, hC⟩, hB⟩
      exact ⟨⟨hA, by rw [hC]; exact hB⟩, hC⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  rw [h1, blowUp_fiber_eq_image H q hab hac hbc ht]
  have h2 : (((univ : Finset (Fin q × Fin q × Fin q)).image
        (fun p => ({(a, p.1), (b, p.2.1), (c, p.2.2)} : Finset (W × Fin q)))).filter
        (fun t' => phase t' < m ({a, b, c} : Finset W)))
      = ((univ : Finset (Fin q × Fin q × Fin q)).filter
          (fun p => (p.1.val + p.2.1.val + p.2.2.val) % q < m ({a, b, c} : Finset W))).image
          (fun p => ({(a, p.1), (b, p.2.1), (c, p.2.2)} : Finset (W × Fin q))) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro p _
    rw [phase_triple hab hac hbc]
  rw [h2, Finset.card_image_of_injective _ (blowUp_triple_injective hab hac hbc),
    card_shift_triple hq hmt]

/-- **The selected family has `m t` triangles above `t` through a given blow-up edge.** -/
theorem card_selTri_fiber_edge (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (m : Finset W → ℕ) {t : Finset W} (ht : H.IsNClique 3 t) (hmt : m t ≤ q)
    {x y : W × Fin q} (hne : x.1 ≠ y.1) (hx : x.1 ∈ t) (hy : y.1 ∈ t) :
    #((selTri H q m).filter (fun t' => t'.image Prod.fst = t ∧
        ({x, y} : Finset (W × Fin q)) ⊆ t')) = m t := by
  classical
  have h1 : (selTri H q m).filter (fun t' => t'.image Prod.fst = t ∧
        ({x, y} : Finset (W × Fin q)) ⊆ t')
      = (((blowUp H q).cliqueFinset 3).filter (fun t' => t'.image Prod.fst = t ∧
          ({x, y} : Finset (W × Fin q)) ⊆ t')).filter (fun t' => phase t' < m t) := by
    unfold selTri
    ext t'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, hB⟩, hC, hD⟩
      exact ⟨⟨hA, hC, hD⟩, by rw [hC] at hB; exact hB⟩
    · rintro ⟨⟨hA, hC, hD⟩, hB⟩
      exact ⟨⟨hA, by rw [hC]; exact hB⟩, hC, hD⟩
  -- name the third vertex
  have hsub : ({x.1, y.1} : Finset W) ⊆ t := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hcard2 : #({x.1, y.1} : Finset W) = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have hcard1 : #(t \ ({x.1, y.1} : Finset W)) = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, ht.card_eq, hcard2]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  have hcmem : c ∈ t \ ({x.1, y.1} : Finset W) := by rw [hc]; simp
  have hct : c ∈ t := (Finset.mem_sdiff.mp hcmem).1
  have hcab : c ∉ ({x.1, y.1} : Finset W) := (Finset.mem_sdiff.mp hcmem).2
  have hca : x.1 ≠ c := by intro h; exact hcab (by simp [h])
  have hcb : y.1 ≠ c := by intro h; exact hcab (by simp [h])
  have htabc : t = ({x.1, y.1, c} : Finset W) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    · rw [ht.card_eq, Finset.card_insert_of_notMem (by simp [hne, hca]),
        Finset.card_insert_of_notMem (by simp [hcb]), Finset.card_singleton]
  subst htabc
  have hxx : ((x.1, x.2) : W × Fin q) = x := rfl
  have hyy : ((y.1, y.2) : W × Fin q) = y := rfl
  rw [h1]
  rw [show ({x, y} : Finset (W × Fin q))
      = ({(x.1, x.2), (y.1, y.2)} : Finset (W × Fin q)) from rfl]
  rw [blowUp_fiber_edge_eq_image H q hne hca hcb ht x.2 y.2]
  have h2 : (((univ : Finset (Fin q)).image
        (fun k => ({(x.1, x.2), (y.1, y.2), (c, k)} : Finset (W × Fin q)))).filter
        (fun t' => phase t' < m ({x.1, y.1, c} : Finset W)))
      = ((univ : Finset (Fin q)).filter
          (fun k => (x.2.val + y.2.val + k.val) % q < m ({x.1, y.1, c} : Finset W))).image
          (fun k => ({(x.1, x.2), (y.1, y.2), (c, k)} : Finset (W × Fin q))) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro k _
    rw [phase_triple hne hca hcb]
  rw [h2]
  have hinj : Function.Injective
      (fun k : Fin q => ({(x.1, x.2), (y.1, y.2), (c, k)} : Finset (W × Fin q))) := by
    intro k k' h
    have h' : ({(x.1, x.2), (y.1, y.2), (c, k)} : Finset (W × Fin q))
        = ({(x.1, x.2), (y.1, y.2), (c, k')} : Finset (W × Fin q)) := h
    have hmem : ((c, k) : W × Fin q)
        ∈ ({(x.1, x.2), (y.1, y.2), (c, k')} : Finset (W × Fin q)) := by
      rw [← h']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1', -⟩ | ⟨h1', -⟩ | ⟨-, h1'⟩
    · exact absurd h1'.symm hca
    · exact absurd h1'.symm hcb
    · exact h1'
  rw [Finset.card_image_of_injective _ hinj, card_shift hq (x.2.val + y.2.val) hmt]

/-- **The total size of the selected family.** -/
theorem card_selTri (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (m : Finset W → ℕ) (hm : ∀ t ∈ H.cliqueFinset 3, m t ≤ q) :
    #(selTri H q m) = (∑ t ∈ H.cliqueFinset 3, m t) * q ^ 2 := by
  classical
  have hmaps : ∀ t' ∈ selTri H q m, t'.image Prod.fst ∈ H.cliqueFinset 3 := by
    intro t' ht'
    have := selTri_subset H q m ht'
    rw [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact isNClique_image_fst this
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  exact card_selTri_fiber H hq m (SimpleGraph.mem_cliqueFinset_iff.mp ht) (hm t ht)

/-- **The number of selected triangles through a blow-up edge.** -/
theorem card_selTri_edge (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (m : Finset W → ℕ) (hm : ∀ t ∈ H.cliqueFinset 3, m t ≤ q) {x y : W × Fin q}
    (hne : x.1 ≠ y.1) :
    #((selTri H q m).filter (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t'))
      = ∑ t ∈ (H.cliqueFinset 3).filter (fun t => ({x.1, y.1} : Finset W) ⊆ t), m t := by
  classical
  have hmaps : ∀ t' ∈ (selTri H q m).filter (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t'),
      t'.image Prod.fst ∈ (H.cliqueFinset 3).filter (fun t => ({x.1, y.1} : Finset W) ⊆ t) := by
    intro t' ht'
    rw [Finset.mem_filter] at ht'
    obtain ⟨ht'sel, ht'sub⟩ := ht'
    have hcl := selTri_subset H q m ht'sel
    rw [SimpleGraph.mem_cliqueFinset_iff] at hcl
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨isNClique_image_fst hcl, ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_image_of_mem Prod.fst (ht'sub (by simp))
    · exact Finset.mem_image_of_mem Prod.fst (ht'sub (by simp))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨htcl, htsub⟩ := ht
  have hx : x.1 ∈ t := htsub (by simp)
  have hy : y.1 ∈ t := htsub (by simp)
  have hfil : ((selTri H q m).filter
        (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t')).filter (fun t' => t'.image Prod.fst = t)
      = (selTri H q m).filter (fun t' => t'.image Prod.fst = t ∧
          ({x, y} : Finset (W × Fin q)) ⊆ t') := by
    ext t'
    simp only [Finset.mem_filter]
    tauto
  rw [hfil]
  exact card_selTri_fiber_edge H hq m htcl
    (hm t (SimpleGraph.mem_cliqueFinset_iff.mpr htcl)) hne hx hy

/-! ### From a family of triangles to a sub-hypergraph of the triangle hypergraph -/

section EdgeType

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three edges of a triangle, as a hyperedge on the edge type. -/
def edgeTriple (t : Finset V) : Finset (EdgeV G) :=
  (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)

theorem mem_edgeTriple (t : Finset V) (E : EdgeV G) :
    E ∈ edgeTriple G t ↔ E.val ⊆ t := by
  rw [edgeTriple, Finset.mem_subtype, Finset.mem_powersetCard]
  exact ⟨fun h => h.1, fun h => ⟨h, (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq⟩⟩

theorem edgeTriple_injOn :
    Set.InjOn (edgeTriple G) (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  apply Finset.eq_of_subset_of_card_le _ (by rw [ht.card_eq, ht'.card_eq])
  intro a ha
  obtain ⟨b, hbt, hba⟩ : ∃ b ∈ t, b ≠ a := by
    have hne : (t.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht.card_eq]; omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, Finset.mem_of_mem_erase hb, Finset.ne_of_mem_erase hb⟩
  have hsub : ({a, b} : Finset V) ⊆ t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hbt
  have hedge : ({a, b} : Finset V) ∈ G.cliqueFinset 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨ht.isClique.subset hsub, Finset.card_pair (Ne.symm hba)⟩
  have hmem : (⟨{a, b}, hedge⟩ : EdgeV G) ∈ edgeTriple G t := (mem_edgeTriple G t _).mpr hsub
  rw [heq] at hmem
  exact ((mem_edgeTriple G t' _).mp hmem) (by simp)

/-- The hyperedge family attached to a family of triangles. -/
def triFam (S : Finset (Finset V)) : Finset (Finset (EdgeV G)) := S.image (edgeTriple G)

theorem triFam_subset {S : Finset (Finset V)} (hS : S ⊆ G.cliqueFinset 3) :
    triFam G S ⊆ triangleHypergraphSub G := by
  rw [triFam, triangleHypergraphSub]
  exact Finset.image_subset_image hS

theorem card_triFam {S : Finset (Finset V)} (hS : S ⊆ G.cliqueFinset 3) :
    #(triFam G S) = #S :=
  Finset.card_image_of_injOn ((edgeTriple_injOn G).mono (Finset.coe_subset.mpr hS))

/-- **The degree in the attached hypergraph counts the triangles of the family through the edge.** -/
theorem degree_triFam {S : Finset (Finset V)} (hS : S ⊆ G.cliqueFinset 3) (E : EdgeV G) :
    Hypergraph.degree (triFam G S) E = #(S.filter (fun t => E.val ⊆ t)) := by
  classical
  have hset : (triFam G S).filter (fun T => E ∈ T)
      = (S.filter (fun t => E.val ⊆ t)).image (edgeTriple G) := by
    ext T
    simp only [triFam, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hE⟩
      exact ⟨t, ⟨ht, (mem_edgeTriple G t E).mp hE⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hsub⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩,
        (mem_edgeTriple G t E).mpr hsub⟩
  rw [Hypergraph.degree, hset, Finset.card_image_of_injOn]
  exact (edgeTriple_injOn G).mono
    (Finset.coe_subset.mpr (Finset.Subset.trans (Finset.filter_subset _ _) hS))

/-- The codegree of a subfamily is at most the codegree of the family. -/
theorem codegree_mono {X : Type} [Fintype X] [DecidableEq X] {A B : Finset (Finset X)}
    (hAB : A ⊆ B) (u v : X) : Hypergraph.codegree A u v ≤ Hypergraph.codegree B u v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

end EdgeType

/-! ### The selected hypergraph on the edge type of the blow-up -/

/-- An `H`-adjacent pair gives `q²` edges of the blow-up. -/
theorem card_edges_blowUp_ge (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ) {a b : W}
    (hab : H.Adj a b) : q ^ 2 ≤ #((blowUp H q).cliqueFinset 2) := by
  classical
  have hinj : Function.Injective
      (fun p : Fin q × Fin q => ({(a, p.1), (b, p.2)} : Finset (W × Fin q))) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : ({(a, i), (b, j)} : Finset (W × Fin q)) = {(a, i'), (b, j')} := h
    have h1 : ((a, i) : W × Fin q) ∈ ({(a, i'), (b, j')} : Finset (W × Fin q)) := by
      rw [← h']; simp
    have h2 : ((b, j) : W × Fin q) ∈ ({(a, i'), (b, j')} : Finset (W × Fin q)) := by
      rw [← h']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2
    have e1 : i = i' := by
      rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hab.ne
    have e2 : j = j' := by
      rcases h2 with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm hab.ne
      · exact h
    simp [e1, e2]
  have hsub : ((univ : Finset (Fin q × Fin q)).image
      (fun p : Fin q × Fin q => ({(a, p.1), (b, p.2)} : Finset (W × Fin q))))
      ⊆ (blowUp H q).cliqueFinset 2 := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    rw [SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · intro u hu v hv huv
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        simp_all [blowUp_adj, hab.symm]
    · rw [Finset.card_insert_of_notMem (by simp [hab.ne]), Finset.card_singleton]
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, ← pow_two] at hcard

/-- **The degrees of the selected hypergraph are bounded by `q`.** -/
theorem degree_selTri_le (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} (hq : 0 < q)
    (m : Finset W → ℕ) (hm : ∀ t ∈ H.cliqueFinset 3, m t ≤ q)
    (hedge : ∀ e ∈ H.cliqueFinset 2, ∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t), m t ≤ q)
    (E : EdgeV (blowUp H q)) :
    Hypergraph.degree (triFam (blowUp H q) (selTri H q m)) E ≤ q := by
  classical
  rw [degree_triFam _ (selTri_subset H q m)]
  obtain ⟨hcl, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp E.2
  obtain ⟨x, y, hxy, hExy⟩ := Finset.card_eq_two.mp hcard
  have hadj : (blowUp H q).Adj x y :=
    hcl (by rw [hExy]; simp) (by rw [hExy]; simp) hxy
  have hadjH : H.Adj x.1 y.1 := hadj
  have hne : x.1 ≠ y.1 := hadjH.ne
  have hfil : (selTri H q m).filter (fun t => E.val ⊆ t)
      = (selTri H q m).filter (fun t' => ({x, y} : Finset (W × Fin q)) ⊆ t') := by
    apply Finset.filter_congr
    intro t _
    rw [hExy]
  rw [hfil, card_selTri_edge H hq m hm hne]
  refine hedge ({x.1, y.1} : Finset W) ?_
  rw [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · intro u hu v hv huv
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp_all [hadjH.symm]
  · rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]

/-! ### The multiplicities coming from a fractional packing -/

/-- **The rounded multiplicities satisfy the capacity constraint at every edge.** -/
theorem sum_floor_edge_le (H : SimpleGraph W) [DecidableRel H.Adj] {w : Finset (Finset W) → ℝ}
    (hw : IsFracPacking H w) (q : ℕ) {e : Finset W} (he : e ∈ H.cliqueFinset 2) :
    ∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t), ⌊w (t.powersetCard 2) * q⌋₊ ≤ q := by
  classical
  have hcard2 : #e = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp he).card_eq
  have hcon := hw.2.2 e
  rw [sum_triangleHypergraphE_filter H hcard2 w] at hcon
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hstep : ((∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t),
      ⌊w (t.powersetCard 2) * q⌋₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
    push_cast
    calc ∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t),
            (⌊w (t.powersetCard 2) * (q : ℝ)⌋₊ : ℝ)
        ≤ ∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t), w (t.powersetCard 2) * (q : ℝ) :=
          Finset.sum_le_sum (fun t _ => Nat.floor_le (mul_nonneg (hw.1 _) hqnn))
      _ = (∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t), w (t.powersetCard 2)) * (q : ℝ) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (q : ℝ) := mul_le_mul_of_nonneg_right hcon hqnn
      _ = (q : ℝ) := one_mul _
  exact_mod_cast hstep

/-- **Each rounded multiplicity is at most `q`.** -/
theorem floor_le_of_mem (H : SimpleGraph W) [DecidableRel H.Adj] {w : Finset (Finset W) → ℝ}
    (hw : IsFracPacking H w) (q : ℕ) {t : Finset W} (ht : t ∈ H.cliqueFinset 3) :
    ⌊w (t.powersetCard 2) * q⌋₊ ≤ q := by
  classical
  have htcl := SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨e, he⟩ : (t.powersetCard 2).Nonempty := by
    rw [← Finset.card_pos, Finset.card_powersetCard, htcl.card_eq]; decide
  rw [Finset.mem_powersetCard] at he
  have hemem : e ∈ H.cliqueFinset 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨htcl.isClique.subset he.1, he.2⟩
  refine le_trans ?_ (sum_floor_edge_le H hw q hemem)
  refine Finset.single_le_sum (f := fun s : Finset W => ⌊w (s.powersetCard 2) * (q : ℝ)⌋₊)
    (fun _ _ => Nat.zero_le _) ?_
  exact Finset.mem_filter.mpr ⟨ht, he.1⟩

/-- **The rounded multiplicities lose at most one unit per triangle.** -/
theorem sum_floor_ge (H : SimpleGraph W) [DecidableRel H.Adj] (w : Finset (Finset W) → ℝ)
    (q : ℕ) :
    (q : ℝ) * (∑ T ∈ triangleHypergraphE H, w T) - (#(H.cliqueFinset 3) : ℝ)
      ≤ ((∑ t ∈ H.cliqueFinset 3, ⌊w (t.powersetCard 2) * q⌋₊ : ℕ) : ℝ) := by
  classical
  have hstep : ∀ t ∈ H.cliqueFinset 3,
      w (t.powersetCard 2) * (q : ℝ) - 1 ≤ (⌊w (t.powersetCard 2) * (q : ℝ)⌋₊ : ℝ) := by
    intro t _
    have := Nat.lt_floor_add_one (w (t.powersetCard 2) * (q : ℝ))
    linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_mul] at hsum
  rw [sum_triangleHypergraphE H w]
  push_cast
  rw [mul_comm ((q : ℝ))]
  exact hsum

/-! ### The deficiency of a bounded-degree family -/

/-- The total deficiency of a `3`-uniform family whose degrees are bounded by `d`. -/
theorem deficTot_eq_of_degree_le {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X))
    (d : ℕ) (huni : IsUniform K 3) (hdeg : ∀ v : X, Hypergraph.degree K v ≤ d) :
    (Pad.deficTot K d : ℝ) = (d : ℝ) * (Fintype.card X : ℝ) - 3 * (#K : ℝ) := by
  classical
  have hnat : Pad.deficTot K d + 3 * #K = Fintype.card X * d := by
    have hterm : ∀ v : X, Pad.defic K d v + Hypergraph.degree K v = d := by
      intro v
      have := hdeg v
      simp only [Pad.defic]
      omega
    have : Pad.deficTot K d + ∑ v : X, Hypergraph.degree K v = Fintype.card X * d := by
      rw [Pad.deficTot, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
    rwa [Hypergraph.sum_degree K huni] at this
  have hcast : ((Pad.deficTot K d + 3 * #K : ℕ) : ℝ) = ((Fintype.card X * d : ℕ) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hnat
  push_cast at hcast
  linarith

/-! ### The general blow-up theorem -/

/-- The arithmetic of the final estimate: `ε/3` for the rounding of the multiplicities, `ε/3` for
the triangles lost to the flooring, `ε/3` for the nibble's own loss. -/
private theorem blowup_final_arith {q nu N R S Mc W2 ε : ℝ}
    (hε : 0 < ε) (hq : 0 < q) (hR : 0 ≤ R) (hW2 : 1 ≤ W2)
    (h1 : 3 * S * q - ε / 3 * R ≤ 3 * Mc)
    (hS : q * (nu - ε / 3) - N ≤ S)
    (hRle : R ≤ q ^ 2 * W2)
    (hqN : 3 * N ≤ ε * q) :
    q ^ 2 * nu - ε * (q ^ 2 * W2) ≤ Mc := by
  have hSq : 3 * (q * (nu - ε / 3) - N) * q ≤ 3 * S * q := by nlinarith
  have hRq : ε / 3 * R ≤ ε / 3 * (q ^ 2 * W2) := by nlinarith
  have hNq : 3 * N * q ≤ ε * q * q := by nlinarith
  have hq2 : q ^ 2 ≤ q ^ 2 * W2 := by nlinarith [sq_nonneg q]
  nlinarith [hSq, hRq, hNq, hq2, mul_pos hq hq]

/-- **The blow-up theorem, with no regularity hypothesis on the host.**  For every accuracy `ε` and
every graph `H` there is a `q₀` such that every blow-up `H[q]` with `q ≥ q₀` carries an integral
edge-disjoint triangle packing of size at least `q²·ν₃*(H) − ε·|V(H[q])|²`.

This is the statement `ROUTE_BLOWUP.md` isolates as the missing ingredient of the block-cover route:
`Nibble.AX1.nu3_blowUp_ge` proves it only for a host whose triangle hypergraph is near-regular,
whereas a Szemerédi reduced graph carries no degree information at all.  The regularity hypothesis
is removed by the phase selection `Nibble.AX1.selTri` (which turns an optimal fractional packing of
`H` into a bounded-degree sub-hypergraph of the blow-up's triangle hypergraph) together with the
deficiency-aware padded nibble `Nibble.Pad.exists_matching_defic`. -/
theorem nu3_blowUp_ge_general (H : SimpleGraph W) [DecidableRel H.Adj] {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q →
      (q : ℝ) ^ 2 * nu3star H - ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2
        ≤ (nu3 (blowUp H q) : ℝ) := by
  classical
  by_cases hex : ∃ a b : W, H.Adj a b
  · obtain ⟨a, b, hab⟩ := hex
    -- the vertex count is at least one
    have hWpos : (1 : ℝ) ≤ (Fintype.card W : ℝ) := by
      have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨a⟩
      exact_mod_cast this
    set N₃ : ℝ := (#(H.cliqueFinset 3) : ℝ) with hN₃def
    have hN₃nn : (0 : ℝ) ≤ N₃ := Nat.cast_nonneg _
    -- the padded nibble
    obtain ⟨d₀, C, hround⟩ := Pad.exists_matching_defic (ε / 3) (by positivity)
    -- a nearly optimal fractional packing
    have hSne : ({x : ℝ | ∃ w, IsFracPacking H w ∧
        x = ∑ T ∈ triangleHypergraphE H, w T}).Nonempty := by
      refine ⟨0, ⟨fun _ => 0, ?_, by simp⟩⟩
      exact ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩
    have hSsup : nu3star H = sSup {x : ℝ | ∃ w, IsFracPacking H w ∧
        x = ∑ T ∈ triangleHypergraphE H, w T} := rfl
    have hlt : nu3star H - ε / 3 < sSup {x : ℝ | ∃ w, IsFracPacking H w ∧
        x = ∑ T ∈ triangleHypergraphE H, w T} := by rw [← hSsup]; linarith
    obtain ⟨x, hxmem, hxlt⟩ := exists_lt_of_lt_csSup hSne hlt
    obtain ⟨w, hw, rfl⟩ := hxmem
    refine ⟨max (max 1 d₀) (max ⌈C⌉₊ ⌈3 * N₃ / ε⌉₊) + 1, by omega, ?_⟩
    intro q hq₀
    have hq : 0 < q := by omega
    have hd₀ : d₀ ≤ q := by omega
    have hCq : C ≤ (q : ℝ) := by
      have h1 : ⌈C⌉₊ ≤ q := by omega
      have h2 : (⌈C⌉₊ : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
      exact le_trans (Nat.le_ceil C) h2
    have hNq : 3 * N₃ / ε ≤ (q : ℝ) := by
      have h1 : ⌈3 * N₃ / ε⌉₊ ≤ q := by omega
      have h2 : ((⌈3 * N₃ / ε⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
      exact le_trans (Nat.le_ceil _) h2
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    -- the selected hypergraph
    set m : Finset W → ℕ := fun t => ⌊w (t.powersetCard 2) * q⌋₊ with hmdef
    have hm : ∀ t ∈ H.cliqueFinset 3, m t ≤ q := fun t ht => floor_le_of_mem H hw q ht
    have hmedge : ∀ e ∈ H.cliqueFinset 2,
        ∑ t ∈ (H.cliqueFinset 3).filter (fun t => e ⊆ t), m t ≤ q :=
      fun e he => sum_floor_edge_le H hw q he
    set K : Finset (Finset (EdgeV (blowUp H q))) := triFam (blowUp H q) (selTri H q m) with hKdef
    have hKsub : K ⊆ triangleHypergraphSub (blowUp H q) :=
      triFam_subset _ (selTri_subset H q m)
    have huni : IsUniform K 3 :=
      fun e he => triangleHypergraphSub_uniform (blowUp H q) e (hKsub he)
    have hcod : ∀ E E' : EdgeV (blowUp H q), E ≠ E' → Hypergraph.codegree K E E' ≤ 1 :=
      fun E E' hEE' => le_trans (codegree_mono hKsub E E')
        (triangleHypergraphSub_codegree_le_one (blowUp H q) hEE')
    have hdegq : ∀ E : EdgeV (blowUp H q), Hypergraph.degree K E ≤ q :=
      fun E => degree_selTri_le H hq m hm hmedge E
    -- the size hypothesis
    have hcardR : (Fintype.card (EdgeV (blowUp H q)) : ℝ)
        = (#((blowUp H q).cliqueFinset 2) : ℝ) := by
      rw [card_EdgeV]
    have hq2 : ((q : ℝ)) ^ 2 ≤ (Fintype.card (EdgeV (blowUp H q)) : ℝ) := by
      rw [hcardR]
      have := card_edges_blowUp_ge H q hab
      have h2 : ((q ^ 2 : ℕ) : ℝ) ≤ (#((blowUp H q).cliqueFinset 2) : ℝ) := by exact_mod_cast this
      push_cast at h2
      exact h2
    have hsizeC : C * (q : ℝ) ≤ (Fintype.card (EdgeV (blowUp H q)) : ℝ) := by
      have : C * (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by nlinarith
      nlinarith [hq2]
    obtain ⟨M, hM, hMle⟩ := hround K q hd₀ huni hcod hdegq hsizeC
    -- the sizes
    obtain ⟨Rn, hRndef⟩ : ∃ r : ℝ, r = (Fintype.card (EdgeV (blowUp H q)) : ℝ) := ⟨_, rfl⟩
    obtain ⟨S, hSdef⟩ : ∃ s : ℝ, s = ((∑ t ∈ H.cliqueFinset 3, m t : ℕ) : ℝ) := ⟨_, rfl⟩
    have hKcard : (#K : ℝ) = S * (q : ℝ) ^ 2 := by
      rw [hSdef, hKdef, card_triFam _ (selTri_subset H q m), card_selTri H hq m hm]
      push_cast
      ring
    have hdefic : (Pad.deficTot K q : ℝ) = (q : ℝ) * Rn - 3 * (#K : ℝ) := by
      rw [hRndef]
      exact deficTot_eq_of_degree_le K q huni hdegq
    have hMbound : Rn - 3 * (M.card : ℝ)
        ≤ (Pad.deficTot K q : ℝ) / (q : ℝ) + ε / 3 * Rn := by
      rw [hRndef]; exact hMle
    have hdiv : (Pad.deficTot K q : ℝ) / (q : ℝ) = Rn - 3 * S * (q : ℝ) := by
      rw [hdefic, hKcard, div_eq_iff (ne_of_gt hqR)]
      ring
    -- the lower bound on the number of selected triangles
    have hmsum : ((∑ t ∈ H.cliqueFinset 3, m t : ℕ) : ℝ)
        = ((∑ t ∈ H.cliqueFinset 3, ⌊w (t.powersetCard 2) * q⌋₊ : ℕ) : ℝ) := rfl
    have hS : (q : ℝ) * (nu3star H - ε / 3) - N₃ ≤ S := by
      have h1 := sum_floor_ge H w q
      have h2 : (q : ℝ) * (nu3star H - ε / 3)
          ≤ (q : ℝ) * (∑ T ∈ triangleHypergraphE H, w T) := by
        nlinarith only [hxlt, hqR]
      rw [hSdef, hmsum]
      linarith only [h1, h2]
    -- the number of edges of the blow-up
    have hRle : Rn ≤ (q : ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2 := by
      rw [hRndef, card_EdgeV]
      have hcard : (Fintype.card (W × Fin q) : ℝ) = (q : ℝ) * (Fintype.card W : ℝ) := by
        simp [Fintype.card_prod]; ring
      have hle := edge_card_le_card_sq (blowUp H q)
      rw [hcard] at hle
      calc (#((blowUp H q).cliqueFinset 2) : ℝ) ≤ ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := hle
        _ = (q : ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2 := by ring
    have hRnn : (0 : ℝ) ≤ Rn := by rw [hRndef]; exact Nat.cast_nonneg _
    -- the matching is a triangle packing of the blow-up
    have hMnu : (M.card : ℝ) ≤ (nu3 (blowUp H q) : ℝ) := by
      have hMmatch : IsMatching (triangleHypergraphSub (blowUp H q)) M :=
        ⟨Finset.Subset.trans hM.subset hKsub, hM.disjoint⟩
      exact_mod_cast sub_matching_card_le_nu3 (blowUp H q) hMmatch
    -- the final arithmetic
    have hqN₃ : 3 * N₃ ≤ ε * (q : ℝ) := by
      rw [div_le_iff₀ hε] at hNq
      linarith
    have hW2 : (1 : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by nlinarith
    have h1 : 3 * S * (q : ℝ) - ε / 3 * Rn ≤ 3 * (M.card : ℝ) := by
      rw [hdiv] at hMbound
      linarith
    have hkey := blowup_final_arith hε hqR hRnn hW2 h1 hS hRle hqN₃
    have hgoal : ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2
        = ε * ((q : ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2) := by ring
    rw [hgoal]
    linarith only [hkey, hMnu]
  · -- no edges at all: the fractional packing number vanishes
    push_neg at hex
    refine ⟨1, one_pos, ?_⟩
    intro q hq
    have hempty : H.cliqueFinset 2 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      obtain ⟨hcl, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      exact hex u v (hcl (by simp) (by simp) huv)
    have hstar : nu3star H ≤ 0 := by
      have := nu3star_le H
      rw [hempty] at this
      simpa using this
    have h1 : (q : ℝ) ^ 2 * nu3star H ≤ 0 := by nlinarith [sq_nonneg ((q : ℝ))]
    have h2 : (0 : ℝ) ≤ ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ (nu3 (blowUp H q) : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The general blow-up theorem, gap form.**  Along blow-ups of *any* fixed host the integrality
gap of the triangle-packing LP is `o(|V|²)`. -/
theorem nu3star_sub_nu3_blowUp_le_general (H : SimpleGraph W) [DecidableRel H.Adj] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q →
      nu3star (blowUp H q) - (nu3 (blowUp H q) : ℝ)
        ≤ ε * (Fintype.card (W × Fin q) : ℝ) ^ 2 := by
  obtain ⟨q₀, hq₀, hmain⟩ := nu3_blowUp_ge_general H hε
  refine ⟨q₀, hq₀, ?_⟩
  intro q hq
  have hqpos : 0 < q := lt_of_lt_of_le hq₀ hq
  have hcard : (Fintype.card (W × Fin q) : ℝ) = (q : ℝ) * (Fintype.card W : ℝ) := by
    simp [Fintype.card_prod]; ring
  rw [hcard, nu3star_blowUp H hqpos]
  linarith only [hmain q hq]

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.nu3_blowUp_ge_general
#print axioms Nibble.AX1.nu3star_sub_nu3_blowUp_le_general

end AxCheck

end Nibble.AX1
