import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The RD09-L2 moment chain

The factor–candidate averaging of RD09-L2 needs exactly three elementary counting
facts about the core clique `K_p`, its bases (= its edges) and the *defect*
`d z = a z + u z` of a core vertex (`a z` missing exterior incidences, `u z`
phase-I-used incidences).  Writing `A = ∑ a`, `2 f = ∑ u`, `S = A + 2 f = ∑ d`,
`D = max a` and `u z ≤ 2 t`, the chain is

* **first moment**   `∑ e, b e ≤ (p - 1) * S`,
* **second moment**  `∑ e, b e ^ 2 ≤ (p - 2) * ∑ z, d z ^ 2 + S ^ 2`,
* **defect moment**  `∑ z, d z ^ 2 ≤ (D + 4 t) * A + 4 t * f`,

for any base weight `b` with `b {x,y} ≤ d x + d y`.

Everything is stated over `ℕ`, and the two structural identities are given first in
*subtraction-free* form (`sum_corePairs_defect`, `sum_corePairs_defect_sq`), so that the
`p - 1` and `p - 2` forms are literal consequences and no truncated subtraction is ever
hidden inside a proof.

Bases of the core clique are represented by the ordered pairs `x < y` of core vertices
(`corePairs`), one representative per unordered pair.
-/

namespace PaperIV.RD09FactorCandidateMoments

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [LinearOrder Z]

/-! ## The bases of the core clique -/

variable (Z) in
/-- The bases of the core clique `K_p`: one ordered representative `x < y` for each
unordered pair of distinct core vertices. -/
def corePairs : Finset (Z × Z) := univ.filter fun e => e.1 < e.2

omit [DecidableEq Z] in
@[simp] theorem mem_corePairs {e : Z × Z} : e ∈ corePairs Z ↔ e.1 < e.2 := by
  simp [corePairs]

/-- The number of bases of `K_p` is `p (p-1) / 2`; only the following symmetrisation is
needed: an ordered sum over distinct pairs is a sum over bases of the symmetrised
summand. -/
theorem sum_offDiag_eq_sum_corePairs (F : Z → Z → ℕ) :
    (∑ e ∈ (univ : Finset Z).offDiag, F e.1 e.2)
      = ∑ e ∈ corePairs Z, (F e.1 e.2 + F e.2 e.1) := by
  classical
  have hunion : (univ : Finset Z).offDiag
      = corePairs Z ∪ (corePairs Z).image Prod.swap := by
    ext ⟨x, y⟩
    simp only [Finset.mem_offDiag, mem_univ, true_and, Finset.mem_union, Finset.mem_image,
      corePairs, mem_filter, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · intro hxy
      rcases lt_or_gt_of_ne hxy with h | h
      · exact Or.inl h
      · exact Or.inr ⟨y, x, h, rfl, rfl⟩
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
  have hdisj : Disjoint (corePairs Z) ((corePairs Z).image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hx hy
    simp only [corePairs, mem_filter, mem_univ, true_and] at hx
    simp only [Finset.mem_image, corePairs, mem_filter, mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hy
    obtain ⟨a, b, hab, rfl, rfl⟩ := hy
    exact absurd hx (not_lt.mpr (le_of_lt hab))
  rw [hunion, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Prod.swap_injective h), Finset.sum_add_distrib]
  simp

/-! ## The two structural identities over the core clique -/

omit [LinearOrder Z] in
/-- Every core vertex lies in `p - 1` bases, in subtraction-free form. -/
theorem sum_offDiag_fst (g : Z → ℕ) :
    (∑ e ∈ (univ : Finset Z).offDiag, g e.1) + ∑ z, g z = Fintype.card Z * ∑ z, g z := by
  classical
  have key : (∑ e ∈ ((univ : Finset Z) ×ˢ (univ : Finset Z)), g e.1)
      = (∑ e ∈ (univ : Finset Z).diag, g e.1)
        + ∑ e ∈ (univ : Finset Z).offDiag, g e.1 := by
    rw [← Finset.diag_union_offDiag (univ : Finset Z),
      Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  rw [Finset.sum_product, Finset.sum_diag] at key
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at key
  omega

omit [LinearOrder Z] in
/-- The off-diagonal square expansion, in subtraction-free form. -/
theorem sum_offDiag_mul (g : Z → ℕ) :
    (∑ e ∈ (univ : Finset Z).offDiag, g e.1 * g e.2) + ∑ z, g z * g z
      = (∑ z, g z) * (∑ z, g z) := by
  classical
  have key : (∑ e ∈ ((univ : Finset Z) ×ˢ (univ : Finset Z)), g e.1 * g e.2)
      = (∑ e ∈ (univ : Finset Z).diag, g e.1 * g e.2)
        + ∑ e ∈ (univ : Finset Z).offDiag, g e.1 * g e.2 := by
    rw [← Finset.diag_union_offDiag (univ : Finset Z),
      Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  rw [Finset.sum_product, Finset.sum_diag] at key
  simp only at key
  rw [Finset.sum_mul_sum]
  omega

/-- **First structural identity**, subtraction-free:
`∑_e (d x + d y) + ∑_z d z = p * ∑_z d z`. -/
theorem sum_corePairs_defect (d : Z → ℕ) :
    (∑ e ∈ corePairs Z, (d e.1 + d e.2)) + ∑ z, d z = Fintype.card Z * ∑ z, d z := by
  rw [← sum_offDiag_eq_sum_corePairs (fun x _ => d x)]
  exact sum_offDiag_fst d

/-- **Second structural identity**, subtraction-free:
`∑_e (d x + d y) ^ 2 + 2 * ∑_z d z ^ 2 = p * ∑_z d z ^ 2 + (∑_z d z) ^ 2`. -/
theorem sum_corePairs_defect_sq (d : Z → ℕ) :
    (∑ e ∈ corePairs Z, (d e.1 + d e.2) ^ 2) + 2 * ∑ z, d z ^ 2
      = Fintype.card Z * (∑ z, d z ^ 2) + (∑ z, d z) ^ 2 := by
  classical
  have hsq := sum_offDiag_fst (fun z => d z ^ 2)
  have hmul := sum_offDiag_mul d
  have hsplit1 : (∑ e ∈ (univ : Finset Z).offDiag, d e.1 ^ 2)
      = ∑ e ∈ corePairs Z, (d e.1 ^ 2 + d e.2 ^ 2) :=
    sum_offDiag_eq_sum_corePairs (fun x _ => d x ^ 2)
  have hsplit2 : (∑ e ∈ (univ : Finset Z).offDiag, d e.1 * d e.2)
      = ∑ e ∈ corePairs Z, (d e.1 * d e.2 + d e.2 * d e.1) :=
    sum_offDiag_eq_sum_corePairs (fun x y => d x * d y)
  have hexp : (∑ e ∈ corePairs Z, (d e.1 + d e.2) ^ 2)
      = (∑ e ∈ corePairs Z, (d e.1 ^ 2 + d e.2 ^ 2))
        + ∑ e ∈ corePairs Z, (d e.1 * d e.2 + d e.2 * d e.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hsqsum : (∑ z, d z * d z) = ∑ z, d z ^ 2 :=
    Finset.sum_congr rfl fun z _ => by ring
  rw [hexp, ← hsplit1, ← hsplit2]
  rw [hsqsum] at hmul
  have hpow : (∑ z, d z) * (∑ z, d z) = (∑ z, d z) ^ 2 := by ring
  rw [hpow] at hmul
  omega

/-! ## The moment chain -/

variable {d b : Z → ℕ} {p : ℕ}

/-- **First moment of the failed-base weights.**  If `b e ≤ d x + d y` for every base
`e = {x, y}`, then `∑_e b e ≤ (p - 1) * S` with `S = ∑_z d z`. -/
theorem sum_b_le (d : Z → ℕ) (b : Z × Z → ℕ)
    (hb : ∀ e ∈ corePairs Z, b e ≤ d e.1 + d e.2) :
    (∑ e ∈ corePairs Z, b e) ≤ (Fintype.card Z - 1) * ∑ z, d z := by
  classical
  have h1 : (∑ e ∈ corePairs Z, b e) ≤ ∑ e ∈ corePairs Z, (d e.1 + d e.2) :=
    Finset.sum_le_sum hb
  have h2 := sum_corePairs_defect d
  rcases Nat.eq_zero_or_pos (Fintype.card Z) with hz | hpos
  · have : IsEmpty Z := Fintype.card_eq_zero_iff.mp hz
    simp [corePairs, Finset.univ_eq_empty]
  · obtain ⟨m, hm⟩ : ∃ m, Fintype.card Z = m + 1 := ⟨Fintype.card Z - 1, by omega⟩
    rw [hm] at h2
    have hexp : (m + 1) * ∑ z, d z = m * (∑ z, d z) + ∑ z, d z := by ring
    rw [hexp] at h2
    have : Fintype.card Z - 1 = m := by omega
    rw [this]
    omega

/-- **Second moment of the failed-base weights.**  If `b e ≤ d x + d y` for every base,
then `∑_e (b e) ^ 2 ≤ (p - 2) * ∑_z d z ^ 2 + S ^ 2`. -/
theorem sum_b_sq_le (d : Z → ℕ) (b : Z × Z → ℕ)
    (hb : ∀ e ∈ corePairs Z, b e ≤ d e.1 + d e.2) :
    (∑ e ∈ corePairs Z, (b e) ^ 2)
      ≤ (Fintype.card Z - 2) * (∑ z, d z ^ 2) + (∑ z, d z) ^ 2 := by
  classical
  have h1 : (∑ e ∈ corePairs Z, (b e) ^ 2) ≤ ∑ e ∈ corePairs Z, (d e.1 + d e.2) ^ 2 :=
    Finset.sum_le_sum fun e he => Nat.pow_le_pow_left (hb e he) 2
  have h2 := sum_corePairs_defect_sq d
  rcases Nat.lt_or_ge (Fintype.card Z) 2 with hlt | hge
  · -- with at most one core vertex there are no bases at all
    have hempty : corePairs Z = ∅ := by
      rw [corePairs, Finset.filter_eq_empty_iff]
      rintro ⟨x, y⟩ -
      have hxy : x = y := by
        by_contra hne
        have : 2 ≤ Fintype.card Z := Fintype.one_lt_card_iff.mpr ⟨x, y, hne⟩
        omega
      simp [hxy]
    rw [hempty, Finset.sum_empty]
    exact Nat.zero_le _
  · obtain ⟨m, hm⟩ : ∃ m, Fintype.card Z = m + 2 := ⟨Fintype.card Z - 2, by omega⟩
    rw [hm] at h2
    have hexp : (m + 2) * (∑ z, d z ^ 2) = m * (∑ z, d z ^ 2) + 2 * ∑ z, d z ^ 2 := by ring
    rw [hexp] at h2
    have hcard : Fintype.card Z - 2 = m := by omega
    rw [hcard]
    omega

omit [DecidableEq Z] [LinearOrder Z] in
/-- **The defect moment.**  With `a z ≤ D`, `u z ≤ 2 t`, `∑ a = A` and `∑ u = 2 f`,
`∑_z (a z + u z) ^ 2 ≤ (D + 4 t) * A + 4 t * f`. -/
theorem sum_defect_sq_le (a u : Z → ℕ) {D t A f : ℕ}
    (hD : ∀ z, a z ≤ D) (hu : ∀ z, u z ≤ 2 * t)
    (hA : (∑ z, a z) = A) (hf : (∑ z, u z) = 2 * f) :
    (∑ z, (a z + u z) ^ 2) ≤ (D + 4 * t) * A + 4 * t * f := by
  classical
  have hterm : ∀ z, (a z + u z) ^ 2 ≤ D * a z + 4 * t * a z + 2 * t * u z := by
    intro z
    have h1 : a z * a z ≤ D * a z := Nat.mul_le_mul_right _ (hD z)
    have h2 : u z * u z ≤ 2 * t * u z := Nat.mul_le_mul_right _ (hu z)
    have h3 : 2 * (a z * u z) ≤ 2 * (a z * (2 * t)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hu z))
    have h4 : 2 * (a z * (2 * t)) = 4 * t * a z := by ring
    have hexp : (a z + u z) ^ 2 = a z * a z + 2 * (a z * u z) + u z * u z := by ring
    omega
  calc (∑ z, (a z + u z) ^ 2)
      ≤ ∑ z, (D * a z + 4 * t * a z + 2 * t * u z) := Finset.sum_le_sum fun z _ => hterm z
    _ = D * (∑ z, a z) + 4 * t * (∑ z, a z) + 2 * t * ∑ z, u z := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum]
    _ = (D + 4 * t) * A + 4 * t * f := by rw [hA, hf]; ring

/-- **The full moment chain.**  Combining the three moments: the second moment of the
failed-base weights is bounded by the physical accounts `A`, `f`, `D`, `t`, `p`. -/
theorem sum_b_sq_le_accounts (a u : Z → ℕ) (b : Z × Z → ℕ) {D t A f : ℕ}
    (hb : ∀ e ∈ corePairs Z, b e ≤ (a e.1 + u e.1) + (a e.2 + u e.2))
    (hD : ∀ z, a z ≤ D) (hu : ∀ z, u z ≤ 2 * t)
    (hA : (∑ z, a z) = A) (hf : (∑ z, u z) = 2 * f) :
    (∑ e ∈ corePairs Z, (b e) ^ 2)
      ≤ (Fintype.card Z - 2) * ((D + 4 * t) * A + 4 * t * f) + (A + 2 * f) ^ 2 := by
  classical
  have hsum : (∑ z, (a z + u z)) = A + 2 * f := by
    rw [Finset.sum_add_distrib, hA, hf]
  have h1 := sum_b_sq_le (fun z => a z + u z) b hb
  have h2 := sum_defect_sq_le a u hD hu hA hf
  rw [hsum] at h1
  exact h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) _)

/-- The first moment expressed through the physical accounts: `∑_e b e ≤ (p-1)(A + 2f)`. -/
theorem sum_b_le_accounts (a u : Z → ℕ) (b : Z × Z → ℕ) {A f : ℕ}
    (hb : ∀ e ∈ corePairs Z, b e ≤ (a e.1 + u e.1) + (a e.2 + u e.2))
    (hA : (∑ z, a z) = A) (hf : (∑ z, u z) = 2 * f) :
    (∑ e ∈ corePairs Z, b e) ≤ (Fintype.card Z - 1) * (A + 2 * f) := by
  have hsum : (∑ z, (a z + u z)) = A + 2 * f := by
    rw [Finset.sum_add_distrib, hA, hf]
  have h1 := sum_b_le (fun z => a z + u z) b hb
  rwa [hsum] at h1

end PaperIV.RD09FactorCandidateMoments


