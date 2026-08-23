/-
# The diagonal grid labelling is balanced (piece 2).

Building on `Nibble.AX1.gridShift_label_injective` and the block-pair injectivities of
`Nibble/GridShiftUnique.lean`:

* `gridShift_image_card` — the `n × n` grid produces exactly `n²` distinct (hence pairwise
  edge-disjoint) sub-triples;
* `gridShift_fiber_card` — **balance**: every target `U`-block value `a < n` is hit by exactly `n`
  cells, i.e. `f(j,k) = (j+k) mod n` is a Latin square in the first coordinate.  This keeps the
  per-block load at `≈ (total)/n`, the ingredient the deterministic R1 route and the AX2 balanced
  pairing both need.
-/
import Nibble.GridShiftUnique
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.Bound

open Finset

namespace Nibble.AX1

/-- The `n × n` grid gives `n²` distinct labelled sub-triples. -/
theorem gridShift_image_card {n : ℕ} :
    ((univ : Finset (Fin n × Fin n)).image
        (fun p => (gridShift n p.1 p.2, p.1.val, p.2.val))).card = n ^ 2 := by
  rw [Finset.card_image_of_injective _ gridShift_label_injective]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]

/-- For a target value `a < n` and each `j`, the partner `k` with `(j+k) % n = a`. -/
def gridPartner (n a : ℕ) (j : Fin n) : Fin n :=
  ⟨(a + (n - j.val)) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩

theorem gridShift_partner {n a : ℕ} (ha : a < n) (j : Fin n) :
    gridShift n j (gridPartner n a j) = a := by
  have hj : j.val ≤ n := le_of_lt j.isLt
  show (j.val + (a + (n - j.val)) % n) % n = a
  have h : (j.val + (a + (n - j.val)) % n) ≡ a [MOD n] := by
    calc (j.val + (a + (n - j.val)) % n)
        ≡ j.val + (a + (n - j.val)) [MOD n] :=
          (Nat.ModEq.refl _).add (Nat.mod_modEq _ _)
      _ = a + n := by omega
      _ ≡ a [MOD n] := Nat.add_mod_right a n
  calc (j.val + (a + (n - j.val)) % n) % n = a % n := h
    _ = a := Nat.mod_eq_of_lt ha

/-- **Balance / Latin-square property**: exactly `n` cells map to each `U`-block value `a < n`. -/
theorem gridShift_fiber_card {n a : ℕ} (ha : a < n) :
    ((univ : Finset (Fin n × Fin n)).filter (fun p => gridShift n p.1 p.2 = a)).card = n := by
  classical
  have hinj : Function.Injective (fun j : Fin n => (j, gridPartner n a j)) := by
    intro x y h; exact congrArg Prod.fst h
  have hset : (univ.filter (fun p : Fin n × Fin n => gridShift n p.1 p.2 = a))
      = univ.image (fun j : Fin n => (j, gridPartner n a j)) := by
    ext ⟨j, k⟩
    simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
    constructor
    · intro hgs
      refine ⟨j, rfl, ?_⟩
      have h1 : gridShift n j (gridPartner n a j) = gridShift n j k := by
        rw [gridShift_partner ha, hgs]
      have h2 : (gridPartner n a j).val ≡ k.val [MOD n] :=
        Nat.ModEq.add_left_cancel' j.val (by simpa [gridShift, Nat.ModEq] using h1)
      have hk : (gridPartner n a j).val = k.val := by
        have := h2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (gridPartner n a j).isLt, Nat.mod_eq_of_lt k.isLt] at this
      exact Fin.ext hk
    · rintro ⟨j', hj', hk'⟩
      subst hj'
      rw [← hk']
      exact gridShift_partner ha j'
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The `U`-block map `(j,k) ↦ (f(j,k), j)` packaged into `Fin n × Fin n`. -/
def gridUW (n : ℕ) (p : Fin n × Fin n) : Fin n × Fin n :=
  (⟨gridShift n p.1 p.2, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) p.2.isLt)⟩, p.1)

/-- **Exact cover (full Latin square)**: `(j,k) ↦ (f(j,k), j)` is a bijection of `Fin n × Fin n`,
so every `(U`-block value, `W`-block index) pair is used *exactly once* — the loss-free coverage
the deterministic grid route relies on. -/
theorem gridUW_injective {n : ℕ} : Function.Injective (gridUW n) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  simp only [gridUW, Prod.mk.injEq, Fin.mk.injEq] at h
  exact gridShift_UW_injective (Prod.ext h.1 (congrArg Fin.val h.2))

theorem gridUW_bijective {n : ℕ} : Function.Bijective (gridUW n) :=
  (Finite.injective_iff_bijective).mp gridUW_injective

/-! ### Deterministic two-sided balance: a Latin-square assignment spreads every line.

The obstruction to the AX2 §10 reservoir was two-sided: a vertex's deficient classes may form a
whole grid line of the *given* class family, so both a row-imbalance and a column-imbalance of
`Θ(h·t)` appear.  The fix is a **Latin-square assignment** of the `h²` classes to the `h × h` grid
cells: the diagonal shift `i ↦ (i + c) mod h` is a bijection of `Fin h`, so the `h` classes of any
single line land in `h` **distinct** rows (and, symmetrically, distinct columns) — one deficient
class per row.  This is the deterministic core that replaces the missing concentration bound. -/

/-- The diagonal shift `i ↦ (i + c) mod h` is a bijection of `Fin h`: **any line spreads to a full
transversal** (one class per row/column). -/
theorem diagShift_bijective {h : ℕ} (c : ℕ) :
    Function.Bijective
      (fun i : Fin h => (⟨(i.val + c) % h, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin h)) := by
  refine (Finite.injective_iff_bijective).mp ?_
  intro a b h'
  have hb : (a.val + c) % h = (b.val + c) % h := by simpa [Fin.ext_iff] using h'
  have : a.val % h = b.val % h := by
    have hmod : (a.val + c) ≡ (b.val + c) [MOD h] := hb
    exact Nat.ModEq.add_right_cancel' c hmod
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this)

/-- **Line-to-transversal spread.**  For any line `{(i, c) : i}` (a column of the original class
family, indexed by `c`), the row indices `(i + c) mod h` under the diagonal assignment are pairwise
distinct — so the image meets each of the `h` rows at most once.  This is the two-sided balance the
reservoir design needs, achieved deterministically. -/
theorem diagShift_line_injOn {h : ℕ} (c : ℕ) :
    Function.Injective (fun i : Fin h => ((i.val + c) % h)) := by
  intro a b h'
  have : a.val % h = b.val % h :=
    Nat.ModEq.add_right_cancel' c (show (a.val + c) ≡ (b.val + c) [MOD h] from h')
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this)

end Nibble.AX1


