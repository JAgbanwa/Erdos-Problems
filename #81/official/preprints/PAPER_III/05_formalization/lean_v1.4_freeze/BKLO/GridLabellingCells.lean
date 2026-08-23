/-
# The grid labelling, with its **cell** fibres.

`BKLO.exists_grid_labelling` exports only the row and the column fibres of the labelling it builds.
For the pairing step of §10 that is not enough: two outer vertices of the *same cell* have the same
designed region, so all of them compete for the same `(2h-1)t` vertices, and a row fibre bound
alone allows a cell to hold `|D|/h` outer vertices — far more than a region can pair up
edge-disjointly.

The labelling actually built — number `D` and read the number in base `h` — has cells of size
`|D|/h² + 1`, and this file exports that as well.  Nothing in `BKLO/GridLabelling.lean` is changed;
`BKLO.exists_grid_labelling_cells` is strictly stronger than `BKLO.exists_grid_labelling`.

Everything here is `sorry`-free.
-/
import BKLO.GridLabelling

open Finset

namespace BKLO

/-- The two base-`h` digits of a number determine its residue modulo `h²`. -/
theorem mod_sq_of_digits {n h p q : ℕ} (hp : n % h = p) (hq : n / h % h = q) :
    n % (h * h) = p + q * h := by
  have h1 : n % (h * h) % h = n % h := Nat.mod_mod_of_dvd n ⟨h, rfl⟩
  have h2 : n % (h * h) / h = n / h % h := Nat.mod_mul_right_div_self n h h
  have h3 : h * (n % (h * h) / h) + n % (h * h) % h = n % (h * h) :=
    Nat.div_add_mod (n % (h * h)) h
  rw [h1, h2, hp, hq] at h3
  rw [← h3]; ring

variable {V : Type*} [DecidableEq V]

/-- **A balanced grid labelling, with cells.**  Every finite set `D` can be mapped to the grid
`[h] × [h]` so that each row fibre and each column fibre has at most `|D|/h + h` elements *and*
each cell has at most `|D|/h² + 1` elements. -/
theorem exists_grid_labelling_cells (D : Finset V) {h : ℕ} (hh : 0 < h) :
    ∃ x y : V → ℕ, (∀ u ∈ D, x u < h) ∧ (∀ u ∈ D, y u < h) ∧
      (∀ p : ℕ, (D.filter (fun u => x u = p)).card * h ≤ D.card + h * h) ∧
      (∀ q : ℕ, (D.filter (fun u => y u = q)).card * h ≤ D.card + h * h) ∧
      (∀ p q : ℕ, (D.filter (fun u => x u = p ∧ y u = q)).card * (h * h)
        ≤ D.card + h * h) := by
  classical
  -- the same construction as `BKLO.exists_grid_labelling`
  set e := D.equivFin with he
  set idx : V → ℕ := fun u => if hu : u ∈ D then ((e ⟨u, hu⟩ : Fin D.card) : ℕ) else 0 with hidx
  have hidxlt : ∀ u ∈ D, idx u < D.card := by
    intro u hu
    simp only [hidx, dif_pos hu]
    exact (e ⟨u, hu⟩).2
  have hidxinj : ∀ u ∈ D, ∀ v ∈ D, idx u = idx v → u = v := by
    intro u hu v hv huv
    simp only [hidx, dif_pos hu, dif_pos hv] at huv
    have h1 : e ⟨u, hu⟩ = e ⟨v, hv⟩ := Fin.ext huv
    exact congrArg Subtype.val (e.injective h1)
  obtain ⟨x, y, hx, hy, hxfib, hyfib⟩ := exists_grid_labelling D hh
  -- the row and column bounds are the old ones; only the cell bound is new, and for it we
  -- rebuild the labelling explicitly
  refine ⟨fun u => idx u % h, fun u => idx u / h % h, fun u _ => Nat.mod_lt _ hh,
    fun u _ => Nat.mod_lt _ hh, ?_, ?_, ?_⟩
  · -- the row fibres
    intro p
    have hcard : (D.filter (fun u => idx u % h = p)).card
        ≤ ((Finset.range D.card).filter (fun i => i % h = p)).card := by
      refine Finset.card_le_card_of_injOn idx ?_ ?_
      · intro u hu
        obtain ⟨huD, hup⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hidxlt u huD), hup⟩
      · intro u hu v hv huv
        exact hidxinj u (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).1 v
          (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).1 huv
    have hb := card_filter_mod_le_grid D.card h p
    have h1 : D.card / h * h ≤ D.card := Nat.div_mul_le_self _ _
    have h2 : h ≤ h * h := Nat.le_mul_of_pos_left _ hh
    calc (D.filter (fun u => idx u % h = p)).card * h ≤ (D.card / h + 1) * h :=
          Nat.mul_le_mul_right _ (le_trans hcard hb)
      _ ≤ D.card + h * h := by
          have : (D.card / h + 1) * h = D.card / h * h + h := by ring
          omega
  · -- the column fibres
    intro q
    have hcard : (D.filter (fun u => idx u / h % h = q)).card
        ≤ ((Finset.range D.card).filter (fun i => i / h % h = q)).card := by
      refine Finset.card_le_card_of_injOn idx ?_ ?_
      · intro u hu
        obtain ⟨huD, huq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hidxlt u huD), huq⟩
      · intro u hu v hv huv
        exact hidxinj u (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).1 v
          (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).1 huv
    have hb := card_filter_div_mod_le_grid D.card h q hh
    have h1 : (h * h) * (D.card / (h * h)) ≤ D.card := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    calc (D.filter (fun u => idx u / h % h = q)).card * h
        ≤ (h * (D.card / (h * h) + 1)) * h := Nat.mul_le_mul_right _ (le_trans hcard hb)
      _ ≤ D.card + h * h := by
          have : (h * (D.card / (h * h) + 1)) * h = (h * h) * (D.card / (h * h)) + h * h := by
            ring
          omega
  · -- the cells
    intro p q
    have hcard : (D.filter (fun u => idx u % h = p ∧ idx u / h % h = q)).card
        ≤ ((Finset.range D.card).filter (fun i => i % (h * h) = p + q * h)).card := by
      refine Finset.card_le_card_of_injOn idx ?_ ?_
      · intro u hu
        obtain ⟨huD, hup, huq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hidxlt u huD), mod_sq_of_digits hup huq⟩
      · intro u hu v hv huv
        exact hidxinj u (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).1 v
          (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).1 huv
    have hb := card_filter_mod_le_grid D.card (h * h) (p + q * h)
    have h1 : D.card / (h * h) * (h * h) ≤ D.card := Nat.div_mul_le_self _ _
    calc (D.filter (fun u => idx u % h = p ∧ idx u / h % h = q)).card * (h * h)
        ≤ (D.card / (h * h) + 1) * (h * h) := Nat.mul_le_mul_right _ (le_trans hcard hb)
      _ ≤ D.card + h * h := by
          have : (D.card / (h * h) + 1) * (h * h) = D.card / (h * h) * (h * h) + h * h := by ring
          omega

end BKLO
