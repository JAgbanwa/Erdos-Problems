/-
# A balanced grid labelling of a finite set.

The reservoir of `BKLO/ReservoirDesign.lean` gives each outer vertex `u ∈ W \ W'` a *cell*
`(x u, y u) ∈ [h] × [h]` and reserves for `u` the classes of its row and of its column.  Two outer
vertices then always share the class of the cell `(x u, y v)`, which is what makes the reserved
common neighbourhoods abundant, while a class of the cell `(p, q)` is reserved only for the outer
vertices with `x u = p` or `y u = q` — a `2/h` fraction of them, which is what makes the reservoir
sparse.

`BKLO.exists_grid_labelling` provides the labelling: any finite set can be labelled by `[h] × [h]`
so that every row fibre and every column fibre is small.  The labelling is the explicit one: number
the set `0, 1, …, |D| - 1` and read the number in base `h`.

Everything here is `sorry`-free.
-/
import BKLO.LevelSampling

open Finset

namespace BKLO

/-! ### Counting residues below `n` -/

/-- At most `n/h + 1` of the numbers below `n` are congruent to `p` modulo `h`. -/
theorem card_filter_mod_le_grid (n h p : ℕ) :
    (((Finset.range n).filter (fun i => i % h = p)).card) ≤ n / h + 1 := by
  classical
  have hsub : ((Finset.range n).filter (fun i => i % h = p)).card
      ≤ (Finset.range (n / h + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun i => i / h) ?_ ?_
    · intro i hi
      obtain ⟨hin, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      have hin' : i < n := Finset.mem_range.1 hin
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hin'.le))
    · intro i hi j hj hij
      obtain ⟨-, hip⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      obtain ⟨-, hjp⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
      have hij' : i / h = j / h := hij
      have h1 : h * (i / h) + i % h = i := Nat.div_add_mod i h
      have h2 : h * (j / h) + j % h = j := Nat.div_add_mod j h
      rw [← h1, ← h2, hij', hip, hjp]
  simpa using hsub

/-- At most `h(n/h² + 1)` of the numbers below `n` have their `h`-digit of order one equal to
`q`. -/
theorem card_filter_div_mod_le_grid (n h q : ℕ) (hh : 0 < h) :
    (((Finset.range n).filter (fun i => i / h % h = q)).card) ≤ h * (n / (h * h) + 1) := by
  classical
  have hsub : ((Finset.range n).filter (fun i => i / h % h = q)).card
      ≤ ((Finset.range h) ×ˢ (Finset.range (n / (h * h) + 1))).card := by
    refine Finset.card_le_card_of_injOn (fun i => (i % h, i / h / h)) ?_ ?_
    · intro i hi
      obtain ⟨hin, -⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      have hin' : i < n := Finset.mem_range.1 hin
      refine Finset.mem_product.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hh), ?_⟩
      show i / h / h ∈ Finset.range (n / (h * h) + 1)
      refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
      rw [Nat.div_div_eq_div_mul]
      exact Nat.div_le_div_right hin'.le
    · intro i hi j hj hij
      obtain ⟨-, hiq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
      obtain ⟨-, hjq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
      have hij' : (i % h, i / h / h) = (j % h, j / h / h) := hij
      obtain ⟨hmod, hdiv⟩ := Prod.mk.injEq .. ▸ hij'
      have h1 : h * (i / h) + i % h = i := Nat.div_add_mod i h
      have h2 : h * (j / h) + j % h = j := Nat.div_add_mod j h
      have h3 : h * (i / h / h) + i / h % h = i / h := Nat.div_add_mod (i / h) h
      have h4 : h * (j / h / h) + j / h % h = j / h := Nat.div_add_mod (j / h) h
      have hdd : i / h = j / h := by rw [← h3, ← h4, hdiv, hiq, hjq]
      rw [← h1, ← h2, hdd, hmod]
  simpa [Finset.card_product] using hsub

/-! ### The labelling -/

variable {V : Type*} [DecidableEq V]

/-- **A balanced grid labelling.**  Every finite set `D` can be mapped to the grid `[h] × [h]` in
such a way that each row fibre and each column fibre has at most `|D|/h + h` elements. -/
theorem exists_grid_labelling (D : Finset V) {h : ℕ} (hh : 0 < h) :
    ∃ x y : V → ℕ, (∀ u ∈ D, x u < h) ∧ (∀ u ∈ D, y u < h) ∧
      (∀ p : ℕ, (D.filter (fun u => x u = p)).card * h ≤ D.card + h * h) ∧
      (∀ q : ℕ, (D.filter (fun u => y u = q)).card * h ≤ D.card + h * h) := by
  classical
  -- number the elements of `D`
  set e := D.equivFin with he
  set idx : V → ℕ := fun u => if hu : u ∈ D then ((e ⟨u, hu⟩ : Fin D.card) : ℕ) else 0 with hidx
  have hidxlt : ∀ u ∈ D, idx u < D.card := by
    intro u hu
    simp only [hidx, dif_pos hu]
    exact (e ⟨u, hu⟩).2
  have hidxinj : ∀ u ∈ D, ∀ v ∈ D, idx u = idx v → u = v := by
    intro u hu v hv huv
    simp only [hidx, dif_pos hu, dif_pos hv] at huv
    have : e ⟨u, hu⟩ = e ⟨v, hv⟩ := Fin.ext huv
    have := e.injective this
    exact congrArg Subtype.val this
  refine ⟨fun u => idx u % h, fun u => idx u / h % h, ?_, ?_, ?_, ?_⟩
  · exact fun u _ => Nat.mod_lt _ hh
  · exact fun u _ => Nat.mod_lt _ hh
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
    have hmul : (D.card / h + 1) * h ≤ D.card + h * h := by
      have h1 : D.card / h * h ≤ D.card := Nat.div_mul_le_self _ _
      have h2 : h ≤ h * h := Nat.le_mul_of_pos_left _ hh
      calc (D.card / h + 1) * h = D.card / h * h + h := by ring
        _ ≤ D.card + h * h := by omega
    calc (D.filter (fun u => idx u % h = p)).card * h ≤ (D.card / h + 1) * h :=
          Nat.mul_le_mul_right _ (le_trans hcard hb)
      _ ≤ D.card + h * h := hmul
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
    have hmul : (h * (D.card / (h * h) + 1)) * h ≤ D.card + h * h := by
      have h1 : D.card / (h * h) * (h * h) ≤ D.card := Nat.div_mul_le_self _ _
      calc (h * (D.card / (h * h) + 1)) * h = (h * h) * (D.card / (h * h)) + h * h := by ring
        _ ≤ D.card + h * h := by linarith only [h1]
    calc (D.filter (fun u => idx u / h % h = q)).card * h ≤ (h * (D.card / (h * h) + 1)) * h :=
          Nat.mul_le_mul_right _ (le_trans hcard hb)
      _ ≤ D.card + h * h := hmul

end BKLO
