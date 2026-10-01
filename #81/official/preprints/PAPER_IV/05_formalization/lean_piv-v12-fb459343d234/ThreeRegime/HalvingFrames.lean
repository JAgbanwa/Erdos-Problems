import ThreeRegime.LatinBlocks

/-!
# Los dos marcos concretos sobre `ZMod M`

* `oddFrame` (`M` impar): `x ∘ y = (x + y)/2`.  El cuadrado es la identidad, todos los puntos
  son fijos y las columnas pueden agrandarse a `K₄` con el punto extra.  Es la construcción de
  Bose.
* `evenFrame` (`M = 2t` par): `x ∘ y = f (x + y)` con `f` la biyección que envía `2u ↦ u` y
  `2u+1 ↦ u+t`.  La mitad de los puntos son fijos y la otra mitad se empareja con ellos a
  través del punto extra.  Es la construcción de Skolem.
-/

namespace ThreeRegime.Latin

open Finset PaperIV PaperIV.FarRounding

/-! ## 1. El marco impar (Bose) -/

/-- El inverso de `2` en `ZMod M` para `M` impar. -/
def halfC (M : ℕ) : ZMod M := ((M + 1) / 2 : ℕ)

theorem two_mul_halfC {M : ℕ} (hM : M % 2 = 1) : (2 : ZMod M) * halfC M = 1 := by
  have h : 2 * ((M + 1) / 2) = M + 1 := by omega
  calc (2 : ZMod M) * halfC M = ((2 * ((M + 1) / 2) : ℕ) : ZMod M) := by
        rw [halfC]; push_cast; ring
    _ = ((M + 1 : ℕ) : ZMod M) := by rw [h]
    _ = 1 := by push_cast [ZMod.natCast_self]; ring

/-- El marco de Bose: `x ∘ y = (x+y)/2` sobre `ZMod M` con `M` impar. -/
def oddFrame (M : ℕ) (hM : M % 2 = 1) (k4 : Bool) : Frame (ZMod M) where
  op x y := (x + y) * halfC M
  solve x c := 2 * c - x
  tw x := x
  k4 := k4
  op_comm x y := by ring
  op_solve x c := by
    have h2 := two_mul_halfC hM
    calc (x + (2 * c - x)) * halfC M = c * (2 * halfC M) := by ring
      _ = c := by rw [h2, mul_one]
  solve_op x y := by
    have h2 := two_mul_halfC hM
    calc 2 * ((x + y) * halfC M) - x = (x + y) * (2 * halfC M) - x := by ring
      _ = y := by rw [h2, mul_one]; ring
  s_idem x := by
    have h2 := two_mul_halfC hM
    have hs : (x + x) * halfC M = x := by
      calc (x + x) * halfC M = x * (2 * halfC M) := by ring
        _ = x := by rw [h2, mul_one]
    rw [hs, hs]
  s_inj x y hx := by
    exfalso
    refine hx ?_
    have h2 := two_mul_halfC hM
    calc (x + x) * halfC M = x * (2 * halfC M) := by ring
      _ = x := by rw [h2, mul_one]
  tw_spec y hy := by
    exfalso
    refine hy ?_
    have h2 := two_mul_halfC hM
    calc (y + y) * halfC M = y * (2 * halfC M) := by ring
      _ = y := by rw [h2, mul_one]
  k4_fixed _ x := by
    have h2 := two_mul_halfC hM
    calc (x + x) * halfC M = x * (2 * halfC M) := by ring
      _ = x := by rw [h2, mul_one]

theorem oddFrame_s (M : ℕ) (hM : M % 2 = 1) (k4 : Bool) (x : ZMod M) :
    (oddFrame M hM k4).s x = x := by
  have h2 := two_mul_halfC hM
  show (x + x) * halfC M = x
  calc (x + x) * halfC M = x * (2 * halfC M) := by ring
    _ = x := by rw [h2, mul_one]

@[simp] theorem oddFrame_k4 (M : ℕ) (hM : M % 2 = 1) (k4 : Bool) :
    (oddFrame M hM k4).k4 = k4 := rfl

theorem oddFrame_hasPartner (M : ℕ) [NeZero M] (hM : M % 2 = 1) :
    (oddFrame M hM true).HasPartner := fun _ _ => Or.inl rfl

/-! ## 2. El marco par (Skolem) -/

section Even

variable (M : ℕ) [NeZero M]

/-- La mitad «con desplazamiento»: `2u ↦ u`, `2u+1 ↦ u + M/2`. -/
def halfMap (z : ZMod M) : ZMod M := ((z.val / 2 + (z.val % 2) * (M / 2) : ℕ) : ZMod M)

/-- Su inversa: `w ↦ 2w` si `w < M/2`, y `w ↦ 2(w − M/2) + 1` si no. -/
def halfInv (w : ZMod M) : ZMod M :=
  ((if w.val < M / 2 then 2 * w.val else 2 * (w.val - M / 2) + 1 : ℕ) : ZMod M)

/-- El cuadrado del cuasigrupo par. -/
def sq (x : ZMod M) : ZMod M := halfMap M (x + x)

variable {M}

private theorem M_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

private theorem natCast_val_self (a : ZMod M) : ((a.val : ℕ) : ZMod M) = a := by
  simp [ZMod.natCast_val, ZMod.cast_id]

private theorem eq_of_val_eq {a b : ZMod M} (h : a.val = b.val) : a = b := by
  rw [← natCast_val_self a, ← natCast_val_self b, h]

theorem val_halfMap (hM : M % 2 = 0) (z : ZMod M) :
    (halfMap M z).val = z.val / 2 + (z.val % 2) * (M / 2) := by
  have hz : z.val < M := ZMod.val_lt z
  have hpos : 0 < M := M_pos
  have hpar : z.val % 2 = 0 ∨ z.val % 2 = 1 := by omega
  refine ZMod.val_natCast_of_lt ?_
  rcases hpar with h | h <;> rw [h] <;> omega

theorem val_halfInv (hM : M % 2 = 0) (w : ZMod M) :
    (halfInv M w).val = if w.val < M / 2 then 2 * w.val else 2 * (w.val - M / 2) + 1 := by
  have hw : w.val < M := ZMod.val_lt w
  have hpos : 0 < M := M_pos
  refine ZMod.val_natCast_of_lt ?_
  split <;> omega

theorem halfMap_halfInv (hM : M % 2 = 0) (w : ZMod M) : halfMap M (halfInv M w) = w := by
  have hw : w.val < M := ZMod.val_lt w
  have hpos : 0 < M := M_pos
  rw [halfMap, val_halfInv hM]
  split_ifs with hlt
  · rw [show 2 * w.val / 2 = w.val by omega, show 2 * w.val % 2 = 0 by omega,
      Nat.zero_mul, Nat.add_zero]
    exact natCast_val_self w
  · rw [show (2 * (w.val - M / 2) + 1) / 2 = w.val - M / 2 by omega,
      show (2 * (w.val - M / 2) + 1) % 2 = 1 by omega, Nat.one_mul,
      show w.val - M / 2 + M / 2 = w.val by omega]
    exact natCast_val_self w

theorem halfInv_halfMap (hM : M % 2 = 0) (z : ZMod M) : halfInv M (halfMap M z) = z := by
  have hz : z.val < M := ZMod.val_lt z
  have hpos : 0 < M := M_pos
  rw [halfInv, val_halfMap hM]
  have hpar : z.val % 2 = 0 ∨ z.val % 2 = 1 := by omega
  rcases hpar with h | h <;> rw [h]
  · rw [if_pos (by omega), show 2 * (z.val / 2 + 0 * (M / 2)) = z.val by omega]
    exact natCast_val_self z
  · rw [if_neg (by omega),
      show 2 * (z.val / 2 + 1 * (M / 2) - M / 2) + 1 = z.val by omega]
    exact natCast_val_self z

theorem val_sq (hM : M % 2 = 0) (x : ZMod M) :
    (sq M x).val = if x.val < M / 2 then x.val else x.val - M / 2 := by
  have hx : x.val < M := ZMod.val_lt x
  have hpos : 0 < M := M_pos
  have hval : (x + x).val = (2 * x.val) % M := by
    rw [ZMod.val_add]; congr 1; omega
  rw [sq, val_halfMap hM, hval]
  rcases Nat.lt_or_ge x.val (M / 2) with h | h
  · rw [Nat.mod_eq_of_lt (by omega), show 2 * x.val / 2 = x.val by omega,
      show 2 * x.val % 2 = 0 by omega, Nat.zero_mul, Nat.add_zero, if_pos h]
  · have hmod : 2 * x.val % M = 2 * (x.val - M / 2) := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hmod, show 2 * (x.val - M / 2) / 2 = x.val - M / 2 by omega,
      show 2 * (x.val - M / 2) % 2 = 0 by omega, Nat.zero_mul, Nat.add_zero,
      if_neg (by omega)]

theorem val_sq_lt (hM : M % 2 = 0) (x : ZMod M) : (sq M x).val < M / 2 := by
  have hx : x.val < M := ZMod.val_lt x
  have hpos : 0 < M := M_pos
  rw [val_sq hM]
  split <;> omega

theorem sq_eq_self_iff (hM : M % 2 = 0) (x : ZMod M) : sq M x = x ↔ x.val < M / 2 := by
  have hx : x.val < M := ZMod.val_lt x
  have hpos : 0 < M := M_pos
  constructor
  · intro h
    have := val_sq_lt hM x
    rw [h] at this
    exact this
  · intro h
    refine eq_of_val_eq ?_
    rw [val_sq hM, if_pos h]

theorem sq_sq (hM : M % 2 = 0) (x : ZMod M) : sq M (sq M x) = sq M x :=
  (sq_eq_self_iff hM (sq M x)).2 (val_sq_lt hM x)

theorem val_natCast_half (hM : M % 2 = 0) : ((M / 2 : ℕ) : ZMod M).val = M / 2 := by
  have hpos : 0 < M := M_pos
  exact ZMod.val_natCast_of_lt (by omega)

/-- El marco de Skolem. -/
def evenFrame (hM : M % 2 = 0) : Frame (ZMod M) where
  op x y := halfMap M (x + y)
  solve x c := halfInv M c - x
  tw x := x + ((M / 2 : ℕ) : ZMod M)
  k4 := false
  op_comm x y := by rw [add_comm]
  op_solve x c := by
    rw [show x + (halfInv M c - x) = halfInv M c by ring, halfMap_halfInv hM]
  solve_op x y := by rw [halfInv_halfMap hM]; ring
  s_idem x := sq_sq hM x
  s_inj x y hx hy hxy := by
    have hxv : ¬ (x.val < M / 2) := fun h => hx ((sq_eq_self_iff hM x).2 h)
    have hyv : ¬ (y.val < M / 2) := fun h => hy ((sq_eq_self_iff hM y).2 h)
    have h1 : (sq M x).val = (sq M y).val := congrArg ZMod.val hxy
    rw [val_sq hM, val_sq hM, if_neg hxv, if_neg hyv] at h1
    have hx2 : x.val < M := ZMod.val_lt x
    have hy2 : y.val < M := ZMod.val_lt y
    exact eq_of_val_eq (by omega)
  tw_spec y hy := by
    have hyv : ¬ (y.val < M / 2) := fun h => hy ((sq_eq_self_iff hM y).2 h)
    have hy2 : y.val < M := ZMod.val_lt y
    have hpos : 0 < M := M_pos
    refine eq_of_val_eq ?_
    show ((sq M y) + ((M / 2 : ℕ) : ZMod M)).val = y.val
    rw [ZMod.val_add, val_sq hM, if_neg hyv, val_natCast_half hM,
      Nat.mod_eq_of_lt (by omega)]
    omega
  k4_fixed h := by simp at h

theorem evenFrame_k4 (hM : M % 2 = 0) : (evenFrame hM).k4 = false := rfl

theorem evenFrame_s (hM : M % 2 = 0) (x : ZMod M) : (evenFrame hM).s x = sq M x := rfl

theorem evenFrame_hasPartner (hM : M % 2 = 0) (h2 : 2 ≤ M) :
    (evenFrame hM).HasPartner := by
  intro x hx
  right
  have hpos : 0 < M := M_pos
  have hxv : x.val < M / 2 := (sq_eq_self_iff hM x).1 hx
  have hxval : (x + ((M / 2 : ℕ) : ZMod M)).val = x.val + M / 2 := by
    rw [ZMod.val_add, val_natCast_half hM, Nat.mod_eq_of_lt (by omega)]
  constructor
  · refine eq_of_val_eq ?_
    show (sq M (x + ((M / 2 : ℕ) : ZMod M))).val = x.val
    rw [val_sq hM, hxval, if_neg (by omega)]
    omega
  · intro h
    have : (x + ((M / 2 : ℕ) : ZMod M)).val = x.val := congrArg ZMod.val h
    rw [hxval] at this
    omega

end Even

end ThreeRegime.Latin
