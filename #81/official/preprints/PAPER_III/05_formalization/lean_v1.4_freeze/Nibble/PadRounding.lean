/-
# Nibble — rounding a deficiency profile: the padded nibble

This file turns the library's own nibble theorem `Nibble.nibbleTheoremMostCeil_holds` into a
*deficiency-aware* rounding statement for an arbitrary `3`-uniform hypergraph `H` of codegree `≤ 1`
whose degrees are bounded by `d`:

> for every `ε > 0` there are `d₀`, `C` such that whenever `d₀ ≤ d`, `C·d ≤ |R|`, the hypergraph
> `H` has a matching `M` with `|R| - 3|M| ≤ (∑_r (d - deg_H r))/d + ε|R|`.

The point is that the nibble in the library only applies to *near-regular* hypergraphs, whereas `H`
need not be near-regular at all: its degrees are only bounded above by `d`. The bridge is the
explicit degree-balancing padding of `Nibble/PadHypergraph.lean`: we add `MD` dummy vertices and one
padding hyperedge for each unit of deficiency, which makes every real vertex have degree *exactly*
`d`, keeps the dummy degrees balanced, and keeps all codegrees small. The nibble then applies to the
padded hypergraph, and pulling the matching back costs at most `MD/2 ≈ (∑_r (d - deg_H r))/d`
hyperedges — exactly the allowed slack.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.PadHypergraph
import Nibble.TightNibble

open Finset Hypergraph

namespace Nibble.Pad

/-! ### Arithmetic of the balanced block size

Throughout, `T` is the total deficiency, `W = T / d`, the number of dummy vertices is
`MD = 2W + 2d + 2K + 2`, and `Q = T / MD` is the balanced dummy block count, so that every dummy
vertex has degree between `2Q` and `2Q + 2`. -/

/-- The number of dummy vertices. -/
def padSize (T d K : ℕ) : ℕ := 2 * (T / d) + 2 * d + 2 * K + 2

theorem padSize_pos (T d K : ℕ) : 0 < padSize T d K := by
  unfold padSize; omega

theorem two_K_lt_padSize (T d K : ℕ) : 2 * K < padSize T d K := by
  unfold padSize; omega

theorem le_padSize (T d K : ℕ) : d ≤ padSize T d K := by
  unfold padSize; omega

/-- **Upper bound on the balanced block count**: `2Q < d`, unconditionally. -/
theorem padQ_upper {T d K : ℕ} (hd : 0 < d) : 2 * (T / padSize T d K) < d := by
  set W := T / d with hW
  set MD := padSize T d K with hMD
  set Q := T / MD with hQ
  have hMDpos : 0 < MD := padSize_pos T d K
  have hMDge : 2 * (W + 1) ≤ MD := by unfold padSize at hMD; omega
  have hQMD : Q * MD ≤ T := Nat.div_mul_le_self T MD
  have hT : T < (W + 1) * d := by
    have h1 := Nat.div_add_mod T d
    have h2 : T % d < d := Nat.mod_lt _ hd
    have : T = d * W + T % d := by rw [hW]; omega
    linarith only [this, h2]
  have hkey : 2 * Q * (W + 1) ≤ Q * MD := by
    calc 2 * Q * (W + 1) = Q * (2 * (W + 1)) := by ring
      _ ≤ Q * MD := Nat.mul_le_mul_left _ hMDge
  have : 2 * Q * (W + 1) < (W + 1) * d := by omega
  exact Nat.lt_of_mul_lt_mul_right (by linarith only [this] : 2 * Q * (W + 1) < d * (W + 1))

/-- **Lower bound on the balanced block count** in the *active* regime `L·d² ≤ T`. -/
theorem padQ_lower {T d K L : ℕ} (hd : 0 < d) (hL : 0 < L) (hdK : K + 1 ≤ d)
    (hact : L * (d * d) ≤ T) :
    L * d < (2 * (T / padSize T d K) + 2) * (L + 2) := by
  set W := T / d with hW
  set MD := padSize T d K with hMD
  set Q := T / MD with hQ
  have hMDpos : 0 < MD := padSize_pos T d K
  have hWge : L * d ≤ W := by
    rw [hW, Nat.le_div_iff_mul_le hd]
    calc L * d * d = L * (d * d) := by ring
      _ ≤ T := hact
  have hWpos : 0 < W := lt_of_lt_of_le (Nat.mul_pos hL hd) hWge
  have hWd : W * d ≤ T := by
    rw [hW]
    exact Nat.div_mul_le_self T d
  have hTlt : T < (Q + 1) * MD := by
    have h1 := Nat.div_add_mod T MD
    have h2 : T % MD < MD := Nat.mod_lt _ hMDpos
    have : T = MD * Q + T % MD := by rw [hQ]; omega
    linarith only [this, h2]
  -- `A = 2d + 2K + 2 ≤ 4d`, hence `L·A ≤ 4W`
  have hA : MD = 2 * W + (2 * d + 2 * K + 2) := by unfold padSize at hMD; omega
  have hAle : 2 * d + 2 * K + 2 ≤ 4 * d := by omega
  have hLA : L * (2 * d + 2 * K + 2) ≤ 4 * W := by
    calc L * (2 * d + 2 * K + 2) ≤ L * (4 * d) := Nat.mul_le_mul_left _ hAle
      _ = 4 * (L * d) := by ring
      _ ≤ 4 * W := Nat.mul_le_mul_left _ hWge
  have hstep : L * (W * d) < (Q + 1) * (W * (2 * L + 4)) := by
    have h1 : L * (W * d) ≤ L * T := Nat.mul_le_mul_left _ hWd
    have h2 : L * T < L * ((Q + 1) * MD) := by
      exact Nat.mul_lt_mul_of_pos_left hTlt hL
    have h3 : L * ((Q + 1) * MD) = (Q + 1) * (2 * L * W + L * (2 * d + 2 * K + 2)) := by
      rw [hA]; ring
    have h4 : (Q + 1) * (2 * L * W + L * (2 * d + 2 * K + 2))
        ≤ (Q + 1) * (2 * L * W + 4 * W) := by
      exact Nat.mul_le_mul_left _ (by omega)
    have h5 : (Q + 1) * (2 * L * W + 4 * W) = (Q + 1) * (W * (2 * L + 4)) := by ring
    omega
  have hfinal : L * d < (Q + 1) * (2 * L + 4) := by
    have : W * (L * d) < W * ((Q + 1) * (2 * L + 4)) := by
      calc W * (L * d) = L * (W * d) := by ring
        _ < (Q + 1) * (W * (2 * L + 4)) := hstep
        _ = W * ((Q + 1) * (2 * L + 4)) := by ring
    exact Nat.lt_of_mul_lt_mul_left this
  calc L * d < (Q + 1) * (2 * L + 4) := hfinal
    _ = (2 * Q + 2) * (L + 2) := by ring


instance instNeZeroPadSize (T d K : ℕ) : NeZero (padSize T d K) :=
  ⟨by have := padSize_pos T d K; omega⟩

/-! ### The padded hypergraph attached to a degree ceiling -/

section Bridge

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The deficiency of `r` relative to the degree ceiling `d`. -/
def defic (H : Finset (Finset R)) (d : ℕ) : R → ℕ := fun r => d - degree H r

/-- The total deficiency. -/
def deficTot (H : Finset (Finset R)) (d : ℕ) : ℕ := ∑ r : R, defic H d r

theorem deficTot_eq_padTot (H : Finset (Finset R)) (d : ℕ) :
    deficTot H d = padTot (defic H d) := rfl

/-- The number of dummy vertices used to balance the degrees of `H` at ceiling `d`. -/
def dummyCard (H : Finset (Finset R)) (d K : ℕ) : ℕ := padSize (deficTot H d) d K

instance instNeZeroDummyCard (H : Finset (Finset R)) (d K : ℕ) : NeZero (dummyCard H d K) :=
  instNeZeroPadSize _ _ _

/-- The degree-balanced padding of `H` at ceiling `d`. -/
noncomputable def padded (H : Finset (Finset R)) (d K : ℕ) :
    Finset (Finset (R ⊕ Fin (dummyCard H d K))) :=
  padHyper (dummyCard H d K) H (defic H d) K

theorem defic_le_dummyCard (H : Finset (Finset R)) (d K : ℕ) (r : R) :
    defic H d r ≤ dummyCard H d K :=
  le_trans (Nat.sub_le _ _) (le_padSize _ _ _)

theorem two_K_lt_dummyCard (H : Finset (Finset R)) (d K : ℕ) : 2 * K < dummyCard H d K :=
  two_K_lt_padSize _ _ _

/-- Every real vertex of the padded hypergraph has degree exactly `d`. -/
theorem degree_padded_inl {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K)
    (hdeg : ∀ r, degree H r ≤ d) (r : R) :
    degree (padded H d K) (Sum.inl r) = d := by
  rw [padded, degree_padHyper_inl _ hK (two_K_lt_dummyCard H d K) (defic_le_dummyCard H d K)]
  have := hdeg r
  simp only [defic]
  omega

/-- The balanced block count of the padding. -/
def padQ (H : Finset (Finset R)) (d K : ℕ) : ℕ := deficTot H d / dummyCard H d K

theorem degree_padded_inr {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K)
    (x : Fin (dummyCard H d K)) :
    2 * padQ H d K ≤ degree (padded H d K) (Sum.inr x) ∧
      degree (padded H d K) (Sum.inr x) ≤ 2 * padQ H d K + 2 :=
  degree_padHyper_inr _ hK (two_K_lt_dummyCard H d K) (defic_le_dummyCard H d K) x

theorem two_padQ_lt {H : Finset (Finset R)} {d K : ℕ} (hd : 0 < d) : 2 * padQ H d K < d :=
  padQ_upper hd

/-- **All codegrees of the padded hypergraph are small.**  Real/real codegrees are inherited from
`H`, mixed codegrees are at most `4`, and dummy/dummy codegrees are at most `2 + (d+1)/K`. -/
theorem codegree_padded_le {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K) (hd : 0 < d)
    (hcod : ∀ x y : R, x ≠ y → codegree H x y ≤ 1)
    {u v : R ⊕ Fin (dummyCard H d K)} (hne : u ≠ v) :
    (codegree (padded H d K) u v : ℝ) ≤ 4 + ((d : ℝ) + 1) / (K : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hnn : (0 : ℝ) ≤ ((d : ℝ) + 1) / (K : ℝ) := by positivity
  have hKMD : 2 * K < dummyCard H d K := two_K_lt_dummyCard H d K
  have haMD := defic_le_dummyCard H d K
  match u, v with
  | Sum.inl r, Sum.inl r' =>
      have hrr : r ≠ r' := fun h => hne (by rw [h])
      have := codegree_padHyper_inl_inl (H := H) (a := defic H d) (K := K) _ hK hKMD haMD hrr
      have h1 : codegree (padded H d K) (Sum.inl r) (Sum.inl r') ≤ 1 := by
        rw [padded, this]; exact hcod r r' hrr
      have : (codegree (padded H d K) (Sum.inl r) (Sum.inl r') : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
  | Sum.inl r, Sum.inr x =>
      have h1 := codegree_padHyper_inl_inr (H := H) (a := defic H d) (K := K) _ hK hKMD haMD r x
      have : (codegree (padded H d K) (Sum.inl r) (Sum.inr x) : ℝ) ≤ 4 := by
        rw [padded]; exact_mod_cast h1
      linarith
  | Sum.inr x, Sum.inl r =>
      have h1 := codegree_padHyper_inl_inr (H := H) (a := defic H d) (K := K) _ hK hKMD haMD r x
      have h2 : codegree (padded H d K) (Sum.inr x) (Sum.inl r)
          = codegree (padded H d K) (Sum.inl r) (Sum.inr x) := codegree_symm _ _ _
      have : (codegree (padded H d K) (Sum.inr x) (Sum.inl r) : ℝ) ≤ 4 := by
        rw [h2, padded]; exact_mod_cast h1
      linarith
  | Sum.inr x, Sum.inr y =>
      have hxy : x ≠ y := fun h => hne (by rw [h])
      have h1 := codegree_padHyper_inr_inr (H := H) (a := defic H d) (K := K) _ hK hKMD haMD hxy
      have h2 : codegree (padded H d K) (Sum.inr x) (Sum.inr y)
          ≤ 2 * ((padQ H d K + 1) / K + 1) := by rw [padded]; exact h1
      have h3 : (((padQ H d K + 1) / K : ℕ) : ℝ) ≤ ((padQ H d K : ℝ) + 1) / (K : ℝ) := by
        have h := Nat.cast_div_le (α := ℝ) (m := padQ H d K + 1) (n := K)
        simpa using h
      have h4 : (2 : ℝ) * ((padQ H d K : ℝ) + 1) ≤ (d : ℝ) + 1 := by
        have hn : 2 * padQ H d K + 1 ≤ d := by
          have := two_padQ_lt (H := H) (d := d) (K := K) hd; omega
        have hr : ((2 * padQ H d K + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hn
        push_cast at hr
        linarith
      have h5 : (codegree (padded H d K) (Sum.inr x) (Sum.inr y) : ℝ)
          ≤ 2 * (((padQ H d K : ℝ) + 1) / (K : ℝ) + 1) := by
        have : (codegree (padded H d K) (Sum.inr x) (Sum.inr y) : ℝ)
            ≤ ((2 * ((padQ H d K + 1) / K + 1) : ℕ) : ℝ) := by exact_mod_cast h2
        refine le_trans this ?_
        push_cast
        have : (((padQ H d K + 1) / K : ℕ) : ℝ) ≤ ((padQ H d K : ℝ) + 1) / (K : ℝ) := h3
        linarith
      have hdiv : (2 * ((padQ H d K : ℝ) + 1)) / (K : ℝ) ≤ ((d : ℝ) + 1) / (K : ℝ) := by
        gcongr
      have hre : 2 * (((padQ H d K : ℝ) + 1) / (K : ℝ))
          = (2 * ((padQ H d K : ℝ) + 1)) / (K : ℝ) := by ring
      have h6 : 2 * (((padQ H d K : ℝ) + 1) / (K : ℝ) + 1) ≤ 4 + ((d : ℝ) + 1) / (K : ℝ) := by
        linarith
      linarith

/-- The padded hypergraph is `3`-uniform. -/
theorem padded_uniform {H : Finset (Finset R)} {d K : ℕ} (hunif : IsUniform H 3) (hK : 0 < K) :
    IsUniform (padded H d K) 3 :=
  padHyper_uniform _ hunif hK (by have := two_K_lt_dummyCard H d K; omega)

theorem card_padded_vertex (H : Finset (Finset R)) (d K : ℕ) :
    Fintype.card (R ⊕ Fin (dummyCard H d K)) = Fintype.card R + dummyCard H d K := by
  simp

/-- **The global degree ceiling** of the padded hypergraph. -/
theorem degree_padded_le_ceil {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K) (hd : 0 < d)
    (hdeg : ∀ r, degree H r ≤ d) {μ : ℝ} (hμd : 1 ≤ μ * (d : ℝ))
    (x : R ⊕ Fin (dummyCard H d K)) :
    (degree (padded H d K) x : ℝ) ≤ (1 + μ) * (d : ℝ) := by
  match x with
  | Sum.inl r =>
      rw [degree_padded_inl hK hdeg r]
      nlinarith only [hμd]
  | Sum.inr y =>
      have h := (degree_padded_inr (H := H) (d := d) (K := K) hK y).2
      have hQ : 2 * padQ H d K + 2 ≤ d + 1 := by
        have := two_padQ_lt (H := H) (d := d) (K := K) hd; omega
      have : degree (padded H d K) (Sum.inr y) ≤ d + 1 := le_trans h hQ
      have hr : (degree (padded H d K) (Sum.inr y) : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast this
      linarith

/-- **Near-regularity in the active regime** `K·d² ≤ ∑_r (d - deg_H r)`: every vertex, real or
dummy, has degree within `(1±μ)d`, so the exceptional set is empty. -/
theorem padded_nearlyRegularMost_active {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K)
    (hdK : K + 1 ≤ d) (hdeg : ∀ r, degree H r ≤ d) {μ : ℝ} (hμ : 0 < μ)
    (hμK : 4 / μ ≤ (K : ℝ)) (hμd : 4 ≤ μ * (d : ℝ))
    (hact : K * (d * d) ≤ deficTot H d) {η : ℝ} (hη : 0 ≤ η) :
    NearlyRegularMost (padded H d K) (d : ℝ) μ η := by
  have hd : 0 < d := by omega
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hkR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hμkR : 4 ≤ μ * (K : ℝ) := by
    rw [div_le_iff₀ hμ] at hμK; linarith
  refine ⟨∅, ?_, ?_⟩
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hη (Nat.cast_nonneg _)
  intro v _
  refine ⟨?_, degree_padded_le_ceil hK hd hdeg (by linarith) v⟩
  match v with
  | Sum.inl r =>
      rw [degree_padded_inl hK hdeg r]
      nlinarith
  | Sum.inr y =>
      have hlow := (degree_padded_inr (H := H) (d := d) (K := K) hK y).1
      have hlowR : (2 * padQ H d K : ℝ) ≤ (degree (padded H d K) (Sum.inr y) : ℝ) := by
        exact_mod_cast hlow
      -- the balanced block count is close to `d/2`
      have hQ := padQ_lower (T := deficTot H d) (d := d) (K := K) (L := K) hd hK hdK
        (by rw [deficTot_eq_padTot] at hact ⊢; exact hact)
      have hQR : (K : ℝ) * (d : ℝ) < (2 * (padQ H d K : ℝ) + 2) * ((K : ℝ) + 2) := by
        have : ((K * d : ℕ) : ℝ) < (((2 * padQ H d K + 2) * (K + 2) : ℕ) : ℝ) := by
          exact_mod_cast hQ
        push_cast at this
        linarith
      set q : ℝ := (padQ H d K : ℝ)
      set D : ℝ := (d : ℝ)
      set k : ℝ := (K : ℝ)
      have e1 : 4 * D ≤ μ * D * k := by nlinarith
      have e2 : 4 * k ≤ μ * D * k := by nlinarith
      have hsuff : 2 * D + 2 * k + 4 ≤ μ * D * k + 2 * (μ * D) := by nlinarith
      have hexp : (1 - μ) * D * (k + 2) ≤ k * D - 2 * (k + 2) := by nlinarith
      have hlt : (1 - μ) * D * (k + 2) < (2 * q) * (k + 2) := by nlinarith
      have hk2 : (0 : ℝ) < k + 2 := by linarith
      have : (1 - μ) * D < 2 * q := lt_of_mul_lt_mul_right hlt (le_of_lt hk2)
      linarith

/-- **Near-regularity in the inactive regime**: the padding is small, so all dummy vertices fit into
the exceptional set, while every real vertex has degree exactly `d`. -/
theorem padded_nearlyRegularMost_inactive {H : Finset (Finset R)} {d K : ℕ} (hK : 0 < K)
    (hd : 0 < d) (hdeg : ∀ r, degree H r ≤ d) {μ : ℝ} (hμ : 0 < μ) {η : ℝ}
    (hEx : (dummyCard H d K : ℝ)
      ≤ η * (Fintype.card (R ⊕ Fin (dummyCard H d K)) : ℝ)) :
    NearlyRegularMost (padded H d K) (d : ℝ) μ η := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  classical
  set inr' : Fin (dummyCard H d K) → R ⊕ Fin (dummyCard H d K) := Sum.inr with hinr'
  refine ⟨(Finset.univ : Finset (Fin (dummyCard H d K))).image inr', ?_, ?_⟩
  · have hcard : ((Finset.univ : Finset (Fin (dummyCard H d K))).image inr').card
        = dummyCard H d K := by
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
        Fintype.card_fin]
    rw [hcard]
    exact hEx
  · intro v hv
    match v with
    | Sum.inl r =>
        rw [degree_padded_inl hK hdeg r]
        constructor
        · nlinarith
        · nlinarith
    | Sum.inr y =>
        exact absurd (Finset.mem_image_of_mem inr' (Finset.mem_univ y)) hv

theorem deficTot_le (H : Finset (Finset R)) (d : ℕ) : deficTot H d ≤ Fintype.card R * d := by
  rw [deficTot]
  calc ∑ r : R, defic H d r ≤ ∑ _r : R, d := Finset.sum_le_sum fun r _ => Nat.sub_le _ _
    _ = Fintype.card R * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem dummyCard_le_of_inactive {H : Finset (Finset R)} {d K : ℕ} (hd : 0 < d)
    (hin : deficTot H d < K * (d * d)) : dummyCard H d K ≤ (4 * K + 4) * d := by
  have h1 : deficTot H d / d ≤ K * d := by
    calc deficTot H d / d ≤ (K * (d * d)) / d := Nat.div_le_div_right (le_of_lt hin)
      _ = K * d := by
          rw [show K * (d * d) = (K * d) * d by ring, Nat.mul_div_cancel _ hd]
  have h2 : dummyCard H d K = 2 * (deficTot H d / d) + 2 * d + 2 * K + 2 := rfl
  have h3 : K ≤ K * d := Nat.le_mul_of_pos_right K hd
  have h4 : (4 * K + 4) * d = 4 * (K * d) + 4 * d := by ring
  rw [h4]
  set m := K * d with hm
  omega

end Bridge

/-! ### Monotonicity of majority near-regularity in the tolerance -/

theorem nearlyRegularMost_mono {W : Type} [Fintype W] [DecidableEq W] {Hp : Finset (Finset W)}
    {d μ μ' η : ℝ} (hd : 0 ≤ d) (hle : μ ≤ μ') (h : NearlyRegularMost Hp d μ η) :
    NearlyRegularMost Hp d μ' η := by
  obtain ⟨Exc, hExc, hband⟩ := h
  refine ⟨Exc, hExc, fun v hv => ⟨?_, ?_⟩⟩
  · have := (hband v hv).1; nlinarith
  · have := (hband v hv).2; nlinarith

/-! ### The deficiency-aware rounding theorem -/

/-- **Rounding a degree ceiling to a matching.**  For a `3`-uniform hypergraph `H` of codegree `≤ 1`
all of whose degrees are at most `d`, the number of vertices left uncovered by a suitable matching
exceeds the total deficiency divided by `d` by at most `ε|R|`.  Note that `H` is *not* assumed to be
near-regular: the deficiency term measures exactly how far it is from `d`-regular. -/
theorem exists_matching_defic (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∃ C : ℝ, ∀ {R : Type} [Fintype R] [DecidableEq R]
      (H : Finset (Finset R)) (d : ℕ),
      d₀ ≤ d → IsUniform H 3 → (∀ x y : R, x ≠ y → codegree H x y ≤ 1) →
      (∀ r : R, degree H r ≤ d) → C * (d : ℝ) ≤ (Fintype.card R : ℝ) →
      ∃ M : Finset (Finset R), IsMatching H M ∧
        (Fintype.card R : ℝ) - 3 * (M.card : ℝ)
          ≤ (deficTot H d : ℝ) / (d : ℝ) + ε * (Fintype.card R : ℝ) := by
  obtain ⟨μ, hμ, η, hη, dr₀, hdr₀, hmain⟩ :=
    nibbleTheoremMostCeil_holds 3 (by norm_num) (ε / 6) (by positivity)
  set μ₁ : ℝ := min μ 1 with hμ₁def
  have hμ₁ : 0 < μ₁ := lt_min hμ one_pos
  have hμ₁le : μ₁ ≤ μ := min_le_left _ _
  set K : ℕ := ⌈8 / μ₁⌉₊ + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hKμ : 8 / μ₁ ≤ (K : ℝ) := by
    have h := Nat.le_ceil (8 / μ₁)
    rw [hKdef]; push_cast; linarith
  have hμ₁K : 8 ≤ μ₁ * (K : ℝ) := by rw [div_le_iff₀ hμ₁] at hKμ; linarith
  refine ⟨max (⌈dr₀⌉₊ + 1) (K + 1), 4 * (1 + ε) / ε + (4 * (K : ℝ) + 4) / η + 1, ?_⟩
  intro R _ _ H d hd hunif hcod hdeg hN
  set N : ℝ := (Fintype.card R : ℝ) with hNdef
  have hdK : K + 1 ≤ d := le_trans (le_max_right _ _) hd
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hKd : (K : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hdK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hdr : dr₀ ≤ (d : ℝ) := by
    have h1 : ⌈dr₀⌉₊ + 1 ≤ d := le_trans (le_max_left _ _) hd
    have h2 : (⌈dr₀⌉₊ : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : ⌈dr₀⌉₊ ≤ d)
    exact le_trans (Nat.le_ceil _) h2
  have hμ₁d : 8 ≤ μ₁ * (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hKd (le_of_lt hμ₁)
    linarith only [h, hμ₁K, hμ₁]
  -- the padded hypergraph satisfies all four nibble hypotheses
  have hunifP : IsUniform (padded H d K) 3 := padded_uniform hunif hK
  have hceil : ∀ x : R ⊕ Fin (dummyCard H d K),
      (degree (padded H d K) x : ℝ) ≤ (1 + μ) * (d : ℝ) := by
    intro x
    have h := degree_padded_le_ceil (H := H) (d := d) (K := K) hK hdpos hdeg
      (μ := μ₁) (by linarith) x
    refine le_trans h ?_
    have := mul_le_mul_of_nonneg_right hμ₁le (le_of_lt hdR)
    linarith
  have hcodP : CodegreeBounded (padded H d K) (μ * (d : ℝ)) := by
    intro u v huv
    refine le_trans (codegree_padded_le hK hdpos hcod huv) ?_
    have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
    have hstep : ((d : ℝ) + 1) / (K : ℝ) ≤ μ₁ * (d : ℝ) / 4 := by
      rw [div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 4)]
      linarith only [mul_le_mul_of_nonneg_left hμ₁K (le_of_lt hdR), hd1]
    have hmono := mul_le_mul_of_nonneg_right hμ₁le (le_of_lt hdR)
    linarith
  have hcardW : (Fintype.card (R ⊕ Fin (dummyCard H d K)) : ℝ) = N + (dummyCard H d K : ℝ) := by
    rw [card_padded_vertex]; push_cast; ring
  -- the size budget
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hAnn : (0 : ℝ) ≤ 4 * (1 + ε) / ε := by positivity
  have hBnn : (0 : ℝ) ≤ (4 * (K : ℝ) + 4) / η := by positivity
  have hCa : (4 * (1 + ε) / ε) * (d : ℝ) ≤ N := by
    have h1 : (0 : ℝ) ≤ ((4 * (K : ℝ) + 4) / η) * (d : ℝ) :=
      mul_nonneg hBnn (le_of_lt hdR)
    linarith only [hN, h1, hdR]
  have hCb : ((4 * (K : ℝ) + 4) / η) * (d : ℝ) ≤ N := by
    have h1 : (0 : ℝ) ≤ (4 * (1 + ε) / ε) * (d : ℝ) := mul_nonneg hAnn (le_of_lt hdR)
    linarith only [hN, h1, hdR]
  have hCa' : (4 + 4 * ε) * (d : ℝ) ≤ ε * N := by
    have h := mul_le_mul_of_nonneg_left hCa (le_of_lt hε)
    have he : ε * (4 * (1 + ε) / ε * (d : ℝ)) = (4 + 4 * ε) * (d : ℝ) := by
      field_simp
    linarith
  have hCb' : (4 * (K : ℝ) + 4) * (d : ℝ) ≤ η * N := by
    have h := mul_le_mul_of_nonneg_left hCb (le_of_lt hη)
    have he : η * ((4 * (K : ℝ) + 4) / η * (d : ℝ)) = (4 * (K : ℝ) + 4) * (d : ℝ) := by
      field_simp
    linarith
  have hregP : NearlyRegularMost (padded H d K) (d : ℝ) μ η := by
    by_cases hact : K * (d * d) ≤ deficTot H d
    · refine nearlyRegularMost_mono (le_of_lt hdR) hμ₁le ?_
      have h4K : (4 : ℝ) / μ₁ ≤ (K : ℝ) := by rw [div_le_iff₀ hμ₁]; linarith
      exact padded_nearlyRegularMost_active hK hdK hdeg hμ₁ h4K (by linarith) hact (le_of_lt hη)
    · refine padded_nearlyRegularMost_inactive hK hdpos hdeg hμ ?_
      rw [hcardW]
      have hle : dummyCard H d K ≤ (4 * K + 4) * d :=
        dummyCard_le_of_inactive hdpos (by omega)
      have hleR : (dummyCard H d K : ℝ) ≤ (4 * (K : ℝ) + 4) * (d : ℝ) := by
        have hc : ((dummyCard H d K : ℕ) : ℝ) ≤ (((4 * K + 4) * d : ℕ) : ℝ) := by
          exact_mod_cast hle
        push_cast at hc; linarith
      have hMDnn : (0 : ℝ) ≤ (dummyCard H d K : ℝ) := Nat.cast_nonneg _
      have hηMD : (0 : ℝ) ≤ η * (dummyCard H d K : ℝ) := mul_nonneg (le_of_lt hη) hMDnn
      linarith only [hCb', hleR, hηMD]
  obtain ⟨M, hMmatch, hMcard⟩ :=
    hmain (padded H d K) (d : ℝ) hdR hdr hunifP hregP hcodP hceil
  refine ⟨pullback (dummyCard H d K) H M, pullback_isMatching _ hMmatch, ?_⟩
  set M' := pullback (dummyCard H d K) H M with hM'def
  have hpull : 2 * M.card ≤ 2 * M'.card + dummyCard H d K :=
    card_le_pullback_add _ hK (two_K_lt_dummyCard H d K) hMmatch
  have hpullR : 2 * (M.card : ℝ) ≤ 2 * (M'.card : ℝ) + (dummyCard H d K : ℝ) := by
    exact_mod_cast hpull
  have hMcard' : (1 - ε / 6) * ((N + (dummyCard H d K : ℝ)) / 3) ≤ (M.card : ℝ) := by
    have h := hMcard
    rw [hcardW] at h
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3] at h
    exact h
  set P : ℝ := (deficTot H d : ℝ) / (d : ℝ) with hPdef
  have hPnn : (0 : ℝ) ≤ P := by positivity
  have hPN : P ≤ N := by
    rw [hPdef, div_le_iff₀ hdR]
    have hle := deficTot_le H d
    have h2 : ((deficTot H d : ℕ) : ℝ) ≤ ((Fintype.card R * d : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast at h2
    linarith
  have hMDle : (dummyCard H d K : ℝ) ≤ 2 * P + 2 * (d : ℝ) + 2 * (K : ℝ) + 2 := by
    have h2 : dummyCard H d K = 2 * (deficTot H d / d) + 2 * d + 2 * K + 2 := rfl
    have h3 : ((deficTot H d / d : ℕ) : ℝ) ≤ P := by
      rw [hPdef]; exact Nat.cast_div_le
    have h4 : ((dummyCard H d K : ℕ) : ℝ)
        = 2 * ((deficTot H d / d : ℕ) : ℝ) + 2 * (d : ℝ) + 2 * (K : ℝ) + 2 := by
      rw [h2]; push_cast; ring
    rw [h4]; linarith
  have hMDnn : (0 : ℝ) ≤ (dummyCard H d K : ℝ) := Nat.cast_nonneg _
  have hεMD : ε * (dummyCard H d K : ℝ) ≤ ε * (2 * P + 2 * (d : ℝ) + 2 * (K : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hMDle (le_of_lt hε)
  have hεP : ε * P ≤ ε * N := mul_le_mul_of_nonneg_left hPN (le_of_lt hε)
  have hεK : ε * ((K : ℝ) + 1) ≤ ε * (d : ℝ) := mul_le_mul_of_nonneg_left hKd (le_of_lt hε)
  have hεD : (0 : ℝ) ≤ ε * (d : ℝ) := by positivity
  linarith

end Nibble.Pad
