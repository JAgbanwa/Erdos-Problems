module

public import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Mean square density of a partition

For a partition `P` of the vertex set of a graph `G` on `n` vertices, the *mean square density*
(the "index" in the proofs of the regularity lemmas) is
`q(P) = ∑_{i ≠ j} d(Vᵢ, Vⱼ)² |Vᵢ| |Vⱼ| / n²`.
We write it vertex by vertex: `q(P) = n⁻² ∑_{a, b : P(a) ≠ P(b)} d(P(a), P(b))²`, where `P(a)` is the
part containing `a`.

The main result is the *variance inequality*: if `B` refines `A` then
`∑_{a, b : A(a) ≠ A(b)} (d(B(a), B(b)) - d(A(a), A(b)))² ≤ n² (q(B) - q(A))`.
So if `q(B)` is close to `q(A)`, then for most pairs of vertices the density between their
`B`-parts is close to the density between their `A`-parts.
-/

@[expose] public section

open Finset Fintype

namespace AFKS

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edge density `d(s, t)` as a real number. -/
noncomputable def dens (s t : Finset V) : ℝ := (G.edgeDensity s t : ℝ)

/-- `d(P(a), P(b))`: the density between the parts of `P` containing `a` and `b`. -/
noncomputable def pd (P : Finpartition (univ : Finset V)) (a b : V) : ℝ :=
  dens G (P.part a) (P.part b)

/-- The mean square density `q(P) = n⁻² ∑_{a, b : P(a) ≠ P(b)} d(P(a), P(b))²`. -/
noncomputable def msd (P : Finpartition (univ : Finset V)) : ℝ :=
  (∑ a, ∑ b, if P.part a ≠ P.part b then pd G P a b ^ 2 else 0) / (card V : ℝ) ^ 2

omit [Fintype V] [DecidableEq V] in
theorem dens_nonneg (s t : Finset V) : 0 ≤ dens G s t := by
  unfold dens; exact_mod_cast G.edgeDensity_nonneg s t

omit [Fintype V] [DecidableEq V] in
theorem dens_le_one (s t : Finset V) : dens G s t ≤ 1 := by
  unfold dens; exact_mod_cast G.edgeDensity_le_one s t

theorem msd_nonneg (P : Finpartition (univ : Finset V)) : 0 ≤ msd G P := by
  unfold msd
  refine div_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_) (by positivity)
  split_ifs <;> positivity

theorem msd_le_one (P : Finpartition (univ : Finset V)) : msd G P ≤ 1 := by
  unfold msd
  rcases Nat.eq_zero_or_pos (card V) with h0 | hpos
  · simp [h0]
  rw [div_le_one (by positivity)]
  calc (∑ a, ∑ b, if P.part a ≠ P.part b then pd G P a b ^ 2 else 0)
      ≤ ∑ _a : V, ∑ _b : V, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · have h0 := dens_nonneg G (P.part a) (P.part b)
          have h1 := dens_le_one G (P.part a) (P.part b)
          unfold pd; nlinarith
        · norm_num
    _ = (card V : ℝ) ^ 2 := by simp [Finset.card_univ]; ring

/-- Edge indicator. -/
noncomputable def ind (a b : V) : ℝ := if G.Adj a b then 1 else 0

omit [Fintype V] [DecidableEq V] in
/-- `|s| |t| d(s, t) = e(s, t)` for nonempty `s`, `t`. -/
theorem card_mul_card_mul_dens {s t : Finset V} (hs : s.Nonempty) (ht : t.Nonempty) :
    (#s : ℝ) * #t * dens G s t = ∑ a ∈ s, ∑ b ∈ t, ind G a b := by
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have ht' : (0 : ℝ) < #t := by exact_mod_cast ht.card_pos
  unfold dens ind
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  rw [mul_div_cancel₀ _ (by positivity)]
  unfold SimpleGraph.interedges Rel.interedges
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  rfl

/-- Summing over a partition part by part. -/
theorem sum_univ_eq_sum_parts (P : Finpartition (univ : Finset V)) (g : V → ℝ) :
    ∑ a, g a = ∑ U ∈ P.parts, ∑ a ∈ U, g a := by
  conv_lhs => rw [← P.biUnion_parts]
  rw [Finset.sum_biUnion P.disjoint]
  rfl

/-- If `B` refines `A`, a part `U` of `A` is the union of the parts of `B` inside it. -/
theorem sum_part_eq_sum_subparts {A B : Finpartition (univ : Finset V)} (hBA : B ≤ A)
    {U : Finset V} (hU : U ∈ A.parts) (g : V → ℝ) :
    ∑ a ∈ U, g a = ∑ U' ∈ B.parts.filter (· ⊆ U), ∑ a ∈ U', g a := by
  have hUeq : U = (B.parts.filter (· ⊆ U)).biUnion id := by
    ext x
    constructor
    · intro hx
      refine Finset.mem_biUnion.2 ⟨B.part x, Finset.mem_filter.2 ⟨B.part_mem.2 (mem_univ x), ?_⟩,
        B.mem_part (mem_univ x)⟩
      obtain ⟨C, hC, hBC⟩ := hBA (B.part_mem.2 (mem_univ x))
      have hxC : x ∈ C := hBC (B.mem_part (mem_univ x))
      have : C = U := by
        rw [← A.part_eq_of_mem hC hxC, A.part_eq_of_mem hU hx]
      rw [← this]; exact hBC
    · intro hx
      obtain ⟨U', hU', hxU'⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hU').2 hxU'
  conv_lhs => rw [hUeq]
  rw [Finset.sum_biUnion]
  · rfl
  · exact B.disjoint.subset (by intro x hx; exact (Finset.mem_filter.1 hx).1)

/-- On a block `U × W` of parts of `P`, the densities `d(P(a), P(b))` add up to `e(U, W)`. -/
theorem sum_pd_block (P : Finpartition (univ : Finset V)) {U W : Finset V} (hU : U ∈ P.parts)
    (hW : W ∈ P.parts) : ∑ a ∈ U, ∑ b ∈ W, pd G P a b = ∑ a ∈ U, ∑ b ∈ W, ind G a b := by
  have h : ∑ a ∈ U, ∑ b ∈ W, pd G P a b = ∑ a ∈ U, ∑ b ∈ W, dens G U W := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    unfold pd
    rw [P.part_eq_of_mem hU ha, P.part_eq_of_mem hW hb]
  rw [h, ← card_mul_card_mul_dens G (Finset.nonempty_iff_ne_empty.2 (P.ne_bot hU))
    (Finset.nonempty_iff_ne_empty.2 (P.ne_bot hW))]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- If `B` refines `A`, then on a block `U × W` of parts of `A` the densities of `B` and of `A`
have the same sum. -/
theorem sum_pd_block_refine {A B : Finpartition (univ : Finset V)} (hBA : B ≤ A)
    {U W : Finset V} (hU : U ∈ A.parts) (hW : W ∈ A.parts) :
    ∑ a ∈ U, ∑ b ∈ W, pd G B a b = ∑ a ∈ U, ∑ b ∈ W, pd G A a b := by
  rw [sum_pd_block G A hU hW]
  have decomp : ∀ g : V → V → ℝ, ∑ a ∈ U, ∑ b ∈ W, g a b =
      ∑ U' ∈ B.parts.filter (· ⊆ U), ∑ W' ∈ B.parts.filter (· ⊆ W),
        ∑ a ∈ U', ∑ b ∈ W', g a b := by
    intro g
    rw [sum_part_eq_sum_subparts hBA hU]
    refine Finset.sum_congr rfl fun U' _ => ?_
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; skip
    have : ∀ b, ∑ a ∈ U', g a b = ∑ a ∈ U', g a b := fun b => rfl
    rw [sum_part_eq_sum_subparts hBA hW (fun b => ∑ a ∈ U', g a b)]
    refine Finset.sum_congr rfl fun W' _ => ?_
    rw [Finset.sum_comm]
  rw [decomp, decomp]
  refine Finset.sum_congr rfl fun U' hU' => Finset.sum_congr rfl fun W' hW' => ?_
  exact sum_pd_block G B (Finset.mem_filter.1 hU').1 (Finset.mem_filter.1 hW').1

/-- If `B` refines `A` and two vertices are in different parts of `A`, they are in different
parts of `B`. -/
theorem part_ne_of_le {A B : Finpartition (univ : Finset V)} (hBA : B ≤ A) {a b : V}
    (h : A.part a ≠ A.part b) : B.part a ≠ B.part b := by
  intro hB
  apply h
  obtain ⟨C, hC, hBC⟩ := hBA (B.part_mem.2 (mem_univ a))
  rw [A.part_eq_of_mem hC (hBC (B.mem_part (mem_univ a))),
    A.part_eq_of_mem hC (hBC (hB ▸ B.mem_part (mem_univ b)))]

/-- **Variance inequality.** If `B` refines `A`, then
`∑_{a, b : A(a) ≠ A(b)} (d(B(a), B(b)) - d(A(a), A(b)))² ≤ n² (q(B) - q(A))`. -/
theorem sum_sq_sub_le_msd_sub {A B : Finpartition (univ : Finset V)} (hBA : B ≤ A) :
    (∑ a, ∑ b, if A.part a ≠ A.part b then (pd G B a b - pd G A a b) ^ 2 else 0) ≤
      (card V : ℝ) ^ 2 * (msd G B - msd G A) := by
  -- the cross term vanishes
  have hK : (∑ a, ∑ b, if A.part a ≠ A.part b then pd G A a b * (pd G B a b - pd G A a b)
      else 0) = 0 := by
    rw [sum_univ_eq_sum_parts A]
    refine Finset.sum_eq_zero fun U hU => ?_
    rw [Finset.sum_comm' (t' := univ) (s' := fun _ => U) (by simp)]
    rw [sum_univ_eq_sum_parts A]
    refine Finset.sum_eq_zero fun W hW => ?_
    have h : ∀ b ∈ W, ∀ a ∈ U, (if A.part a ≠ A.part b then
        pd G A a b * (pd G B a b - pd G A a b) else 0) =
        if U ≠ W then dens G U W * (pd G B a b - pd G A a b) else 0 := by
      intro b hb a ha
      rw [A.part_eq_of_mem hU ha, A.part_eq_of_mem hW hb]
      unfold pd
      rw [A.part_eq_of_mem hU ha, A.part_eq_of_mem hW hb]
    rw [Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl (h b hb)]
    split_ifs with hUW
    · rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      rw [sum_pd_block_refine G hBA hU hW, sub_self, mul_zero]
    · simp
  have hpos : (0 : ℝ) ≤ (card V : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos (card V) with h0 | hcard
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 h0
    simp
  have hcard' : (0 : ℝ) < (card V : ℝ) ^ 2 := by positivity
  unfold msd
  rw [mul_sub, mul_div_cancel₀ _ hcard'.ne', mul_div_cancel₀ _ hcard'.ne']
  -- pointwise inequality
  have hpt : ∀ a b, (if A.part a ≠ A.part b then (pd G B a b - pd G A a b) ^ 2 else 0) ≤
      (if B.part a ≠ B.part b then pd G B a b ^ 2 else 0) -
        (if A.part a ≠ A.part b then pd G A a b ^ 2 else 0) -
        2 * (if A.part a ≠ A.part b then pd G A a b * (pd G B a b - pd G A a b) else 0) := by
    intro a b
    by_cases hA : A.part a ≠ A.part b
    · rw [if_pos hA, if_pos hA, if_pos hA, if_pos (part_ne_of_le hBA hA)]
      nlinarith
    · rw [if_neg hA, if_neg hA, if_neg hA]
      split_ifs <;> nlinarith [sq_nonneg (pd G B a b)]
  calc _ ≤ ∑ a, ∑ b, ((if B.part a ≠ B.part b then pd G B a b ^ 2 else 0) -
        (if A.part a ≠ A.part b then pd G A a b ^ 2 else 0) -
        2 * (if A.part a ≠ A.part b then pd G A a b * (pd G B a b - pd G A a b) else 0)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hK]; ring

end AFKS
