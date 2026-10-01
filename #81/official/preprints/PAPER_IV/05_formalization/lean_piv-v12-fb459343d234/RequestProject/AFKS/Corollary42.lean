module

public import RequestProject.AFKS.Lemma41
public import RequestProject.AFKS.Selection
import Mathlib.Data.Nat.Choose.Cast

/-!
# Corollary 4.2 of AFKS (= Lemma 3.8 of Alon–Shapira)

> **Lemma 3.8 of Alon–Shapira ([AFKS, Corollary 4.2]).** For every integer `m` and every function
> `E : ℕ → (0, 1)` there is `S = S(m, E)` such that every graph `G` on `n ≥ S` vertices has an
> equipartition `A = {Vᵢ | 1 ≤ i ≤ k}` of `V(G)` and an induced subgraph `U` of `G` with an
> equipartition `B = {Uᵢ | 1 ≤ i ≤ k}` of the vertices of `U` that satisfy:
> 1. `m ≤ k ≤ S`;
> 2. `Uᵢ ⊆ Vᵢ` for all `i`, and `|Uᵢ| ≥ n/S`;
> 3. in the equipartition `B`, all pairs are `E(k)`-regular;
> 4. all but at most `E(0) (k choose 2)` of the pairs `1 ≤ i < j ≤ k` satisfy
>    `|d(Vᵢ, Vⱼ) - d(Uᵢ, Uⱼ)| < E(0)`.

Alon–Shapira state it for monotone non-increasing `E`. The proof does not use monotonicity, so we
drop that hypothesis.

## Proof

Apply the strong regularity lemma `strong_regularity` with `f(k) = E(k) / (64 (k+1)²)` and
`θ = E(0)³ / 64`. This gives `A` (with `k` parts) and a refinement `B`. Choose a uniformly random
vertex `xᵢ ∈ Vᵢ` in every part of `A`, and let `Uᵢ` be the part of `B` containing `xᵢ`.
* The expected number of ordered pairs `(Uᵢ, Uⱼ)`, `i ≠ j`, that are not `f(k)`-uniform is at most
  `E(k)/4 < 1/4`, because `B` is `f(k)`-uniform.
* By the variance inequality `sum_sq_sub_le_msd_sub` and Chebyshev, the expected number of
  ordered pairs with `|d(Vᵢ, Vⱼ) - d(Uᵢ, Uⱼ)| ≥ E(0)` is at most `(1/4) E(0) (k choose 2)`.
Hence some choice has no irregular pair and fewer than `E(0) (k choose 2)` bad pairs.
-/

@[expose] public section

open Finset Fintype

universe u

namespace AFKS

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Definition 3.1 of Alon–Shapira (`γ`-regular pair).** `(A, B)` is `γ`-regular if for all
`A' ⊆ A`, `B' ⊆ B` with `|A'| ≥ γ|A|` and `|B'| ≥ γ|B|` we have `|d(A', B') - d(A, B)| ≤ γ`. -/
def IsRegularPair (γ : ℝ) (A B : Finset V) : Prop :=
  ∀ A' ⊆ A, ∀ B' ⊆ B, γ * #A ≤ #A' → γ * #B ≤ #B' → |dens G A' B' - dens G A B| ≤ γ

omit [Fintype V] [DecidableEq V] in
/-- Mathlib's `ε`-uniformity of a pair implies `γ`-regularity for every `γ ≥ ε`. -/
theorem isRegularPair_of_isUniform {ε γ : ℝ} (hεγ : ε ≤ γ) {A B : Finset V}
    (h : G.IsUniform ε A B) : IsRegularPair G γ A B := by
  intro A' hA' B' hB' hA'c hB'c
  have hε0 : 0 < ε := h.pos
  have := h.mono hεγ hA' hB' (by linarith) (by linarith)
  unfold dens
  exact this.le

/-- Sizes of the parts of an equipartition of `V` into `p ≤ n` parts: `n ≤ 2p|U|` and
`p|U| ≤ 2n`. -/
theorem card_part_bounds {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition)
    (hp : #P.parts ≤ card V) {U : Finset V} (hU : U ∈ P.parts) :
    card V ≤ 2 * #P.parts * #U ∧ #P.parts * #U ≤ 2 * card V := by
  have h1 := IsEquipartition.mul_card_sub_one_lt hP hU
  have h2 := IsEquipartition.lt_mul_card_add_one hP hU
  have h3 := hP.average_le_card_part hU
  rw [card_univ] at h1 h2 h3
  have hpos : 0 < #P.parts := Finset.card_pos.2 ⟨U, hU⟩
  have hU1 : 1 ≤ #U := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (P.ne_bot hU))
  have h4 : 1 ≤ card V / #P.parts := (Nat.le_div_iff_mul_le hpos).2 (by omega)
  constructor
  · have : #P.parts * 1 ≤ #P.parts * #U := Nat.mul_le_mul_left _ hU1
    nlinarith
  · have : #P.parts * (#U - 1) + #P.parts = #P.parts * #U := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- If `B` is an `ε`-uniform equipartition into `p ≤ n` parts, the number of ordered pairs of
vertices lying in distinct, non-`ε`-uniform parts is at most `4 ε n²`. -/
theorem sum_nonuniform_le {B : Finpartition (univ : Finset V)} (hB : B.IsEquipartition)
    (hp : #B.parts ≤ card V) {ε : ℝ} (hε : 0 ≤ ε) (hBu : B.IsUniform G ε) :
    (∑ a, ∑ b, if B.part a ≠ B.part b ∧ ¬ G.IsUniform ε (B.part a) (B.part b) then (1 : ℝ)
      else 0) ≤ 4 * ε * (card V : ℝ) ^ 2 := by
  set p := #B.parts
  set n := card V
  set I : Finset V → Finset V → ℝ := fun U W =>
    if U ≠ W ∧ ¬ G.IsUniform ε U W then (1 : ℝ) else 0 with hI
  have hIn : ∀ U W, 0 ≤ I U W := fun U W => by simp only [hI]; split_ifs <;> norm_num
  -- regroup by parts
  have h1 : (∑ a, ∑ b, if B.part a ≠ B.part b ∧ ¬ G.IsUniform ε (B.part a) (B.part b)
      then (1 : ℝ) else 0) = ∑ U ∈ B.parts, ∑ W ∈ B.parts, (#U : ℝ) * #W * I U W := by
    rw [sum_univ_eq_sum_parts B]
    refine Finset.sum_congr rfl fun U hU => ?_
    have : ∀ a ∈ U, (∑ b, if B.part a ≠ B.part b ∧ ¬ G.IsUniform ε (B.part a) (B.part b)
        then (1 : ℝ) else 0) = ∑ W ∈ B.parts, (#W : ℝ) * I U W := by
      intro a ha
      rw [sum_univ_eq_sum_parts B]
      refine Finset.sum_congr rfl fun W hW => ?_
      rw [Finset.sum_congr rfl fun b hb => by rw [B.part_eq_of_mem hU ha, B.part_eq_of_mem hW hb]]
      simp [hI]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W _ => by ring
  -- count of non-uniform pairs
  have h2 : ∑ U ∈ B.parts, ∑ W ∈ B.parts, I U W = #(B.nonUniforms G ε) := by
    have : B.nonUniforms G ε =
        (B.parts ×ˢ B.parts).filter (fun x => x.1 ≠ x.2 ∧ ¬ G.IsUniform ε x.1 x.2) := by
      ext x
      simp [Finpartition.nonUniforms, Finset.mem_offDiag, and_assoc]
    rw [this, Finset.card_filter, ← Finset.sum_product']
    push_cast
    rfl
  have hBu' : (#(B.nonUniforms G ε) : ℝ) ≤ (p * (p - 1) : ℕ) * ε := hBu
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · rw [h1]
    have : B.parts = ∅ := Finset.card_eq_zero.1 hp0
    simp [this]
    positivity
  -- each block has at most `(2n/p)²` pairs
  have hsz : ∀ U ∈ B.parts, (#U : ℝ) ≤ 2 * n / p := by
    intro U hU
    have := (card_part_bounds hB hp hU).2
    rw [le_div_iff₀ (by exact_mod_cast hppos)]
    exact_mod_cast (by linarith : #U * p ≤ 2 * n)
  rw [h1]
  calc ∑ U ∈ B.parts, ∑ W ∈ B.parts, (#U : ℝ) * #W * I U W
      ≤ ∑ U ∈ B.parts, ∑ W ∈ B.parts, (2 * n / p) * (2 * n / p) * I U W := by
        refine Finset.sum_le_sum fun U hU => Finset.sum_le_sum fun W hW => ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hsz U hU) (hsz W hW) (by positivity)
          (by positivity)) (hIn U W)
    _ = (2 * n / p) * (2 * n / p) * #(B.nonUniforms G ε) := by
        rw [← h2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => by rw [Finset.mul_sum]
    _ ≤ (2 * n / p) * (2 * n / p) * ((p * (p - 1) : ℕ) * ε) :=
        mul_le_mul_of_nonneg_left hBu' (by positivity)
    _ ≤ 4 * ε * (n : ℝ) ^ 2 := by
        have hp' : (0 : ℝ) < p := by exact_mod_cast hppos
        have : ((p * (p - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ 2 := by
          have : p * (p - 1) ≤ p * p := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          calc ((p * (p - 1) : ℕ) : ℝ) ≤ ((p * p : ℕ) : ℝ) := by exact_mod_cast this
            _ = (p : ℝ) ^ 2 := by push_cast; ring
        calc (2 * n / p) * (2 * n / p) * ((p * (p - 1) : ℕ) * ε)
            ≤ (2 * n / p) * (2 * n / p) * ((p : ℝ) ^ 2 * ε) := by gcongr
          _ = 4 * ε * (n : ℝ) ^ 2 := by field_simp; ring

/-- **Averaging over a random vertex in each part.** Choose `xᵢ ∈ Vᵢ` uniformly and independently
in every part `Vᵢ` of an equipartition `A` into `k` parts with `2k ≤ n`. For `F ≥ 0`, the expected
value of `∑_{i ≠ j} F(xᵢ, xⱼ)` is at most `(4k²/n²) ∑_{a, b : A(a) ≠ A(b)} F(a, b)`. -/
theorem sum_expect_le {A : Finpartition (univ : Finset V)} (hA : A.IsEquipartition)
    (hk : 2 * #A.parts ≤ card V) (F : V → V → ℝ) (hF : ∀ a b, 0 ≤ F a b) :
    ∑ x ∈ piFinset (fun i : A.parts => (i : Finset V)), ∑ i, ∑ j,
        (if i ≠ j then F (x i) (x j) else 0) ≤
      #(piFinset (fun i : A.parts => (i : Finset V))) * (4 * (#A.parts : ℝ) ^ 2 / (card V) ^ 2) *
        ∑ a, ∑ b, (if A.part a ≠ A.part b then F a b else 0) := by
  set k := #A.parts
  set n := card V
  set X := piFinset (fun i : A.parts => (i : Finset V))
  set T : Finset V → Finset V → ℝ := fun U W => ∑ a ∈ U, ∑ b ∈ W, F a b with hT
  have hkn : k ≤ n := by omega
  -- step A
  have hA' : (∑ a, ∑ b, (if A.part a ≠ A.part b then F a b else 0)) =
      ∑ U ∈ A.parts, ∑ W ∈ A.parts, (if U ≠ W then T U W else 0) := by
    rw [sum_univ_eq_sum_parts A]
    refine Finset.sum_congr rfl fun U hU => ?_
    rw [Finset.sum_comm' (t' := univ) (s' := fun _ => U) (by simp), sum_univ_eq_sum_parts A]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Finset.sum_comm]
    split_ifs with hUW
    · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      rw [A.part_eq_of_mem hU ha, A.part_eq_of_mem hW hb, if_pos hUW]
    · refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
      rw [A.part_eq_of_mem hU ha, A.part_eq_of_mem hW hb, if_neg hUW]
  -- step B
  have hcard : ∀ U ∈ A.parts, (n : ℝ) / (2 * k) ≤ #U := by
    intro U hU
    have h := (card_part_bounds hA hkn hU).1
    have hkpos : 0 < k := Finset.card_pos.2 ⟨U, hU⟩
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (by linarith : n ≤ #U * (2 * k))
  have hB : ∀ i j : A.parts, i ≠ j →
      ∑ x ∈ X, F (x i) (x j) ≤ #X * (4 * (k : ℝ) ^ 2 / n ^ 2) * T i j := by
    intro i j hij
    have key := sum_piFinset_pair (fun i : A.parts => (i : Finset V)) hij F
    have hi := hcard i i.2
    have hj := hcard j j.2
    have hkpos' : 0 < k := Finset.card_pos.2 ⟨i.1, i.2⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hkpos'
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hij' : (n : ℝ) ^ 2 / (4 * k ^ 2) ≤ (#(i : Finset V) : ℝ) * #(j : Finset V) := by
      calc (n : ℝ) ^ 2 / (4 * k ^ 2) = (n / (2 * k)) * (n / (2 * k)) := by field_simp; ring
        _ ≤ _ := mul_le_mul hi hj (by positivity) (by positivity)
    have hTn : 0 ≤ T i j := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hF a b
    have hXn : (0 : ℝ) ≤ #X := by positivity
    have hpos : (0 : ℝ) < (#(i : Finset V) : ℝ) * #(j : Finset V) :=
      lt_of_lt_of_le (by positivity) hij'
    have e : ∑ x ∈ X, F (x i) (x j) = #X * T i j / (#(i : Finset V) * #(j : Finset V)) := by
      rw [eq_div_iff hpos.ne']; exact key
    rw [e, div_le_iff₀ hpos]
    have : (1 : ℝ) ≤ 4 * k ^ 2 / n ^ 2 * (#(i : Finset V) * #(j : Finset V)) := by
      rw [div_le_iff₀ (by positivity)] at hij'
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    nlinarith [mul_nonneg hXn hTn]
  -- step C
  calc ∑ x ∈ X, ∑ i, ∑ j, (if i ≠ j then F (x i) (x j) else 0)
      = ∑ i : A.parts, ∑ j : A.parts, (if i ≠ j then ∑ x ∈ X, F (x i) (x j) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ i : A.parts, ∑ j : A.parts,
          (if i ≠ j then #X * (4 * (k : ℝ) ^ 2 / n ^ 2) * T i j else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hij
        · exact hB i j hij
        · exact le_rfl
    _ = #X * (4 * (k : ℝ) ^ 2 / n ^ 2) *
          ∑ U ∈ A.parts, ∑ W ∈ A.parts, (if U ≠ W then T U W else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_coe_sort A.parts]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_coe_sort A.parts]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_pos hij, if_pos (fun h => hij (Subtype.ext h))]
    _ = _ := by rw [hA']

/-- Numerical inequality used in the proof of `corollary_4_2`. -/
theorem aux_ineq (e0 k : ℝ) (he0 : 0 < e0) (hk : 2 ≤ k) :
    4 * k ^ 2 * (e0 ^ 3 / 64) / e0 ^ 2 ≤ e0 * (k * (k - 1) / 2) / 4 := by
  have h1 : 4 * k ^ 2 * (e0 ^ 3 / 64) / e0 ^ 2 = e0 * k ^ 2 / 16 := by
    field_simp; ring
  rw [h1]
  have : 0 ≤ e0 * k * (k - 2) := mul_nonneg (mul_nonneg he0.le (by linarith)) (by linarith)
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Lemma 3.8 of Alon–Shapira = Corollary 4.2 of Alon–Fischer–Krivelevich–Szegedy.** -/
theorem corollary_4_2 (m : ℕ) (E : ℕ → ℝ) (hEpos : ∀ r, 0 < E r) (hE1 : ∀ r, E r < 1) :
    ∃ S : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], S ≤ card V →
        ∃ (k : ℕ) (Vp Up : Fin k → Finset V),
          -- `A = {Vᵢ}` is an equipartition of `V(G)`
          (∀ i j, i ≠ j → Disjoint (Vp i) (Vp j)) ∧ (∀ v, ∃ i, v ∈ Vp i) ∧
          (∀ i j, #(Vp i) ≤ #(Vp j) + 1) ∧
          -- 1.
          m ≤ k ∧ k ≤ S ∧
          -- 2.
          (∀ i, Up i ⊆ Vp i) ∧ (∀ i, (card V : ℝ) ≤ S * #(Up i)) ∧
          -- `B = {Uᵢ}` is an equipartition of `U = ⋃ Uᵢ`
          (∀ i j, #(Up i) ≤ #(Up j) + 1) ∧
          -- 3.
          (∀ i j, i ≠ j → IsRegularPair G (E k) (Up i) (Up j)) ∧
          -- 4.
          ((#{p : Fin k × Fin k | p.1 < p.2 ∧
              E 0 ≤ |dens G (Vp p.1) (Vp p.2) - dens G (Up p.1) (Up p.2)|} : ℕ) : ℝ) ≤
            E 0 * k.choose 2 := by
  set e0 := E 0 with he0
  have he0pos : 0 < e0 := hEpos 0
  have he01 : e0 < 1 := hE1 0
  set f : ℕ → ℝ := fun k => E k / (64 * ((k : ℝ) + 1) ^ 2) with hfdef
  have hf : ∀ k, 0 < f k := fun k => by simp only [hfdef]; have := hEpos k; positivity
  set θ := e0 ^ 3 / 64 with hθdef
  have hθ : 0 < θ := by positivity
  obtain ⟨S1, hS1⟩ := strong_regularity.{u} (max m 2) f hf hθ
  refine ⟨2 * S1, ?_⟩
  intro V _ _ G _ hS
  obtain ⟨A, B, hA, hB, hBA, hmk, hBS, hBu, hq⟩ := hS1 G (by omega)
  set k := #A.parts with hkdef
  set p := #B.parts with hpdef
  set n := card V with hndef
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hmk
  have hmk' : m ≤ k := le_trans (le_max_left _ _) hmk
  have hkp : k ≤ p := Finpartition.card_mono hBA
  have hpn : p ≤ n := by omega
  have h2k : 2 * k ≤ n := by omega
  have hnpos : 0 < n := by omega
  set X := piFinset (fun i : A.parts => (i : Finset V)) with hXdef
  -- the two "badness" counts of a choice `x`
  set irr : (A.parts → V) → ℝ := fun x => ∑ i, ∑ j,
    (if i ≠ j then (if ¬ G.IsUniform (f k) (B.part (x i)) (B.part (x j)) then (1 : ℝ) else 0)
      else 0) with hirrdef
  set bad : (A.parts → V) → ℝ := fun x => ∑ i, ∑ j,
    (if i ≠ j then (if e0 ≤ |pd G A (x i) (x j) - pd G B (x i) (x j)| then (1 : ℝ) else 0)
      else 0) with hbaddef
  have hXpos : (0 : ℝ) < #X := by
    rw [hXdef, card_piFinset]
    push_cast
    exact Finset.prod_pos fun i _ => by
      exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (A.ne_bot i.2))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hirr : ∑ x ∈ X, irr x ≤ #X * (E k / 4) := by
    have h1 := sum_expect_le hA h2k
      (fun a b => if ¬ G.IsUniform (f k) (B.part a) (B.part b) then (1 : ℝ) else 0)
      (fun a b => by beta_reduce; split_ifs <;> norm_num)
    have h2 : (∑ a, ∑ b, (if A.part a ≠ A.part b then
        (if ¬ G.IsUniform (f k) (B.part a) (B.part b) then (1 : ℝ) else 0) else 0)) ≤
        4 * f k * (n : ℝ) ^ 2 := by
      refine le_trans ?_ (sum_nonuniform_le G hB hpn (hf k).le hBu)
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      by_cases hab : A.part a ≠ A.part b
      · have := part_ne_of_le hBA hab
        by_cases hu : G.IsUniform (f k) (B.part a) (B.part b) <;> simp [hab, this, hu]
      · rw [if_neg hab]; split_ifs <;> norm_num
    refine h1.trans ?_
    have hfk : 16 * (k : ℝ) ^ 2 * f k ≤ E k / 4 := by
      simp only [hfdef]
      have hEk := hEpos k
      rw [show 16 * (k : ℝ) ^ 2 * (E k / (64 * ((k : ℝ) + 1) ^ 2)) =
        E k / 4 * ((k : ℝ) ^ 2 / ((k : ℝ) + 1) ^ 2) by field_simp; ring]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one (by positivity)]
      nlinarith
    calc (#X : ℝ) * (4 * (k : ℝ) ^ 2 / n ^ 2) * (∑ a, ∑ b, (if A.part a ≠ A.part b then
          (if ¬ G.IsUniform (f k) (B.part a) (B.part b) then (1 : ℝ) else 0) else 0))
        ≤ #X * (4 * (k : ℝ) ^ 2 / n ^ 2) * (4 * f k * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = #X * (16 * (k : ℝ) ^ 2 * f k) := by field_simp; ring
      _ ≤ #X * (E k / 4) := mul_le_mul_of_nonneg_left hfk hXpos.le
  have hbad : ∑ x ∈ X, bad x ≤ #X * (4 * (k : ℝ) ^ 2 * θ / e0 ^ 2) := by
    have h1 := sum_expect_le hA h2k
      (fun a b => if e0 ≤ |pd G A a b - pd G B a b| then (1 : ℝ) else 0)
      (fun a b => by beta_reduce; split_ifs <;> norm_num)
    have hvar := sum_sq_sub_le_msd_sub G hBA
    have h2 : (∑ a, ∑ b, (if A.part a ≠ A.part b then
        (if e0 ≤ |pd G A a b - pd G B a b| then (1 : ℝ) else 0) else 0)) ≤
        (n : ℝ) ^ 2 * θ / e0 ^ 2 := by
      rw [le_div_iff₀ (by positivity), Finset.sum_mul]
      refine le_trans ?_ (hvar.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
      refine Finset.sum_le_sum fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun b _ => ?_
      split_ifs with hab hbig
      · rw [one_mul]
        have : e0 ^ 2 ≤ |pd G A a b - pd G B a b| ^ 2 := pow_le_pow_left₀ he0pos.le hbig 2
        rw [sq_abs] at this
        nlinarith
      · rw [zero_mul]; positivity
      · simp
    refine h1.trans ?_
    calc (#X : ℝ) * (4 * (k : ℝ) ^ 2 / n ^ 2) * (∑ a, ∑ b, (if A.part a ≠ A.part b then
          (if e0 ≤ |pd G A a b - pd G B a b| then (1 : ℝ) else 0) else 0))
        ≤ #X * (4 * (k : ℝ) ^ 2 / n ^ 2) * ((n : ℝ) ^ 2 * θ / e0 ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = #X * (4 * (k : ℝ) ^ 2 * θ / e0 ^ 2) := by field_simp
  set c : ℝ := e0 * (k * (k - 1) / 2) with hcdef
  have hcpos : 0 < c := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    exact mul_pos he0pos (div_pos (mul_pos (by linarith) (by linarith)) two_pos)
  obtain ⟨x, hxX, hx⟩ : ∃ x ∈ X, irr x + bad x / c < 1 := by
    refine Finset.exists_lt_of_sum_lt ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hin : 4 * (k : ℝ) ^ 2 * θ / e0 ^ 2 ≤ c / 4 := aux_ineq e0 k he0pos hkR
    have hbc : (∑ x ∈ X, bad x) / c ≤ #X * (1 / 4) := by
      rw [div_le_iff₀ hcpos]
      calc ∑ x ∈ X, bad x ≤ #X * (4 * (k : ℝ) ^ 2 * θ / e0 ^ 2) := hbad
        _ ≤ #X * (c / 4) := mul_le_mul_of_nonneg_left hin hXpos.le
        _ = #X * (1 / 4) * c := by ring
    have h3 : (#X : ℝ) * (E k / 4) < #X * (1 / 4) :=
      mul_lt_mul_of_pos_left (by linarith [hE1 k]) hXpos
    linarith
  have hnn : ∀ (P : Prop) [Decidable P] (Q : Prop) [Decidable Q],
      (0 : ℝ) ≤ (if P then (if Q then (1 : ℝ) else 0) else 0) := by
    intro P _ Q _; split_ifs <;> norm_num
  have hirr0 : 0 ≤ irr x := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn _ _
  have hbad0 : 0 ≤ bad x := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn _ _
  have hirr1 : irr x < 1 := by have := div_nonneg hbad0 hcpos.le; linarith
  have hbadc : bad x < c := by
    have : bad x / c < 1 := by linarith
    rwa [div_lt_one hcpos] at this
  have hmemX : ∀ i : A.parts, x i ∈ (i : Finset V) := fun i => Fintype.mem_piFinset.1 hxX i
  have hApart : ∀ i : A.parts, A.part (x i) = i := fun i => A.part_eq_of_mem i.2 (hmemX i)
  have huni : ∀ i j : A.parts, i ≠ j → G.IsUniform (f k) (B.part (x i)) (B.part (x j)) := by
    intro i j hij
    by_contra hnu
    have hterm : (if i ≠ j then (if ¬ G.IsUniform (f k) (B.part (x i)) (B.part (x j)) then
        (1 : ℝ) else 0) else 0) = 1 := by simp [hij, hnu]
    have h1 : (1 : ℝ) ≤ irr x := by
      calc (1 : ℝ) = _ := hterm.symm
        _ ≤ ∑ j', (if i ≠ j' then (if ¬ G.IsUniform (f k) (B.part (x i)) (B.part (x j')) then
              (1 : ℝ) else 0) else 0) :=
            Finset.single_le_sum (f := fun j' => (if i ≠ j' then (if ¬ G.IsUniform (f k)
              (B.part (x i)) (B.part (x j')) then (1 : ℝ) else 0) else 0))
              (fun j' _ => hnn _ _) (mem_univ j)
        _ ≤ irr x :=
            Finset.single_le_sum (f := fun i' => ∑ j', (if i' ≠ j' then (if ¬ G.IsUniform (f k)
              (B.part (x i')) (B.part (x j')) then (1 : ℝ) else 0) else 0))
              (fun i' _ => Finset.sum_nonneg fun j' _ => hnn _ _) (mem_univ i)
    linarith
  have hsub : ∀ i : A.parts, B.part (x i) ⊆ (i : Finset V) := by
    intro i
    obtain ⟨C, hC, hBC⟩ := hBA (B.part_mem.2 (mem_univ (x i)))
    have : C = i := by
      rw [← A.part_eq_of_mem hC (hBC (B.mem_part (mem_univ (x i)))), hApart]
    rw [← this]; exact hBC
  have hfkE : f k ≤ E k := by
    simp only [hfdef]
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
    exact div_le_self (hEpos k).le (by linarith)
  set e := A.parts.equivFin with hedef
  have hpdA : ∀ i j : A.parts, pd G A (x i) (x j) = dens G i j := by
    intro i j; simp only [pd, hApart]
  refine ⟨k, fun l => (e.symm l : Finset V), fun l => B.part (x (e.symm l)), ?_, ?_, ?_, hmk',
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' hll'
    exact A.disjoint (Finset.mem_coe.2 (e.symm l).2) (Finset.mem_coe.2 (e.symm l').2)
      (fun h => hll' (e.symm.injective (Subtype.ext h)))
  · intro v
    refine ⟨e ⟨A.part v, A.part_mem.2 (mem_univ v)⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact A.mem_part (mem_univ v)
  · intro l l'
    exact hA (Finset.mem_coe.2 (e.symm l).2) (Finset.mem_coe.2 (e.symm l').2)
  · intro l; exact hsub _
  · intro l
    have h := (card_part_bounds hB hpn (B.part_mem.2 (mem_univ (x (e.symm l))))).1
    have h' : n ≤ 2 * S1 * #(B.part (x (e.symm l))) :=
      h.trans (Nat.mul_le_mul_right _ (by omega))
    exact_mod_cast h'
  · intro l l'
    exact hB (Finset.mem_coe.2 (B.part_mem.2 (mem_univ _)))
      (Finset.mem_coe.2 (B.part_mem.2 (mem_univ _)))
  · intro l l' hll'
    exact isRegularPair_of_isUniform G hfkE (huni _ _ (fun h => hll' (e.symm.injective h)))
  · calc ((#{q : Fin k × Fin k | q.1 < q.2 ∧ e0 ≤ |dens G (e.symm q.1 : Finset V)
          (e.symm q.2 : Finset V) - dens G (B.part (x (e.symm q.1)))
            (B.part (x (e.symm q.2)))|} : ℕ) : ℝ)
        = ∑ q : Fin k × Fin k, (if q.1 < q.2 ∧ e0 ≤ |dens G (e.symm q.1 : Finset V)
          (e.symm q.2 : Finset V) - dens G (B.part (x (e.symm q.1)))
            (B.part (x (e.symm q.2)))| then (1 : ℝ) else 0) := by
          rw [Finset.card_filter]; push_cast; rfl
      _ ≤ ∑ q : Fin k × Fin k, (if e.symm q.1 ≠ e.symm q.2 then
            (if e0 ≤ |pd G A (x (e.symm q.1)) (x (e.symm q.2)) -
              pd G B (x (e.symm q.1)) (x (e.symm q.2))| then (1 : ℝ) else 0) else 0) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [hpdA]
          by_cases hq : q.1 < q.2 ∧ e0 ≤ |dens G (e.symm q.1 : Finset V)
            (e.symm q.2 : Finset V) - dens G (B.part (x (e.symm q.1)))
              (B.part (x (e.symm q.2)))|
          · have hne : e.symm q.1 ≠ e.symm q.2 := fun h => (ne_of_lt hq.1) (e.symm.injective h)
            rw [if_pos hq, if_pos hne, if_pos (show e0 ≤ |dens G ↑(e.symm q.1) ↑(e.symm q.2) -
              pd G B (x (e.symm q.1)) (x (e.symm q.2))| from hq.2)]
          · rw [if_neg hq]; exact hnn _ _
      _ = bad x := by
          rw [Fintype.sum_prod_type, hbaddef]
          dsimp only
          rw [← Equiv.sum_comp e.symm]
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Equiv.sum_comp e.symm (fun j => (if e.symm i ≠ j then
            (if e0 ≤ |pd G A (x (e.symm i)) (x j) - pd G B (x (e.symm i)) (x j)| then (1 : ℝ)
              else 0) else 0))
      _ ≤ c := hbadc.le
      _ = e0 * k.choose 2 := by rw [hcdef, Nat.cast_choose_two]

end AFKS
