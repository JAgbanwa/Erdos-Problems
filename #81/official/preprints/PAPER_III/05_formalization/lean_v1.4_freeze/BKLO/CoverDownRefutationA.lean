/-
# The counting counterexample to the cover-down input, at ratio `K = 2`.

This file builds, for every size threshold `n₀`, a configuration `W'' = ∅ ⊆ W' ⊆ W` with
`2|W'| ≤ |W| ≤ 4|W'|` and a triangle-divisible edge set `F` spanned by `W` of minimum degree
`(19/20)|W| > (91/100)|W|` for which the conclusion of `BKLO.CoverDownK3` fails at `K = 2`.

The configuration is a **complete `20`-partite graph**: the vertex set is `Fin 20 × Fin s` with
`s = 6u`, the twenty parts are the fibres of the first coordinate, `W` is everything, `W'` is the
union of the first ten parts and `A = W \ W'` the union of the last ten.  So

* every one of the `|W'|·|A| = 100s²` edges between `W'` and `A` is present, and every one of them
  has to be covered by the triangle family;
* there are only `45s²` edges inside `A`.

Since each triangle has at most two edges crossing between `W'` and `A`, and its third edge then
lies inside `A` or inside `W'`, covering all `100s²` crossing edges needs at least
`100s² - 2·45s² = 10s²` edges inside `W'` — while the damage tolerance `γ = 1/20` allows only
`γ|W'|² = 5s²` of them.  This is `BKLO.cover_counting_obstruction`.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownObstruction

open Finset

namespace BKLO

namespace RefutationA

/-- The vertex type: twenty blocks of size `s`. -/
abbrev VA (s : ℕ) : Type := Fin 20 × Fin s

variable (s : ℕ)

/-- The `a`-th block. -/
def blk (s : ℕ) (a : Fin 20) : Finset (VA s) := univ.filter (fun z => z.1 = a)

/-- The next vortex level `W'`: the first ten blocks. -/
def low (s : ℕ) : Finset (VA s) := univ.filter (fun z => z.1.val < 10)

/-- The complement `A = W \ W'`: the last ten blocks. -/
def high (s : ℕ) : Finset (VA s) := univ.filter (fun z => ¬ z.1.val < 10)

/-- The edges inside the blocks: the ones that are *absent*. -/
def rem (s : ℕ) : Finset (Sym2 (VA s)) :=
  (univ : Finset (Fin 20)).biUnion (fun a => cliqueEdges (blk s a))

/-- The complete `20`-partite edge set. -/
def edgesA (s : ℕ) : Finset (Sym2 (VA s)) := cliqueEdges (univ : Finset (VA s)) \ rem s

/-! ### Cardinalities of the vertex sets -/

theorem mem_blk {s : ℕ} {a : Fin 20} {z : VA s} : z ∈ blk s a ↔ z.1 = a := by simp [blk]

theorem card_univA : (univ : Finset (VA s)).card = 20 * s := by simp

theorem card_blk (a : Fin 20) : (blk s a).card = s := by
  classical
  have h : blk s a = ({a} : Finset (Fin 20)) ×ˢ (univ : Finset (Fin s)) := by
    ext z
    simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    tauto
  rw [h, Finset.card_product]
  simp

theorem card_low : (low s).card = 10 * s := by
  classical
  have h : low s
      = ((univ : Finset (Fin 20)).filter (fun a => a.val < 10)) ×ˢ (univ : Finset (Fin s)) := by
    ext z
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    tauto
  have h2 : ((univ : Finset (Fin 20)).filter (fun a => a.val < 10)).card = 10 := by decide +kernel
  rw [h, Finset.card_product, h2]
  simp

theorem card_high : (high s).card = 10 * s := by
  classical
  have h : high s
      = ((univ : Finset (Fin 20)).filter (fun a => ¬ a.val < 10)) ×ˢ (univ : Finset (Fin s)) := by
    ext z
    simp only [high, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    tauto
  have h2 : ((univ : Finset (Fin 20)).filter (fun a => ¬ a.val < 10)).card = 10 := by decide +kernel
  rw [h, Finset.card_product, h2]
  simp

theorem mem_low_or_high (z : VA s) : z ∈ low s ∨ z ∈ high s := by
  by_cases h : z.1.val < 10
  · exact Or.inl (by simp [low]; omega)
  · exact Or.inr (by simp [high]; omega)

theorem low_disjoint_high : Disjoint (low s) (high s) := by
  refine Finset.disjoint_left.2 fun z hz hz' => ?_
  simp only [low, high, Finset.mem_filter] at hz hz'
  exact hz'.2 hz.2

theorem blk_subset (a : Fin 20) : blk s a ⊆ low s ∨ blk s a ⊆ high s := by
  by_cases h : a.val < 10
  · refine Or.inl fun z hz => ?_
    have hz1 : z.1 = a := mem_blk.1 hz
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and, hz1]
    omega
  · refine Or.inr fun z hz => ?_
    have hz1 : z.1 = a := mem_blk.1 hz
    simp only [high, Finset.mem_filter, Finset.mem_univ, true_and, hz1]
    omega

/-! ### Degrees -/

theorem disj_blk {s : ℕ} {a b : Fin 20} (hab : a ≠ b) :
    Disjoint (cliqueEdges (blk s a)) (cliqueEdges (blk s b)) := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  induction e using Sym2.ind with
  | _ x y =>
    have h1 : x ∈ blk s a := (mem_cliqueEdgesV.1 he).1 x (by simp)
    have h2 : x ∈ blk s b := (mem_cliqueEdgesV.1 he').1 x (by simp)
    exact hab ((mem_blk.1 h1).symm.trans (mem_blk.1 h2))

theorem rem_subset : rem s ⊆ cliqueEdges (univ : Finset (VA s)) := by
  intro e he
  obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 he
  exact cliqueEdges_mono (Finset.subset_univ _) ha

theorem edgesA_subset : edgesA s ⊆ cliqueEdges (univ : Finset (VA s)) := Finset.sdiff_subset

theorem edeg_rem (v : VA s) : edeg (rem s) v = s - 1 := by
  classical
  have hfil : (rem s).filter (fun e => v ∈ e)
      = (cliqueEdges (blk s v.1)).filter (fun e => v ∈ e) := by
    ext e
    simp only [Finset.mem_filter, rem, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨a, ha⟩, hv⟩
      have hv' : v ∈ blk s a := (mem_cliqueEdgesV.1 ha).1 v hv
      have : v.1 = a := mem_blk.1 hv'
      subst this
      exact ⟨ha, hv⟩
    · rintro ⟨ha, hv⟩
      exact ⟨⟨v.1, ha⟩, hv⟩
  have h := edeg_cliqueEdges_of_mem (W := blk s v.1) (v := v) (mem_blk.2 rfl)
  unfold edeg at *
  rw [hfil, h, card_blk]

theorem edeg_edgesA (v : VA s) : edeg (edgesA s) v = 19 * s := by
  have h1 : edeg (rem s) v + edeg (edgesA s) v = edeg (cliqueEdges (univ : Finset (VA s))) v :=
    edeg_sdiff_add (rem_subset s) v
  have h2 : edeg (cliqueEdges (univ : Finset (VA s))) v = 20 * s - 1 := by
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v)]
    simp
  have h3 := edeg_rem s v
  have h4 : 1 ≤ s := by
    by_contra hs
    have : s = 0 := by omega
    exact absurd (v.2.2) (by simp [this])
  omega

/-! ### Edge counts -/

theorem card_rem : (rem s).card = 20 * (s.choose 2) := by
  classical
  unfold rem
  rw [Finset.card_biUnion (fun a _ b _ hab => disj_blk hab)]
  rw [Finset.sum_congr rfl (fun a _ => by rw [card_cliqueEdges, card_blk])]
  simp [Finset.sum_const, Nat.mul_comm]

theorem card_edgesA : (edgesA s).card = 190 * s ^ 2 := by
  classical
  have hcard : (edgesA s).card = (20 * s).choose 2 - 20 * (s.choose 2) := by
    unfold edgesA
    rw [Finset.card_sdiff_of_subset (rem_subset s), card_cliqueEdges, card_univA, card_rem]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [hcard]
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hA : 2 * ((20 * (t + 1)).choose 2) = 20 * (t + 1) * (20 * (t + 1) - 1) :=
      two_mul_choose_two _
    have hB : 2 * ((t + 1).choose 2) = (t + 1) * ((t + 1) - 1) := two_mul_choose_two _
    have e1 : 20 * (t + 1) * (20 * (t + 1) - 1) = 400 * t ^ 2 + 780 * t + 380 := by
      have : 20 * (t + 1) - 1 = 20 * t + 19 := by omega
      rw [this]; ring
    have e2 : (t + 1) * ((t + 1) - 1) = t ^ 2 + t := by
      simp only [Nat.add_sub_cancel]; ring
    have e3 : 190 * (t + 1) ^ 2 = 190 * t ^ 2 + 380 * t + 190 := by ring
    rw [e1] at hA
    rw [e2] at hB
    omega

theorem crossA_eq :
    edgesA s \ (cliqueEdges (low s) ∪ cliqueEdges (high s))
      = cliqueEdges (univ : Finset (VA s)) \ (cliqueEdges (low s) ∪ cliqueEdges (high s)) := by
  classical
  have hrem : rem s ⊆ cliqueEdges (low s) ∪ cliqueEdges (high s) := by
    intro e he
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 he
    rcases blk_subset s a with h | h
    · exact Finset.mem_union_left _ (cliqueEdges_mono h ha)
    · exact Finset.mem_union_right _ (cliqueEdges_mono h ha)
  ext e
  simp only [edgesA, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun hc => h2 (hrem hc)⟩, h2⟩

theorem disj_cliqueEdges_low_high :
    Disjoint (cliqueEdges (low s)) (cliqueEdges (high s)) := by
  refine Finset.disjoint_left.2 fun e he he' => ?_
  induction e using Sym2.ind with
  | _ x y =>
    have h1 : x ∈ low s := (mem_cliqueEdgesV.1 he).1 x (by simp)
    have h2 : x ∈ high s := (mem_cliqueEdgesV.1 he').1 x (by simp)
    exact (Finset.disjoint_left.1 (low_disjoint_high s)) h1 h2

theorem card_crossA :
    (edgesA s \ (cliqueEdges (low s) ∪ cliqueEdges (high s))).card = 100 * s ^ 2 := by
  classical
  have hsub : cliqueEdges (low s) ∪ cliqueEdges (high s) ⊆ cliqueEdges (univ : Finset (VA s)) :=
    Finset.union_subset (cliqueEdges_mono (Finset.subset_univ _))
      (cliqueEdges_mono (Finset.subset_univ _))
  have hcard : (edgesA s \ (cliqueEdges (low s) ∪ cliqueEdges (high s))).card
      = (20 * s).choose 2 - ((10 * s).choose 2 + (10 * s).choose 2) := by
    rw [crossA_eq, Finset.card_sdiff_of_subset hsub,
      Finset.card_union_of_disjoint (disj_cliqueEdges_low_high s), card_cliqueEdges,
      card_cliqueEdges, card_cliqueEdges, card_univA, card_low, card_high]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [hcard]
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hA : 2 * ((20 * (t + 1)).choose 2) = 20 * (t + 1) * (20 * (t + 1) - 1) :=
      two_mul_choose_two _
    have hB : 2 * ((10 * (t + 1)).choose 2) = 10 * (t + 1) * (10 * (t + 1) - 1) :=
      two_mul_choose_two _
    have e1 : 20 * (t + 1) * (20 * (t + 1) - 1) = 400 * t ^ 2 + 780 * t + 380 := by
      have : 20 * (t + 1) - 1 = 20 * t + 19 := by omega
      rw [this]; ring
    have e2 : 10 * (t + 1) * (10 * (t + 1) - 1) = 100 * t ^ 2 + 190 * t + 90 := by
      have : 10 * (t + 1) - 1 = 10 * t + 9 := by omega
      rw [this]; ring
    have e3 : 100 * (t + 1) ^ 2 = 100 * t ^ 2 + 200 * t + 100 := by ring
    rw [e1] at hA
    rw [e2] at hB
    omega

/-- The blocks inside `A`. -/
def remHigh (s : ℕ) : Finset (Sym2 (VA s)) :=
  ((univ : Finset (Fin 20)).filter (fun a => ¬ a.val < 10)).biUnion (fun a => cliqueEdges (blk s a))

theorem remHigh_subset : remHigh s ⊆ cliqueEdges (high s) := by
  intro e he
  obtain ⟨a, ha, hae⟩ := Finset.mem_biUnion.1 he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  refine cliqueEdges_mono ?_ hae
  intro z hz
  have hz1 : z.1 = a := mem_blk.1 hz
  simp only [high, Finset.mem_filter, Finset.mem_univ, true_and, hz1]
  omega

theorem inHighA_eq : edgesA s ∩ cliqueEdges (high s) = cliqueEdges (high s) \ remHigh s := by
  classical
  ext e
  simp only [edgesA, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, fun hc => h2 (Finset.mem_biUnion.2 (by
      obtain ⟨a, ha, hae⟩ := Finset.mem_biUnion.1 hc
      exact ⟨a, Finset.mem_univ a, hae⟩))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨cliqueEdges_mono (Finset.subset_univ _) h1, fun hc => h2 ?_⟩, h1⟩
    obtain ⟨a, -, hae⟩ := Finset.mem_biUnion.1 hc
    refine Finset.mem_biUnion.2 ⟨a, ?_, hae⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- the block of `a` meets `high`, so `a` is a high block
    intro hlt
    induction e using Sym2.ind with
    | _ x y =>
      have hx1 : x ∈ blk s a := (mem_cliqueEdgesV.1 hae).1 x (by simp)
      have hx2 : x ∈ high s := (mem_cliqueEdgesV.1 h1).1 x (by simp)
      have : x.1 = a := mem_blk.1 hx1
      simp only [high, Finset.mem_filter] at hx2
      exact hx2.2 (this ▸ hlt)

theorem card_remHigh : (remHigh s).card = 10 * (s.choose 2) := by
  classical
  unfold remHigh
  rw [Finset.card_biUnion (fun a _ b _ hab => disj_blk hab)]
  rw [Finset.sum_congr rfl (fun a _ => by rw [card_cliqueEdges, card_blk])]
  have h2 : ((univ : Finset (Fin 20)).filter (fun a => ¬ a.val < 10)).card = 10 := by decide +kernel
  rw [Finset.sum_const, h2, smul_eq_mul]

theorem card_inHighA : (edgesA s ∩ cliqueEdges (high s)).card = 45 * s ^ 2 := by
  classical
  have hcard : (edgesA s ∩ cliqueEdges (high s)).card
      = (10 * s).choose 2 - 10 * (s.choose 2) := by
    rw [inHighA_eq, Finset.card_sdiff_of_subset (remHigh_subset s), card_cliqueEdges, card_high,
      card_remHigh]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [hcard]
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hA : 2 * ((10 * (t + 1)).choose 2) = 10 * (t + 1) * (10 * (t + 1) - 1) :=
      two_mul_choose_two _
    have hB : 2 * ((t + 1).choose 2) = (t + 1) * ((t + 1) - 1) := two_mul_choose_two _
    have e1 : 10 * (t + 1) * (10 * (t + 1) - 1) = 100 * t ^ 2 + 190 * t + 90 := by
      have : 10 * (t + 1) - 1 = 10 * t + 9 := by omega
      rw [this]; ring
    have e2 : (t + 1) * ((t + 1) - 1) = t ^ 2 + t := by
      simp only [Nat.add_sub_cancel]; ring
    have e3 : 45 * (t + 1) ^ 2 = 45 * t ^ 2 + 90 * t + 45 := by ring
    rw [e1] at hA
    rw [e2] at hB
    omega

/-! ### Divisibility -/

theorem triDivisible_edgesA (u : ℕ) : TriDivisible (edgesA (6 * u)) := by
  constructor
  · intro v
    show Even (edeg (edgesA (6 * u)) v)
    rw [edeg_edgesA]
    exact ⟨57 * u, by ring⟩
  · show 3 ∣ (edgesA (6 * u)).card
    rw [card_edgesA]
    exact ⟨2280 * u ^ 2, by ring⟩

end RefutationA

open RefutationA in
/-- **The cover-down conclusion fails at `K = 2`**, for the density `c = 91/100 > 9/10` and the
damage tolerance `γ = 1/20`: the complete `20`-partite configuration has too few edges inside
`A = W \ W'` to cover its edges between `W'` and `A`. -/
theorem not_coverDownK3At_two (n₀ : ℕ) : ¬ CoverDownK3At (91 / 100) (1 / 20) 2 n₀ := by
  classical
  intro h
  set u : ℕ := n₀ + 1 with hu
  set s : ℕ := 6 * u with hs
  have hs1 : 1 ≤ s := by omega
  have hcardW : (univ : Finset (VA s)).card = 20 * s := card_univA s
  obtain ⟨P, hP, hleft, -, hdam⟩ :=
    h (V := VA s) (univ : Finset (VA s)) (low s) (∅ : Finset (VA s)) (edgesA s)
      (by rw [hcardW]; omega)
      (Finset.subset_univ _) (Finset.empty_subset _)
      (by rw [hcardW, card_low]; omega)
      (by rw [hcardW, card_low]; omega)
      (by rw [card_low]; simp)
      (edgesA_subset s) (triDivisible_edgesA u)
      (by
        intro v _
        rw [edeg_edgesA, hcardW]
        have : (0 : ℝ) ≤ (s : ℝ) := by positivity
        push_cast
        linarith)
  have hobstr := cover_counting_obstruction (W := (univ : Finset (VA s))) (W' := low s)
    (A := high s) (γ := 1 / 20) (edgesA_subset s) (fun x _ => mem_low_or_high s x) hP hleft hdam
  rw [card_crossA, card_inHighA, card_low] at hobstr
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  push_cast at hobstr
  nlinarith only [hobstr, hspos]

end BKLO
