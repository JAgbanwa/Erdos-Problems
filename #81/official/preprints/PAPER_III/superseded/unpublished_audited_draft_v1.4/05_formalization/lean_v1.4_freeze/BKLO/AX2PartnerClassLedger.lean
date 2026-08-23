/-
# The partner-class ledger of a counted classification

`BKLO/AX2PartnerClassSpread.lean` isolates the clause the one-link step needs and the vehicle does
not carry: `BKLO.PartnerClassSpread`, a cap on the number of links at which a single place has been
paired into a single class.  This file *decomposes* that quantity along the classification
`BKLO.IsCountClassification`, so that one can see exactly which caps have to be paid, and which of
them the counted invariant already pays.

`BKLO.partnerClassLoad_le_split` is the balance sheet: for a place `a` and a class index `i < h²`,

```
partnerClassLoad ≤ prescribedClassLoad          -- the class-matched, non-exceptional links
                 + cycleClassLoad               -- the three-class cycle blocks
                 + excRouteCount S Pc a rt (i / h)   -- column-routed leftovers at the forced index
                 + excRouteCount S Pr a rt (i % h)   -- row-routed leftovers at the forced index
                 + foreignClassLoad.            -- the foreign plan
```

The two middle terms are the ones the counted invariant caps, at `5 K² t + 1` each
(`BKLO.IsCountClassification`), and `BKLO.FibreBalanced` makes the cap usable at *every* index.  The
places-in-no-class family `Po` contributes nothing, since its partners lie in no class at all.

The engines take a class-level degree `m` with `q + 4 m + 8 ≤ 2 c`, i.e. `m ≤ 3 c / 14 ≈ 0.14 t`.
`BKLO.counted_cap_too_coarse_for_engine` is the arithmetic consequence of the split: at the counted
cap `5 K² t + 1 ≈ 20 t` the two routed terms *alone* are already an order of magnitude above what
the engines tolerate, so the split cannot be closed at the current plan ceiling — whereas
`BKLO.partnerClassSpread_of_caps` shows it closes as soon as the four caps are of size `≈ c / 14`,
which is what a plan ceiling of `t / 16` would deliver through `BKLO.FibreBalanced`
(`BKLO.excRouteCount_le_of_fibreBalanced`: a plan claiming a place at `B · h` links routes it at
most `B` times at each index).

Everything here is `sorry`-free.
-/
import BKLO.AX2PartnerClassSpread

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The three uncounted terms -/

/-- The links at which `a` is paired into `C i` **by the class matching**, i.e. without being a
leftover. -/
def prescribedClassLoad (C : ℕ → Finset V) (X : V → Finset V) (S : Finset V) (g : V → V → V)
    (Exc : V → Finset V) (a : V) (i : ℕ) : ℕ :=
  (S.filter (fun w => a ∈ X w ∧ a ∉ Exc w ∧ g w a ∈ C i)).card

/-- The links at which `a` is paired into `C i` as a **cycle** leftover. -/
def cycleClassLoad (C : ℕ → Finset V) (S : Finset V) (g : V → V → V) (Cc Cr : V → Finset V)
    (a : V) (i : ℕ) : ℕ :=
  (S.filter (fun w => (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i)).card

/-- The links at which `a` is paired into `C i` as a **foreign** leftover. -/
def foreignClassLoad (C : ℕ → Finset V) (S : Finset V) (g : V → V → V) (Fo : V → Finset V)
    (a : V) (i : ℕ) : ℕ :=
  (S.filter (fun w => a ∈ Fo w ∧ g w a ∈ C i)).card

/-! ### The split -/

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-- **The partner-class ledger of a counted classification.**  Every link at which the place `a` is
paired into the class `C i` is one of five things: a class-matched link, a cycle leftover, a
column-routed leftover *at the index `i / h` forced by the class*, a row-routed leftover at the
forced index `i % h`, or a foreign leftover.  A place paired outside every class contributes
nothing. -/
theorem partnerClassLoad_le_split
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    (X : V → Finset V) (a : V) {i : ℕ} (hi : i < gridSize ε K * gridSize ε K) :
    partnerClassLoad C X S g a i
      ≤ prescribedClassLoad C X S g Exc a i + cycleClassLoad C S g Cc Cr a i
        + excRouteCount S Pc a (fun w => rt w a) (i / gridSize ε K)
        + excRouteCount S Pr a (fun w => rt w a) (i % gridSize ε K)
        + foreignClassLoad C S g Fo a i := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  obtain ⟨hsplit, -, -, hrtlt, hroute, -, -, -, -, -, -, -, hPo⟩ := hcls
  set A₁ : Finset V := S.filter (fun w => a ∈ X w ∧ a ∉ Exc w ∧ g w a ∈ C i) with hA₁
  set A₂ : Finset V := S.filter (fun w => (a ∈ Cc w ∨ a ∈ Cr w) ∧ g w a ∈ C i) with hA₂
  set A₃ : Finset V := S.filter (fun w => a ∈ Pc w ∧ rt w a = i / h) with hA₃
  set A₄ : Finset V := S.filter (fun w => a ∈ Pr w ∧ rt w a = i % h) with hA₄
  set A₅ : Finset V := S.filter (fun w => a ∈ Fo w ∧ g w a ∈ C i) with hA₅
  have hsub : S.filter (fun w => a ∈ X w ∧ g w a ∈ C i) ⊆ ((A₁ ∪ A₂) ∪ (A₃ ∪ A₄)) ∪ A₅ := by
    intro w hw
    obtain ⟨hwS, hwX, hwC⟩ : w ∈ S ∧ a ∈ X w ∧ g w a ∈ C i := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact ⟨h1, h2.1, h2.2⟩
    by_cases hexc : a ∈ Exc w
    · have hxw : x w < h := hgrid.rowLt w (hSD hwS)
      have hyw : y w < h := hgrid.colLt w (hSD hwS)
      have hidx : ∀ j : ℕ, j < h * h → g w a ∈ C j → j = i := by
        intro j hj hmem
        by_contra hne
        exact (Finset.disjoint_left.1 (hgrid.classDisjoint j hj i hi hne)) hmem hwC
      rcases Finset.mem_union.1 (hsplit w hwS hexc) with hcase | hcase
      · rcases Finset.mem_union.1 hcase with hcase | hcase
        · -- cycle leftover
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hwS, Finset.mem_union.1 hcase, hwC⟩)))
        · -- routed leftover
          rcases Finset.mem_union.1 hcase with hcase | hcase
          · have hrt : rt w a < h := hrtlt w hwS a
            have hmem : g w a ∈ C (rt w a * h + y w) := (hroute w hwS).1 a hcase
            have hlt : rt w a * h + y w < h * h := by
              have : rt w a * h + y w < rt w a * h + h := by omega
              calc rt w a * h + y w < (rt w a + 1) * h := by rw [Nat.succ_mul]; omega
                _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
            have heq : rt w a * h + y w = i := hidx _ hlt hmem
            have hdiv : i / h = rt w a := by
              rw [← heq, Nat.mul_comm (rt w a) h, Nat.mul_add_div hhpos, Nat.div_eq_of_lt hyw,
                Nat.add_zero]
            exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_filter.2 ⟨hwS, hcase, hdiv.symm⟩)))
          · have hrt : rt w a < h := hrtlt w hwS a
            have hmem : g w a ∈ C (x w * h + rt w a) := (hroute w hwS).2 a hcase
            have hlt : x w * h + rt w a < h * h := by
              calc x w * h + rt w a < (x w + 1) * h := by rw [Nat.succ_mul]; omega
                _ ≤ h * h := Nat.mul_le_mul_right h (by omega)
            have heq : x w * h + rt w a = i := hidx _ hlt hmem
            have hmod : i % h = rt w a := by
              rw [← heq, Nat.mul_add_mod', Nat.mod_eq_of_lt hrt]
            exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_filter.2 ⟨hwS, hcase, hmod.symm⟩)))
      · rcases Finset.mem_union.1 hcase with hcase | hcase
        · -- foreign leftover
          exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwS, hcase, hwC⟩)
        · -- partner in no class at all: impossible
          exact absurd hwC (hPo w hwS a hcase i hi)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hwS, hwX, hexc, hwC⟩)))
  have hcard := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (A₁ ∪ A₂) (A₃ ∪ A₄)
  have h2 := Finset.card_union_le A₁ A₂
  have h3 := Finset.card_union_le A₃ A₄
  have h4 := Finset.card_union_le ((A₁ ∪ A₂) ∪ (A₃ ∪ A₄)) A₅
  simp only [partnerClassLoad, prescribedClassLoad, cycleClassLoad, foreignClassLoad,
    excRouteCount, ← hA₁, ← hA₂, ← hA₃, ← hA₄, ← hA₅]
  omega

/-! ### What the split says about the caps -/

/-- **The missing clause, from five caps.**  If each of the three uncounted terms of the split is
capped by `B` and the two counted terms by `Bc`, the sweep is partner-class spread at
`3 B + 2 Bc`. -/
theorem partnerClassSpread_of_caps
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} (hSD : S ⊆ W \ W')
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {X : V → Finset V} {B Bc : ℕ}
    (hpre : ∀ a i, prescribedClassLoad C X S g Exc a i ≤ B)
    (hcyc : ∀ a i, cycleClassLoad C S g Cc Cr a i ≤ B)
    (hfor : ∀ a i, foreignClassLoad C S g Fo a i ≤ B)
    (hPc : ∀ a P, excRouteCount S Pc a (fun w => rt w a) P ≤ Bc)
    (hPr : ∀ a Q, excRouteCount S Pr a (fun w => rt w a) Q ≤ Bc) :
    PartnerClassSpread (gridSize ε K) C X S g (3 * B + 2 * Bc) := by
  intro a i hi
  have hsplit := partnerClassLoad_le_split hgrid hSD hcls X a hi
  have h1 := hpre a i
  have h2 := hcyc a i
  have h3 := hfor a i
  have h4 := hPc a (i / gridSize ε K)
  have h5 := hPr a (i % gridSize ε K)
  omega

/-- **The counted cap is too coarse for the engines.**  Even if the three uncounted terms of the
split were zero, the two counted terms alone give a class-level degree `2 (5 K² t + 1)`, and the
hypothesis `q + 4 m + 8 ≤ 2 c` of every pairing engine of the development fails there: the class
fibre is `c ≤ q ≤ t` while the cap is `≈ 20 t`.  This is the arithmetic of the surviving
obstruction: the plan ceiling `5 K² t + 1` of `BKLO.CellSpreadLeftoverPlan` — hence the counted cap
it produces — has to come down to about `c / 14` before a class-level degree bound can be read off
the invariant. -/
theorem counted_cap_too_coarse_for_engine {K t c q : ℕ} (hK : 2 ≤ K) (hqt : q ≤ t)
    (hcq : c ≤ q) :
    ¬ (q + 4 * (2 * (5 * (K * K) * t + 1)) + 8 ≤ 2 * c) := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have h2 : 20 * t ≤ 5 * (K * K) * t := by
    have h3 : 5 * 4 * t ≤ 5 * (K * K) * t := Nat.mul_le_mul_right t (by omega)
    omega
  omega

/-- **What a tight plan ceiling would buy.**  With all five caps at `B`, the engines' hypothesis
`q + 4 m + 8 ≤ 2 c` holds as soon as `20 B + q + 8 ≤ 2 c`; at the design's sizes `q ≤ t`,
`3 t ≤ 4 q ≤ 32 c / 7` this is implied by `B ≤ t / 64` — a ceiling the leftover demand
(`≈ t / 32` places per link, spread over `≈ 1.1 h t` places of the region) leaves ample room
for. -/
theorem engine_hypothesis_of_tight_caps {t q c B : ℕ} (hqc : 7 * q ≤ 8 * c)
    (h3t : 3 * t ≤ 4 * q) (hB : 64 * B ≤ t) (ht : 32 ≤ t) :
    q + 4 * (5 * B) + 8 ≤ 2 * c := by omega

end BKLO
