/-
# The partner-class spread of a sweep, and what the counted invariant still admits

`BKLO/AX2FibreBalance.lean` repaired the *index supply*: under `BKLO.FibreBalanced` every routing
index of every planned place is usable.  This file audits the next clause the one-link step needs,
and which no invariant of the development carries: a bound on how many times a *single place* has
already been paired into a *single class*.

## The quantity

`BKLO.partnerClassLoad C X S g a i` is the number of links `w` of the history at which the place
`a` was paired into the class `C i`.  Every one of those links burns one candidate partner of `a`
inside `C i`, permanently: `BKLO.UsedForbidden` forbids re-using an edge.

`BKLO.PartnerClassSpread h C X S g mc` is the clause "no place is paired into any class more than
`mc` times".

## Why the merge needs it

Every pairing engine of the library — `BKLO.exists_classMatched_pairing_cycle_shift`,
`BKLO.exists_classMatched_pairing_perturbed`, `BKLO.exists_three_class_cycle_block` — takes its
forbidden set through a hypothesis of the shape

```
∀ a ∈ resLink R W' u, ∀ k < h * h, ((C k ∩ resLink R W' u).filter (fun b => s(a,b) ∈ U)).card ≤ m
```

with `q + 4 m + 8 ≤ 2 c`: a **class-level** degree, of size at most `3 c / 14`.  What the vehicle
`BKLO.TwoSidedUsedClassMatchedResized6hPairing` hands the merge is
`(resLink U (X u) a).card ≤ m` with `12 n + 8 m ≤ (2 h - 1) c`: a **region-level** degree, and
`BKLO.class_blocking_within_step_margin` shows that hypothesis is satisfied even by an `m` twice
the size of a whole class fibre `c`.  `BKLO.cycle_engine_hypothesis_fails_of_class_blocked` is the
other side: at such an `m` the engine hypothesis is false, so no engine of the library applies.

`BKLO.class_degree_le_of_partnerClassSpread` is the bridge that closes that gap: the class-level
degree of the *used* pairs at any place is exactly the partner-class load of the place, so the
clause `BKLO.PartnerClassSpread` is precisely the missing hypothesis, and
`BKLO.exists_classMatched_pairing_of_partnerClassSpread` runs the unperturbed engine under it.

## What an adversarial history can still do

`BKLO.blocked_place_mem_exc` and `BKLO.blocked_class_subset_exc` are the instance-level statement of
the obstruction — not a ledger count: if the history has burnt, for one place `a` of the link, all
the partners the class matching allows it at `u`, then `a` *must* be left over at `u`; and if it
has done so for every place of a class of the link, then the whole class fibre is left over, so the
merge faces a leftover demand of `c` places at that single link — a factor `32 c / t ≈ 20` above the
`t / 32` the perturbation forces and the allocation of `BKLO/AX2CountedMergeAllocation.lean` is
sized for.  Nothing in `BKLO.IsCountClassificationBalanced` forbids such a history: its per-index
cap is `5 K² t + 1 ≈ 20 t`, far above the `c ≈ 0.65 t` partners a class has inside a link
(`BKLO.counted_cap_admits_class_exhaustion`).

Everything here is `sorry`-free.
-/
import BKLO.AX2BalancedMerge
import BKLO.AX2CyclePairing

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The partner-class load -/

/-- **The partner-class load**: the number of links of `S` at which the place `a` belongs to the
link and is paired into the class `C i`. -/
def partnerClassLoad (C : ℕ → Finset V) (X : V → Finset V) (S : Finset V) (g : V → V → V)
    (a : V) (i : ℕ) : ℕ :=
  (S.filter (fun w => a ∈ X w ∧ g w a ∈ C i)).card

/-- **The partner-class spread clause**: no place is ever paired into one class more than `mc`
times. -/
def PartnerClassSpread (h : ℕ) (C : ℕ → Finset V) (X : V → Finset V) (S : Finset V)
    (g : V → V → V) (mc : ℕ) : Prop :=
  ∀ a : V, ∀ i < h * h, partnerClassLoad C X S g a i ≤ mc

/-- The empty history is spread. -/
theorem partnerClassSpread_empty (h : ℕ) (C : ℕ → Finset V) (X : V → Finset V) (g : V → V → V)
    (mc : ℕ) : PartnerClassSpread h C X (∅ : Finset V) g mc := by
  intro a i _
  simp [partnerClassLoad]

/-- **The class-level degree of the used pairs is the partner-class load.**  A place `b` of the
class `C i` with `s(a, b)` already used is the partner of `a` at some link of the history: either
`a` was the source there, or `b` was — and then, the pairing at that link being an involution of
its own link, `a` was the source too.  So the used degree of `a` inside `C i` never exceeds
`BKLO.partnerClassLoad`. -/
theorem card_used_class_le_partnerClassLoad {C : ℕ → Finset V} {X : V → Finset V} {S : Finset V}
    {g : V → V → V} (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g w b ∈ X w)
    (hginv : ∀ w ∈ S, ∀ b ∈ X w, g w (g w b) = b) (a : V) (i : ℕ) (T : Finset V) :
    (((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S)).card
      ≤ partnerClassLoad C X S g a i := by
  classical
  have hsub : ((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S)
      ⊆ (S.filter (fun w => a ∈ X w ∧ g w a ∈ C i)).image (fun w => g w a) := by
    intro b hb
    obtain ⟨hbCT, hbU⟩ := Finset.mem_filter.1 hb
    have hbC : b ∈ C i := (Finset.mem_inter.1 hbCT).1
    obtain ⟨w, hw, z, hz, heq⟩ := mem_usedPairs.1 hbU
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have haX : a ∈ X w := by rw [h1]; exact hz
      have hgab : g w a = b := by rw [h1]; exact h2.symm
      exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, haX, by rw [hgab]; exact hbC⟩, hgab⟩
    · have hbX : b ∈ X w := by rw [h2]; exact hz
      have hgba : g w b = a := by rw [h2]; exact h1.symm
      have haX : a ∈ X w := by rw [← hgba]; exact hmaps w hw b hbX
      have hgab : g w a = b := by rw [← hgba, hginv w hw b hbX]
      exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, haX, by rw [hgab]; exact hbC⟩, hgab⟩
  calc (((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S)).card
      ≤ ((S.filter (fun w => a ∈ X w ∧ g w a ∈ C i)).image (fun w => g w a)).card :=
        Finset.card_le_card hsub
    _ ≤ (S.filter (fun w => a ∈ X w ∧ g w a ∈ C i)).card := Finset.card_image_le
    _ = partnerClassLoad C X S g a i := rfl

/-- **The class-level degree of the forbidden set, under the spread clause.**  A forbidden edge is a
used pair or meets the protected level (`BKLO.UsedForbidden`); at a place outside the protected
level the first kind is capped by `BKLO.PartnerClassSpread` and the second by the protected part of
the class. -/
theorem class_degree_le_of_partnerClassSpread {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V}
    {S W'' : Finset V} {g : V → V → V} {U : Finset (Sym2 V)} {mc : ℕ}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g w b ∈ X w)
    (hginv : ∀ w ∈ S, ∀ b ∈ X w, g w (g w b) = b)
    (hUused : UsedForbidden X g S W'' U)
    (hspread : PartnerClassSpread h C X S g mc)
    {a : V} (haW'' : a ∉ W'') {i : ℕ} (hi : i < h * h) (T : Finset V) :
    (((C i ∩ T)).filter (fun b => s(a, b) ∈ U)).card
      ≤ mc + (((C i ∩ T)).filter (fun b => b ∈ W'')).card := by
  classical
  have hsplit : ((C i ∩ T)).filter (fun b => s(a, b) ∈ U)
      ⊆ (((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S))
        ∪ (((C i ∩ T)).filter (fun b => b ∈ W'')) := by
    intro b hb
    obtain ⟨hbCT, hbU⟩ := Finset.mem_filter.1 hb
    rcases hUused a b hbU with h1 | h1 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hbCT, h1⟩)
    · exact absurd h1 haW''
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hbCT, h1⟩)
  calc (((C i ∩ T)).filter (fun b => s(a, b) ∈ U)).card
      ≤ ((((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S))
          ∪ (((C i ∩ T)).filter (fun b => b ∈ W''))).card := Finset.card_le_card hsplit
    _ ≤ (((C i ∩ T)).filter (fun b => s(a, b) ∈ usedPairs X g S)).card
          + (((C i ∩ T)).filter (fun b => b ∈ W'')).card := Finset.card_union_le _ _
    _ ≤ mc + (((C i ∩ T)).filter (fun b => b ∈ W'')).card := by
        have := card_used_class_le_partnerClassLoad (C := C) hmaps hginv a i T
        have h2 := hspread a i hi
        omega

/-! ### What a class-blocked place must become -/

/-- **A place whose prescribed partners are all forbidden is a leftover.**  If, at the link `u`, the
forbidden set contains every edge from `a` to the two classes the class matching allows `a` — the
row target `C (ρ u β · h + y u)` and the column target `C (x u · h + σ u α)` — then any pairing `p`
of the link avoiding `U` and extending the class-matched sweep must put `a` in the exceptional set
of `u`. -/
theorem blocked_place_mem_exc {h : ℕ} {C : ℕ → Finset V} {R : Finset (Sym2 V)} {W' : Finset V}
    {X : V → Finset V} {x y : V → ℕ} {ρ σ : V → ℕ → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V} {u : V} {p : V → V} {e : Finset V} {U : Finset (Sym2 V)}
    (hsweep : IsClassMatchedSweep h C R W' X x y ρ σ (insert u S) (Function.update g u p)
      (Function.update Exc u e))
    (hpX : ∀ a ∈ X u, p a ∈ X u) (hpU : ∀ a ∈ X u, s(a, p a) ∉ U)
    {a : V} {α β : ℕ} (hα : α < h) (hβ : β < h) (haC : a ∈ C (α * h + β))
    (haX : a ∈ X u) (haR : a ∈ resLink R W' u)
    (hrow : ∀ b ∈ C (ρ u β * h + y u) ∩ X u, s(a, b) ∈ U)
    (hcol : ∀ b ∈ C (x u * h + σ u α) ∩ X u, s(a, b) ∈ U) :
    a ∈ e := by
  classical
  by_contra hae
  have hExc : a ∉ Function.update Exc u e u := by
    rwa [Function.update_self]
  have hcross := hsweep a α β hα hβ haC u (Finset.mem_insert_self u S) haX haR hExc
  rw [Function.update_self] at hcross
  have hpaX : p a ∈ X u := hpX a haX
  rcases hcross with ⟨-, hmem⟩ | ⟨-, hmem⟩
  · exact hpU a haX (hrow (p a) (Finset.mem_inter.2 ⟨hmem, hpaX⟩))
  · exact hpU a haX (hcol (p a) (Finset.mem_inter.2 ⟨hmem, hpaX⟩))

/-- **A class all of whose places are blocked is left over whole.**  The instance-level form of the
obstruction: the leftover demand a single link can be made to carry is a whole class fibre of the
link, not the `t / 32` the perturbation forces. -/
theorem blocked_class_subset_exc {h : ℕ} {C : ℕ → Finset V} {R : Finset (Sym2 V)} {W' : Finset V}
    {X : V → Finset V} {x y : V → ℕ} {ρ σ : V → ℕ → ℕ} {S : Finset V} {g : V → V → V}
    {Exc : V → Finset V} {u : V} {p : V → V} {e : Finset V} {U : Finset (Sym2 V)}
    (hsweep : IsClassMatchedSweep h C R W' X x y ρ σ (insert u S) (Function.update g u p)
      (Function.update Exc u e))
    (hpX : ∀ a ∈ X u, p a ∈ X u) (hpU : ∀ a ∈ X u, s(a, p a) ∉ U)
    {α β : ℕ} (hα : α < h) (hβ : β < h)
    (hblock : ∀ a ∈ C (α * h + β) ∩ (X u ∩ resLink R W' u),
      (∀ b ∈ C (ρ u β * h + y u) ∩ X u, s(a, b) ∈ U) ∧
      (∀ b ∈ C (x u * h + σ u α) ∩ X u, s(a, b) ∈ U)) :
    C (α * h + β) ∩ (X u ∩ resLink R W' u) ⊆ e := by
  intro a ha
  obtain ⟨haC, haXR⟩ := Finset.mem_inter.1 ha
  obtain ⟨haX, haR⟩ := Finset.mem_inter.1 haXR
  obtain ⟨hrow, hcol⟩ := hblock a ha
  exact blocked_place_mem_exc hsweep hpX hpU hα hβ haC haX haR hrow hcol

/-! ### The gap between the vehicle's degree hypothesis and the engines' -/

/-- **The vehicle's margin admits a forbidden set twice as dense as a whole class fibre.**  With the
sizes the design guarantees — `4 n ≤ t`, `3 t ≤ 4 q`, `7 q ≤ 8 c` — the hypothesis
`12 n + 8 m ≤ (2 h - 1) c` of `BKLO.RoutedSweepInvCellCountBalancedWide6hStep` holds at `m = 2 c`:
the step must survive a history whose used degree at a place of the link is twice the number of
places a class has there. -/
theorem class_blocking_within_step_margin {h t q c n : ℕ} (hh : 21 ≤ h) (hn : 4 * n ≤ t)
    (hq3 : 3 * t ≤ 4 * q) (hqc : 7 * q ≤ 8 * c) :
    12 * n + 8 * (2 * c) ≤ (2 * h - 1) * c := by
  have h1 : 12 * n ≤ 3 * t := by omega
  have h2 : 3 * t ≤ 4 * q := hq3
  have h3 : 7 * (4 * q) ≤ 4 * (8 * c) := by omega
  have h4 : 12 * n ≤ 5 * c := by omega
  have h5 : 41 * c ≤ (2 * h - 1) * c := Nat.mul_le_mul_right c (by omega)
  omega

/-- **At such a degree no engine of the library applies.**  The hypothesis
`q + 4 m + 8 ≤ 2 c` of `BKLO.exists_classMatched_pairing_cycle_shift` — and of every other pairing
engine of the development — fails as soon as the *class-level* degree reaches the class fibre. -/
theorem cycle_engine_hypothesis_fails_of_class_blocked {q c m : ℕ} (hc : 0 < c) (hm : c ≤ m) :
    ¬ (q + 4 * m + 8 ≤ 2 * c) := by omega

/-- **The counted cap does not forbid class exhaustion.**  The per-index cap of
`BKLO.IsCountClassification` is `5 K² t + 1`, while a class holds at most `q ≤ t` places
(`BKLO.IsGridTwoSidedReservoir.classCardLe`) and only `c ≤ q` of them inside a link; so at `K ≥ 2`
the cap is a factor `20` above the number of partners a class has to offer at a link, and a history
still admitted by `BKLO.IsCountClassificationBalanced` can have burnt every one of them. -/
theorem counted_cap_admits_class_exhaustion {K t c q : ℕ} (hK : 2 ≤ K) (hqt : q ≤ t)
    (hcq : c ≤ q) :
    c ≤ 5 * (K * K) * t + 1 := by
  have hKK : 4 ≤ K * K := Nat.mul_le_mul hK hK
  have h2 : 20 * t ≤ 5 * (K * K) * t := by
    have h3 : 5 * 4 * t ≤ 5 * (K * K) * t := Nat.mul_le_mul_right t (by omega)
    omega
  omega

/-- **The protected level is invisible inside a class.**  `BKLO.IsGridTwoSidedReservoir` keeps the
classes disjoint from `W''`, so the second term of
`BKLO.class_degree_le_of_partnerClassSpread` vanishes: the class-level degree of the forbidden set
is the partner-class load alone. -/
theorem card_protected_in_class_eq_zero {ε : ℝ} {K : ℕ} {W W' W'' : Finset V}
    {F R : Finset (Sym2 V)} {C : ℕ → Finset V} {x y : V → ℕ}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    {k : ℕ} (hk : k < gridSize ε K * gridSize ε K) (T : Finset V) :
    (((C k ∩ T)).filter (fun b => b ∈ W'')).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b hb hbW''
  have hbC : b ∈ C k := (Finset.mem_inter.1 hb).1
  exact (Finset.disjoint_left.1 (hgrid.classAvoid k hk)) hbC hbW''

/-! ### The engine, under the missing clause -/

/-- **Under the partner-class spread clause the unperturbed engine runs.**  This is the exact sense
in which `BKLO.PartnerClassSpread` is the missing hypothesis of the one-link step: with it — and
with the protected level thin inside the classes of the link — the class-level degree bound the
engines take is available, and `BKLO.exists_classMatched_pairing_cycle_shift` produces the
class-matched pairing of the link, cycle blocks and all. -/
theorem exists_classMatched_pairing_of_partnerClassSpread
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {X : V → Finset V} {S : Finset V} {g : V → V → V} {U : Finset (Sym2 V)}
    {q c mc mp : ℕ}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hW'W : W' ⊆ W)
    {u : V} (hu : u ∈ W \ W')
    (hq : ∀ k < gridSize ε K * gridSize ε K, (C k).card = q)
    (hc : ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u), (C i ∩ resLink R W' u).card = c)
    {φ : V → ℕ} (hφlt : φ u < gridSize ε K)
    (hAne : crossShift (gridSize ε K) φ (y u) u ≠ x u)
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g w b ∈ X w)
    (hginv : ∀ w ∈ S, ∀ b ∈ X w, g w (g w b) = b)
    (hUused : UsedForbidden X g S W'' U)
    (hspread : PartnerClassSpread (gridSize ε K) C X S g mc)
    (hlinkW'' : ∀ a ∈ resLink R W' u, a ∉ W'')
    (hprot : ∀ k < gridSize ε K * gridSize ε K,
      ((C k ∩ resLink R W' u).filter (fun b => b ∈ W'')).card ≤ mp)
    (heven : Even c) (hsize : q + 4 * (mc + mp) + 8 ≤ 2 * c) :
    ∃ (p : V → V) (Ecol Erow : Finset V),
      Erow ⊆ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u) ∩ resLink R W' u ∧
      Ecol ⊆ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u)
        ∩ resLink R W' u ∧
      2 * Erow.card = c ∧ 2 * Ecol.card = c ∧
      (∀ a ∈ resLink R W' u, p a ∈ resLink R W' u) ∧
      (∀ a ∈ resLink R W' u, p (p a) = a) ∧ (∀ a ∈ resLink R W' u, p a ≠ a) ∧
      (∀ a ∈ resLink R W' u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      (∀ a ∈ Ecol, a ∈ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u) ∧
        p a ∈ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u)) ∧
      (∀ a ∈ Erow, a ∈ C (crossShift (gridSize ε K) φ (y u) u * gridSize ε K + y u) ∧
        p a ∈ C (x u * gridSize ε K + crossShiftInv (gridSize ε K) φ (x u) u)) ∧
      ∀ (a : V) (α β : ℕ), α < gridSize ε K → β < gridSize ε K →
        a ∈ C (α * gridSize ε K + β) → a ∈ resLink R W' u → a ∉ Ecol → a ∉ Erow →
        IsCrossSideAt (gridSize ε K) C x y α β u (p a)
          (crossShift (gridSize ε K) φ β u) (crossShiftInv (gridSize ε K) φ α u) := by
  classical
  refine exists_classMatched_pairing_cycle_shift hgrid hW'W hu hq hc hφlt hAne ?_ heven hsize
  intro a ha k hk
  have hdeg := class_degree_le_of_partnerClassSpread (W'' := W'') hmaps hginv hUused hspread
    (hlinkW'' a ha) hk (resLink R W' u)
  have hp := hprot k hk
  omega


/-! ### How many classes a history can exhaust -/

/-- The number of places of `T` inside the class `C k` that the forbidden set already denies to
`a`. -/
def usedClassDegree (C : ℕ → Finset V) (T : Finset V) (U : Finset (Sym2 V)) (a : V) (k : ℕ) : ℕ :=
  ((C k ∩ T).filter (fun b => s(a, b) ∈ U)).card

/-- The classes in which the forbidden set denies `a` more than `m₀` places of `T`. -/
def heavyClasses (h : ℕ) (C : ℕ → Finset V) (T : Finset V) (U : Finset (Sym2 V)) (a : V)
    (m₀ : ℕ) : Finset ℕ :=
  (Finset.range (h * h)).filter (fun k => m₀ < usedClassDegree C T U a k)

/-- **A history exhausts only a few classes.**  The classes are disjoint, so the class-level
degrees of a place add up to its total degree: a region-level degree bound `m` — the only bound the
vehicle `BKLO.TwoSidedUsedClassMatchedResized6hPairing` supplies — already implies that at most
`m / (m₀ + 1)` classes carry a degree above `m₀`.

This is the shape the missing engine hypothesis has to take.  A *uniform* class-level bound
`∀ k, usedClassDegree ≤ m₀` with `m₀ ≈ 3 c / 14` — what every engine of the development assumes —
is not available and cannot be made available: `BKLO.blocked_class_subset_exc` exhibits a history
that empties one class pair completely.  What *is* available is this counting bound: with the
ledger's `m ≈ h t / 9` and `m₀ = c ≈ 0.65 t` at most about `0.17 h` of the `2 h` classes of the
region are exhausted for any one place, so a merge that may *choose* the class of a leftover — and
`BKLO.FibreBalanced` makes every routing index usable — always has classes to choose from. -/
theorem card_heavyClasses_mul_le {h : ℕ} {C : ℕ → Finset V} {T : Finset V} {U : Finset (Sym2 V)}
    {a : V} {m₀ m : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hdeg : (T.filter (fun b => s(a, b) ∈ U)).card ≤ m) :
    (heavyClasses h C T U a m₀).card * (m₀ + 1) ≤ m := by
  classical
  set D : ℕ → Finset V := fun k => (C k ∩ T).filter (fun b => s(a, b) ∈ U) with hD
  set H : Finset ℕ := heavyClasses h C T U a m₀ with hH
  have hHlt : ∀ k ∈ H, k < h * h := by
    intro k hk
    exact Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  have hdisjD : (H : Set ℕ).PairwiseDisjoint D := by
    intro k hk j hj hkj
    refine Finset.disjoint_left.2 fun b hb hb' => ?_
    have h1 : b ∈ C k := (Finset.mem_inter.1 (Finset.mem_filter.1 hb).1).1
    have h2 : b ∈ C j := (Finset.mem_inter.1 (Finset.mem_filter.1 hb').1).1
    exact (Finset.disjoint_left.1 (hdisj k (hHlt k hk) j (hHlt j hj) hkj)) h1 h2
  have hbi : H.biUnion D ⊆ T.filter (fun b => s(a, b) ∈ U) := by
    intro b hb
    obtain ⟨k, -, hbk⟩ := Finset.mem_biUnion.1 hb
    obtain ⟨hbCT, hbU⟩ := Finset.mem_filter.1 hbk
    exact Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hbCT).2, hbU⟩
  have hsum : ∑ k ∈ H, (D k).card = (H.biUnion D).card := (Finset.card_biUnion hdisjD).symm
  have hlow : H.card * (m₀ + 1) ≤ ∑ k ∈ H, (D k).card := by
    calc H.card * (m₀ + 1) = ∑ _k ∈ H, (m₀ + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ k ∈ H, (D k).card := by
          refine Finset.sum_le_sum fun k hk => ?_
          have := (Finset.mem_filter.1 hk).2
          simpa [hD, usedClassDegree] using this
  have hup : (H.biUnion D).card ≤ m :=
    le_trans (Finset.card_le_card hbi) hdeg
  omega


/-- **At the presented link, a place is denied a whole class fibre in fewer than `h / 4` classes.**
The specialisation of `BKLO.card_heavyClasses_mul_le` to the data the one-link step is handed: the
degree bound `(resLink U (X u) a).card ≤ m` with the margin `12 n + 8 m ≤ (2 h - 1) c`.  So even a
history that empties class pairs whole — `BKLO.blocked_class_subset_exc` — leaves more than three
quarters of the classes of the grid open to every place of the link, and the merge, which chooses
the routing index of a leftover and may choose it at any index
(`BKLO.excRouteCount_le_of_fibreBalanced`), always has a class to route it to. -/
theorem card_heavyClasses_lt_quarter {h : ℕ} {C : ℕ → Finset V} {X : V → Finset V}
    {U : Finset (Sym2 V)} {u a : V} {n m c : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hdeg : (resLink U (X u) a).card ≤ m)
    (hmargin : 12 * n + 8 * m ≤ (2 * h - 1) * c) (hh : 0 < h) :
    4 * (heavyClasses h C (X u) U a c).card < h := by
  classical
  set r : ℕ := (heavyClasses h C (X u) U a c).card with hr
  have hdeg' : ((X u).filter (fun b => s(a, b) ∈ U)).card ≤ m := by
    simpa [resLink] using hdeg
  have h1 : r * (c + 1) ≤ m := card_heavyClasses_mul_le hdisj hdeg'
  have h2 : 8 * m ≤ (2 * h - 1) * c := by omega
  have h3 : (2 * h - 1) * c ≤ 2 * (h * c) := by
    calc (2 * h - 1) * c ≤ (2 * h) * c := Nat.mul_le_mul_right c (by omega)
      _ = 2 * (h * c) := by ring
  have e1 : r * (c + 1) = r * c + r := by ring
  by_contra hcon
  push_neg at hcon
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · omega
    · exact h0
  have h4 : 2 * (h * c) ≤ 8 * (r * c) := by
    calc 2 * (h * c) = (2 * h) * c := by ring
      _ ≤ (8 * r) * c := Nat.mul_le_mul_right c (by omega)
      _ = 8 * (r * c) := by ring
  omega

end BKLO
