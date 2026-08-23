/-
# What the sweep-wide perturbation hypothesis does, and what it still leaves open

`BKLO/AX2BalancedMergeRefutation.lean` refutes `BKLO.RoutedSweepInvCellCountBalancedWide6hStep` by a
*quantifier* defect: the step constrains the link system only at the presented link, so a history
link may have `X w` disjoint from its reserved link and pair its places completely freely.
`BKLO/AX2BalancedMergeFixed.lean` states the repair —
`BKLO.RoutedSweepInvCellCountBalancedWide6hStepFixed`, the same step with the perturbation budget
asked at every swept link — and re-threads the chain against it.

This file audits what the repair buys and what it does not.

## 1. What it buys

`BKLO/AX2PrescribedClassFibre.lean` and `BKLO/AX2PartnerSpreadRepaired.lean`: under the repair the
class-matched and cycle parts of the partner-class load of a place become **cell-shift fibres** of
the design — of size `|cell| / h + 1 ≈ 120 K²` — because the class matching of a link is the shift
by `φ w` and the cell-balance of `φ` splits a cell into `h` pieces.  Together with
`BKLO.FibreBalanced`, which divides the plan's global load by `h`, this assembles
`BKLO.PartnerClassSpread` — the clause `BKLO/AX2BalancedMergeObstruction.lean` reported missing —
with the constant

```
mc = N + 4 (|cell| / h + 1) + 2 BL + BM,
```

`N` the sweep-wide perturbation multiplicity of the place, `BL · h` the global per-place load of the
cell plan and `BM` that of the foreign plan.  `BKLO.engine_threshold_of_spread_constants` is the
arithmetic that turns `64 mc ≤ t` into the hypothesis `q + 4 mc + 8 ≤ 2 c` of every pairing engine
of the development, so the engines run as soon as those four constants are of size `t / 256`.

## 2. What it does not buy: the perturbation *multiplicity*

The two clauses of `BKLO.RoutedSweepInvCellCountBalancedWide6hStepFixed` bound, at each swept link,
how far `X w` is from `resLink R W' w`.  They do **not** bound how many links a *single place* may
be perturbed at, and the term `N` above is exactly that count.  The two theorems

* `BKLO.classMatchedSweep_congr_off_link` — the class-matched sweep is blind to the pairing of a
  place that lies outside the reserved link of its link;
* `BKLO.isCountClassification_congr_off_exc` — the counted classification is blind to the pairing
  of a place outside the exceptional set,

say that those pairings are free: a history may spend the whole per-link perturbation budget
`t / 32` on places of two classes of the presented link and pair them across, and
`BKLO.perturbation_multiplicity_budget_witness` is the count showing that the design has far more
links than the `2 c² / d` such a burn costs.  So the two clauses alone still admit the class
exhaustion that the refutation exploits.

The bound that closes this is the third sweep-wide clause,

```
∀ a ∈ W', 32 * ((W \ W').filter (fun w => a ∈ X w \ resLink R W' w)).card
  ≤ gridClassSize ε K W'.card,
```

which `BKLO.GridPairingClauseTwoSidedEighth` supplies alongside the other two (its hypothesis
`hXmult8`, weakened by `BKLO.twoSided_perturbation_eighth` exactly as the other two are), and which
`BKLO.multiplicity_clause_blocks_class_exhaustion` shows is incompatible with exhausting a class.

## 3. What it does not buy: the scale of the perturbation

The remaining constant is `BL`, the global per-place load of the cell plan divided by `h`.  The
plan has to hold the leftovers the perturbation *forces*: a class trace short by `d` at a link
forces `d` leftovers in the class the class matching pairs it with, and both members of a leftover
pair must be planned.  A cell has `|cell| ≈ 20 K² t` links and a class `q` places, so some place of
the class carries at least `|cell| · d / q` of the demand of one cell, and `BKLO.FibreBalanced`
turns a global load of `B · h` into a per-index cap of `B`.  At the perturbation scale the vehicle
fixes — `32 d ≤ t` — this is

```
|cell| · d / q ≈ 20 K² t · (t / 32) / (3 t / 4) ≈ 0.83 K² t,
```

above the `c ≈ 0.65 t` at which a place's partners inside one class run out
(`BKLO.plan_load_at_current_scale_witness`), whereas at a scale `64 K² d ≤ t` it is a factor
`2 K²` below it (`BKLO.plan_load_at_scaled_perturbation_witness`).  The perturbation scale is not
fixed by the mathematics: `BKLO.reservoirPairingResidual4_of_gridPairingResidualTwoSidedEighth`
*chooses* the cleanliness `η` of the design, and the factor `32` of
`BKLO.twoSided_perturbation_eighth` is where that choice enters the sweep.

So the audit of the repaired step is: with the third sweep-wide clause and a perturbation scale of
`64 K² d ≤ t`, the four constants of the spread are all below `t / 256` and every pairing engine of
the development runs at the presented link; at the scale `32 d ≤ t` the plan the merge is forced to
build is itself dense enough to let a history exhaust a class through the routed leftovers.

Everything here is `sorry`-free.
-/
import BKLO.AX2PartnerSpreadRepaired

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]

/-! ### The sweep and the classification are blind outside the reserved link -/

/-- **The class-matched sweep is blind to the pairing outside the reserved link.**  Two histories
that agree at every place of every reserved link are class-matched together: what a link does with
a place the perturbation added to it is unconstrained. -/
theorem classMatchedSweep_congr_off_link {h : ℕ} {C : ℕ → Finset V} {R : Finset (Sym2 V)}
    {W' : Finset V} {X : V → Finset V} {x y : V → ℕ} {ρ σ : V → ℕ → ℕ} {S : Finset V}
    {g g' : V → V → V} {Exc : V → Finset V}
    (hsweep : IsClassMatchedSweep h C R W' X x y ρ σ S g Exc)
    (hagree : ∀ w ∈ S, ∀ a ∈ resLink R W' w, g' w a = g w a) :
    IsClassMatchedSweep h C R W' X x y ρ σ S g' Exc := by
  intro a α β hα hβ haC w hw haX haR haE
  rw [hagree w hw a haR]
  exact hsweep a α β hα hβ haC w hw haX haR haE

/-- **The counted classification is blind to the pairing outside the exceptional set.**  Every
clause of `BKLO.IsCountClassification` that mentions the pairing mentions it at a place of one of
the five leftover families; a history is free at every other place. -/
theorem isCountClassification_congr_off_exc {ε : ℝ} {K : ℕ} {W' : Finset V} {C : ℕ → Finset V}
    {x y φ : V → ℕ} {L M : V → Finset V} {S : Finset V} {g g' : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    (hagree : ∀ w ∈ S, ∀ a : V,
      (a ∈ Cc w ∨ a ∈ Cr w ∨ a ∈ Pc w ∨ a ∈ Pr w ∨ a ∈ Po w) → g' w a = g w a) :
    IsCountClassification ε K W' C x y φ L M S g' Exc Cc Cr Pc Pr Fo Po rt := by
  obtain ⟨hsplit, hdisjC, hcyc, hrtlt, hroute, hPcL, hPrL, hPcRow, hPrCol, hcntC, hcntR, hFoM,
    hPo⟩ := hcls
  refine ⟨hsplit, hdisjC, ?_, hrtlt, ?_, hPcL, hPrL, hPcRow, hPrCol, hcntC, hcntR, hFoM, ?_⟩
  · intro w hw
    refine ⟨fun a ha => ⟨((hcyc w hw).1 a ha).1, ?_⟩, fun a ha => ⟨((hcyc w hw).2 a ha).1, ?_⟩⟩
    · rw [hagree w hw a (Or.inl ha)]; exact ((hcyc w hw).1 a ha).2
    · rw [hagree w hw a (Or.inr (Or.inl ha))]; exact ((hcyc w hw).2 a ha).2
  · intro w hw
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [hagree w hw a (Or.inr (Or.inr (Or.inl ha)))]; exact (hroute w hw).1 a ha
    · rw [hagree w hw a (Or.inr (Or.inr (Or.inr (Or.inl ha))))]; exact (hroute w hw).2 a ha
  · intro w hw a ha i hi
    rw [hagree w hw a (Or.inr (Or.inr (Or.inr (Or.inr ha))))]
    exact hPo w hw a ha i hi

/-! ### The perturbation multiplicity -/

/-- **The design has room to burn a class pair with perturbation places alone.**  At the sizes the
step guarantees — `K = 2`, `h = 25600`, `t = 6 h`, `3 t ≤ 4 c`, and a per-link perturbation budget
`d` with `32 d ≤ t` — a link can pair `d / 2` perturbation places across the two classes, and the
outer part of the design has at least `10 h² t` links, far more than the `2 c² / d` needed to burn
every edge between the two traces.  So the two sweep-wide clauses of
`BKLO.RoutedSweepInvCellCountBalancedWide6hStepFixed` do not by themselves forbid the exhaustion
the refutation exploits. -/
theorem perturbation_multiplicity_budget_witness :
    ∃ K h t c d L : ℕ, K = 2 ∧ 6400 * (K * K) ≤ h ∧ 6 * h ≤ t ∧ 3 * t ≤ 4 * c ∧ c ≤ t ∧
      32 * d ≤ t ∧ 10 * (h * h) * t ≤ L ∧ 2 * (c * c) ≤ L * d := by
  refine ⟨2, 25600, 153600, 115200, 4800, 10 * (25600 * 25600) * 153600, ?_⟩
  norm_num

/-- **The multiplicity clause forbids it.**  The third sweep-wide clause bounds the number of links
at which one place is perturbed by `t / 32`, and a place needs its partners inside a class — at
least `c ≥ 3 t / 4` of them — burnt to be exhausted there. -/
theorem multiplicity_clause_blocks_class_exhaustion {t c N : ℕ} (hc : 3 * t ≤ 4 * c)
    (hN : 32 * N ≤ t) (ht : 0 < t) : N < c := by omega

/-! ### The threshold of the engines, from the four constants of the spread -/

/-- **The engines run as soon as the partner-class spread is of size `t / 64`.**  This is the
arithmetic that connects `BKLO.partnerClassSpread_of_spreadPlans` to the hypothesis
`q + 4 mc + 8 ≤ 2 c` of `BKLO.exists_classMatched_pairing_cycle_shift` and of every other pairing
engine of the development. -/
theorem engine_threshold_of_spread_constants {t q c mc : ℕ} (hq : 3 * t ≤ 4 * q) (hqt : q ≤ t)
    (hqc : 7 * q ≤ 8 * c) (hmc : 64 * mc ≤ t) (ht : 64 ≤ t) : q + 4 * mc + 8 ≤ 2 * c := by
  omega

/-! ### The scale of the perturbation -/

/-- **At the perturbation scale the vehicle fixes, the forced plan is dense enough to allow routed
class exhaustion.**  A cell of `|cell| = 20 K² t + 1` links each forcing `d = t / 32` leftovers puts
`|cell| · d` slots on a class of `q = 3 t / 4` places, so some place of the class carries at least
`c` of them in a single cell — the number of partners it has inside one class of the link. -/
theorem plan_load_at_current_scale_witness :
    ∃ t q c cell d : ℕ, 4 * q = 3 * t ∧ q = c ∧ cell = 80 * t + 1 ∧ 32 * d = t ∧
      c * q ≤ cell * d := by
  refine ⟨153600, 115200, 115200, 80 * 153600 + 1, 4800, ?_⟩
  norm_num

/-- **At a perturbation scale `64 K² d ≤ t` it is a factor `2 K²` below it.**  The same count at
`K = 2` and `1024 d = t`: the demand of a cell on a class is then well below the class fibre, so
`BKLO.FibreBalanced` keeps the routed terms of the partner-class ledger under the engines'
threshold. -/
theorem plan_load_at_scaled_perturbation_witness :
    ∃ t q c cell d : ℕ, 4 * q = 3 * t ∧ q = c ∧ cell = 80 * t + 1 ∧ 1024 * d = t ∧
      4 * (cell * d) < c * q := by
  refine ⟨153600, 115200, 115200, 80 * 153600 + 1, 150, ?_⟩
  norm_num

end BKLO
