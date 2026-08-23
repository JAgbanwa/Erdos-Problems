/-
# The foreign family of the counted classification, and what still blocks the construction

`BKLO/AX2ScaledPerturbation.lean` and `BKLO/AX2ScaledCompleteStep.lean` re-thread the whole AX2
reduction at the finer perturbation scale `8192 K² d ≤ t` the audit of
`BKLO/AX2SweepWideAudit.lean` asks for.  At that scale the three constants of
`BKLO.partnerClassSpread_of_spreadPlans` that the perturbation controls are comfortably inside the
engines' threshold `64 mc ≤ t` (`BKLO.spread_constants_fit_at_scaled_scale_witness`), so the
routed part of the partner-class ledger is no longer the binding constraint.

This file records the constraint that **is** binding, and which the perturbation scale does not
touch: the **foreign** family `Fo` of `BKLO.IsCountClassification`.

## 1. The forcing

The perturbed link system `X u` may contain a place `b ∈ X u \ resLink R W' u` lying in a class
`C (A h + B)` of the design with `A ≠ x u` and `B ≠ y u` — a class outside the region of `u`.
Nothing in `BKLO.GridPairingClauseTwoSidedScaled` forbids this: the only clause on `X u` is
`X u ⊆ W'`.  If the new pairing sends a place `z` of `X u ∩ resLink R W' u` to such a `b`, then

* `z` violates the cross-side rule of `BKLO.IsClassMatchedSweep`, so `z ∈ Exc u`;
* every family of `BKLO.IsCountClassification` except `Fo` is excluded: `Cc`, `Cr`, `Pc`, `Pr` all
  put `g u z` in a class of the region of `u` (one of its two digits is `x u` or `y u`), and `Po`
  puts `g u z` in no class at all.

`BKLO.foreign_forced_of_offRegion_partner` is that implication, and
`BKLO.foreignPlan_contains_partner_of_offRegion_added` is its consequence for the plan: `z ∈ M u`.

## 2. The pool

`z` also has to satisfy `s(z, b) ∈ F \ U`.  The only bound the invariant gives on the used set `U`
is the class-level one of `BKLO.classDegree_le_of_partnerClassLoad`: `U` burns at most `mc` places
of any *one* class against `b`.  So the plan `M u` has to offer, at the link `u`, more than `mc`
places inside a single class — a pool of size `mc + 1` at least — or the construction has no legal
partner for `b` at all (`BKLO.no_partner_of_burnt_foreign_pool`).

## 3. The capacity, and the exact inequality that fails

The same constant `mc` bounds the *global* per-place load `BM` of the foreign plan: `BM` is one of
the four summands of `mc` in `BKLO.partnerClassSpread_of_spreadPlans`, so `BM ≤ mc` always.
Double counting the plan over the links (`BKLO.sum_card_plan_le_of_planGlobalLoad`) then gives

```
|W \ W'| · (mc + 1)  ≤  Σ_{u ∈ W \ W'} |M u ∩ W'|  ≤  |W'| · BM  ≤  |W'| · mc,
```

so the construction needs

```
|W \ W'| · (mc + 1) ≤ |W'| · mc,          in particular      |W \ W'| ≤ |W'|,
```

while the reduction supplies `K · |W'| ≤ |W|` with `K ≥ 800`, i.e. `|W \ W'| ≥ 799 · |W'|`
(`BKLO.foreign_pool_capacity_obstruction`, `BKLO.outer_card_ge_of_design`).

**The gap is a factor `K - 1 ≥ 799`, and it is independent of the perturbation scale**: the
adversary needs only *one* off-region added place per link, a perturbation multiplicity of about
`K²` per place, which is inside every scale bound the reduction can impose
(`BKLO.foreign_forcing_is_scale_free_witness`).  Making `η` smaller — the fix that closes the
routed terms — leaves this inequality exactly where it is.

## 4. What it would take

The foreign term is the only one of the four that carries **no** cell or index structure: `Fo` is
constrained by `BKLO.IsCountClassification` only through `Fo w ⊆ M w`.  The routed families are
paid by `BKLO.FibreBalanced`, which divides a global plan load by `h`; the class-matched and cycle
families are paid by cell-shift fibres.  Any repair therefore has to give the foreign family a
structure of the same kind — a class index for `Fo` together with a fibre-balance clause over the
`h²` classes, so that the foreign term of `BKLO.partnerClassSpread_of_spreadPlans` becomes
`BM / h² + 1` instead of `BM`.  The foreign plan may then carry the whole global load
`BM = 3 K² t` that `BKLO.ForeignSpreadLeftoverPlanWide` and the ledger already allow, and both the
capacity inequality and the engines' threshold hold at the design sizes with room to spare
(`BKLO.foreign_capacity_with_fibre_balanced_term_witness`).  That is a change to the *invariant*,
not to the perturbation scale, and it is not carried out here.

Everything here is `sorry`-free.
-/
import BKLO.AX2ScaledCompleteStep
import BKLO.AX2SweepWideAudit

open Finset

namespace BKLO

variable {V : Type} [DecidableEq V]
variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {L M : V → Finset V}

/-! ### A class index is determined by its two digits -/

/-- Two grid digits below `h` name a class index below `h * h`. -/
theorem gridIndex_lt {h A B : ℕ} (hA : A < h) (hB : B < h) : A * h + B < h * h := by
  calc A * h + B < A * h + h := by omega
    _ = (A + 1) * h := by ring
    _ ≤ h * h := Nat.mul_le_mul_right h (by omega)

/-- **A place lies in at most one class.**  If the two digit pairs differ, disjointness of the
classes forbids a common place. -/
theorem digits_eq_of_mem_classes {h : ℕ} {C : ℕ → Finset V} {z : V} {A B P Q : ℕ}
    (hdisj : ∀ i < h * h, ∀ j < h * h, i ≠ j → Disjoint (C i) (C j))
    (hA : A < h) (hB : B < h) (hP : P < h) (hQ : Q < h)
    (h1 : z ∈ C (A * h + B)) (h2 : z ∈ C (P * h + Q)) : A = P ∧ B = Q := by
  by_cases heq : A * h + B = P * h + Q
  · exact gridDigits_inj hB hQ heq
  · exact absurd (Finset.disjoint_left.1
      (hdisj _ (gridIndex_lt hA hB) _ (gridIndex_lt hP hQ) heq) h1) (by simpa using h2)

/-! ### The forcing: an off-region partner forces the foreign family -/

/-- **A place whose partner lies in a class outside the region of its link is a foreign
leftover.**  All of `Cc`, `Cr`, `Pc`, `Pr` place the partner in a class one of whose digits is
`x w` or `y w`, and `Po` places it in no class at all; so the split clause of
`BKLO.IsCountClassification` leaves only `Fo`. -/
theorem foreign_forced_of_offRegion_partner
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hdisj : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
      i ≠ j → Disjoint (C i) (C j))
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {w : V} (hw : w ∈ S) (hxlt : x w < gridSize ε K) (hylt : y w < gridSize ε K)
    {z : V} (hz : z ∈ Exc w) {A B : ℕ} (hA : A < gridSize ε K) (hB : B < gridSize ε K)
    (hgz : g w z ∈ C (A * gridSize ε K + B)) (hAx : A ≠ x w) (hBy : B ≠ y w) :
    z ∈ Fo w := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  obtain ⟨hsplit, -, hcyc, hrtlt, hroute, -, -, -, -, -, -, -, hPo⟩ := hcls
  rcases Finset.mem_union.1 (hsplit w hw hz) with hcase | hcase
  · rcases Finset.mem_union.1 hcase with hc | hc
    · -- the two cycle families
      rcases Finset.mem_union.1 hc with hc | hc
      · exact absurd ((digits_eq_of_mem_classes hdisj hA hB
          (crossShift_lt hhpos φ (y w) w) hylt hgz ((hcyc w hw).1 z hc).2).2) hBy
      · exact absurd ((digits_eq_of_mem_classes hdisj hA hB hxlt
          (crossShiftInv_lt hhpos φ (x w) w) hgz ((hcyc w hw).2 z hc).2).1) hAx
    · -- the two routed families
      rcases Finset.mem_union.1 hc with hc | hc
      · exact absurd ((digits_eq_of_mem_classes hdisj hA hB (hrtlt w hw z) hylt hgz
          ((hroute w hw).1 z hc)).2) hBy
      · exact absurd ((digits_eq_of_mem_classes hdisj hA hB hxlt (hrtlt w hw z) hgz
          ((hroute w hw).2 z hc)).1) hAx
  · rcases Finset.mem_union.1 hcase with hc | hc
    · exact hc
    · exact absurd hgz (hPo w hw z hc _ (gridIndex_lt hA hB))

/-- **The foreign plan has to contain the partner of an off-region added place.**  The forcing of
`BKLO.foreign_forced_of_offRegion_partner` together with the clause `Fo w ⊆ M w`. -/
theorem foreignPlan_contains_partner_of_offRegion_added
    {φ : V → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ}
    (hdisj : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
      i ≠ j → Disjoint (C i) (C j))
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    {w : V} (hw : w ∈ S) (hxlt : x w < gridSize ε K) (hylt : y w < gridSize ε K)
    {z : V} (hz : z ∈ Exc w) {A B : ℕ} (hA : A < gridSize ε K) (hB : B < gridSize ε K)
    (hgz : g w z ∈ C (A * gridSize ε K + B)) (hAx : A ≠ x w) (hBy : B ≠ y w) :
    z ∈ M w :=
  hcls.2.2.2.2.2.2.2.2.2.2.2.1 w hw
    (foreign_forced_of_offRegion_partner hdisj hcls hw hxlt hylt hz hA hB hgz hAx hBy)

/-- **A place of the reserved link that is paired off-region is exceptional.**  This is the other
half of the forcing: the cross-side rule of `BKLO.IsClassMatchedSweep` cannot hold for it. -/
theorem mem_exc_of_offRegion_partner
    {X : V → Finset V} {ρ σ : V → ℕ → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    (hdisj : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
      i ≠ j → Disjoint (C i) (C j))
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g Exc)
    (hρ : ∀ w β, ρ w β < gridSize ε K) (hσ : ∀ w α, σ w α < gridSize ε K)
    {w : V} (hw : w ∈ S) (hxlt : x w < gridSize ε K) (hylt : y w < gridSize ε K)
    {z : V} {α β : ℕ} (hα : α < gridSize ε K) (hβ : β < gridSize ε K)
    (hzC : z ∈ C (α * gridSize ε K + β)) (hzX : z ∈ X w) (hzR : z ∈ resLink R W' w)
    {A B : ℕ} (hA : A < gridSize ε K) (hB : B < gridSize ε K)
    (hgz : g w z ∈ C (A * gridSize ε K + B)) (hAx : A ≠ x w) (hBy : B ≠ y w) :
    z ∈ Exc w := by
  by_contra hz
  rcases hsweep z α β hα hβ hzC w hw hzX hzR hz with ⟨-, hmem⟩ | ⟨-, hmem⟩
  · exact hBy (digits_eq_of_mem_classes hdisj hA hB (hρ w β) hylt hgz hmem).2
  · exact hAx (digits_eq_of_mem_classes hdisj hA hB hxlt (hσ w α) hgz hmem).1

/-! ### The pool the foreign plan has to offer -/

/-- **If the used set burns the whole foreign pool of a class against an added off-region place,
the construction has no partner for it there.**  The partner `z = p b` of such a place, if it lies
in the reserved link and in a class, has to be a member of the foreign plan `M u`, and its pairing
edge has to avoid `U`.  So a plan whose intersection with the classes of the reserved link is
entirely burnt against `b` leaves the step no legal choice inside the reserved link. -/
theorem no_partner_of_burnt_foreign_pool
    {X : V → Finset V} {ρ σ : V → ℕ → ℕ} {S : Finset V} {g : V → V → V} {Exc : V → Finset V}
    {φ : V → ℕ} {Cc Cr Pc Pr Fo Po : V → Finset V} {rt : V → V → ℕ} {U : Finset (Sym2 V)}
    (hdisj : ∀ i < gridSize ε K * gridSize ε K, ∀ j < gridSize ε K * gridSize ε K,
      i ≠ j → Disjoint (C i) (C j))
    (hsweep : IsClassMatchedSweep (gridSize ε K) C R W' X x y ρ σ S g Exc)
    (hcls : IsCountClassification ε K W' C x y φ L M S g Exc Cc Cr Pc Pr Fo Po rt)
    (hρ : ∀ w β, ρ w β < gridSize ε K) (hσ : ∀ w α, σ w α < gridSize ε K)
    {u : V} (hu : u ∈ S) (hxlt : x u < gridSize ε K) (hylt : y u < gridSize ε K)
    {b z : V} {A B : ℕ} (hA : A < gridSize ε K) (hB : B < gridSize ε K)
    (hbC : b ∈ C (A * gridSize ε K + B)) (hAx : A ≠ x u) (hBy : B ≠ y u)
    (hzX : z ∈ X u) (hzR : z ∈ resLink R W' u)
    {α β : ℕ} (hα : α < gridSize ε K) (hβ : β < gridSize ε K)
    (hzC : z ∈ C (α * gridSize ε K + β))
    (hpair : g u z = b) (hlegal : s(z, g u z) ∉ U)
    (hburn : ∀ a ∈ M u, s(z, b) ∈ U) : False := by
  have hz : z ∈ Exc u :=
    mem_exc_of_offRegion_partner hdisj hsweep hρ hσ hu hxlt hylt hα hβ hzC hzX hzR hA hB
      (hpair ▸ hbC) hAx hBy
  have hzM : z ∈ M u :=
    foreignPlan_contains_partner_of_offRegion_added hdisj hcls hu hxlt hylt hz hA hB
      (hpair ▸ hbC) hAx hBy
  exact hlegal (hpair ▸ hburn z hzM)

/-! ### The capacity of the foreign plan -/

/-- **Double counting a plan over the links of the design.**  A plan of global per-place load `BM`
can offer, in total over all links, at most `|W'| · BM` places of `W'`. -/
theorem sum_card_plan_le_of_planGlobalLoad {BM : ℕ} (hM : PlanGlobalLoad W W' M BM)
    {D : Finset V} (hD : D ⊆ W \ W') :
    ∑ u ∈ D, (W'.filter (fun a => a ∈ M u)).card ≤ W'.card * BM := by
  classical
  have hstep : ∑ u ∈ D, (W'.filter (fun a => a ∈ M u)).card
      = ∑ a ∈ W', (D.filter (fun u => a ∈ M u)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hstep]
  calc ∑ a ∈ W', (D.filter (fun u => a ∈ M u)).card
      ≤ ∑ _a ∈ W', BM := by
        refine Finset.sum_le_sum fun a _ => le_trans (Finset.card_le_card ?_) (hM a)
        intro u hu
        obtain ⟨huD, huM⟩ := Finset.mem_filter.1 hu
        exact Finset.mem_filter.2 ⟨hD huD, huM⟩
    _ = W'.card * BM := by rw [Finset.sum_const, smul_eq_mul]

/-- **The capacity requirement, in arithmetic form.**  A pool of `mc + 1` at each of `D` links
cannot be met by a plan of global per-place load `BM ≤ mc` over `n'` places unless `D ≤ n'`. -/
theorem plan_pool_capacity_requirement {D n' BM mc : ℕ} (hBM : BM ≤ mc) (hn' : n' ≤ D)
    (hpos : 0 < n') (h : D * (mc + 1) ≤ n' * BM) : False := by
  have h2 : n' * (mc + 1) ≤ D * (mc + 1) := Nat.mul_le_mul_right _ hn'
  have h3 : n' * BM ≤ n' * mc := Nat.mul_le_mul_left _ hBM
  linarith only [hpos, h, h2, h3]

/-- **The foreign plan cannot offer a pool at every link.**  If every link of the outer part needs
`mc + 1` places of the plan and the plan's global per-place load is at most `mc`, the design must
have at most as many outer links as inner places — which the design never has. -/
theorem foreign_pool_capacity_obstruction {BM mc : ℕ} (hM : PlanGlobalLoad W W' M BM)
    (hBM : BM ≤ mc)
    (hpool : ∀ u ∈ W \ W', mc + 1 ≤ (W'.filter (fun a => a ∈ M u)).card)
    (hcard : W'.card ≤ (W \ W').card) (hpos : 0 < W'.card) : False := by
  classical
  refine plan_pool_capacity_requirement hBM hcard hpos ?_
  calc (W \ W').card * (mc + 1) = ∑ _u ∈ W \ W', (mc + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ W \ W', (W'.filter (fun a => a ∈ M u)).card :=
        Finset.sum_le_sum fun u hu => hpool u hu
    _ ≤ W'.card * BM := sum_card_plan_le_of_planGlobalLoad hM (Finset.Subset.refl _)

/-- **The design has far more outer links than inner places.**  From `K |W'| ≤ |W|` and
`W' ⊆ W` with `2 ≤ K` and `W'` nonempty. -/
theorem outer_card_ge_of_design (hW'W : W' ⊆ W) (hK : 1 ≤ K) (hKW' : K * W'.card ≤ W.card) :
    (K - 1) * W'.card ≤ (W \ W').card := by
  have h1 : (W \ W').card = W.card - W'.card := Finset.card_sdiff_of_subset hW'W
  have h0 : W'.card ≤ W.card := Finset.card_le_card hW'W
  have h2 : (K - 1) * W'.card = K * W'.card - W'.card := Nat.sub_one_mul K W'.card
  have h3 : W'.card ≤ K * W'.card := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The design has at least as many outer links as inner places already at `K = 2`; at the `K` the
reduction supplies, `800 ≤ K`, it has `799` times as many. -/
theorem outer_card_le_of_design (hW'W : W' ⊆ W) (hK : 2 ≤ K) (hKW' : K * W'.card ≤ W.card) :
    W'.card ≤ (W \ W').card := by
  have h := outer_card_ge_of_design hW'W (by omega) hKW'
  have h2 : 1 * W'.card ≤ (K - 1) * W'.card := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The foreign plan's global load is one of the four summands of the spread constant.**  This
is why the plan cannot be widened: `BM` is capped by the same `mc` the pool has to beat, in
`BKLO.partnerClassSpread_of_spreadPlans`. -/
theorem foreignLoad_le_spreadConstant (N cf BL BM : ℕ) : BM ≤ N + 4 * cf + 2 * BL + BM := by omega

/-- **The foreign plan of the merge is infeasible at the design.**  Combining the pool the forcing
needs at every outer link with the capacity a plan of global per-place load `BM ≤ mc` has, at a
design with `K ≥ 2` and a nonempty inner part.  This is the inequality the construction of
`BKLO.RoutedSweepInvCellCountBalancedWide6hStepScaledComplete` is short of, and it does not mention
the perturbation scale. -/
theorem foreign_plan_infeasible_at_design {BM mc : ℕ} (hW'W : W' ⊆ W) (hK : 2 ≤ K)
    (hKW' : K * W'.card ≤ W.card) (hpos : 0 < W'.card)
    (hM : PlanGlobalLoad W W' M BM) (hBM : BM ≤ mc)
    (hpool : ∀ u ∈ W \ W', mc + 1 ≤ (W'.filter (fun a => a ∈ M u)).card) : False :=
  foreign_pool_capacity_obstruction hM hBM hpool (outer_card_le_of_design hW'W hK hKW') hpos

/-! ### The two witnesses: the finer scale fixes the routed terms, and misses this one -/

/-- **At the finer perturbation scale the four constants of the spread fit under the engines'
threshold.**  With `K = 2`, `h = 25600`, `t = 6 h`, the perturbation multiplicity `N` bounded by
the finer scale `8192 K² N ≤ t`, and plan loads `BL`, `BM` of order `t / 1000`, the spread constant
`mc = N + 4 ((20 K² t + 1) / h + 1) + 2 BL + BM` of
`BKLO.partnerClassSpread_of_spreadPlans` satisfies `64 mc ≤ t`, which is the hypothesis
`BKLO.engine_threshold_of_spread_constants` turns into the engines' `q + 4 mc + 8 ≤ 2 c`. -/
theorem spread_constants_fit_at_scaled_scale_witness :
    ∃ K h t N BL BM mc : ℕ, K = 2 ∧ 6400 * (K * K) ≤ h ∧ 6 * h ≤ t ∧
      8192 * (K * K) * N ≤ t ∧
      mc = N + 4 * ((20 * (K * K) * t + 1) / h + 1) + 2 * BL + BM ∧
      64 * mc ≤ t := by
  refine ⟨2, 25600, 153600, 4, 150, 172, 2400, ?_⟩
  norm_num

/-- **The foreign forcing costs the adversary almost no perturbation.**  One off-region added
place at every outer link is a perturbation of one place per link, and a multiplicity of about
`K²` per inner place — inside the finer scale's budget `8192 K² N ≤ t` already at the smallest
sizes the step allows.  So no choice of perturbation scale removes the forcing. -/
theorem foreign_forcing_is_scale_free_witness :
    ∃ K h t d N : ℕ, K = 2 ∧ 6400 * (K * K) ≤ h ∧ 6 * h ≤ t ∧ d = 1 ∧ N = K * K ∧
      8192 * (K * K) * d ≤ t ∧ 8192 * (K * K) * N ≤ t := by
  refine ⟨2, 25600, 153600, 1, 4, ?_⟩
  norm_num

/-- **The exact inequality the construction is short of.**  With a pool of `mc + 1` per link and a
foreign plan of global per-place load `BM ≤ mc`, feasibility asks `|W \ W'| ≤ |W'|`, while the
design has `|W \ W'| ≥ (K - 1) |W'|`; at `K = 800` that is a factor `799`.  A foreign term paid
`BM / h` instead of `BM` — the repair §4 of the header describes — would ask
`|W \ W'| (mc + 1) ≤ |W'| h mc` instead, which the design meets. -/
theorem foreign_capacity_gap_witness :
    ∃ K h t n' D mc : ℕ, K = 800 ∧ 6400 * (K * K) ≤ h ∧ 6 * h ≤ t ∧
      64 * mc ≤ t ∧ (K - 1) * n' ≤ D ∧ 0 < n' ∧
      ¬ (D * (mc + 1) ≤ n' * mc) ∧ D * (mc + 1) ≤ n' * (h * mc) := by
  refine ⟨800, 4096000000, 24576000000, 1, 799, 384000000, ?_⟩
  norm_num

/-- **What a repair has to change, in arithmetic.**  Suppose the foreign term of
`BKLO.partnerClassSpread_of_spreadPlans` were paid the way the two routed terms are — by a
fibre-balance of the foreign family over the `h²` classes, so that it contributes
`BM / h² + 1` instead of `BM`.  Then the foreign plan may carry the full global load
`BM = 3 K² t` that `BKLO.ForeignSpreadLeftoverPlanWide` and the ledger already allow, and the
capacity inequality the pool needs,

```
|W \ W'| · (mc + 1) ≤ |W'| · BM,
```

holds at the design sizes with room to spare, *while* the spread constant

```
mc = N + 4 ((20 K² t + 1) / h + 1) + 2 BL + (BM / h² + 1)
```

still satisfies the engines' threshold `64 mc ≤ t`.  The witness is at `K = 800`,
`h = 6400 K²`, `t = 6 h`, with `|W \ W'| = 20 K² h² t` and `|W'| = 10 h² t` — the outer and inner
volumes of `BKLO.IsGridTwoSidedReservoir` — and the perturbation multiplicity `N` at the finer
scale of `BKLO/AX2ScaledPerturbation.lean`. -/
theorem foreign_capacity_with_fibre_balanced_term_witness :
    ∃ K h t N BL BM mc links places : ℕ,
      K = 800 ∧ 6400 * (K * K) ≤ h ∧ 6 * h ≤ t ∧
      8192 * (K * K) * N ≤ t ∧
      BM = 3 * (K * K) * t ∧
      links = 20 * (K * K) * (h * h) * t ∧ places = 10 * (h * h) * t ∧
      mc = N + 4 * ((20 * (K * K) * t + 1) / h + 1) + 2 * BL + (BM / (h * h) + 1) ∧
      64 * mc ≤ t ∧
      links * (mc + 1) ≤ places * BM := by
  refine ⟨800, 4096000000, 24576000000, 4, 10000000, 3 * (800 * 800) * 24576000000,
    327200009, 20 * (800 * 800) * (4096000000 * 4096000000) * 24576000000,
    10 * (4096000000 * 4096000000) * 24576000000, ?_⟩
  norm_num

end BKLO
