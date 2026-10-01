import PaperIV.RD09CandidateCounting
import PaperIV.RD09FactorCandidateMoments
import PaperIV.RD09FiniteAveraging
import PaperIV.RD09PhaseII
import PaperIV.RD09RootFactorPhase
import PaperIV.RD09PhysicalLedger

/-!
# RD09-L2: the factor–candidate second-moment bound, and its physical phase-II adapter

## The combinatorial model

A clique core has `p` vertices (indexed by a linearly ordered fintype `Z`); its *bases*
are the edges of `K_p`, represented by the ordered pairs `x < y`
(`RD09FactorCandidateMoments.corePairs`).  `K_p` is partitioned into `k` matching
factors by `fac : Z × Z → Fin k` (`k = p - 1` for `p` even, `k = p` for `p` odd; only
`p - 1 ≤ k` is used).  The exterior candidate set is a fintype `Cand` with `q = #Cand`
vertices, `q ≥ k`, `q ≥ 2`.

With `s = max (2 k - q) 0`, exactly `s` factors receive one candidate slot and the
remaining `k - s` factors receive two, and all `2 k - s ≤ q` slots are injected into
*distinct* candidates.  A literal assignment is therefore a pair

```text
α = (pos, ι) : (Fin k ↪ Fin k) × (Slot k s ↪ Cand)
```

where `pos` labels the factors by positions — the `s` factors whose position is at
least `k - s` are the one-slot factors — and `ι` injects the slots
`Slot k s = Fin k ⊕ Fin (k - s)` (one primary slot per factor, one secondary slot per
two-slot factor) into the candidates.  Averaging over *this* finite family is averaging
over the choice of the `s` one-slot factors and over the injections, exactly as the
source prescribes.

A base `e` with invalid-host set `bad e` **fails** if every slot of its own factor lands
in `bad e` (`Fails`).

## What is proved

* the reusable moment chain (in `PaperIV.RD09FactorCandidateMoments`):
  `∑ e, b e ≤ (p-1) S`, `∑ e, b e ^ 2 ≤ (p-2) ∑ d ^ 2 + S ^ 2`,
  `∑ z, d z ^ 2 ≤ (D + 4t) A + 4t f`;
* the exact per-base moments of the assignment family
  (`PaperIV.RD09CandidateCounting`), in cross-multiplied integral form;
* `exists_assign_rd09L2`: **one literal assignment** whose failed-base family has
  cardinality `g` with
  `g ≤ (s/q)(A+2f) + ((p-2)((D+4t)A+4tf) + (A+2f)^2) / (q(q-1))`;
* the physical adapter: from that assignment, singleton hubs over one valid host for
  every surviving base give a literal `RD09PhaseII.IsPhaseTwoFamily`, compatible
  (`RD09PhaseII.IsPhaseCompatible`) with any supplied phase-I
  `MultiHostTriangleLift.IsMultiExteriorHub`, hence a literal union packing;
* the ledger interface: the RD09-L2 bound, under explicit scalar budgets, yields the
  integral `L10` consumed by `RD09PhysicalLedger`.

Nothing is postulated: every hypothesis is either a literal structural fact about the
supplied finite data or an explicitly named scalar budget.
-/

namespace PaperIV.RD09FactorCandidateAverage

open Finset
open PaperIV.RD09CandidateCounting PaperIV.RD09FactorCandidateMoments

/-! ## The source parameters -/

/-- **The slot hypotheses come from the source parameters.**  With `q ≥ k` exterior
candidates and `s = max (2k - q) 0` one-slot factors, exactly `s ≤ k` factors get one slot
and the `k + (k - s) = 2k - s` slots fit injectively into the `q` candidates. -/
theorem slot_hypotheses {k q s : ℕ} (hqk : k ≤ q) (hs : s = max (2 * k - q) 0) :
    s ≤ k ∧ k + (k - s) ≤ q := by
  subst hs
  omega

/-- **The factor count.**  `k = p - 1` for `p` even and `k = p` for `p` odd; only
`p - 1 ≤ k` is used by RD09-L2. -/
theorem sub_one_le_of_factor_count {p k : ℕ} (hk : k = p - 1 ∨ k = p) : p - 1 ≤ k := by
  rcases hk with rfl | rfl <;> omega

/-! ## The assignment family -/

variable {k s : ℕ} {Cand : Type*} [Fintype Cand] [DecidableEq Cand]

/-- The slots: one primary slot per factor, plus one secondary slot for each of the
`k - s` two-slot factors. -/
abbrev Slot (k s : ℕ) : Type := Fin k ⊕ Fin (k - s)

/-- A literal assignment: a labelling of the factors by positions (the `s` factors at
positions `≥ k - s` are the one-slot factors) together with an injection of all slots
into distinct exterior candidates. -/
abbrev Assign (k s : ℕ) (Cand : Type*) : Type _ := (Fin k ↪ Fin k) × (Slot k s ↪ Cand)

/-- The factor `F` is a *one-slot* factor of the assignment. -/
def IsOneSlot (s : ℕ) (pos : Fin k ↪ Fin k) (F : Fin k) : Prop := k - s ≤ (pos F : ℕ)

instance (s : ℕ) (pos : Fin k ↪ Fin k) (F : Fin k) : Decidable (IsOneSlot s pos F) := by
  unfold IsOneSlot; infer_instance

/-- A base with invalid-host set `bad`, lying in factor `F`, **fails**: its factor's only
slot is invalid (one-slot factor), or both of its factor's slots are invalid. -/
def Fails (s : ℕ) (α : Assign k s Cand) (bad : Finset Cand) (F : Fin k) : Prop :=
  if h : k - s ≤ (α.1 F : ℕ) then α.2 (Sum.inl F) ∈ bad
  else α.2 (Sum.inl F) ∈ bad ∧ α.2 (Sum.inr ⟨(α.1 F : ℕ), by omega⟩) ∈ bad

instance (s : ℕ) (α : Assign k s Cand) (bad : Finset Cand) (F : Fin k) :
    Decidable (Fails s α bad F) := by unfold Fails; infer_instance

/-- The slot actually used by a base of factor `F`: the primary slot unless it is
invalid and a secondary slot exists. -/
def slotUsed (s : ℕ) (α : Assign k s Cand) (bad : Finset Cand) (F : Fin k) : Slot k s :=
  if h : k - s ≤ (α.1 F : ℕ) then Sum.inl F
  else if α.2 (Sum.inl F) ∈ bad then Sum.inr ⟨(α.1 F : ℕ), by omega⟩ else Sum.inl F

/-- The host chosen for a base of factor `F`. -/
def hostUsed (s : ℕ) (α : Assign k s Cand) (bad : Finset Cand) (F : Fin k) : Cand :=
  α.2 (slotUsed s α bad F)

omit [Fintype Cand] in
/-- **A nonfailed base gets a valid host.** -/
theorem hostUsed_notMem {α : Assign k s Cand} {bad : Finset Cand} {F : Fin k}
    (h : ¬ Fails s α bad F) : hostUsed s α bad F ∉ bad := by
  unfold hostUsed slotUsed
  unfold Fails at h
  by_cases hone : k - s ≤ (α.1 F : ℕ)
  · rw [dif_pos hone] at h ⊢
    exact h
  · rw [dif_neg hone] at h ⊢
    by_cases hb : α.2 (Sum.inl F) ∈ bad
    · rw [if_pos hb]
      exact fun hc => h ⟨hb, hc⟩
    · rw [if_neg hb]
      exact hb

omit [Fintype Cand] in
/-- The slot used by a base is one of the two slots of its own factor. -/
theorem slotUsed_spec (s : ℕ) (α : Assign k s Cand) (bad : Finset Cand) (F : Fin k) :
    slotUsed s α bad F = Sum.inl F ∨
      ∃ h : (α.1 F : ℕ) < k - s, slotUsed s α bad F = Sum.inr ⟨(α.1 F : ℕ), h⟩ := by
  unfold slotUsed
  by_cases hone : k - s ≤ (α.1 F : ℕ)
  · rw [dif_pos hone]; exact Or.inl rfl
  · rw [dif_neg hone]
    by_cases hb : α.2 (Sum.inl F) ∈ bad
    · rw [if_pos hb]; exact Or.inr ⟨by omega, rfl⟩
    · rw [if_neg hb]; exact Or.inl rfl

omit [Fintype Cand] in
/-- The slot used by a base belongs to that base's own factor, so two bases in distinct
factors use distinct slots. -/
theorem slotUsed_ne {α : Assign k s Cand} {bad bad' : Finset Cand} {F F' : Fin k}
    (h : F ≠ F') : slotUsed s α bad F ≠ slotUsed s α bad' F' := by
  intro hc
  rcases slotUsed_spec s α bad F with h1 | ⟨hlt, h1⟩ <;>
    rcases slotUsed_spec s α bad' F' with h2 | ⟨hlt', h2⟩ <;> rw [h1, h2] at hc
  · exact h (Sum.inl_injective hc)
  · exact absurd hc (by simp)
  · exact absurd hc (by simp)
  · have hval : (⟨(α.1 F : ℕ), hlt⟩ : Fin (k - s)) = ⟨(α.1 F' : ℕ), hlt'⟩ := by
      simpa using hc
    have hnat : (α.1 F : ℕ) = (α.1 F' : ℕ) :=
      congrArg (fun x : Fin (k - s) => (x : ℕ)) hval
    exact h (α.1.injective (Fin.val_injective hnat))

omit [Fintype Cand] in
/-- Two bases in distinct factors get distinct hosts. -/
theorem hostUsed_ne {α : Assign k s Cand} {bad bad' : Finset Cand} {F F' : Fin k}
    (h : F ≠ F') : hostUsed s α bad F ≠ hostUsed s α bad' F' :=
  fun hc => slotUsed_ne h (α.2.injective hc)

/-! ## The exact moments of the assignment family -/

omit [DecidableEq Cand] in
/-- The number of positions at least `k - s` is `s`. -/
theorem card_filter_oneSlot_positions (hsk : s ≤ k) :
    ((univ : Finset (Fin k)).filter fun i : Fin k => k - s ≤ (i : ℕ)).card = s := by
  classical
  have hlt : ∀ m : ℕ, m ≤ k →
      ((univ : Finset (Fin k)).filter fun i : Fin k => (i : ℕ) < m).card = m := by
    intro m hm
    have heq : ((univ : Finset (Fin k)).filter fun i : Fin k => (i : ℕ) < m)
        = Finset.map (Fin.castLEEmb hm) univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.mem_map, Fin.castLEEmb,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hi
        exact ⟨⟨(i : ℕ), hi⟩, by ext; simp⟩
      · rintro ⟨j, rfl⟩
        simp
    rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h1 := hlt (k - s) (Nat.sub_le _ _)
  have h2 : ((univ : Finset (Fin k)).filter fun i : Fin k => (i : ℕ) < k - s).card
      + ((univ : Finset (Fin k)).filter fun i : Fin k => ¬ ((i : ℕ) < k - s)).card
      = Fintype.card (Fin k) := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have h3 : ((univ : Finset (Fin k)).filter fun i : Fin k => ¬ ((i : ℕ) < k - s))
      = ((univ : Finset (Fin k)).filter fun i : Fin k => k - s ≤ (i : ℕ)) :=
    Finset.filter_congr fun x _ => by simp [not_lt]
  rw [h3, h1, Fintype.card_fin] at h2
  omega

/-- **The exact frequency of the one-slot factors.**  Over the family of position
labellings, every factor is a one-slot factor in exactly the fraction `s / k` of
cases, in cross-multiplied form. -/
theorem card_mul_card_filter_isOneSlot (hsk : s ≤ k) (F : Fin k) :
    k * ((univ : Finset (Fin k ↪ Fin k)).filter fun pos => IsOneSlot s pos F).card
      = s * Fintype.card (Fin k ↪ Fin k) := by
  classical
  have h := card_mul_card_filter_apply_mem (α := Fin k) (β := Fin k) F
    ((univ : Finset (Fin k)).filter fun i : Fin k => k - s ≤ (i : ℕ))
  rw [card_filter_oneSlot_positions hsk, Fintype.card_fin] at h
  have hset : ((univ : Finset (Fin k ↪ Fin k)).filter fun pos =>
        pos F ∈ (univ : Finset (Fin k)).filter fun i : Fin k => k - s ≤ (i : ℕ))
      = (univ : Finset (Fin k ↪ Fin k)).filter fun pos => IsOneSlot s pos F :=
    Finset.filter_congr fun pos _ => by simp [IsOneSlot]
  rw [hset] at h
  exact h

/-- **The exact per-position moment.**  For a fixed position labelling the failure
probability of a base is `b / q` if its factor is a one-slot factor, and at most
`b ^ 2 / (q (q-1))` otherwise. -/
theorem card_mul_pred_mul_card_filter_fails_le (pos : Fin k ↪ Fin k) (bad : Finset Cand)
    (F : Fin k) :
    Fintype.card Cand * (Fintype.card Cand - 1)
        * ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => Fails s (pos, ι) bad F).card
      ≤ (if IsOneSlot s pos F then (Fintype.card Cand - 1) * bad.card else bad.card ^ 2)
          * Fintype.card (Slot k s ↪ Cand) := by
  classical
  by_cases hone : k - s ≤ (pos F : ℕ)
  · rw [if_pos (show IsOneSlot s pos F from hone)]
    have hset : ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => Fails s (pos, ι) bad F)
        = (univ : Finset (Slot k s ↪ Cand)).filter fun ι => ι (Sum.inl F) ∈ bad := by
      refine Finset.filter_congr fun ι _ => ?_
      unfold Fails
      rw [dif_pos hone]
    rw [hset]
    have hcount := card_mul_card_filter_apply_mem (α := Slot k s) (β := Cand) (Sum.inl F) bad
    calc Fintype.card Cand * (Fintype.card Cand - 1)
          * ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => ι (Sum.inl F) ∈ bad).card
        = (Fintype.card Cand - 1) * (Fintype.card Cand
            * ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => ι (Sum.inl F) ∈ bad).card) := by
          ring
      _ = (Fintype.card Cand - 1) * (bad.card * Fintype.card (Slot k s ↪ Cand)) := by
          rw [hcount]
      _ ≤ (Fintype.card Cand - 1) * bad.card * Fintype.card (Slot k s ↪ Cand) := by
          rw [mul_assoc]
  · rw [if_neg (show ¬ IsOneSlot s pos F from hone)]
    have hlt : (pos F : ℕ) < k - s := by omega
    set v : Slot k s := Sum.inr ⟨(pos F : ℕ), hlt⟩ with hv
    have hset : ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => Fails s (pos, ι) bad F)
        = (univ : Finset (Slot k s ↪ Cand)).filter fun ι =>
            ι (Sum.inl F) ∈ bad ∧ ι v ∈ bad := by
      refine Finset.filter_congr fun ι _ => ?_
      unfold Fails
      rw [dif_neg hone]
    rw [hset]
    exact card_mul_pred_mul_card_filter_pair_le (Sum.inl F) v (by simp [hv]) bad

/-- Summing a property of assignments splits along the two independent coordinates. -/
theorem card_filter_fails_eq_sum (bad : Finset Cand) (F : Fin k) :
    ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card
      = ∑ pos : Fin k ↪ Fin k,
          ((univ : Finset (Slot k s ↪ Cand)).filter fun ι => Fails s (pos, ι) bad F).card := by
  classical
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- **The exact per-base moment of the whole assignment family**, in cross-multiplied
integral form:
`k q (q-1) #{α | base fails} ≤ ((q-1) s b + k b ^ 2) * #assignments`. -/
theorem key_per_base (hsk : s ≤ k) (bad : Finset Cand) (F : Fin k) :
    k * (Fintype.card Cand * (Fintype.card Cand - 1))
        * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card
      ≤ ((Fintype.card Cand - 1) * s * bad.card + k * bad.card ^ 2)
          * Fintype.card (Assign k s Cand) := by
  classical
  set q := Fintype.card Cand with hq
  set Nι := Fintype.card (Slot k s ↪ Cand) with hNι
  set Npos := Fintype.card (Fin k ↪ Fin k) with hNpos
  set One := ((univ : Finset (Fin k ↪ Fin k)).filter fun pos => IsOneSlot s pos F).card with hOne
  set Two := ((univ : Finset (Fin k ↪ Fin k)).filter fun pos => ¬ IsOneSlot s pos F).card with hTwo
  have hstep : q * (q - 1)
      * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card
      ≤ ∑ pos : Fin k ↪ Fin k,
          (if IsOneSlot s pos F then (q - 1) * bad.card else bad.card ^ 2) * Nι := by
    rw [card_filter_fails_eq_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun pos _ => card_mul_pred_mul_card_filter_fails_le pos bad F
  have hsum : (∑ pos : Fin k ↪ Fin k,
      (if IsOneSlot s pos F then (q - 1) * bad.card else bad.card ^ 2) * Nι)
      = (One * ((q - 1) * bad.card) + Two * bad.card ^ 2) * Nι := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_ite]
    simp [hOne, hTwo, mul_comm]
  rw [hsum] at hstep
  have hOneCount : k * One = s * Npos := card_mul_card_filter_isOneSlot hsk F
  have hTwoCount : Two ≤ Npos := by
    rw [hTwo, hNpos, ← Finset.card_univ]
    exact Finset.card_filter_le _ _
  have hcardAssign : Fintype.card (Assign k s Cand) = Npos * Nι := by
    rw [hNpos, hNι]
    exact Fintype.card_prod _ _
  have hmain : k * (q * (q - 1))
      * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card
      ≤ k * ((One * ((q - 1) * bad.card) + Two * bad.card ^ 2) * Nι) := by
    calc k * (q * (q - 1))
        * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card
        = k * (q * (q - 1)
            * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α bad F).card) := by
          ring
      _ ≤ k * ((One * ((q - 1) * bad.card) + Two * bad.card ^ 2) * Nι) :=
          Nat.mul_le_mul_left _ hstep
  refine hmain.trans ?_
  have hexpand : k * ((One * ((q - 1) * bad.card) + Two * bad.card ^ 2) * Nι)
      = ((k * One) * ((q - 1) * bad.card) + (k * Two) * bad.card ^ 2) * Nι := by ring
  rw [hexpand, hcardAssign, hOneCount]
  have hle : (k * Two) * bad.card ^ 2 ≤ (k * Npos) * bad.card ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hTwoCount)
  calc (s * Npos * ((q - 1) * bad.card) + k * Two * bad.card ^ 2) * Nι
      ≤ (s * Npos * ((q - 1) * bad.card) + k * Npos * bad.card ^ 2) * Nι :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left hle _)
    _ = ((q - 1) * s * bad.card + k * bad.card ^ 2) * (Npos * Nι) := by ring

/-! ## Averaging over the assignment family -/

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [LinearOrder Z]

/-- The failed bases of an assignment: the core bases whose factor offers them no valid
candidate host. -/
def failedBases (s : ℕ) (α : Assign k s Cand) (fac : Z × Z → Fin k)
    (bad : Z × Z → Finset Cand) : Finset (Z × Z) :=
  (corePairs Z).filter fun e => Fails s α (bad e) (fac e)

theorem mem_failedBases {α : Assign k s Cand} {fac : Z × Z → Fin k}
    {bad : Z × Z → Finset Cand} {e : Z × Z} :
    e ∈ failedBases s α fac bad ↔ e ∈ corePairs Z ∧ Fails s α (bad e) (fac e) := by
  simp [failedBases]

/-- Double counting: the total number of (assignment, failed base) incidences. -/
theorem sum_card_failedBases (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) :
    (∑ α : Assign k s Cand, (failedBases s α fac bad).card)
      = ∑ e ∈ corePairs Z,
          ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α (bad e) (fac e)).card := by
  classical
  simp only [failedBases, Finset.card_filter]
  exact Finset.sum_comm

/-- **The total second-moment bound over the whole assignment family.** -/
theorem total_bound (hsk : s ≤ k) (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) :
    k * (Fintype.card Cand * (Fintype.card Cand - 1))
        * (∑ α : Assign k s Cand, (failedBases s α fac bad).card)
      ≤ ((Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2)
          * Fintype.card (Assign k s Cand) := by
  classical
  rw [sum_card_failedBases, Finset.mul_sum]
  calc (∑ e ∈ corePairs Z, k * (Fintype.card Cand * (Fintype.card Cand - 1))
          * ((univ : Finset (Assign k s Cand)).filter fun α => Fails s α (bad e) (fac e)).card)
      ≤ ∑ e ∈ corePairs Z, ((Fintype.card Cand - 1) * s * (bad e).card
            + k * (bad e).card ^ 2) * Fintype.card (Assign k s Cand) :=
        Finset.sum_le_sum fun e _ => key_per_base hsk (bad e) (fac e)
    _ = ((Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2)
          * Fintype.card (Assign k s Cand) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The assignment family is nonempty as soon as there are at least as many candidates as
slots. -/
theorem card_assign_pos (hslots : k + (k - s) ≤ Fintype.card Cand) :
    0 < Fintype.card (Assign k s Cand) := by
  classical
  rw [Fintype.card_prod]
  refine Nat.mul_pos (card_embedding_pos le_rfl) (card_embedding_pos ?_)
  simpa [Slot, Fintype.card_sum] using hslots

/-- **The integral RD09-L2 certificate.**  Some literal assignment has
`k q (q-1) g ≤ (q-1) s ∑ b + k ∑ b ^ 2`. -/
theorem exists_assign_integral (hsk : s ≤ k) (hslots : k + (k - s) ≤ Fintype.card Cand)
    (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) :
    ∃ α : Assign k s Cand,
      k * (Fintype.card Cand * (Fintype.card Cand - 1)) * (failedBases s α fac bad).card
        ≤ (Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2 := by
  classical
  have hpos := card_assign_pos (k := k) (s := s) (Cand := Cand) hslots
  haveI : Nonempty (Assign k s Cand) := Fintype.card_pos_iff.mp hpos
  obtain ⟨α, hα⟩ := PaperIV.RD09FiniteAveraging.exists_card_mul_natCost_le_sum
    (fun α : Assign k s Cand => (failedBases s α fac bad).card)
  refine ⟨α, ?_⟩
  have hmul : Fintype.card (Assign k s Cand)
      * (k * (Fintype.card Cand * (Fintype.card Cand - 1)) * (failedBases s α fac bad).card)
      ≤ Fintype.card (Assign k s Cand)
        * ((Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2) := by
    calc Fintype.card (Assign k s Cand)
        * (k * (Fintype.card Cand * (Fintype.card Cand - 1)) * (failedBases s α fac bad).card)
        = k * (Fintype.card Cand * (Fintype.card Cand - 1))
            * (Fintype.card (Assign k s Cand) * (failedBases s α fac bad).card) := by ring
      _ ≤ k * (Fintype.card Cand * (Fintype.card Cand - 1))
            * (∑ α : Assign k s Cand, (failedBases s α fac bad).card) :=
          Nat.mul_le_mul_left _ hα
      _ ≤ ((Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2)
          * Fintype.card (Assign k s Cand) := total_bound hsk fac bad
      _ = Fintype.card (Assign k s Cand)
          * ((Fintype.card Cand - 1) * s * (∑ e ∈ corePairs Z, (bad e).card)
            + k * ∑ e ∈ corePairs Z, (bad e).card ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hpos


/-! ## The RD09-L2 inequality -/

/-- The right-hand side of RD09-L2:
`(s/q)(A + 2f) + ((p-2)((D + 4t)A + 4tf) + (A + 2f)^2) / (q (q-1))`. -/
def rd09L2Bound (q p D t A f s : ℕ) : ℚ :=
  (s : ℚ) / (q : ℚ) * ((A : ℚ) + 2 * f)
    + (((p : ℚ) - 2) * (((D : ℚ) + 4 * t) * (A : ℚ) + 4 * t * f) + ((A : ℚ) + 2 * f) ^ 2)
        / ((q : ℚ) * ((q : ℚ) - 1))

/-- **RD09-L2, the exact rational bound.**  Averaging over the choice of the `s`
one-slot factors and over the injections of all slots into distinct exterior candidates
produces **one literal assignment** whose failed-base family has cardinality

`g ≤ (s/q)(A + 2f) + ((p-2)((D + 4t)A + 4tf) + (A + 2f)^2) / (q (q-1))`.

Here `p = #Z` is the core size, `q = #Cand` the number of exterior candidates, `k` the
number of matching factors (`p - 1 ≤ k`: `k = p-1` for `p` even and `k = p` for `p` odd),
`a` the missing and `u` the phase-I-used exterior incidences, `A = ∑ a`, `2f = ∑ u`,
`a z ≤ D`, `u z ≤ 2t`, and `b e = #(bad e) ≤ d x + d y` the number of invalid candidate
hosts of the base `e = {x, y}`. -/
theorem exists_assign_rd09L2 {p D t A f : ℕ}
    (hp : Fintype.card Z = p) (hp2 : 2 ≤ p)
    (hsk : s ≤ k) (hkp : p - 1 ≤ k) (hk : 0 < k)
    (hq2 : 2 ≤ Fintype.card Cand) (hslots : k + (k - s) ≤ Fintype.card Cand)
    (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) (a u : Z → ℕ)
    (hb : ∀ e ∈ corePairs Z, (bad e).card ≤ (a e.1 + u e.1) + (a e.2 + u e.2))
    (hD : ∀ z, a z ≤ D) (hu : ∀ z, u z ≤ 2 * t)
    (hA : (∑ z, a z) = A) (hf : (∑ z, u z) = 2 * f) :
    ∃ α : Assign k s Cand,
      ((failedBases s α fac bad).card : ℚ)
        ≤ rd09L2Bound (Fintype.card Cand) p D t A f s := by
  classical
  simp only [rd09L2Bound]
  obtain ⟨α, hα⟩ := exists_assign_integral (Z := Z) hsk hslots fac bad
  refine ⟨α, ?_⟩
  -- the two moment bounds
  have hmom1 : (∑ e ∈ corePairs Z, (bad e).card) ≤ (p - 1) * (A + 2 * f) := by
    have := sum_b_le_accounts a u (fun e => (bad e).card) hb hA hf
    rwa [hp] at this
  have hmom2 : (∑ e ∈ corePairs Z, (bad e).card ^ 2)
      ≤ (p - 2) * ((D + 4 * t) * A + 4 * t * f) + (A + 2 * f) ^ 2 := by
    have := sum_b_sq_le_accounts a u (fun e => (bad e).card) hb hD hu hA hf
    rwa [hp] at this
  -- the integral certificate, with the moments substituted
  have hnat : k * (Fintype.card Cand * (Fintype.card Cand - 1))
      * (failedBases s α fac bad).card
      ≤ (Fintype.card Cand - 1) * s * ((p - 1) * (A + 2 * f))
        + k * ((p - 2) * ((D + 4 * t) * A + 4 * t * f) + (A + 2 * f) ^ 2) := by
    refine hα.trans (Nat.add_le_add ?_ ?_)
    · exact Nat.mul_le_mul_left _ hmom1
    · exact Nat.mul_le_mul_left _ hmom2
  -- pass to ℚ
  set Q : ℚ := (Fintype.card Cand : ℚ) with hQ
  set S : ℚ := (A : ℚ) + 2 * f with hS
  set M : ℚ := ((D : ℚ) + 4 * t) * A + 4 * t * f with hM
  set g : ℚ := ((failedBases s α fac bad).card : ℚ) with hg
  have hq1 : 1 ≤ Fintype.card Cand := by omega
  have hQ2 : (2 : ℚ) ≤ Q := by rw [hQ]; exact_mod_cast hq2
  have hQpos : (0 : ℚ) < Q := by linarith
  have hQ1pos : (0 : ℚ) < Q - 1 := by linarith
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hSnonneg : (0 : ℚ) ≤ S := by rw [hS]; positivity
  have hMnonneg : (0 : ℚ) ≤ M := by rw [hM]; positivity
  have hgnonneg : (0 : ℚ) ≤ g := by rw [hg]; positivity
  have hcast : (k : ℚ) * (Q * (Q - 1)) * g
      ≤ (Q - 1) * s * (((p : ℚ) - 1) * S) + k * (((p : ℚ) - 2) * M + S ^ 2) := by
    have := (Nat.cast_le (α := ℚ)).mpr hnat
    rw [hQ, hS, hM, hg]
    push_cast [Nat.cast_sub hq1, Nat.cast_sub (show 1 ≤ p by omega),
      Nat.cast_sub (show 2 ≤ p from hp2)] at this ⊢
    convert this using 2 <;> ring
  have hpk : ((p : ℚ) - 1) ≤ (k : ℚ) := by
    have : ((p - 1 : ℕ) : ℚ) ≤ (k : ℚ) := by exact_mod_cast hkp
    rwa [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one] at this
  have hstep : (Q - 1) * s * (((p : ℚ) - 1) * S) ≤ (Q - 1) * s * ((k : ℚ) * S) := by
    have h1 : ((p : ℚ) - 1) * S ≤ (k : ℚ) * S := by nlinarith
    have h2 : (0 : ℚ) ≤ (Q - 1) * s := by positivity
    exact mul_le_mul_of_nonneg_left h1 h2
  have hfinal : (k : ℚ) * (Q * (Q - 1)) * g
      ≤ (k : ℚ) * (Q * (Q - 1))
        * ((s : ℚ) / Q * S + (((p : ℚ) - 2) * M + S ^ 2) / (Q * (Q - 1))) := by
    have hrhs : (k : ℚ) * (Q * (Q - 1))
        * ((s : ℚ) / Q * S + (((p : ℚ) - 2) * M + S ^ 2) / (Q * (Q - 1)))
        = (Q - 1) * s * ((k : ℚ) * S) + k * (((p : ℚ) - 2) * M + S ^ 2) := by
      field_simp
    rw [hrhs]
    linarith
  have hcoef : (0 : ℚ) < (k : ℚ) * (Q * (Q - 1)) := by positivity
  exact le_of_mul_le_mul_left hfinal hcoef


/-! ## The physical phase-II adapter -/

section Physical

open PaperIV.Model PaperIV.ExteriorTriangleLift PaperIV.MultiHostTriangleLift
open PaperIV.RD09PhaseII

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **The literal geometric input of a factor–candidate phase II.**  The core is a clique
of `G` embedded by `core`, the exterior candidates are embedded by `cand` and are disjoint
from the core, a candidate that is *not* invalid for a base is adjacent to both of its
endpoints, and the factor map is a partition of the bases into matchings: two distinct
bases of the same factor share no core vertex. -/
structure IsFactorCandidateData (G : SimpleGraph V) [DecidableRel G.Adj] (core : Z ↪ V)
    (cand : Cand ↪ V) (fac : Z × Z → Fin k) (bad : Z × Z → Finset Cand) : Prop where
  /-- the core is a clique of `G` -/
  coreClique : ∀ x y : Z, x ≠ y → G.Adj (core x) (core y)
  /-- candidates are exterior to the core -/
  candNotCore : ∀ (c : Cand) (x : Z), cand c ≠ core x
  /-- a valid candidate host of a base is adjacent to both of its endpoints -/
  validHost : ∀ e ∈ corePairs Z, ∀ c : Cand, c ∉ bad e →
    G.Adj (cand c) (core e.1) ∧ G.Adj (cand c) (core e.2)
  /-- every factor is a matching: distinct bases of one factor share no core vertex -/
  facMatching : ∀ e ∈ corePairs Z, ∀ e' ∈ corePairs Z, e ≠ e' → fac e = fac e' →
    ∀ x : Z, (x = e.1 ∨ x = e.2) → (x = e'.1 ∨ x = e'.2) → False

/-- The surviving bases of an assignment: the core bases that do not fail and are not
already used by phase I. -/
def survivingBases (s : ℕ) (α : Assign k s Cand) (fac : Z × Z → Fin k)
    (bad : Z × Z → Finset Cand) (used : Finset (Z × Z)) : Finset (Z × Z) :=
  (corePairs Z).filter fun e => ¬ Fails s α (bad e) (fac e) ∧ e ∉ used

theorem mem_survivingBases {s : ℕ} {α : Assign k s Cand} {fac : Z × Z → Fin k}
    {bad : Z × Z → Finset Cand} {used : Finset (Z × Z)} {e : Z × Z} :
    e ∈ survivingBases s α fac bad used ↔
      e ∈ corePairs Z ∧ ¬ Fails s α (bad e) (fac e) ∧ e ∉ used := by
  simp [survivingBases, and_assoc]

/-- The index type of the phase-II family: the surviving bases. -/
abbrev SurvivingBase (s : ℕ) (α : Assign k s Cand) (fac : Z × Z → Fin k)
    (bad : Z × Z → Finset Cand) (used : Finset (Z × Z)) : Type _ :=
  {e : Z × Z // e ∈ survivingBases s α fac bad used}

/-- The singleton hub of a surviving base: its chosen valid candidate host. -/
def survivingHub (s : ℕ) (α : Assign k s Cand) (fac : Z × Z → Fin k)
    (bad : Z × Z → Finset Cand) (used : Finset (Z × Z)) (cand : Cand ↪ V) :
    SurvivingBase s α fac bad used → Finset V :=
  fun j => {cand (hostUsed s α (bad j.1) (fac j.1))}

/-- The literal base edge of a surviving base. -/
def survivingBaseEdge (s : ℕ) (α : Assign k s Cand) (fac : Z × Z → Fin k)
    (bad : Z × Z → Finset Cand) (used : Finset (Z × Z)) (core : Z ↪ V) :
    SurvivingBase s α fac bad used → Sym2 V :=
  fun j => s(core j.1.1, core j.1.2)

variable {s : ℕ} {α : Assign k s Cand} {fac : Z × Z → Fin k} {bad : Z × Z → Finset Cand}
  {used : Finset (Z × Z)} {core : Z ↪ V} {cand : Cand ↪ V}

@[simp] theorem survivingHub_apply (j : SurvivingBase s α fac bad used) :
    survivingHub s α fac bad used cand j = {cand (hostUsed s α (bad j.1) (fac j.1))} := rfl

@[simp] theorem survivingBaseEdge_apply (j : SurvivingBase s α fac bad used) :
    survivingBaseEdge s α fac bad used core j = s(core j.1.1, core j.1.2) := rfl

/-- The chosen host of a surviving base is a valid host. -/
theorem hostUsed_surviving_notMem (j : SurvivingBase s α fac bad used) :
    hostUsed s α (bad j.1) (fac j.1) ∉ bad j.1 :=
  hostUsed_notMem (mem_survivingBases.mp j.2).2.1

theorem mem_survivingPiece {j : SurvivingBase s α fac bad used} {x : V} :
    x ∈ piece (survivingHub s α fac bad used cand) (survivingBaseEdge s α fac bad used core) j
      ↔ x = cand (hostUsed s α (bad j.1) (fac j.1)) ∨ x = core j.1.1 ∨ x = core j.1.2 := by
  simp [RD09PhaseII.mem_piece, or_assoc]

/-- Two bases of the core clique sharing two distinct core vertices are equal. -/
theorem eq_of_two_common {e e' : Z × Z} (he : e ∈ corePairs Z) (he' : e' ∈ corePairs Z)
    {v w : Z} (hvw : v ≠ w)
    (hv : v = e.1 ∨ v = e.2) (hw : w = e.1 ∨ w = e.2)
    (hv' : v = e'.1 ∨ v = e'.2) (hw' : w = e'.1 ∨ w = e'.2) : e = e' := by
  obtain ⟨x, y⟩ := e
  obtain ⟨x', y'⟩ := e'
  rw [mem_corePairs] at he he'
  simp only at he he' hv hw hv' hw' ⊢
  have key : ∀ {c d : Z}, (v = c ∨ v = d) → (w = c ∨ w = d) →
      (v = c ∧ w = d) ∨ (v = d ∧ w = c) := by
    intro c d hvc hwc
    rcases hvc with rfl | rfl <;> rcases hwc with rfl | rfl
    · exact absurd rfl hvw
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hvw
  rcases key hv hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases key hv' hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]
  · exact absurd he (asymm (by rw [← h1, ← h2] at he'; exact he'))
  · exact absurd he (asymm (by rw [← h1, ← h2] at he'; exact he'))
  · rw [← h1, ← h2]

/-- **The dichotomy for a shared vertex of two phase-II pieces**: a vertex shared by the
pieces of two surviving bases is either their common candidate host, or a core vertex
shared by the two bases. -/
theorem shared_vertex_dichotomy (hdata : IsFactorCandidateData G core cand fac bad)
    {j l : SurvivingBase s α fac bad used} {x : V}
    (hx1 : x ∈ piece (survivingHub s α fac bad used cand)
      (survivingBaseEdge s α fac bad used core) j)
    (hx2 : x ∈ piece (survivingHub s α fac bad used cand)
      (survivingBaseEdge s α fac bad used core) l) :
    (x = cand (hostUsed s α (bad j.1) (fac j.1))
        ∧ hostUsed s α (bad j.1) (fac j.1) = hostUsed s α (bad l.1) (fac l.1))
      ∨ ∃ y : Z, x = core y ∧ (y = j.1.1 ∨ y = j.1.2) ∧ (y = l.1.1 ∨ y = l.1.2) := by
  rw [mem_survivingPiece] at hx1 hx2
  rcases hx1 with rfl | hx1
  · rcases hx2 with hx2 | hx2
    · exact Or.inl ⟨rfl, cand.injective hx2⟩
    · exfalso
      rcases hx2 with hx2 | hx2
      · exact hdata.candNotCore _ _ hx2
      · exact hdata.candNotCore _ _ hx2
  · rcases hx1 with rfl | rfl
    · rcases hx2 with hx2 | hx2
      · exact absurd hx2.symm (hdata.candNotCore _ _)
      · rcases hx2 with hx2 | hx2
        · exact Or.inr ⟨j.1.1, rfl, Or.inl rfl, Or.inl (core.injective hx2)⟩
        · exact Or.inr ⟨j.1.1, rfl, Or.inl rfl, Or.inr (core.injective hx2)⟩
    · rcases hx2 with hx2 | hx2
      · exact absurd hx2.symm (hdata.candNotCore _ _)
      · rcases hx2 with hx2 | hx2
        · exact Or.inr ⟨j.1.2, rfl, Or.inr rfl, Or.inl (core.injective hx2)⟩
        · exact Or.inr ⟨j.1.2, rfl, Or.inr rfl, Or.inr (core.injective hx2)⟩

/-- **The surviving bases form a literal phase-II family.**  Every piece is a `K3`
consisting of one valid exterior host and one core base edge. -/
theorem isPhaseTwoFamily_surviving (hdata : IsFactorCandidateData G core cand fac bad) :
    IsPhaseTwoFamily G (survivingHub s α fac bad used cand)
      (survivingBaseEdge s α fac bad used core) := by
  classical
  have hne : ∀ j : SurvivingBase s α fac bad used, j.1.1 ≠ j.1.2 := fun j =>
    ne_of_lt (mem_corePairs.mp (mem_survivingBases.mp j.2).1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [survivingBaseEdge_apply, mem_graphEdges, SimpleGraph.mem_edgeSet]
    exact hdata.coreClique _ _ (hne j)
  · intro j
    exact Or.inl (by simp)
  · intro j
    simp
  · intro j a ha w hw
    have hvalid := hdata.validHost j.1 (mem_survivingBases.mp j.2).1
      (hostUsed s α (bad j.1) (fac j.1)) (hostUsed_surviving_notMem j)
    simp only [survivingHub_apply, Finset.mem_singleton] at hw
    subst hw
    rw [survivingBaseEdge_apply, Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact hvalid.1
    · exact hvalid.2
  · intro j l a ha hmem
    rw [survivingBaseEdge_apply, Sym2.mem_iff] at ha
    simp only [survivingHub_apply, Finset.mem_singleton] at hmem
    rcases ha with rfl | rfl <;> exact hdata.candNotCore _ _ hmem.symm
  · intro j l hjl
    rw [Finset.card_le_one]
    intro v hv w hw
    rw [Finset.mem_inter] at hv hw
    by_contra hvw
    have hej : j.1 ∈ corePairs Z := (mem_survivingBases.mp j.2).1
    have hel : l.1 ∈ corePairs Z := (mem_survivingBases.mp l.2).1
    have hjl' : j.1 ≠ l.1 := fun h => hjl (Subtype.ext h)
    have hsamefactor : hostUsed s α (bad j.1) (fac j.1) = hostUsed s α (bad l.1) (fac l.1) →
        fac j.1 = fac l.1 := by
      intro hhost
      by_contra hf
      exact hostUsed_ne (bad := bad j.1) (bad' := bad l.1) hf hhost
    rcases shared_vertex_dichotomy hdata hv.1 hv.2 with ⟨rfl, hhost⟩ | ⟨y, rfl, hy1, hy2⟩
    · rcases shared_vertex_dichotomy hdata hw.1 hw.2 with ⟨hw1, -⟩ | ⟨y', -, hy1', hy2'⟩
      · exact hvw hw1.symm
      · exact hdata.facMatching j.1 hej l.1 hel hjl' (hsamefactor hhost) y' hy1' hy2'
    · rcases shared_vertex_dichotomy hdata hw.1 hw.2 with ⟨-, hhost⟩ | ⟨y', rfl, hy1', hy2'⟩
      · exact hdata.facMatching j.1 hej l.1 hel hjl' (hsamefactor hhost) y hy1 hy2
      · exact hjl' (eq_of_two_common hej hel (fun h => hvw (by rw [h])) hy1 hy1' hy2 hy2')

/-! ### Compatibility with the supplied phase-I multi-host exterior hub -/

variable {I : Type*} [Fintype I] [DecidableEq I] {z : I → V} {E : I → Finset (Sym2 V)}

/-- **The literal separation data between phase I and the factor–candidate phase II.**
The phase-I hosts avoid both the core and the candidates, no phase-I base edge contains a
candidate, and any base of the core clique whose *two* endpoints lie on a phase-I base
edge is one of the bases already removed (`used`).  In the round-robin split model these
are exactly the facts recorded in `PaperIV.RD09SplitPhaseII`. -/
structure IsPhaseISeparated (z : I → V) (E : I → Finset (Sym2 V)) (core : Z ↪ V)
    (cand : Cand ↪ V) (used : Finset (Z × Z)) : Prop where
  /-- phase-I hosts are not core vertices -/
  hostNotCore : ∀ i (x : Z), z i ≠ core x
  /-- phase-I hosts are not candidates -/
  hostNotCand : ∀ i (c : Cand), z i ≠ cand c
  /-- phase-I base edges contain no candidate -/
  baseNotCand : ∀ i, ∀ e' ∈ E i, ∀ c : Cand, cand c ∉ e'
  /-- a core base carried by a phase-I base edge has already been removed -/
  baseUsed : ∀ i, ∀ e' ∈ E i, ∀ e ∈ corePairs Z, core e.1 ∈ e' → core e.2 ∈ e' → e ∈ used

/-- **The canonical removed family.**  The core bases that are already carried by a
phase-I base edge; these are exactly the bases phase II must not reuse. -/
def usedBases (core : Z ↪ V) (E : I → Finset (Sym2 V)) : Finset (Z × Z) :=
  (corePairs Z).filter fun e => ∃ i, ∃ e' ∈ E i, core e.1 ∈ e' ∧ core e.2 ∈ e'

/-- With the canonical removed family the last separation requirement is automatic: only
the three literal geometric separations have to be supplied. -/
theorem isPhaseISeparated_usedBases
    (hostNotCore : ∀ i (x : Z), z i ≠ core x)
    (hostNotCand : ∀ i (c : Cand), z i ≠ cand c)
    (baseNotCand : ∀ i, ∀ e' ∈ E i, ∀ c : Cand, cand c ∉ e') :
    IsPhaseISeparated z E core cand (usedBases core E) where
  hostNotCore := hostNotCore
  hostNotCand := hostNotCand
  baseNotCand := baseNotCand
  baseUsed := by
    intro i e' he' e he h1 h2
    exact Finset.mem_filter.mpr ⟨he, ⟨i, e', he', h1, h2⟩⟩

/-- **Cross-phase compatibility.**  The surviving factor–candidate phase-II family is
literally `IsPhaseCompatible` with the supplied phase-I data.  Only the weak (literal)
interface is used: no root-host separation is assumed. -/
theorem isPhaseCompatible_surviving (hsep : IsPhaseISeparated z E core cand used) :
    IsPhaseCompatible z E (survivingHub s α fac bad used cand)
      (survivingBaseEdge s α fac bad used core) := by
  classical
  constructor
  · intro i j hmem
    rcases mem_survivingPiece.mp hmem with h | h | h
    · exact hsep.hostNotCand i _ h
    · exact hsep.hostNotCore i _ h
    · exact hsep.hostNotCore i _ h
  · intro i j e' he'
    rw [Finset.card_le_one]
    intro v hv w hw
    rw [Finset.mem_inter, Sym2.mem_toFinset] at hv hw
    by_contra hvw
    have hcore : ∀ x : V, x ∈ e' →
        x ∈ piece (survivingHub s α fac bad used cand)
          (survivingBaseEdge s α fac bad used core) j →
        x = core j.1.1 ∨ x = core j.1.2 := by
      intro x hx1 hx2
      rcases mem_survivingPiece.mp hx2 with h | h
      · exact absurd (h ▸ hx1) (hsep.baseNotCand i e' he' _)
      · exact h
    have hused : j.1 ∈ used := by
      rcases hcore v hv.1 hv.2 with rfl | rfl <;> rcases hcore w hw.1 hw.2 with h | h
      · exact absurd h.symm hvw
      · exact hsep.baseUsed i e' he' j.1 (mem_survivingBases.mp j.2).1 hv.1 (h ▸ hw.1)
      · exact hsep.baseUsed i e' he' j.1 (mem_survivingBases.mp j.2).1 (h ▸ hw.1) hv.1
      · exact absurd h.symm hvw
    exact (mem_survivingBases.mp j.2).2.2 hused

/-! ### The assembled physical packing -/

/-- **The union with phase I is a literal physical packing.** -/
theorem isPacking_union_surviving (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used) :
    IsPacking G (multiLiftedPacking z E
      ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
          (survivingBaseEdge s α fac bad used core)) :=
  isPacking_union_phases h1 (isPhaseTwoFamily_surviving hdata)
    (isPhaseCompatible_surviving hsep)

/-- **The union with phase I is a literal `K3`/`K4` packing**: in fact all of its pieces
are triangles. -/
theorem isK34Packing_union_surviving (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used) :
    PaperIV.PhysicalCompletion.IsK34Packing G (multiLiftedPacking z E
      ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
          (survivingBaseEdge s α fac bad used core)) := by
  classical
  refine { isPacking_union_surviving h1 hdata hsep with big := ?_ }
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Or.inl
      (PaperIV.RD09TerminalAssembly.card_eq_three_of_mem_multiLiftedPacking h1 ht)
  · obtain ⟨j, rfl⟩ := mem_phaseTwoPacking.mp ht
    exact Or.inl ((isPhaseTwoFamily_surviving hdata).card_piece_eq_three (by simp))

/-- The piece count of the assembled two-phase family: the phase-I base edges plus one
triangle per surviving base. -/
theorem card_union_surviving (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used) :
    (multiLiftedPacking z E
        ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
            (survivingBaseEdge s α fac bad used core)).card
      = (∑ i, (E i).card) + (survivingBases s α fac bad used).card := by
  classical
  rw [card_union_phases h1 (isPhaseTwoFamily_surviving hdata)
    (isPhaseCompatible_surviving hsep)]
  congr 1
  simp [SurvivingBase, Fintype.card_coe]

/-! ### The RD09 ledger interface -/

/-- **The scalar specialization of RD09-L2.**  If each of the two RD09-L2 terms fits in
half of the `L10` budget, RD09-L2 gives the recovered bound of
`PaperIV.RD09PhysicalLedger.recovered_upper_of_L10`. -/
theorem recovered_le_of_rd09L2 {A f g : ℕ} {T₁ T₂ : ℚ} (hL2 : (g : ℚ) ≤ T₁ + T₂)
    (h₁ : T₁ ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50)
    (h₂ : T₂ ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50) :
    (g : ℚ) ≤ (7 : ℚ) / 40 * A + (f : ℚ) / 25 := by linarith

/-- **The integral `L10` of `PaperIV.RD09PhysicalLedger`** from the rational recovered
bound. -/
theorem L10_of_recovered_le {A f g : ℕ} (h : (g : ℚ) ≤ (7 : ℚ) / 40 * A + (f : ℚ) / 25) :
    200 * g ≤ 35 * A + 8 * f := by
  have hq : (200 * g : ℚ) ≤ 35 * A + 8 * f := by
    have : ((200 * g : ℕ) : ℚ) = 200 * (g : ℚ) := by push_cast; ring
    linarith
  exact_mod_cast hq

/-- **RD09-L2 discharges the `g`/recovered side of the ledger**, integrally: under the two
scalar budgets the failed-base count satisfies `200 g ≤ 35 A + 8 f`. -/
theorem L10_of_rd09L2 {A f g : ℕ} {T₁ T₂ : ℚ} (hL2 : (g : ℚ) ≤ T₁ + T₂)
    (h₁ : T₁ ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50)
    (h₂ : T₂ ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50) :
    200 * g ≤ 35 * A + 8 * f :=
  L10_of_recovered_le (recovered_le_of_rd09L2 hL2 h₁ h₂)

/-- **The paid RD09 bound for the assembled two-phase configuration.**  This is the
`IsPhaseCompatible`-only analogue of
`PaperIV.RD09PhysicalLedger.twoPhase_count_le_splitBaseline_sub`: the false
`IsRootHostSeparated` hypothesis of the split model is *not* used. -/
theorem count_le_splitBaseline_sub_surviving (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used)
    {B m A f g : ℕ} {n p : ℚ}
    (hbase : (B : ℚ) = PaperIV.splitBaseline n p)
    (hcount : ((∑ i, (E i).card) + (survivingBases s α fac bad used).card)
        + (PaperIV.PhysicalCompletion.uncoveredEdges G (multiLiftedPacking z E
            ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                (survivingBaseEdge s α fac bad used core))).card
        + A + 2 * f = B + m + 2 * g)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A)
    (L10 : 200 * g ≤ 35 * A + 8 * f) :
    ((PaperIV.PhysicalCompletion.completion G (multiLiftedPacking z E
        ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
            (survivingBaseEdge s α fac bad used core))).card : ℚ)
      ≤ PaperIV.splitBaseline n p - (m : ℚ) / 20 - (A : ℚ) / 2 := by
  refine PaperIV.RD09PhysicalLedger.count_le_splitBaseline_sub hbase ?_ L9 L10
  refine PaperIV.RD09PhysicalLedger.L3_of_pieces_uncovered
    (isK34Packing_union_surviving h1 hdata hsep) ?_
  rwa [card_union_surviving h1 hdata hsep]

/-! ## The final public theorem -/

/-- **RD09-L2 with its physical phase-II adapter.**

Averaging over the choice of the `s` one-slot factors and over the injections of the
`2k - s` slots into distinct exterior candidates produces one literal assignment `α` such
that, writing `g` for the cardinality of its failed-base family:

1. `g ≤ (s/q)(A + 2f) + ((p-2)((D + 4t)A + 4tf) + (A + 2f)^2) / (q(q-1))` — RD09-L2;
2. the surviving bases (nonfailed and not already used by phase I), each equipped with one
   *valid* candidate host as a singleton hub, form a literal
   `PaperIV.RD09PhaseII.IsPhaseTwoFamily`;
3. that family is `PaperIV.RD09PhaseII.IsPhaseCompatible` with the supplied phase-I
   `IsMultiExteriorHub` data — the weak literal interface, never
   `IsRootHostSeparated`, which `PaperIV.RD09SplitPhaseII.not_isRootHostSeparated_of_other_host`
   shows to be false in the split model;
4. hence the union of the two phases is a literal physical packing, indeed a `K3`/`K4`
   packing, with the exact piece count `∑ i, #(E i) + #surviving`.

Consequently `isPacking_union_phases`, `card_union_phases` and the RD09 ledger may all
consume the *same* phase-I/phase-II witnesses. -/
theorem exists_rd09L2_phaseTwo_packing {p D t A f : ℕ}
    (hp : Fintype.card Z = p) (hp2 : 2 ≤ p)
    (hsk : s ≤ k) (hkp : p - 1 ≤ k) (hk : 0 < k)
    (hq2 : 2 ≤ Fintype.card Cand) (hslots : k + (k - s) ≤ Fintype.card Cand)
    (a u : Z → ℕ)
    (hb : ∀ e ∈ corePairs Z, (bad e).card ≤ (a e.1 + u e.1) + (a e.2 + u e.2))
    (hD : ∀ x, a x ≤ D) (hu : ∀ x, u x ≤ 2 * t)
    (hA : (∑ x, a x) = A) (hf : (∑ x, u x) = 2 * f)
    (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used) :
    ∃ α : Assign k s Cand,
      ((failedBases s α fac bad).card : ℚ) ≤ rd09L2Bound (Fintype.card Cand) p D t A f s
        ∧ IsPhaseTwoFamily G (survivingHub s α fac bad used cand)
            (survivingBaseEdge s α fac bad used core)
        ∧ IsPhaseCompatible z E (survivingHub s α fac bad used cand)
            (survivingBaseEdge s α fac bad used core)
        ∧ IsPacking G (multiLiftedPacking z E
            ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                (survivingBaseEdge s α fac bad used core))
        ∧ PaperIV.PhysicalCompletion.IsK34Packing G (multiLiftedPacking z E
            ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                (survivingBaseEdge s α fac bad used core))
        ∧ (multiLiftedPacking z E
            ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                (survivingBaseEdge s α fac bad used core)).card
              = (∑ i, (E i).card) + (survivingBases s α fac bad used).card := by
  obtain ⟨α, hα⟩ :=
    exists_assign_rd09L2 (Cand := Cand) (k := k) (s := s) (Z := Z) hp hp2 hsk hkp hk hq2
      hslots fac bad a u hb hD hu hA hf
  exact ⟨α, hα, isPhaseTwoFamily_surviving hdata, isPhaseCompatible_surviving hsep,
    isPacking_union_surviving h1 hdata hsep, isK34Packing_union_surviving h1 hdata hsep,
    card_union_surviving h1 hdata hsep⟩

/-- **The same, carried all the way to the paid RD09 ledger bound.**  Under the two
scalar budgets of the `L10` specialization, the RD09-L2 assignment discharges the
recovered side of `PaperIV.RD09PhysicalLedger`, and the completed two-phase packing obeys
`|completion| ≤ splitBaseline n p - m/20 - A/2`. -/
theorem exists_rd09L2_paid_ledger {p D t A f m B : ℕ} {n pp : ℚ}
    (hp : Fintype.card Z = p) (hp2 : 2 ≤ p)
    (hsk : s ≤ k) (hkp : p - 1 ≤ k) (hk : 0 < k)
    (hq2 : 2 ≤ Fintype.card Cand) (hslots : k + (k - s) ≤ Fintype.card Cand)
    (a u : Z → ℕ)
    (hb : ∀ e ∈ corePairs Z, (bad e).card ≤ (a e.1 + u e.1) + (a e.2 + u e.2))
    (hD : ∀ x, a x ≤ D) (hu : ∀ x, u x ≤ 2 * t)
    (hA : (∑ x, a x) = A) (hf : (∑ x, u x) = 2 * f)
    (h1 : IsMultiExteriorHub G z E)
    (hdata : IsFactorCandidateData G core cand fac bad)
    (hsep : IsPhaseISeparated z E core cand used)
    (hbudget₁ : (s : ℚ) / (Fintype.card Cand : ℚ) * ((A : ℚ) + 2 * f)
      ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50)
    (hbudget₂ : (((p : ℚ) - 2) * (((D : ℚ) + 4 * t) * (A : ℚ) + 4 * t * f)
        + ((A : ℚ) + 2 * f) ^ 2) / ((Fintype.card Cand : ℚ) * ((Fintype.card Cand : ℚ) - 1))
      ≤ (7 : ℚ) / 80 * A + (f : ℚ) / 50)
    (hbase : (B : ℚ) = PaperIV.splitBaseline n pp)
    (L9 : 1600 * m ≤ 2920 * f + 219 * A) :
    ∃ α : Assign k s Cand,
      200 * (failedBases s α fac bad).card ≤ 35 * A + 8 * f
        ∧ (((∑ i, (E i).card) + (survivingBases s α fac bad used).card)
              + (PaperIV.PhysicalCompletion.uncoveredEdges G (multiLiftedPacking z E
                  ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                      (survivingBaseEdge s α fac bad used core))).card
              + A + 2 * f = B + m + 2 * (failedBases s α fac bad).card →
            ((PaperIV.PhysicalCompletion.completion G (multiLiftedPacking z E
                ∪ phaseTwoPacking (survivingHub s α fac bad used cand)
                    (survivingBaseEdge s α fac bad used core))).card : ℚ)
              ≤ PaperIV.splitBaseline n pp - (m : ℚ) / 20 - (A : ℚ) / 2) := by
  obtain ⟨α, hα, -, -, -, -, -⟩ :=
    exists_rd09L2_phaseTwo_packing (Cand := Cand) (k := k) (s := s) (Z := Z) hp hp2 hsk hkp hk
      hq2 hslots a u hb hD hu hA hf h1 hdata hsep
  have hL10 : 200 * (failedBases s α fac bad).card ≤ 35 * A + 8 * f := by
    refine L10_of_rd09L2 (T₁ := (s : ℚ) / (Fintype.card Cand : ℚ) * ((A : ℚ) + 2 * f))
      (T₂ := (((p : ℚ) - 2) * (((D : ℚ) + 4 * t) * (A : ℚ) + 4 * t * f) + ((A : ℚ) + 2 * f) ^ 2)
        / ((Fintype.card Cand : ℚ) * ((Fintype.card Cand : ℚ) - 1)))
      ?_ hbudget₁ hbudget₂
    simpa [rd09L2Bound] using hα
  refine ⟨α, hL10, fun hcount => ?_⟩
  exact count_le_splitBaseline_sub_surviving h1 hdata hsep hbase hcount L9 hL10

end Physical

end PaperIV.RD09FactorCandidateAverage


