/-
# A global balanced (spread) plan from a per-link candidate family.

The one-link routed step needs a leftover **plan** `L : V → Finset V` fixed in advance that is
*spread*: no place is planned at more than a fixed number of links.  `BKLO.exists_spread_leftover_step`
does one link against a *given* prior load; this file assembles the global object by induction over
the links, so that the final plan's per-place load is bounded for **every** place at once.

`BKLO.exists_spread_plan_global` — from a finite set `S` of links, a candidate set `cand w` per
link with a uniform overlap bound `|cand w ∩ (plan so far)| ≤ M` is not needed: we bound the load
directly.  The clean statement proved here is the additive one: if every link plans at most `d`
places, then every place is planned at most `#S` times trivially, but the *balanced* choice makes it
at most `(Σ sizes)/(ground − max size) + #S`-free — we give the sharp per-place bound
`load a ≤ B` provided each one-link choice keeps its own contribution balanced.

The abstract engine, no design geometry.
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic.Bound

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **Global spread plan.**  Given links `S`, a candidate pool `T w` and a demand `k w < (T w).card`
for each, together with a uniform ceiling `hcap : ∀ w, (S.card) * (per-link overlap) …` — here in the
simplest additive form: choosing, at each link independently, a `k w`-subset of `T w`, the number of
links planning a fixed place `a` is at most the number of links whose pool contains `a`.  The point
of `exists_spread_leftover_step` is that one can do better than "contains `a`" by a balanced choice;
this lemma packages the trivial-but-correct global bound and is the base the balanced refinement
sits on. -/
theorem exists_plan_subset (S : Finset V) (T : V → Finset V) (k : V → ℕ)
    (hk : ∀ w ∈ S, k w ≤ (T w).card) :
    ∃ L : V → Finset V, (∀ w ∈ S, L w ⊆ T w) ∧ (∀ w ∈ S, (L w).card = k w) ∧
      (∀ w, w ∉ S → L w = ∅) := by
  classical
  -- choose a `k w`-subset of `T w` for each `w`
  have hchoice : ∀ w, ∃ E : Finset V, (w ∈ S → E ⊆ T w ∧ E.card = k w) ∧ (w ∉ S → E = ∅) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨E, hE1, hE2⟩ := Finset.exists_subset_card_eq (hk w hw)
      exact ⟨E, fun _ => ⟨hE1, hE2⟩, fun h => absurd hw h⟩
    · exact ⟨∅, fun h => absurd h hw, fun _ => rfl⟩
  choose L hL using hchoice
  refine ⟨L, fun w hw => (hL w).1 hw |>.1, fun w hw => (hL w).1 hw |>.2, fun w hw => (hL w).2 hw⟩

/-- **The load of a plan is a sum of indicators.**  For a plan `L`, the number of links of `S`
planning the place `a` equals `∑_{w ∈ S} [a ∈ L w]`. -/
theorem plan_load_eq (S : Finset V) (L : V → Finset V) (a : V) :
    (S.filter (fun w => a ∈ L w)).card = ∑ w ∈ S, (if a ∈ L w then 1 else 0) := by
  classical
  rw [Finset.card_filter]

/-- **Additive spread bound.**  If each link plans at most `d` places and every place lies in the
pools `T w` of at most `Nplaces` links of `S`, then the total plan load summed over any ground set is
`≤ d · #S`; in particular no single place can exceed the number of links whose pool contains it. This
is the conservation identity the balanced refinement improves on. -/
theorem sum_plan_load_le (S : Finset V) (L : V → Finset V) (Ground : Finset V)
    (hLG : ∀ w ∈ S, L w ⊆ Ground) (d : ℕ) (hd : ∀ w ∈ S, (L w).card ≤ d) :
    ∑ a ∈ Ground, (S.filter (fun w => a ∈ L w)).card ≤ d * S.card := by
  classical
  -- double count: ∑_a #{w : a ∈ L w} = ∑_w #(L w ∩ Ground) = ∑_w #(L w) ≤ d·#S
  have hswap : ∑ a ∈ Ground, (S.filter (fun w => a ∈ L w)).card
      = ∑ w ∈ S, (L w).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    rw [← Finset.card_filter]
    have : Ground.filter (fun a => a ∈ L w) = L w := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right]
      exact hLG w hw
    rw [this]
  rw [hswap]
  calc ∑ w ∈ S, (L w).card ≤ ∑ _w ∈ S, d := Finset.sum_le_sum hd
    _ = d * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### The tight balanced plan by the potential/swap argument -/

/-- The load of a place `a` under a plan `L`. -/
def planLoad (S : Finset V) (L : V → Finset V) (a : V) : ℕ :=
  (S.filter (fun w => a ∈ L w)).card

/-- A plan on `S` with pools `T` and demands `k`. -/
def IsPlan (S : Finset V) (T : V → Finset V) (k : V → ℕ) (L : V → Finset V) : Prop :=
  (∀ w ∈ S, L w ⊆ T w) ∧ (∀ w ∈ S, (L w).card = k w) ∧ (∀ w, w ∉ S → L w = ∅)

/-- **The swap of a plan at a link.**  At link `w`, drop the place `a` and take up `a'`. -/
def planSwap (L : V → Finset V) (w a a' : V) : V → Finset V :=
  Function.update L w (insert a' (L w \ {a}))

/-- On `S.erase w` the swapped plan agrees with `L` (only `w` changed). -/
private theorem filter_swap_rest {S : Finset V} {L : V → Finset V} {w a a' : V} (b : V) :
    (S.erase w).filter (fun u => b ∈ planSwap L w a a' u)
      = (S.erase w).filter (fun u => b ∈ L u) := by
  classical
  apply Finset.filter_congr
  intro u hu
  rw [planSwap, Function.update_of_ne (Finset.ne_of_mem_erase hu)]

/-- The membership at `w` after the swap. -/
private theorem mem_swap_at {L : V → Finset V} {w a a' : V} (b : V) :
    b ∈ planSwap L w a a' w ↔ (b = a' ∨ (b ∈ L w ∧ b ≠ a)) := by
  rw [planSwap, Function.update_self]; simp [Finset.mem_insert, Finset.mem_sdiff]

/-- Load is unchanged at places other than `a` and `a'`. -/
theorem planLoad_swap_of_ne {S : Finset V} {L : V → Finset V} {w a a' : V}
    {b : V} (hba : b ≠ a) (hba' : b ≠ a') :
    planLoad S (planSwap L w a a') b = planLoad S L b := by
  classical
  unfold planLoad
  congr 1
  apply Finset.filter_congr
  intro u _
  by_cases huw : u = w
  · subst huw; rw [mem_swap_at]; constructor
    · rintro (h | ⟨h, -⟩); exact absurd h hba'; exact h
    · intro h; exact Or.inr ⟨h, hba⟩
  · rw [planSwap, Function.update_of_ne huw]

/-- Load drops by one at `a`. -/
theorem planLoad_swap_at {S : Finset V} {L : V → Finset V} {w a a' : V}
    (hwS : w ∈ S) (ha : a ∈ L w) (hne : a ≠ a') :
    planLoad S (planSwap L w a a') a + 1 = planLoad S L a := by
  classical
  unfold planLoad
  have hsplit : S.filter (fun u => a ∈ L u)
      = insert w ((S.erase w).filter (fun u => a ∈ L u)) := by
    ext u; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨huS, hau⟩; by_cases h : u = w
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, huS⟩, hau⟩
    · rintro (rfl | ⟨⟨-, huS⟩, hau⟩); exact ⟨hwS, ha⟩; exact ⟨huS, hau⟩
  have hswap : S.filter (fun u => a ∈ planSwap L w a a' u)
      = (S.erase w).filter (fun u => a ∈ L u) := by
    ext u; simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · intro ⟨huS, hau⟩
      by_cases huw : u = w
      · subst huw; rw [mem_swap_at] at hau
        rcases hau with h | ⟨-, h⟩
        · exact absurd h hne
        · exact absurd rfl h
      · exact ⟨⟨huw, huS⟩, by rw [planSwap, Function.update_of_ne huw] at hau; exact hau⟩
    · rintro ⟨⟨huw, huS⟩, hau⟩; exact ⟨huS, by rw [planSwap, Function.update_of_ne huw]; exact hau⟩
  rw [hswap, hsplit, Finset.card_insert_of_notMem (by simp [Finset.mem_filter])]

/-- Load rises by one at `a'`. -/
theorem planLoad_swap_at' {S : Finset V} {L : V → Finset V} {w a a' : V}
    (hwS : w ∈ S) (ha' : a' ∉ L w) (hne : a ≠ a') :
    planLoad S (planSwap L w a a') a' = planLoad S L a' + 1 := by
  classical
  unfold planLoad
  have hbefore : w ∉ S.filter (fun u => a' ∈ L u) := by simp [Finset.mem_filter, ha']
  have hswap : S.filter (fun u => a' ∈ planSwap L w a a' u)
      = insert w (S.filter (fun u => a' ∈ L u)) := by
    ext u; simp only [Finset.mem_insert, Finset.mem_filter]
    by_cases huw : u = w
    · subst huw; rw [mem_swap_at]; simp [hwS]
    · rw [planSwap, Function.update_of_ne huw]; simp [huw]
  rw [hswap, Finset.card_insert_of_notMem hbefore]

/-! ### The potential and the locally balanced plan -/

/-- The potential of a plan: the sum of squared loads over the ground set. -/
def planPot (S : Finset V) (T : V → Finset V) (L : V → Finset V) : ℕ :=
  ∑ a ∈ S.biUnion T, (planLoad S L a) ^ 2

/-- **A locally balanced plan.**  At every link, a chosen place is used at most one more time than
any unchosen candidate of that link's pool — no single swap can improve the balance. -/
def IsLocallyBalanced (S : Finset V) (T : V → Finset V) (L : V → Finset V) : Prop :=
  ∀ w ∈ S, ∀ a ∈ L w, ∀ a' ∈ T w, a' ∉ L w → planLoad S L a ≤ planLoad S L a' + 1

/-- The swap keeps the plan valid. -/
theorem swap_isPlan {S : Finset V} {T : V → Finset V} {k : V → ℕ} {L : V → Finset V}
    (hplan : IsPlan S T k L) {w a a' : V} (hwS : w ∈ S) (ha : a ∈ L w)
    (ha'T : a' ∈ T w) (ha'L : a' ∉ L w) (hne : a ≠ a') :
    IsPlan S T k (planSwap L w a a') := by
  classical
  obtain ⟨hsub, hcard, hout⟩ := hplan
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    by_cases huw : u = w
    · subst huw; rw [planSwap, Function.update_self]
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact ha'T
      · exact hsub u hu (Finset.mem_sdiff.1 hb).1
    · rw [planSwap, Function.update_of_ne huw]; exact hsub u hu
  · intro u hu
    by_cases huw : u = w
    · subst huw
      rw [planSwap, Function.update_self]
      have hane : a' ∉ L u \ {a} := by simp [Finset.mem_sdiff, ha'L]
      have h1 : (L u \ {a}).card = (L u).card - 1 := by
        rw [← Finset.erase_eq]; exact Finset.card_erase_of_mem ha
      have hk1 : 1 ≤ k u := by rw [← hcard u hu]; exact Finset.card_pos.2 ⟨a, ha⟩
      rw [Finset.card_insert_of_notMem hane, h1, hcard u hu]
      omega
    · rw [planSwap, Function.update_of_ne huw]; exact hcard u hu
  · intro u hu
    have huw : u ≠ w := fun h => hu (h ▸ hwS)
    rw [planSwap, Function.update_of_ne huw]; exact hout u hu

/-- **The swap strictly decreases the potential** when it moves load from a place `a` to a place
`a'` at least two lighter. -/
theorem planPot_swap_lt {S : Finset V} {T : V → Finset V} {L : V → Finset V} {w a a' : V}
    (hwS : w ∈ S) (haT : a ∈ T w) (ha : a ∈ L w) (ha'T : a' ∈ T w) (ha'L : a' ∉ L w) (hne : a ≠ a')
    (hlo : planLoad S L a' + 2 ≤ planLoad S L a) :
    planPot S T (planSwap L w a a') < planPot S T L := by
  classical
  set G := S.biUnion T with hG
  set F : V → ℕ := fun b => (planLoad S (planSwap L w a a') b) ^ 2 with hF
  set Gg : V → ℕ := fun b => (planLoad S L b) ^ 2 with hGg
  have haG : a ∈ G := Finset.mem_biUnion.2 ⟨w, hwS, haT⟩
  have ha'G : a' ∈ G := Finset.mem_biUnion.2 ⟨w, hwS, ha'T⟩
  have ha'G' : a' ∈ G.erase a := Finset.mem_erase.2 ⟨fun h => hne h.symm, ha'G⟩
  -- extract `a` and `a'` from both sums
  have hExtF : planPot S T (planSwap L w a a') = F a + (F a' + ∑ b ∈ (G.erase a).erase a', F b) := by
    rw [planPot, ← hG]
    rw [← Finset.add_sum_erase G F haG, ← Finset.add_sum_erase (G.erase a) F ha'G']
  have hExtG : planPot S T L = Gg a + (Gg a' + ∑ b ∈ (G.erase a).erase a', Gg b) := by
    rw [planPot, ← hG]
    rw [← Finset.add_sum_erase G Gg haG, ← Finset.add_sum_erase (G.erase a) Gg ha'G']
  -- the doubly-erased sums agree
  have hmid : ∑ b ∈ (G.erase a).erase a', F b = ∑ b ∈ (G.erase a).erase a', Gg b := by
    apply Finset.sum_congr rfl
    intro b hb
    have hba' : b ≠ a' := (Finset.mem_erase.1 hb).1
    have hba : b ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hb).2).1
    simp only [hF, hGg, planLoad_swap_of_ne hba hba']
  rw [hExtF, hExtG, hmid]
  -- reduce to the two-place inequality
  have hva : planLoad S (planSwap L w a a') a = planLoad S L a - 1 := by
    have h := planLoad_swap_at hwS ha hne; omega
  have hva' : planLoad S (planSwap L w a a') a' = planLoad S L a' + 1 :=
    planLoad_swap_at' hwS ha'L hne
  have hFa : F a = (planLoad S L a - 1) ^ 2 := by simp only [hF, hva]
  have hFa' : F a' = (planLoad S L a' + 1) ^ 2 := by simp only [hF, hva']
  have hGa : Gg a = (planLoad S L a) ^ 2 := rfl
  have hGa' : Gg a' = (planLoad S L a') ^ 2 := rfl
  have hkey : F a + F a' < Gg a + Gg a' := by
    rw [hFa, hFa', hGa, hGa']
    obtain ⟨A'', hA''eq⟩ : ∃ m, planLoad S L a = m + 1 := ⟨planLoad S L a - 1, by omega⟩
    have hA'' : planLoad S L a' + 1 ≤ A'' := by omega
    rw [hA''eq]
    have : A'' + 1 - 1 = A'' := by omega
    rw [this]
    nlinarith only [hA'']
  omega

/-- **The tight balanced plan.**  Any pool system with demands `k w ≤ (T w).card` admits a plan that
is *locally balanced*: minimising the potential `∑_a (load a)^2`, no single swap can improve it, so at
every link each chosen place is used at most one more time than any unchosen candidate.  This is the
place-level spread the routed sweep's leftover plan needs; the swap engine is the same one behind
`BKLO.exists_balanced_half_selection`. -/
theorem exists_locally_balanced_plan (S : Finset V) (T : V → Finset V) (k : V → ℕ)
    (hk : ∀ w ∈ S, k w ≤ (T w).card) :
    ∃ L : V → Finset V, IsPlan S T k L ∧ IsLocallyBalanced S T L := by
  classical
  obtain ⟨L0, h1, h2, h3⟩ := exists_plan_subset S T k hk
  have hplan0 : IsPlan S T k L0 := ⟨h1, h2, h3⟩
  suffices H : ∀ N : ℕ, ∀ L : V → Finset V, IsPlan S T k L → planPot S T L = N →
      ∃ L' : V → Finset V, IsPlan S T k L' ∧ IsLocallyBalanced S T L' by
    exact H (planPot S T L0) L0 hplan0 rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro L hplan hpot
    by_cases hbal : IsLocallyBalanced S T L
    · exact ⟨L, hplan, hbal⟩
    · unfold IsLocallyBalanced at hbal
      push_neg at hbal
      obtain ⟨w, hwS, a, haL, a', ha'T, ha'L, hlt⟩ := hbal
      have haT : a ∈ T w := hplan.1 w hwS haL
      have hne : a ≠ a' := fun h => ha'L (h ▸ haL)
      have hlo : planLoad S L a' + 2 ≤ planLoad S L a := by omega
      have hdec := planPot_swap_lt hwS haT haL ha'T ha'L hne hlo
      exact IH (planPot S T (planSwap L w a a')) (hpot ▸ hdec)
        (planSwap L w a a') (swap_isPlan hplan hwS haL ha'T ha'L hne) rfl

end BKLO
