import PaperIV.NibblePort
import PaperIV.CliqueBagNibble
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.IntervalCases

/-!
# Uniform `K₄` nibble counts on the complete clique (local B2 subcase)

This module discharges, **for complete cliques only**, the two counting hypotheses that
`PaperIV.NibblePort.WeightedNibbleAt` asks of the hypergraph `NibblePort.k4Supports G`,
and packages the result as the local (complete-clique) form of clause 4:

`WeightedNibbleAt → CliqueBagNibble.CliqueBagNibbleAt β` for every `β > 0`.

## What is proved

* `card_filter_superset` — the elementary count: the number of `n`-element subsets of a
  finite type containing a fixed set `A` is `(card V - |A|).choose (n - |A|)`.
* `card_k4Supports_filter` — transport of counts through `k4Supports G = image pairs (…)`
  for a complete `G`; `pairs` is injective on `4`-sets.
* `card_k4Supports_filter_mem` — each edge lies in exactly `C(m-2,2)` copies of `K₄`.
* `card_k4Supports_filter_mem_two` — two distinct edges lie in at most `m-3` copies.
* `card_k4Supports` — there are `C(m,4)` copies of `K₄`.
* `uniformK4Weight` — the uniform real weight `1 / C(m-2,2)` on `k4Supports`.
* `uniformK4Weight_nonneg`, `uniformK4Weight_load_eq_one`, `uniformK4Weight_load_le_one`,
  `uniformK4Weight_codegree_le` (the sharp bound `2/(m-2)`), `uniformK4Weight_sum`
  (`= C(m,2)/6`).
* `exists_nibble_threshold` — the explicit threshold `m₀ = max 4 (⌈2/γ⌉₊ + 3)` making the
  codegree bound at most `γ`.
* `cliqueBagNibbleAt_of_weightedNibble` — the local clause-4 implication.
* `uniformK4Weight_load_eq_one_top`, `uniformK4Weight_codegree_le_top`,
  `uniformK4Weight_sum_top` — the same three facts stated directly for
  `⊤ : SimpleGraph (Fin m)`.

## Scope

This is **only** the complete-clique local B2 subcase.  Nothing here addresses dense bags
(`δ > 0`) or the clause-2 assignment gate; those remain open exactly as before.
-/

namespace PaperIV.K4UniformNibbleCounts

open Finset
open PaperIV.FarRounding
open PaperIV.NibblePort

/-! ## 1. Elementary subset counting -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of `n`-element subsets of `V` containing a fixed set `A` (with `|A| ≤ n`)
is `(card V - |A|).choose (n - |A|)`. -/
theorem card_filter_superset (A : Finset V) (n : ℕ) (hA : A.card ≤ n) :
    (univ.filter (fun K : Finset V => A ⊆ K ∧ K.card = n)).card
      = (Fintype.card V - A.card).choose (n - A.card) := by
  classical
  have hcard : ((univ \ A).card) = Fintype.card V - A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]
  rw [← hcard, ← Finset.card_powersetCard]
  refine Finset.card_bij' (fun K _ => K \ A) (fun S _ => A ∪ S) ?_ ?_ ?_ ?_
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ K) (le_refl A), ?_⟩
    rw [Finset.card_sdiff_of_subset hK.1, hK.2]
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hdisj : Disjoint A S := by
      refine Finset.disjoint_left.2 fun a ha haS => ?_
      have := hS.1 haS
      simp only [Finset.mem_sdiff] at this
      exact this.2 ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.subset_union_left, ?_⟩
    rw [Finset.card_union_of_disjoint hdisj, hS.2]
    omega
  · intro K hK
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hK
    show A ∪ (K \ A) = K
    rw [Finset.union_sdiff_self_eq_union]
    exact Finset.union_eq_right.2 hK.1
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hdisj : Disjoint A S := by
      refine Finset.disjoint_left.2 fun a ha haS => ?_
      have := hS.1 haS
      simp only [Finset.mem_sdiff] at this
      exact this.2 ha
    show (A ∪ S) \ A = S
    rw [Finset.union_sdiff_cancel_left hdisj]

omit [Fintype V] in
/-- A non-diagonal edge lies in `pairs K` exactly when both its endpoints do. -/
theorem mem_pairs_iff_toFinset_subset {K : Finset V} {e : Sym2 V} (he : ¬ e.IsDiag) :
    e ∈ pairs K ↔ e.toFinset ⊆ K := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      simpa [Sym2.isDiag_iff_proj_eq] using he
    rw [mk_mem_pairs, Sym2.toFinset_mk_eq]
    simp [Finset.insert_subset_iff, hab]

omit [Fintype V] in
/-- A non-diagonal element of `Sym2 V` is determined by its two endpoints. -/
theorem sym2_eq_of_toFinset_eq {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (h : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.ind with
  | _ a b =>
    induction f using Sym2.ind with
    | _ c d =>
      have hab : a ≠ b := by simpa [Sym2.isDiag_iff_proj_eq] using he
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at h
      have ha : a ∈ ({c, d} : Finset V) := by rw [← h]; simp
      have hb : b ∈ ({c, d} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rw [Sym2.eq_iff]
      rcases ha with rfl | rfl
      · rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl ⟨rfl, rfl⟩
      · rcases hb with rfl | rfl
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd rfl hab

omit [Fintype V] in
/-- Two distinct non-diagonal edges span at least three and at most four vertices. -/
theorem card_union_toFinset_bounds {e f : Sym2 V} (he : ¬ e.IsDiag) (hf : ¬ f.IsDiag)
    (hef : e ≠ f) :
    3 ≤ (e.toFinset ∪ f.toFinset).card ∧ (e.toFinset ∪ f.toFinset).card ≤ 4 := by
  classical
  have hce : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e he
  have hcf : f.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag f hf
  have hub : (e.toFinset ∪ f.toFinset).card ≤ 4 := by
    have := Finset.card_union_le e.toFinset f.toFinset
    omega
  refine ⟨?_, hub⟩
  by_contra hlt
  push_neg at hlt
  have hEsub : e.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_left
  have hFsub : f.toFinset ⊆ e.toFinset ∪ f.toFinset := Finset.subset_union_right
  have hle : (e.toFinset ∪ f.toFinset).card ≤ e.toFinset.card := by omega
  have h1 : e.toFinset ∪ f.toFinset = e.toFinset :=
    (Finset.eq_of_subset_of_card_le hEsub hle).symm
  have hle' : (e.toFinset ∪ f.toFinset).card ≤ f.toFinset.card := by omega
  have h2 : e.toFinset ∪ f.toFinset = f.toFinset :=
    (Finset.eq_of_subset_of_card_le hFsub hle').symm
  exact hef (sym2_eq_of_toFinset_eq he hf (h1.symm.trans h2))

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a complete graph every `4`-set is an item. -/
theorem isItem_of_card_four (hG : ∀ a b : V, a ≠ b → G.Adj a b) {K : Finset V}
    (h4 : K.card = 4) : IsItem G K :=
  ⟨fun a _ b _ hab => hG a b hab, Or.inr h4⟩

/-- For a complete graph the `K₄` hypergraph is the image of *all* `4`-sets under `pairs`. -/
theorem k4Supports_eq_image (hG : ∀ a b : V, a ≠ b → G.Adj a b) :
    k4Supports G = (univ.filter (fun K : Finset V => K.card = 4)).image pairs := by
  classical
  unfold k4Supports
  congr 1
  ext K
  simp only [Finset.mem_filter, mem_items, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h4 => ⟨isItem_of_card_four hG h4, h4⟩⟩

omit [DecidableRel G.Adj] in
/-- `pairs` is injective on `4`-element sets. -/
theorem pairs_inj_four {K L : Finset V} (hK : K.card = 4) (hL : L.card = 4)
    (h : pairs K = pairs L) : K = L := by
  rw [← cliqueOf_pairs (K := K) (by omega), ← cliqueOf_pairs (K := L) (by omega), h]

/-- Every element of a hyperedge of `k4Supports G` is a genuine (non-diagonal) edge. -/
theorem not_isDiag_of_mem_k4Supports {T : Finset (Sym2 V)} (hT : T ∈ k4Supports G)
    {e : Sym2 V} (he : e ∈ T) : ¬ e.IsDiag := by
  obtain ⟨K, _, _, rfl⟩ := mem_k4Supports.1 hT
  exact (mem_pairs.1 he).2

/-- **Counting transport.**  Counting hyperedges of `k4Supports G` satisfying a predicate
`q` is the same as counting `4`-sets satisfying the matching vertex-side predicate `p`. -/
theorem card_k4Supports_filter (hG : ∀ a b : V, a ≠ b → G.Adj a b)
    (p : Finset V → Prop) [DecidablePred p]
    (q : Finset (Sym2 V) → Prop) [DecidablePred q]
    (hpq : ∀ K : Finset V, K.card = 4 → (q (pairs K) ↔ p K)) :
    ((k4Supports G).filter q).card
      = (univ.filter (fun K : Finset V => p K ∧ K.card = 4)).card := by
  classical
  rw [k4Supports_eq_image hG, Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · congr 1
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨(hpq K h.1).1 h.2, h.1⟩, fun h => ⟨h.2, (hpq K h.2).2 h.1⟩⟩
  · intro K hK L hL h
    have hK4 : K.card = 4 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hK)).1).2
    have hL4 : L.card = 4 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hL)).1).2
    exact pairs_inj_four hK4 hL4 h

/-- **Degree count.**  In a complete graph each edge lies in exactly `C(m-2,2)` copies of
`K₄`, where `m = card V`. -/
theorem card_k4Supports_filter_mem (hG : ∀ a b : V, a ≠ b → G.Adj a b) {e : Sym2 V}
    (he : ¬ e.IsDiag) :
    ((k4Supports G).filter (fun T => e ∈ T)).card = (Fintype.card V - 2).choose 2 := by
  classical
  have hce : e.toFinset.card = 2 := Sym2.card_toFinset_of_not_isDiag e he
  rw [card_k4Supports_filter hG (fun K => e.toFinset ⊆ K) (fun T => e ∈ T)
      (fun K _ => mem_pairs_iff_toFinset_subset he),
    card_filter_superset e.toFinset 4 (by omega), hce]

/-- **Codegree count.**  Two distinct edges lie in at most `m-3` copies of `K₄`. -/
theorem card_k4Supports_filter_mem_two (hG : ∀ a b : V, a ≠ b → G.Adj a b) {e f : Sym2 V}
    (hef : e ≠ f) :
    ((k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T)).card ≤ Fintype.card V - 3 := by
  classical
  by_cases he : e.IsDiag
  · have hempty : (k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro T hT
      rw [Finset.mem_filter] at hT
      exact not_isDiag_of_mem_k4Supports hT.1 hT.2.1 he
    rw [hempty]; simp
  by_cases hf : f.IsDiag
  · have hempty : (k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro T hT
      rw [Finset.mem_filter] at hT
      exact not_isDiag_of_mem_k4Supports hT.1 hT.2.2 hf
    rw [hempty]; simp
  obtain ⟨h3, h4⟩ := card_union_toFinset_bounds he hf hef
  have hmc : (e.toFinset ∪ f.toFinset).card ≤ Fintype.card V := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ
      (e.toFinset ∪ f.toFinset))
  rw [card_k4Supports_filter hG (fun K => (e.toFinset ∪ f.toFinset) ⊆ K)
      (fun T => e ∈ T ∧ f ∈ T)
      (fun K _ => by
        show (e ∈ pairs K ∧ f ∈ pairs K) ↔ (e.toFinset ∪ f.toFinset) ⊆ K
        rw [mem_pairs_iff_toFinset_subset he, mem_pairs_iff_toFinset_subset hf,
          ← Finset.union_subset_iff]),
    card_filter_superset (e.toFinset ∪ f.toFinset) 4 h4]
  interval_cases hcard : (e.toFinset ∪ f.toFinset).card
  · simp [Nat.choose_one_right]
  · simpa using Nat.one_le_iff_ne_zero.2 (by omega)

/-- **Total count.**  A complete graph on `m` vertices has `C(m,4)` copies of `K₄`. -/
theorem card_k4Supports (hG : ∀ a b : V, a ≠ b → G.Adj a b) :
    (k4Supports G).card = (Fintype.card V).choose 4 := by
  classical
  have h := card_k4Supports_filter hG (fun K => (∅ : Finset V) ⊆ K) (fun _ => True)
    (fun K _ => by simp)
  simp only [Finset.filter_true] at h
  rw [h, card_filter_superset (∅ : Finset V) 4 (by simp)]
  simp

end Counting

/-! ## 2. The binomial identities involved -/

/-- `2·C(k+2,2) = (k+2)(k+1)`. -/
theorem two_mul_choose_two (k : ℕ) : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 2) 2
  simp [Nat.descFactorial, Nat.factorial] at h
  rw [← h]; ring

/-- `2·C(m-2,2) = (m-2)(m-3)` for `m ≥ 4`. -/
theorem two_mul_choose_two_sub {m : ℕ} (hm : 4 ≤ m) :
    2 * (m - 2).choose 2 = (m - 2) * (m - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have h := two_mul_choose_two k
  have e2 : k + 4 - 2 = k + 2 := by omega
  have e3 : k + 4 - 3 = k + 1 := by omega
  rw [e2, e3]
  exact h

/-- `6·C(m,4) = C(m,2)·C(m-2,2)` for `m ≥ 4`. -/
theorem six_mul_choose_four {m : ℕ} (hm : 4 ≤ m) :
    6 * m.choose 4 = m.choose 2 * (m - 2).choose 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have h4 := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 4
  have h2 := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 2
  have h2' := Nat.descFactorial_eq_factorial_mul_choose (k + 2) 2
  simp [Nat.descFactorial, Nat.factorial] at h4 h2 h2'
  have e : k + 4 - 2 = k + 2 := by omega
  rw [e]
  nlinarith [h4, h2, h2']

/-- `C(m-2,2) > 0` for `m ≥ 4`. -/
theorem choose_two_pos {m : ℕ} (hm : 4 ≤ m) : 0 < (m - 2).choose 2 :=
  Nat.choose_pos (by omega)

/-! ## 3. The uniform weight on the `K₄` hypergraph of a clique -/

section Weight

/-- **The uniform weight** `1 / C(m-2,2)` on the `K₄` hypergraph of a clique on `m`
vertices. -/
noncomputable def uniformK4Weight (m : ℕ) : Finset (Sym2 (Fin m)) → ℝ :=
  fun _ => 1 / (((m - 2).choose 2 : ℕ) : ℝ)

variable {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]

/-- The uniform weight is nonnegative. -/
theorem uniformK4Weight_nonneg (T : Finset (Sym2 (Fin m))) : 0 ≤ uniformK4Weight m T := by
  unfold uniformK4Weight
  positivity

/-- Summing the uniform weight over any family just counts the family. -/
theorem sum_uniformK4Weight (S : Finset (Finset (Sym2 (Fin m)))) :
    ∑ T ∈ S, uniformK4Weight m T = (S.card : ℝ) * (1 / (((m - 2).choose 2 : ℕ) : ℝ)) := by
  simp [uniformK4Weight, Finset.sum_const, nsmul_eq_mul]

/-- **Every edge-load is exactly `1`.**  Hence the exceptional set of the nibble is
empty. -/
theorem uniformK4Weight_load_eq_one (hm : 4 ≤ m) (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b)
    {e : Sym2 (Fin m)} (he : ¬ e.IsDiag) :
    ∑ T ∈ (k4Supports G).filter (fun T => e ∈ T), uniformK4Weight m T = 1 := by
  classical
  have hpos : 0 < (((m - 2).choose 2 : ℕ) : ℝ) := by exact_mod_cast choose_two_pos hm
  rw [sum_uniformK4Weight, card_k4Supports_filter_mem hG he, Fintype.card_fin]
  field_simp

/-- Every edge-load is at most `1` (trivially `0` for diagonal elements). -/
theorem uniformK4Weight_load_le_one (hm : 4 ≤ m) (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b)
    (e : Sym2 (Fin m)) :
    ∑ T ∈ (k4Supports G).filter (fun T => e ∈ T), uniformK4Weight m T ≤ 1 := by
  classical
  by_cases he : e.IsDiag
  · have hempty : (k4Supports G).filter (fun T => e ∈ T) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro T hT
      rw [Finset.mem_filter] at hT
      exact not_isDiag_of_mem_k4Supports hT.1 hT.2 he
    rw [hempty]; simp
  · rw [uniformK4Weight_load_eq_one hm hG he]

/-- **The codegree bound.**  Any two distinct edges carry weighted codegree at most
`2/(m-2)`, which tends to `0`. -/
theorem uniformK4Weight_codegree_le (hm : 4 ≤ m) (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b)
    {e f : Sym2 (Fin m)} (hef : e ≠ f) :
    ∑ T ∈ (k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T), uniformK4Weight m T
      ≤ 2 / ((m : ℝ) - 2) := by
  classical
  have hpos : 0 < (((m - 2).choose 2 : ℕ) : ℝ) := by exact_mod_cast choose_two_pos hm
  have hm2 : (0 : ℝ) < (m : ℝ) - 2 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcast2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]; norm_num
  have hcast3 : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ m)]; norm_num
  have hkey : 2 * (((m - 2).choose 2 : ℕ) : ℝ) = ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
    have h := two_mul_choose_two_sub hm
    have hc : ((2 * (m - 2).choose 2 : ℕ) : ℝ) = (((m - 2) * (m - 3) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hc
    rw [hcast2, hcast3] at hc
    linarith
  have hcle : ((((k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T)).card : ℕ) : ℝ)
      ≤ (m : ℝ) - 3 := by
    have hnat := card_k4Supports_filter_mem_two hG hef
    rw [Fintype.card_fin] at hnat
    have : ((((k4Supports G).filter (fun T => e ∈ T ∧ f ∈ T)).card : ℕ) : ℝ)
        ≤ ((m - 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [hcast3] at this
    exact this
  rw [sum_uniformK4Weight, mul_one_div, div_le_div_iff₀ hpos hm2]
  nlinarith [hcle, hm2, hkey]

/-- **The fractional value.**  The total uniform weight is `C(m,2)/6`. -/
theorem uniformK4Weight_sum (hm : 4 ≤ m) (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b) :
    ∑ T ∈ k4Supports G, uniformK4Weight m T = ((m.choose 2 : ℕ) : ℝ) / 6 := by
  classical
  have hpos : 0 < (((m - 2).choose 2 : ℕ) : ℝ) := by exact_mod_cast choose_two_pos hm
  rw [sum_uniformK4Weight, card_k4Supports hG, Fintype.card_fin, mul_one_div,
    div_eq_div_iff (ne_of_gt hpos) (by norm_num : (6 : ℝ) ≠ 0)]
  have h : m.choose 4 * 6 = m.choose 2 * (m - 2).choose 2 := by
    rw [mul_comm]; exact six_mul_choose_four hm
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h

end Weight

/-! ## 4. The explicit threshold -/

/-- **Explicit threshold.**  For every `γ > 0` there is an explicit `m₀ ≥ 4`, namely
`max 4 (⌈2/γ⌉₊ + 3)`, such that the codegree bound `2/(m-2)` is at most `γ` for all
`m ≥ m₀`. -/
theorem exists_nibble_threshold {γ : ℝ} (hγ : 0 < γ) :
    ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → 2 / ((m : ℝ) - 2) ≤ γ := by
  refine ⟨max 4 (⌈2 / γ⌉₊ + 3), le_max_left _ _, ?_⟩
  intro m hm
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm
  have hceil : (⌈2 / γ⌉₊ : ℝ) ≤ (m : ℝ) - 3 := by
    have hstep : (⌈2 / γ⌉₊ : ℕ) + 3 ≤ m := le_trans (le_max_right _ _) hm
    have h' : ((⌈2 / γ⌉₊ + 3 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hstep
    push_cast at h'
    linarith
  have hge : 2 / γ ≤ (m : ℝ) - 3 := le_trans (Nat.le_ceil _) hceil
  have hm2 : (0 : ℝ) < (m : ℝ) - 2 := by
    have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
    linarith
  rw [div_le_iff₀ hm2]
  have h2 : 2 / γ ≤ (m : ℝ) - 2 := by linarith
  rw [div_le_iff₀ hγ] at h2
  linarith

/-! ## 5. The local (complete-clique) form of clause 4 -/

/-- Edge count of a complete graph on `Fin m`. -/
theorem card_edgeFinset_of_complete {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hG : ∀ a b : Fin m, a ≠ b → G.Adj a b) :
    G.edgeFinset.card = m.choose 2 := by
  classical
  have hset : G.edgeFinset = pairs (univ : Finset (Fin m)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mk_mem_pairs]
      exact ⟨fun h => ⟨mem_univ _, mem_univ _, G.ne_of_adj h⟩, fun h => hG a b h.2.2⟩
  rw [hset, card_pairs, Finset.card_univ, Fintype.card_fin]

/-- **Local clause 4 (complete cliques).**  The weighted nibble interface implies the
complete-clique nibble statement `CliqueBagNibble.CliqueBagNibbleAt β` for every `β > 0`.

All threshold arithmetic is explicit: given the `γ` produced by `WeightedNibbleAt` at
`r = 6` and `β`, the threshold is `m₀ = max 4 (⌈2/γ⌉₊ + 3)`, which makes the codegree bound
`2/(m-2) ≤ γ`, while the edge-loads are *exactly* `1` and the fractional value is exactly
`C(m,2)/6 = e(G)/6`. -/
theorem cliqueBagNibbleAt_of_weightedNibble (hnib : WeightedNibbleAt) {β : ℚ} (hβ : 0 < β) :
    CliqueBagNibble.CliqueBagNibbleAt β := by
  classical
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  obtain ⟨γ, hγ, hmain⟩ := hnib 6 (by norm_num) (β : ℝ) hβ'
  obtain ⟨m₀, hm₀4, hm₀⟩ := exists_nibble_threshold hγ
  refine ⟨m₀, ?_⟩
  intro m hm G _ hcomplete
  have hm4 : 4 ≤ m := le_trans hm₀4 hm
  obtain ⟨M, hM, hcard⟩ :=
    hmain (W := Sym2 (Fin m)) (k4Supports G) (uniformK4Weight m) k4Supports_uniform
      (uniformK4Weight_nonneg (m := m))
      (fun e => uniformK4Weight_load_le_one hm4 hcomplete e)
      (fun e f hef =>
        le_trans (uniformK4Weight_codegree_le hm4 hcomplete hef) (hm₀ m hm))
  obtain ⟨P, hP⟩ := packing_of_matching M hM
  refine ⟨P, ?_⟩
  rw [uniformK4Weight_sum hm4 hcomplete] at hcard
  have hgain : (P.gain : ℝ) = 5 * (M.card : ℝ) := by rw [hP]; push_cast; ring
  have hedges : (G.edgeFinset.card : ℝ) = ((m.choose 2 : ℕ) : ℝ) := by
    rw [card_edgeFinset_of_complete G hcomplete]
  have hreal : (1 - (β : ℝ)) * ((5 / 6 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (P.gain : ℝ) := by
    rw [hgain, hedges]
    linarith [hcard]
  have hcast : ((((1 : ℚ) - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) : ℚ) : ℝ)
      ≤ ((P.gain : ℚ) : ℝ) := by
    push_cast
    exact hreal
  exact_mod_cast hcast


/-! ## 5b. La misma cláusula, pero desde el nibble que Paper III **sí demuestra** -/

/-- Umbral para el excepcional: `m ≤ η·C(m,2)` en cuanto `m ≥ 2/η + 1`. -/
theorem exists_exceptional_threshold {η : ℝ} (hη : 0 < η) :
    ∃ m₁ : ℕ, 4 ≤ m₁ ∧ ∀ m : ℕ, m₁ ≤ m → (m : ℝ) ≤ η * ((m.choose 2 : ℕ) : ℝ) := by
  refine ⟨max 4 (⌈2 / η⌉₊ + 1), le_max_left _ _, ?_⟩
  intro m hm
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm
  have hm4' : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hceil : (⌈2 / η⌉₊ : ℝ) ≤ (m : ℝ) - 1 := by
    have hstep : (⌈2 / η⌉₊ : ℕ) + 1 ≤ m := le_trans (le_max_right _ _) hm
    have h' : ((⌈2 / η⌉₊ + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hstep
    push_cast at h'
    linarith
  have hge : 2 / η ≤ (m : ℝ) - 1 := le_trans (Nat.le_ceil _) hceil
  rw [div_le_iff₀ hη] at hge
  have hch : ((m.choose 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ m
  rw [hch]
  have hmul := mul_le_mul_of_nonneg_left hge (show (0 : ℝ) ≤ (m : ℝ) by linarith)
  linarith

set_option maxHeartbeats 1000000 in
/-- **Cláusula 4 local, desde el nibble demostrado.**  Idéntica a
`cliqueBagNibbleAt_of_weightedNibble`, pero consumiendo `NibblePort.NearPerfectNibbleAt`
—el enunciado `Nibble.fracNibbleWeighted_nearPerfect` de Paper III, que **está demostrado
allí**— en vez de `WeightedNibbleAt`, que es `Nibble.FracNibbleWeightedTheorem` y en Paper III
sólo se demuestra condicionado a `FracNibbleWeightedHeavyEdge`.

Las dos hipótesis extra se descargan aquí:

* **carga `≥ 1-γ` fuera del excepcional**: en una clique completa la carga de toda arista real
  es **exactamente `1`** (`uniformK4Weight_load_eq_one`), luego basta tomar como excepcional
  el conjunto de los **diagonales** de `Sym2 (Fin m)`, donde la carga es `0`;
* **`|Exc| ≤ η·|W|`**: hay `m` diagonales y `|W| ≥ C(m,2)`, luego la razón es `≈ 2/m → 0`, con
  umbral explícito `exists_exceptional_threshold`.

Con esto, la entrada externa del régimen lejano deja de ser una `Prop` sin demostrar en
ninguna parte del programa y pasa a ser un teorema demostrado y auditado de Paper III. -/
theorem cliqueBagNibbleAt_of_nearPerfectNibble (hnib : NearPerfectNibbleAt) {β : ℚ}
    (hβ : 0 < β) : CliqueBagNibble.CliqueBagNibbleAt β := by
  classical
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  obtain ⟨γ, hγ, η, hη, hmain⟩ := hnib 6 (by norm_num) (β : ℝ) hβ'
  obtain ⟨m₀, hm₀4, hm₀⟩ := exists_nibble_threshold hγ
  obtain ⟨m₁, hm₁4, hm₁⟩ := exists_exceptional_threshold hη
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm G _ hcomplete
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hmm₁ : m₁ ≤ m := le_trans (le_max_right _ _) hm
  have hm4 : 4 ≤ m := le_trans hm₀4 hmm₀
  set Exc : Finset (Sym2 (Fin m)) := Finset.univ.filter (fun e => e.IsDiag) with hExc
  have hExcCard : Exc.card ≤ m := by
    have hsub : Exc ⊆ (Finset.univ : Finset (Fin m)).image (fun a => s(a, a)) := by
      intro e
      induction e using Sym2.ind with
      | _ a b =>
        intro he
        rw [hExc, Finset.mem_filter] at he
        have hab : a = b := by simpa using he.2
        exact Finset.mem_image.2 ⟨a, Finset.mem_univ a, by rw [hab]⟩
    calc Exc.card ≤ ((Finset.univ : Finset (Fin m)).image (fun a => s(a, a))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ = m := by rw [Finset.card_univ, Fintype.card_fin]
  have hExcBound : (Exc.card : ℝ) ≤ η * (Fintype.card (Sym2 (Fin m)) : ℝ) := by
    have h1 : (Exc.card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hExcCard
    have h2 : (m : ℝ) ≤ η * ((m.choose 2 : ℕ) : ℝ) := hm₁ m hmm₁
    have h3 : (m.choose 2 : ℕ) ≤ Fintype.card (Sym2 (Fin m)) := by
      rw [← card_edgeFinset_of_complete G hcomplete, ← Finset.card_univ]
      exact Finset.card_le_univ _
    have h3' : ((m.choose 2 : ℕ) : ℝ) ≤ (Fintype.card (Sym2 (Fin m)) : ℝ) := by
      exact_mod_cast h3
    calc (Exc.card : ℝ) ≤ (m : ℝ) := h1
      _ ≤ η * ((m.choose 2 : ℕ) : ℝ) := h2
      _ ≤ η * (Fintype.card (Sym2 (Fin m)) : ℝ) :=
          mul_le_mul_of_nonneg_left h3' (le_of_lt hη)
  obtain ⟨M, hM, -, hcard⟩ :=
    hmain (W := Sym2 (Fin m)) (k4Supports G) (uniformK4Weight m) Exc k4Supports_uniform
      (uniformK4Weight_nonneg (m := m))
      (fun e => uniformK4Weight_load_le_one hm4 hcomplete e)
      (fun e he => by
        have hnd : ¬ e.IsDiag := fun hd =>
          he (by rw [hExc]; exact Finset.mem_filter.2 ⟨Finset.mem_univ e, hd⟩)
        rw [uniformK4Weight_load_eq_one hm4 hcomplete hnd]
        linarith)
      hExcBound
      (fun e f hef =>
        le_trans (uniformK4Weight_codegree_le hm4 hcomplete hef) (hm₀ m hmm₀))
  obtain ⟨P, hP⟩ := packing_of_matching M hM
  refine ⟨P, ?_⟩
  rw [uniformK4Weight_sum hm4 hcomplete] at hcard
  have hgain : (P.gain : ℝ) = 5 * (M.card : ℝ) := by rw [hP]; push_cast; ring
  have hedges : (G.edgeFinset.card : ℝ) = ((m.choose 2 : ℕ) : ℝ) := by
    rw [card_edgeFinset_of_complete G hcomplete]
  have hreal : (1 - (β : ℝ)) * ((5 / 6 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (P.gain : ℝ) := by
    rw [hgain, hedges]
    linarith [hcard]
  have hcast : ((((1 : ℚ) - β) * ((5 / 6 : ℚ) * (G.edgeFinset.card : ℚ)) : ℚ) : ℝ)
      ≤ ((P.gain : ℚ) : ℝ) := by
    push_cast
    exact hreal
  exact_mod_cast hcast


/-! ## 6. The three nibble hypotheses, stated for `⊤ : SimpleGraph (Fin m)` -/

section Top

variable {m : ℕ}

/-- `⊤` is complete. -/
theorem top_adj_of_ne {a b : Fin m} (h : a ≠ b) : (⊤ : SimpleGraph (Fin m)).Adj a b := h

/-- Edge-load of the uniform weight on the complete graph `⊤`: exactly `1`. -/
theorem uniformK4Weight_load_eq_one_top (hm : 4 ≤ m) {e : Sym2 (Fin m)} (he : ¬ e.IsDiag) :
    ∑ T ∈ (k4Supports (⊤ : SimpleGraph (Fin m))).filter (fun T => e ∈ T),
      uniformK4Weight m T = 1 :=
  uniformK4Weight_load_eq_one hm (fun _ _ h => top_adj_of_ne h) he

/-- Weighted codegree of the uniform weight on `⊤`: at most `2/(m-2)`. -/
theorem uniformK4Weight_codegree_le_top (hm : 4 ≤ m) {e f : Sym2 (Fin m)} (hef : e ≠ f) :
    ∑ T ∈ (k4Supports (⊤ : SimpleGraph (Fin m))).filter (fun T => e ∈ T ∧ f ∈ T),
      uniformK4Weight m T ≤ 2 / ((m : ℝ) - 2) :=
  uniformK4Weight_codegree_le hm (fun _ _ h => top_adj_of_ne h) hef

/-- Total uniform weight on `⊤`: exactly `C(m,2)/6 = e(⊤)/6`. -/
theorem uniformK4Weight_sum_top (hm : 4 ≤ m) :
    ∑ T ∈ k4Supports (⊤ : SimpleGraph (Fin m)), uniformK4Weight m T
      = ((m.choose 2 : ℕ) : ℝ) / 6 :=
  uniformK4Weight_sum hm (fun _ _ h => top_adj_of_ne h)

end Top

end PaperIV.K4UniformNibbleCounts


