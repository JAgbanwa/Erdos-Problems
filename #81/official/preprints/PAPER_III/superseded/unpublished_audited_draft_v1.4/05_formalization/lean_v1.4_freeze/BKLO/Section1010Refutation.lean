/-
# `BKLO.Lemma1010K3` is false: the hyperplane counterexample

BKLO Lemma 10.10 (p. 32) is stated in the paper under the hierarchy `1/n ≪ ρ ≪ α, 1/k, 1/r, 1/f`.
The transcription `BKLO.Lemma1010K3` in `BKLO/Section1012Defs.lean` keeps hypotheses (i)–(v) but
drops the hierarchy: it quantifies over *all* `α, ρ ∈ (0,1)` and all `k`, letting only the size
threshold `n₀` depend on them.  This file shows that the resulting statement is false, by an
explicit construction in the regime `α ≪ ρ`.

The obstruction is `BKLO.degTo_le_edeg_of_triDecomp`: any `H'_V` as in the conclusion has
`Δ(H'_V) ≥ max_{y ∈ V} d_H(y,U)`, while hypothesis (iv) only demands `d_H(y,U) ≤ 2kρ|V|`.  So it
suffices to build a configuration satisfying (i)–(v) in which some `y ∈ V` has `d_H(y,U)` much
larger than `2α|V|`.

**The construction** (`p = 1000003`, `α = 10⁻⁸`, `ρ = 10⁻⁶`, `k = 2`).  For `m ≥ 1` put

* `U = 𝔽_p^m` (directions) and `V = (𝔽_p × 𝔽_p^m) × {0,1}` (the paper's `V`), disjointly;
* `H[V]` is *complete*;
* the apex `a ∈ U` is joined to `N_a = {((⟪a,y⟫, y), b) : y ∈ 𝔽_p^m, b ∈ {0,1}}`, the graph of the
  linear form `⟪a,·⟫`, doubled by the `{0,1}`-coordinate so that `|N_a|` is even.

Thus `|V| = 2p^{m+1}`, `|N_a| = 2p^m = |V|/p` and, for `a ≠ a'`,
`|N_a ∩ N_{a'}| = 2|{y : ⟪a-a', y⟫ = 0}| ≤ 2p^{m-1} = |V|/p²`: the apex neighbourhoods are the
(doubled) linear hyperplanes through the origin, so they are large and pairwise nearly disjoint.
Hypotheses (i)–(v) hold because `1/p ≥ 2·18k√ρ³`, `1/p² ≤ 2ρ²` and `1/p ≤ 2kρ`; this window of `p`
is nonempty exactly when `ρ < 1/(648k²)`, the regime complementary to
`BKLO.lemma1010K3Dense_holds`.

But the point `y₀ = ((0,0), true)` lies in *every* `N_a`, so `d_H(y₀, U) = p^m = |V|/(2p)`, which
is `≫ 2α|V|` for `α = 10⁻⁸`.  Hence no `H'_V` with `Δ(H'_V) ≤ 2α|V|` can exist.

The moral is recorded in `BKLO/Section1010Sparse.lean`: the paper's hierarchy is *needed*, and with
it restored (`BKLO.Lemma1010K3Hier`) the only missing ingredient is the pseudorandom `K_r`-factor
core, BKLO Lemma 10.7.

Everything here is `sorry`-free.
-/
import BKLO.Section1010Obstruction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

open Finset

set_option maxRecDepth 8000

namespace BKLO.Cex

/-! ### The vertex set and the graph -/

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Directions: the linear forms `⟪a, ·⟫` on `𝔽_p^m` are indexed by `a ∈ 𝔽_p^m`. -/
abbrev Dir (m : ℕ) := Fin m → ZMod p

/-- The vertices of the paper's `V`: `𝔽_p × 𝔽_p^m`, doubled by a `Bool` so that all apex
neighbourhoods have even size. -/
abbrev Pt (m : ℕ) := (ZMod p × Dir p m) × Bool

/-- The ambient vertex type: `V ⊔ U`. -/
abbrev Vx (m : ℕ) := Pt p m ⊕ Dir p m

variable {p}

/-- The standard bilinear form on `𝔽_p^m`. -/
def ip {m : ℕ} (a y : Dir p m) : ZMod p := ∑ i, a i * y i

/-- `N_a`, the graph of the linear form `⟪a, ·⟫`, doubled. -/
def nbrPt {m : ℕ} (a : Dir p m) : Finset (Pt p m) :=
  Finset.univ.filter (fun w => w.1.1 = ip a w.1.2)

variable (p)

/-- The paper's `V`. -/
def Wset (m : ℕ) : Finset (Vx p m) := Finset.univ.image Sum.inl

/-- The paper's `U`. -/
def Uset (m : ℕ) : Finset (Vx p m) := Finset.univ.image Sum.inr

/-- The graph `H`: complete on `V`, and each apex `a ∈ U` joined exactly to `N_a`. -/
def Hg (m : ℕ) : Finset (Sym2 (Vx p m)) :=
  cliqueEdges (Wset p m) ∪
    Finset.univ.biUnion (fun a : Dir p m => (nbrPt a).image (fun w => s(Sum.inr a, Sum.inl w)))

variable {p} {m : ℕ}

@[simp] theorem mem_Wset {v : Vx p m} : v ∈ Wset p m ↔ ∃ w, v = Sum.inl w := by
  simp [Wset, eq_comm]

@[simp] theorem mem_Uset {v : Vx p m} : v ∈ Uset p m ↔ ∃ a, v = Sum.inr a := by
  simp [Uset, eq_comm]

theorem inl_mem_Wset (w : Pt p m) : (Sum.inl w : Vx p m) ∈ Wset p m := by simp

theorem inr_mem_Uset (a : Dir p m) : (Sum.inr a : Vx p m) ∈ Uset p m := by simp

theorem disjoint_Uset_Wset : Disjoint (Uset p m) (Wset p m) := by
  refine Finset.disjoint_left.2 fun v hv hv' => ?_
  obtain ⟨a, rfl⟩ := mem_Uset.1 hv
  obtain ⟨w, hw⟩ := mem_Wset.1 hv'
  exact absurd hw (by simp)

/-! ### Which pairs are edges -/

theorem mem_Hg_inl_inl {w w' : Pt p m} :
    s(Sum.inl w, Sum.inl w') ∈ Hg p m ↔ w ≠ w' := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · have h2 := (mem_cliqueEdgesV.1 h).2
      rw [Sym2.isDiag_iff_proj_eq] at h2
      exact fun hc => h2 (by rw [hc])
    · obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 h
      obtain ⟨u, -, hu⟩ := Finset.mem_image.1 ha
      rcases Sym2.eq_iff.1 hu with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1.symm (by simp)
  · intro hne
    refine Finset.mem_union_left _ (mem_cliqueEdgesV.2 ⟨?_, ?_⟩)
    · intro x hx
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> exact inl_mem_Wset _
    · rw [Sym2.isDiag_iff_proj_eq]
      exact fun hc => hne (Sum.inl_injective hc)

theorem mem_Hg_inr_inl {a : Dir p m} {w : Pt p m} :
    s(Sum.inr a, Sum.inl w) ∈ Hg p m ↔ w ∈ nbrPt a := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · have h1 := (mem_cliqueEdgesV.1 h).1 (Sum.inr a) (by simp)
      obtain ⟨u, hu⟩ := mem_Wset.1 h1
      exact absurd hu (by simp)
    · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 h
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.1 hb
      rcases Sym2.eq_iff.1 huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hab : b = a := Sum.inr_injective h1
        have hwu : u = w := Sum.inl_injective h2
        rw [← hab, ← hwu]; exact hu
      · exact absurd h1 (by simp)
  · intro hw
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, ?_⟩)
    exact Finset.mem_image.2 ⟨w, hw, rfl⟩

theorem mem_Hg_inr_inr {a a' : Dir p m} : s(Sum.inr a, Sum.inr a') ∉ Hg p m := by
  intro h
  rcases Finset.mem_union.1 h with h | h
  · have h1 := (mem_cliqueEdgesV.1 h).1 (Sum.inr a) (by simp)
    obtain ⟨u, hu⟩ := mem_Wset.1 h1
    exact absurd hu (by simp)
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 h
    obtain ⟨u, -, huv⟩ := Finset.mem_image.1 hb
    rcases Sym2.eq_iff.1 huv with ⟨-, h2⟩ | ⟨-, h2⟩ <;> exact absurd h2 (by simp)

theorem Hg_loopless : ∀ e ∈ Hg p m, ¬ e.IsDiag := by
  intro e he
  rcases Finset.mem_union.1 he with h | h
  · exact (mem_cliqueEdgesV.1 h).2
  · obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 h
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
    simp

theorem Hg_subset_clique : Hg p m ⊆ cliqueEdges (Finset.univ : Finset (Vx p m)) :=
  fun e he => mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, Hg_loopless e he⟩

/-! ### Neighbourhoods -/

theorem nbhd_inr (a : Dir p m) :
    nbhdIn (Hg p m) (Sum.inr a) (Wset p m) = (nbrPt a).image Sum.inl := by
  ext v
  rw [mem_nbhdIn]
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨w, rfl⟩ := mem_Wset.1 hv
    exact Finset.mem_image.2 ⟨w, mem_Hg_inr_inl.1 he, rfl⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨inl_mem_Wset w, mem_Hg_inr_inl.2 hw⟩

theorem nbhd_inl {T : Finset (Vx p m)} (hT : T ⊆ Wset p m) (w : Pt p m) :
    nbhdIn (Hg p m) (Sum.inl w) T = T.erase (Sum.inl w) := by
  ext v
  rw [mem_nbhdIn, Finset.mem_erase]
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨u, rfl⟩ := mem_Wset.1 (hT hv)
    have hne : u ≠ w := mem_Hg_inl_inl.1 (by rwa [Sym2.eq_swap] at he)
    exact ⟨fun hc => hne (Sum.inl_injective hc), hv⟩
  · rintro ⟨hne, hv⟩
    obtain ⟨u, rfl⟩ := mem_Wset.1 (hT hv)
    refine ⟨hv, ?_⟩
    rw [Sym2.eq_swap]
    exact mem_Hg_inl_inl.2 fun hc => hne (by rw [hc])

theorem nbhd_inl_Uset (w : Pt p m) :
    nbhdIn (Hg p m) (Sum.inl w) (Uset p m)
      = (Finset.univ.filter (fun a : Dir p m => w ∈ nbrPt a)).image Sum.inr := by
  ext v
  rw [mem_nbhdIn]
  constructor
  · rintro ⟨hv, he⟩
    obtain ⟨a, rfl⟩ := mem_Uset.1 hv
    rw [Sym2.eq_swap] at he
    exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      mem_Hg_inr_inl.1 he⟩, rfl⟩
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
    refine ⟨inr_mem_Uset a, ?_⟩
    rw [Sym2.eq_swap]
    exact mem_Hg_inr_inl.2 (Finset.mem_filter.1 ha).2

/-! ### Cardinalities -/

theorem card_Wset : (Wset p m).card = 2 * p ^ (m + 1) := by
  rw [Wset, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ]
  simp [pow_succ]
  ring

theorem card_Uset : (Uset p m).card = p ^ m := by
  rw [Uset, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ]
  simp

theorem card_nbrPt (a : Dir p m) : (nbrPt a).card = 2 * p ^ m := by
  have h : (nbrPt a).card = (Finset.univ : Finset (Dir p m × Bool)).card := by
    refine Finset.card_bij' (fun w _ => (w.1.2, w.2)) (fun z _ => ((ip a z.1, z.1), z.2))
      (fun w _ => Finset.mem_univ _) (fun z _ => by simp [nbrPt]) ?_ (fun z _ => rfl)
    intro w hw
    obtain ⟨⟨c, y⟩, b⟩ := w
    simp only [nbrPt, Finset.mem_filter] at hw
    simp [hw.2]
  rw [h]
  simp [mul_comm]

/-- **The key counting fact.**  A nonzero linear form on `𝔽_p^m` has kernel of size `p^{m-1}`, so
two distinct directions agree on at most `p^{m-1}` points. -/
theorem card_agree_mul_le {a a' : Dir p m} (hne : a ≠ a') :
    (Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)).card * p ≤ p ^ m := by
  classical
  -- a coordinate where the two directions differ
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ a' j := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hm : 1 ≤ m := by have := j.isLt; omega
  -- restriction off `j` is injective on the agreement set
  have hinj : Set.InjOn (fun (y : Dir p m) => fun i : {i : Fin m // i ≠ j} => y i.val)
      (Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)) := by
    intro y hy y' hy' hyy
    have hy1 : ip a y = ip a' y := (Finset.mem_filter.1 hy).2
    have hy2 : ip a y' = ip a' y' := (Finset.mem_filter.1 hy').2
    have hoff : ∀ i, i ≠ j → y i = y' i := fun i hi => congrFun hyy ⟨i, hi⟩
    have hsplit : ∀ (b z : Dir p m), ip b z = b j * z j
        + ∑ i ∈ Finset.univ.erase j, b i * z i := by
      intro b z
      rw [ip, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest : ∀ b : Dir p m, ∑ i ∈ Finset.univ.erase j, b i * y i
        = ∑ i ∈ Finset.univ.erase j, b i * y' i := by
      intro b
      exact Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.mem_erase.1 hi).1]
    have e1 : a j * y j + ∑ i ∈ Finset.univ.erase j, a i * y' i
        = a' j * y j + ∑ i ∈ Finset.univ.erase j, a' i * y' i := by
      rw [← hrest a, ← hrest a', ← hsplit a y, ← hsplit a' y, hy1]
    have e2 : a j * y' j + ∑ i ∈ Finset.univ.erase j, a i * y' i
        = a' j * y' j + ∑ i ∈ Finset.univ.erase j, a' i * y' i := by
      rw [← hsplit a y', ← hsplit a' y', hy2]
    have hkey : (a j - a' j) * (y j - y' j) = 0 := by linear_combination e1 - e2
    have hyj : y j = y' j := by
      rcases mul_eq_zero.1 hkey with h | h
      · exact absurd h (sub_ne_zero.2 hj)
      · exact sub_eq_zero.1 h
    funext i
    by_cases hi : i = j
    · rw [hi]; exact hyj
    · exact hoff i hi
  have hcard : (Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)).card
      ≤ Fintype.card ({i : Fin m // i ≠ j} → ZMod p) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card_of_injOn _ (fun y _ => Finset.mem_univ _) hinj
  have hfc : Fintype.card ({i : Fin m // i ≠ j} → ZMod p) = p ^ (m - 1) := by
    simp [Fintype.card_subtype_compl]
  rw [hfc] at hcard
  calc (Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)).card * p
      ≤ p ^ (m - 1) * p := Nat.mul_le_mul_right _ hcard
    _ = p ^ m := by
        rw [← pow_succ]
        congr 1
        omega

theorem card_inter_nbrPt {a a' : Dir p m} (hne : a ≠ a') :
    (nbrPt a ∩ nbrPt a').card * p ≤ 2 * p ^ m := by
  classical
  have h : (nbrPt a ∩ nbrPt a').card
      = ((Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)) ×ˢ
          (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij' (fun w _ => (w.1.2, w.2)) (fun z _ => ((ip a z.1, z.1), z.2))
      ?_ ?_ ?_ (fun z _ => rfl)
    · intro w hw
      obtain ⟨⟨c, y⟩, b⟩ := w
      simp only [Finset.mem_inter, nbrPt, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [← hw.1, hw.2], trivial⟩
    · intro z hz
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp [nbrPt, hz.1]
    · intro w hw
      obtain ⟨⟨c, y⟩, b⟩ := w
      simp only [Finset.mem_inter, nbrPt, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp [hw.1]
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  have hk := card_agree_mul_le hne
  calc (Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)).card * 2 * p
      = 2 * ((Finset.univ.filter (fun y : Dir p m => ip a y = ip a' y)).card * p) := by ring
    _ ≤ 2 * p ^ m := Nat.mul_le_mul_left 2 hk

/-! ### The five hypotheses of Lemma 10.10, as cardinal identities -/

theorem degTo_inr_Wset (a : Dir p m) : degTo (Hg p m) (Sum.inr a) (Wset p m) = 2 * p ^ m := by
  rw [degTo, nbhd_inr, Finset.card_image_of_injective _ Sum.inl_injective, card_nbrPt]

theorem degTo_inl_Wset (w : Pt p m) :
    degTo (Hg p m) (Sum.inl w) (Wset p m) = 2 * p ^ (m + 1) - 1 := by
  rw [degTo, nbhd_inl (Finset.Subset.refl _) w,
    Finset.card_erase_of_mem (inl_mem_Wset w), card_Wset]

theorem degTo_inl_Uset_le (w : Pt p m) : degTo (Hg p m) (Sum.inl w) (Uset p m) ≤ p ^ m := by
  calc degTo (Hg p m) (Sum.inl w) (Uset p m) ≤ (Uset p m).card := degTo_le_card _ _ _
    _ = p ^ m := card_Uset

/-- At the common point `y₀ = ((0,0), b)` *every* apex is a neighbour. -/
theorem degTo_inl_Uset_zero (b : Bool) :
    degTo (Hg p m) (Sum.inl ((0, 0), b)) (Uset p m) = p ^ m := by
  have h : nbhdIn (Hg p m) (Sum.inl ((0, 0), b)) (Uset p m) = Uset p m := by
    rw [nbhd_inl_Uset, Uset]
    congr 1
    refine Finset.filter_true_of_mem fun a _ => ?_
    simp [nbrPt, ip]
  rw [degTo, h, card_Uset]

theorem codegTo_bound {a a' : Dir p m} (hne : a ≠ a') :
    codegTo (Hg p m) (Sum.inr a) (Sum.inr a') (Wset p m) * p ≤ 2 * p ^ m := by
  have h : nbhdIn (Hg p m) (Sum.inr a) (Wset p m) ∩ nbhdIn (Hg p m) (Sum.inr a') (Wset p m)
      = (nbrPt a ∩ nbrPt a').image Sum.inl := by
    rw [nbhd_inr, nbhd_inr, ← Finset.image_inter _ _ Sum.inl_injective]
  rw [codegTo, h, Finset.card_image_of_injective _ Sum.inl_injective]
  exact card_inter_nbrPt hne

/-- Inside `V` the graph is complete, so hypothesis (ii) reduces to `|N_a| - 1`. -/
theorem degTo_in_nbhd (a : Dir p m) {v : Vx p m}
    (hv : v ∈ nbhdIn (Hg p m) (Sum.inr a) (Wset p m)) :
    degTo (Hg p m) v (nbhdIn (Hg p m) (Sum.inr a) (Wset p m)) = 2 * p ^ m - 1 := by
  have hsub : nbhdIn (Hg p m) (Sum.inr a) (Wset p m) ⊆ Wset p m := nbhdIn_subset _ _ _
  obtain ⟨w, rfl⟩ := mem_Wset.1 (hsub hv)
  rw [degTo, nbhd_inl hsub w, Finset.card_erase_of_mem hv, nbhd_inr,
    Finset.card_image_of_injective _ Sum.inl_injective, card_nbrPt]

theorem card_univ_Vx :
    (Finset.univ : Finset (Vx p m)).card = 2 * p ^ (m + 1) + p ^ m := by
  have h1 : (Wset p m).card = 2 * p ^ (m + 1) := card_Wset
  have h2 : (Uset p m).card = p ^ m := card_Uset
  have h3 : (Finset.univ : Finset (Vx p m)) = Wset p m ∪ Uset p m := by
    ext v
    cases v <;> simp
  rw [h3, Finset.card_union_of_disjoint (Finset.disjoint_left.2 fun v hv hv' => by
    obtain ⟨w, rfl⟩ := mem_Wset.1 hv
    obtain ⟨a, ha⟩ := mem_Uset.1 hv'
    exact absurd ha (by simp)), h1, h2]


/-! ### The counterexample -/

/-- The modulus of the counterexample: a prime `p` with `1/(√2 ρ) ≤ p ≤ 1/(72 ρ^{3/2})` for
`ρ = 10⁻⁶`. -/
def qq : ℕ := 1000003

instance : Fact (Nat.Prime qq) := ⟨by unfold qq; norm_num⟩

theorem qq_real : (qq : ℝ) = 1000003 := by unfold qq; norm_num

/-! ### The hypotheses of Lemma 10.10 hold in the configuration -/

/-- **The configuration satisfies hypotheses (i)–(v) of BKLO Lemma 10.10 for `k = 2`.**

For a prime `p`, `m ≥ 1` and reals `α, ρ` in the window `72√ρ³p ≤ 1/2`, `1 ≤ 2ρ²p²`, `1 ≤ 8ρp`,
`α ≤ 1/8`, the graph `Hg p m` with `U = Uset p m`, `V = Wset p m` and `S = univ` satisfies the size
hypothesis `|S|/k - 1 ≤ |V|` and hypotheses (i)–(v) of `BKLO.Lemma1010K3` (equivalently, of
`BKLO.Lemma1010K3Hier` and of `BKLO.Lemma107K2`) with `k = 2`.

This is used twice: to refute the hierarchy-free transcription (`not_lemma1010K3_of_params`, with
`α` tiny), and to show that the hypotheses of `BKLO.Lemma1010K3Hier` and `BKLO.Lemma107K2` are
*satisfiable* together with the hierarchy `2kρ ≤ α` (`hyps_nonvacuous`, with `α = 1/8`), so that
those statements are not vacuous. -/
theorem cex_hyps {p : ℕ} [Fact (Nat.Prime p)] {α ρ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hρ : 0 < ρ) (h1 : 72 * Real.sqrt ρ ^ 3 * (p : ℝ) ≤ 1 / 2)
    (h2 : 1 ≤ 2 * ρ ^ 2 * (p : ℝ) ^ 2) (h3 : 1 ≤ 8 * ρ * (p : ℝ)) (h4 : α ≤ 1 / 8) :
    ((Finset.univ : Finset (Vx p m)).card : ℝ) / ((2 : ℕ) : ℝ) - 1 ≤ ((Wset p m).card : ℝ)
    ∧ (∀ x ∈ Uset p m, 2 ∣ degTo (Hg p m) x (Wset p m))
    ∧ (∀ x ∈ Uset p m, ∀ y ∈ nbhdIn (Hg p m) x (Wset p m),
        (1 / 2 : ℝ) * (degTo (Hg p m) x (Wset p m) : ℝ)
            + 18 * ((2 : ℕ) : ℝ) * Real.sqrt ρ ^ 3 * ((Wset p m).card : ℝ)
          ≤ (degTo (Hg p m) y (nbhdIn (Hg p m) x (Wset p m)) : ℝ))
    ∧ (∀ x ∈ Uset p m, ∀ x' ∈ Uset p m, x ≠ x' →
        (codegTo (Hg p m) x x' (Wset p m) : ℝ) ≤ 2 * ρ ^ 2 * ((Wset p m).card : ℝ))
    ∧ (∀ y ∈ Wset p m, (degTo (Hg p m) y (Uset p m) : ℝ)
        ≤ 2 * ((2 : ℕ) : ℝ) * ρ * ((Wset p m).card : ℝ))
    ∧ (∀ y ∈ Wset p m, ((1 : ℝ) / 2 + 2 * α) * ((Wset p m).card : ℝ)
        ≤ (degTo (Hg p m) y (Wset p m) : ℝ)) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hPpos : (0 : ℝ) < (p : ℝ) := by linarith only [hP2]
  set D : ℝ := (p : ℝ) ^ m with hD
  have hDcast : ((p ^ m : ℕ) : ℝ) = D := by push_cast [hD]; ring
  have hPD : (p : ℝ) ≤ D := by
    rw [hD]
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ m := pow_le_pow_right₀ (by linarith) hm
  have hD2 : (2 : ℝ) ≤ D := le_trans hP2 hPD
  have hDpos : (0 : ℝ) < D := by linarith only [hD2]
  have hWcard : ((Wset p m).card : ℝ) = 2 * (p : ℝ) * D := by
    rw [card_Wset]; push_cast [hD]; ring
  have hScard : ((Finset.univ : Finset (Vx p m)).card : ℝ) = 2 * (p : ℝ) * D + D := by
    rw [card_univ_Vx]; push_cast [hD]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the size hypothesis `|S|/k - 1 ≤ |V|`
    rw [hScard, hWcard]
    push_cast
    nlinarith only [hP2, hScard]
  · -- (i) `2 ∣ d_H(x, V)`
    intro x hx
    obtain ⟨a, rfl⟩ := mem_Uset.1 hx
    rw [degTo_inr_Wset]
    exact ⟨p ^ m, rfl⟩
  · -- (ii) the minimum degree in the apex neighbourhoods
    intro x hx y hy
    obtain ⟨a, rfl⟩ := mem_Uset.1 hx
    rw [degTo_inr_Wset, degTo_in_nbhd a hy, hWcard]
    have hone : (1 : ℕ) ≤ 2 * p ^ m := by
      have : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
      omega
    rw [Nat.cast_sub hone]
    push_cast [hDcast]
    have hsq : 0 ≤ Real.sqrt ρ ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 hDpos.le]
  · -- (iii) the codegree bound
    intro x hx x' hx' hne
    obtain ⟨a, rfl⟩ := mem_Uset.1 hx
    obtain ⟨a', rfl⟩ := mem_Uset.1 hx'
    have hne' : a ≠ a' := fun hc => hne (by rw [hc])
    have hcd := codegTo_bound (m := m) hne'
    have hcdR : (codegTo (Hg p m) (Sum.inr a) (Sum.inr a') (Wset p m) : ℝ) * (p : ℝ)
        ≤ 2 * D := by
      have : ((codegTo (Hg p m) (Sum.inr a) (Sum.inr a') (Wset p m) * p : ℕ) : ℝ)
          ≤ ((2 * p ^ m : ℕ) : ℝ) := by exact_mod_cast hcd
      push_cast [hDcast] at this
      linarith only [this]
    rw [hWcard]
    nlinarith [hcdR, sq_nonneg ((p : ℝ) * ρ)]
  · -- (iv) the apex degree at a vertex of `V`
    intro y hy
    obtain ⟨w, rfl⟩ := mem_Wset.1 hy
    have hdeg : (degTo (Hg p m) (Sum.inl w) (Uset p m) : ℝ) ≤ D := by
      have := degTo_inl_Uset_le (p := p) (m := m) w
      have hcast : ((degTo (Hg p m) (Sum.inl w) (Uset p m) : ℕ) : ℝ) ≤ ((p ^ m : ℕ) : ℝ) := by
        exact_mod_cast this
      rwa [hDcast] at hcast
    rw [hWcard]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h3 hDpos.le, mul_pos hPpos hDpos]
  · -- (v) the minimum degree inside `V`
    intro y hy
    obtain ⟨w, rfl⟩ := mem_Wset.1 hy
    rw [degTo_inl_Wset, hWcard]
    have hone : (1 : ℕ) ≤ 2 * p ^ (m + 1) := by
      have : 1 ≤ p ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
      omega
    have hcast2 : ((2 * p ^ (m + 1) : ℕ) : ℝ) = 2 * (p : ℝ) * D := by push_cast [hD]; ring
    rw [Nat.cast_sub hone, hcast2]
    have hpd : (4 : ℝ) ≤ (p : ℝ) * D := by nlinarith only [hP2, hD2]
    push_cast
    nlinarith

/-! ### The refutation -/

/-- **The counterexample, with the parameters as hypotheses.**  For a prime `p` and reals
`α, ρ` in the window

* `72 √ρ³ p ≤ 1/2`  (so that hypothesis (ii) holds: `|N_a| = |V|/p` is large enough),
* `1 ≤ 2ρ²p²`      (so that hypothesis (iii) holds: `|N_a ∩ N_{a'}| ≤ |V|/p² ≤ 2ρ²|V|`),
* `1 ≤ 8ρp`        (so that hypothesis (iv) holds: `d_H(y,U) ≤ p^m = |V|/(2p) ≤ 4ρ|V|`),
* `α ≤ 1/8` and `4αp < 1`  (so that hypothesis (v) holds and the conclusion fails),

the configuration of this file satisfies hypotheses (i)–(v) of `BKLO.Lemma1010K3` with `k = 2` but
not its conclusion.  The window is nonempty precisely in the sparse regime `ρ < 1/(648k²)`. -/
theorem not_lemma1010K3_of_params {p : ℕ} [Fact (Nat.Prime p)] {α ρ : ℝ}
    (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (h1 : 72 * Real.sqrt ρ ^ 3 * (p : ℝ) ≤ 1 / 2) (h2 : 1 ≤ 2 * ρ ^ 2 * (p : ℝ) ^ 2)
    (h3 : 1 ≤ 8 * ρ * (p : ℝ)) (h4 : α ≤ 1 / 8) (h5 : 4 * α * (p : ℝ) < 1) :
    ¬ Lemma1010K3 := by
  intro hL
  obtain ⟨n₀, hn⟩ := hL α ρ 2 hα hρ hρ1 (by norm_num)
  classical
  -- the instance: `m = n₀ + 1`
  set m : ℕ := n₀ + 1 with hm
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hPpos : (0 : ℝ) < (p : ℝ) := by linarith
  set D : ℝ := (p : ℝ) ^ m with hD
  have hDcast : ((p ^ m : ℕ) : ℝ) = D := by push_cast [hD]; ring
  have hPD : (p : ℝ) ≤ D := by
    rw [hD]
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ m := pow_le_pow_right₀ (by linarith) (by omega)
  have hD2 : (2 : ℝ) ≤ D := le_trans hP2 hPD
  have hDpos : (0 : ℝ) < D := by linarith
  -- the cardinalities
  have hWcard : ((Wset p m).card : ℝ) = 2 * (p : ℝ) * D := by
    rw [card_Wset]; push_cast [hD]; ring
  -- `n₀ ≤ |S|`
  have hn₀ : n₀ ≤ (Finset.univ : Finset (Vx p m)).card := by
    have hlt : n₀ < 2 ^ m := by
      calc n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp2 m
    rw [card_univ_Vx]
    omega
  obtain ⟨hsize, hi, hii, hiii, hiv, hv⟩ :=
    cex_hyps (p := p) (α := α) (ρ := ρ) (m := m) (by omega) hρ h1 h2 h3 h4
  obtain ⟨HV, hHVsub, hHVdec, hHVdeg⟩ :=
    hn (Hg p m) Finset.univ (Uset p m) (Wset p m) hn₀ Hg_loopless Hg_subset_clique
      (Finset.subset_univ _) (Finset.subset_univ _) disjoint_Uset_Wset hsize hi hii hiii hiv hv
  -- the obstruction at the common point of all the hyperplanes
  have hy₀ : (Sum.inl ((0, 0), true) : Vx p m) ∈ Wset p m := inl_mem_Wset _
  have hlow := degTo_le_edeg_of_triDecomp (H := Hg p m) (HV := HV) disjoint_Uset_Wset
    hHVsub hHVdec hy₀
  rw [degTo_inl_Uset_zero] at hlow
  have hlowR : D ≤ (edeg HV (Sum.inl ((0, 0), true)) : ℝ) := by
    have : ((p ^ m : ℕ) : ℝ) ≤ ((edeg HV (Sum.inl ((0, 0), true)) : ℕ) : ℝ) := by
      exact_mod_cast hlow
    rwa [hDcast] at this
  have hup := hHVdeg (Sum.inl ((0, 0), true))
  rw [hWcard] at hup
  nlinarith

/-- **BKLO Lemma 10.10 as transcribed in `BKLO.Lemma1010K3` is false.**

The transcription drops the paper's hierarchy `1/n ≪ ρ ≪ α, 1/k`; the witness above, with
`p = 1000003`, `α = 10⁻⁸`, `ρ = 10⁻⁶` and `k = 2`, satisfies hypotheses (i)–(v) for arbitrarily
large `n` but has a vertex `y₀ ∈ V` lying in every apex neighbourhood, so
`d_H(y₀, U) = |V|/(2p) ≫ 2α|V|`, and `BKLO.degTo_le_edeg_of_triDecomp` rules out the conclusion.

With the hierarchy restored, `BKLO.Lemma1010K3Hier` (in `BKLO/Section1010Sparse.lean`) follows from
the pseudorandom `K₂`-factor core `BKLO.Lemma107K2`. -/
theorem not_lemma1010K3 : ¬ Lemma1010K3 := by
  have hsqrt : Real.sqrt (1 / 10 ^ 6 : ℝ) = 1 / 10 ^ 3 := by
    rw [show (1 / 10 ^ 6 : ℝ) = (1 / 10 ^ 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine not_lemma1010K3_of_params (p := qq) (α := 1 / 10 ^ 8) (ρ := 1 / 10 ^ 6)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num) ?_
  · rw [hsqrt, qq_real]; norm_num
  · rw [qq_real]; norm_num
  · rw [qq_real]; norm_num
  · rw [qq_real]; norm_num

/-! ### Non-vacuity: the hypotheses are satisfiable together with the hierarchy -/

/-- The configuration really does have apex–`V` edges: the zero direction is joined to the point
`((0,0), true)`.  So Lemma 10.10 is not being asked to decompose the empty graph. -/
theorem edgesBtw_nonempty : (edgesBtw (Hg p m) (Uset p m) (Wset p m)).Nonempty := by
  refine ⟨s(Sum.inr 0, Sum.inl ((0, 0), true)), ?_⟩
  rw [edgesBtw, Finset.mem_filter]
  refine ⟨mem_Hg_inr_inl.2 ?_, Sum.inr 0, inr_mem_Uset _, Sum.inl ((0, 0), true),
    inl_mem_Wset _, rfl⟩
  simp [nbrPt, ip]

/-- **The hypotheses of `BKLO.Lemma1010K3Hier` and `BKLO.Lemma107K2` are satisfiable, for
arbitrarily large `|S|`, together with the paper's hierarchy `2kρ ≤ α`.**

With `p = 1000003`, `ρ = 10⁻⁶`, `α = 1/8` and `k = 2` the hyperplane configuration of this file
satisfies the size hypothesis, hypotheses (i)–(v) and `2kρ ≤ α` (here `4·10⁻⁶ ≤ 1/8`), and has a
nonempty apex–`V` edge set.  Hence `BKLO.Lemma1010K3Hier` and the residual clause
`BKLO.Lemma107K2` are not vacuously quantified: their hypotheses have models with `|S|`
arbitrarily large. -/
theorem hyps_nonvacuous (n₀ : ℕ) :
    ∃ m : ℕ, n₀ ≤ (Finset.univ : Finset (Vx qq m)).card
      ∧ (2 : ℝ) * ((2 : ℕ) : ℝ) * (1 / 10 ^ 6 : ℝ) ≤ (1 / 8 : ℝ)
      ∧ ((Finset.univ : Finset (Vx qq m)).card : ℝ) / ((2 : ℕ) : ℝ) - 1 ≤ ((Wset qq m).card : ℝ)
      ∧ (∀ x ∈ Uset qq m, 2 ∣ degTo (Hg qq m) x (Wset qq m))
      ∧ (∀ x ∈ Uset qq m, ∀ y ∈ nbhdIn (Hg qq m) x (Wset qq m),
          (1 / 2 : ℝ) * (degTo (Hg qq m) x (Wset qq m) : ℝ)
              + 18 * ((2 : ℕ) : ℝ) * Real.sqrt (1 / 10 ^ 6 : ℝ) ^ 3 * ((Wset qq m).card : ℝ)
            ≤ (degTo (Hg qq m) y (nbhdIn (Hg qq m) x (Wset qq m)) : ℝ))
      ∧ (∀ x ∈ Uset qq m, ∀ x' ∈ Uset qq m, x ≠ x' →
          (codegTo (Hg qq m) x x' (Wset qq m) : ℝ)
            ≤ 2 * (1 / 10 ^ 6 : ℝ) ^ 2 * ((Wset qq m).card : ℝ))
      ∧ (∀ y ∈ Wset qq m, (degTo (Hg qq m) y (Uset qq m) : ℝ)
          ≤ 2 * ((2 : ℕ) : ℝ) * (1 / 10 ^ 6 : ℝ) * ((Wset qq m).card : ℝ))
      ∧ (∀ y ∈ Wset qq m, ((1 : ℝ) / 2 + 2 * (1 / 8 : ℝ)) * ((Wset qq m).card : ℝ)
          ≤ (degTo (Hg qq m) y (Wset qq m) : ℝ))
      ∧ (edgesBtw (Hg qq m) (Uset qq m) (Wset qq m)).Nonempty := by
  have hsqrt : Real.sqrt (1 / 10 ^ 6 : ℝ) = 1 / 10 ^ 3 := by
    rw [show (1 / 10 ^ 6 : ℝ) = (1 / 10 ^ 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨n₀ + 1, ?_, by norm_num, ?_⟩
  · -- `n₀ ≤ |S|`
    have hlt : n₀ < 2 ^ (n₀ + 1) := by
      calc n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
        _ ≤ 2 ^ (n₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : 2 ^ (n₀ + 1) ≤ qq ^ (n₀ + 1) :=
      Nat.pow_le_pow_left (Fact.out : Nat.Prime qq).two_le _
    rw [card_univ_Vx]
    omega
  · obtain ⟨hsize, hi, hii, hiii, hiv, hv⟩ :=
      cex_hyps (p := qq) (α := 1 / 8) (ρ := 1 / 10 ^ 6) (m := n₀ + 1) (by omega) (by norm_num)
        (by rw [hsqrt, qq_real]; norm_num) (by rw [qq_real]; norm_num)
        (by rw [qq_real]; norm_num) le_rfl
    exact ⟨hsize, hi, hii, hiii, hiv, hv, edgesBtw_nonempty⟩

end BKLO.Cex
