/-
# Nibble — the weighted (fractional) nibble for fractional matchings of positive density

`Nibble.fracNibble_weightedCodegree_on` proves the repaired weighted nibble
(`Nibble.FracNibbleWeightedTheorem`) for fractional matchings that are *near-perfect*: the vertex
loads `∑_{T ∋ v} w T` have to be within `γ` of `1` at all but an `η`-fraction of the vertices.  This
file removes the near-constant-load restriction in the regime where the loads are, on average,
bounded below: the only hypothesis kept is

`ε · |R| ≤ ∑ w`  (equivalently: the average load on the region `R` carrying the edges is `≥ rε`),

for an arbitrary `ε > 0` fixed in advance.  Nothing is assumed about how the loads are distributed;
they may take every value in `[0,1]`.

The proof is a *deterministic padding* argument.  The deficiency `d v = 1 - load v` of every vertex
is absorbed by an auxiliary transversal design on `(r-1)·m` fresh vertices arranged in `r-1` layers
of size `m = ⌈Δ⌉` where `Δ = ∑_{v ∈ R} d v`: the pad edges are `{v} ∪ {(j, f j) : j}` for all
transversals `f`, carrying weight `d v / m^{r-1}` each.  The padded weighting is then *perfect* at
every real vertex and has load `Δ/m ∈ [1-γ, 1]` at every fresh vertex, while the pad contributes at
most `1/m ≤ γ` to any weighted codegree.  So `Nibble.fracNibble_weightedCodegree_on` applies to the
padded hypergraph, and since a matching can contain at most `m` pad edges (they are disjoint and
each meets the first fresh layer), the real edges of the matching already number
`≥ (1-β)(∑w + Δ) - m ≥ (1-β)∑w - (β+γ)Δ`, which is `≥ (1-β')∑w` because `Δ ≤ |R| ≤ ∑w/ε`.

* `Nibble.fracNibble_weightedCodegree_pad` — the main theorem of this file: the padded weighted
  nibble, with the additive error `(Δ+1)` governed by the total deficiency `Δ`.
* `Nibble.fracNibble_weightedCodegree_dense` (`Nibble.FracNibbleMultiScale`) — the error-free
  form in the dense regime `ε|R| ≤ ∑w`, deduced from it.
* `Nibble.FracNibbleWeightedMixed` (`Nibble.FracNibbleMultiScale`) — the remaining obligation (the
  complementary regime, where the loads genuinely live on several scales).

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.WeightedNibbleRestrict

open Finset Hypergraph

namespace Nibble

namespace DensePad

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The embedding of the real vertices into the padded vertex type. -/
def inlEmb (W : Type) (k m : ℕ) : W ↪ W ⊕ (Fin k × Fin m) :=
  ⟨Sum.inl, Sum.inl_injective⟩

@[simp] lemma inlEmb_apply (k m : ℕ) (v : W) : inlEmb W k m v = Sum.inl v := rfl

/-- The pad edge attached to the real vertex `v` and the transversal `f`: it consists of `v`
together with the fresh vertex `(j, f j)` of each layer `j`. -/
def padEdge {k m : ℕ} (v : W) (f : Fin k → Fin m) : Finset (W ⊕ (Fin k × Fin m)) :=
  insert (Sum.inl v) ((Finset.univ : Finset (Fin k)).image (fun j => Sum.inr (j, f j)))

lemma inl_mem_padEdge {k m : ℕ} (x v : W) (f : Fin k → Fin m) :
    (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ padEdge v f ↔ x = v := by
  simp [padEdge]

lemma inr_mem_padEdge {k m : ℕ} (v : W) (f : Fin k → Fin m) (j : Fin k) (a : Fin m) :
    (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ padEdge v f ↔ f j = a := by
  constructor
  · intro h
    simp only [padEdge, Finset.mem_insert, Finset.mem_image] at h
    rcases h with h | ⟨j', _, h⟩
    · exact absurd h (by simp)
    · have h1 : (j', f j') = (j, a) := by
        simpa using h
      have : j' = j := congrArg Prod.fst h1
      subst this
      exact (congrArg Prod.snd h1)
  · intro h
    subst h
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

lemma padEdge_card {k m : ℕ} (v : W) (f : Fin k → Fin m) : (padEdge v f).card = k + 1 := by
  classical
  have hinj : Function.Injective (fun j : Fin k => (Sum.inr (j, f j) : W ⊕ (Fin k × Fin m))) := by
    intro j j' h
    have : (j, f j) = (j', f j') := by simpa using h
    exact congrArg Prod.fst this
  have hnot : (Sum.inl v : W ⊕ (Fin k × Fin m)) ∉
      ((Finset.univ : Finset (Fin k)).image (fun j => Sum.inr (j, f j))) := by
    simp
  rw [padEdge, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma padEdge_ne_map {k m : ℕ} (hk : 0 < k) (v : W) (f : Fin k → Fin m) (S : Finset W) :
    padEdge v f ≠ S.map (inlEmb W k m) := by
  intro h
  have hmem : (Sum.inr (⟨0, hk⟩, f ⟨0, hk⟩) : W ⊕ (Fin k × Fin m)) ∈ padEdge v f :=
    (inr_mem_padEdge v f _ _).mpr rfl
  rw [h] at hmem
  simp [inlEmb] at hmem

/-! ### Counting transversals -/

lemma card_filter_one (k m : ℕ) (j : Fin k) (a : Fin m) :
    ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a)).card * m = m ^ k := by
  classical
  have hset : ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a))
      = Fintype.piFinset (fun i : Fin k => if i = j then ({a} : Finset (Fin m)) else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi; simp [h]
      · simp [hi]
    · intro h
      have := h j
      simpa using this
  rw [hset, Fintype.card_piFinset]
  have hprod : ∏ i : Fin k, (if i = j then ({a} : Finset (Fin m)) else Finset.univ).card
      = ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, m := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) _ (Finset.mem_univ j)]
    have hj : ((if j = j then ({a} : Finset (Fin m)) else Finset.univ)).card = 1 := by simp
    rw [hj, one_mul]
    exact Finset.prod_congr rfl (fun i hi => by
      rw [if_neg (Finset.mem_erase.mp hi).1, Finset.card_univ, Fintype.card_fin])
  have hmk : m ^ k = m * ∏ i ∈ (Finset.univ : Finset (Fin k)).erase j, m := by
    rw [Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) (fun _ => m) (Finset.mem_univ j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, hmk]
  ring

lemma card_filter_two (k m : ℕ) (j j' : Fin k) (hj : j ≠ j') (a a' : Fin m) :
    ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a ∧ f j' = a')).card * m * m
      = m ^ k := by
  classical
  have hset : ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a ∧ f j' = a'))
      = Fintype.piFinset (fun i : Fin k =>
          if i = j then ({a} : Finset (Fin m)) else if i = j' then ({a'} : Finset (Fin m))
          else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi; simp [h.1]
      · by_cases hi' : i = j'
        · subst hi'; simp [hi, h.2]
        · simp [hi, hi']
    · intro h
      have h1 := h j
      have h2 := h j'
      rw [if_pos rfl] at h1
      rw [if_neg (Ne.symm hj), if_pos rfl] at h2
      exact ⟨by simpa using h1, by simpa using h2⟩
  rw [hset, Fintype.card_piFinset]
  set g : Fin k → ℕ := fun i =>
    (if i = j then ({a} : Finset (Fin m)) else if i = j' then ({a'} : Finset (Fin m))
      else Finset.univ).card with hg
  have hj'mem : j' ∈ (Finset.univ : Finset (Fin k)).erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ j'⟩
  have hprod : ∏ i : Fin k, g i = ∏ i ∈ ((Finset.univ : Finset (Fin k)).erase j).erase j', m := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) g (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ g hj'mem]
    have hgj : g j = 1 := by simp [hg]
    have hgj' : g j' = 1 := by simp [hg, Ne.symm hj]
    rw [hgj, hgj', one_mul, one_mul]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have h1 : i ≠ j' := (Finset.mem_erase.mp hi).1
    have h2 : i ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [hg, h1, h2]
  have hmk : m ^ k = m * (m * ∏ i ∈ ((Finset.univ : Finset (Fin k)).erase j).erase j', m) := by
    rw [Finset.mul_prod_erase _ (fun _ => m) hj'mem,
      Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) (fun _ => m) (Finset.mem_univ j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod, hmk]
  ring

/-! ### The padded hypergraph -/

section Construction

variable (H : Finset (Finset W)) (w : Finset W → ℝ) (R : Finset W) (d : W → ℝ) (k m : ℕ)

/-- The index set of the pad edges: a real vertex together with a transversal. -/
def padIdx : Finset (W × (Fin k → Fin m)) := R ×ˢ (Finset.univ : Finset (Fin k → Fin m))

/-- The family of pad edges. -/
def padH : Finset (Finset (W ⊕ (Fin k × Fin m))) :=
  (padIdx R k m).image (fun p => padEdge p.1 p.2)

/-- The padded hypergraph: the original edges, transported by `Sum.inl`, plus the pad edges. -/
def bigH : Finset (Finset (W ⊕ (Fin k × Fin m))) :=
  H.image (fun S => S.map (inlEmb W k m)) ∪ padH R k m

/-- The padded weighting, written as a sum of indicators so that all its sums can be evaluated by
exchanging the order of summation (parallel pad edges, if any, are automatically merged). -/
noncomputable def bigW : Finset (W ⊕ (Fin k × Fin m)) → ℝ := fun T =>
  (∑ p ∈ padIdx R k m, if T = padEdge p.1 p.2 then d p.1 / (m : ℝ) ^ k else 0)
    + ∑ S ∈ H, if T = S.map (inlEmb W k m) then w S else 0

lemma padEdge_mem_bigH {p : W × (Fin k → Fin m)} (hp : p ∈ padIdx R k m) :
    padEdge p.1 p.2 ∈ bigH H R k m :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

lemma map_mem_bigH {S : Finset W} (hS : S ∈ H) : S.map (inlEmb W k m) ∈ bigH H R k m :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩)

lemma bigW_nonneg (hw : ∀ T, 0 ≤ w T) (hd : ∀ v, 0 ≤ d v) (T : Finset (W ⊕ (Fin k × Fin m))) :
    0 ≤ bigW H w R d k m T := by
  classical
  refine add_nonneg (Finset.sum_nonneg (fun p _ => ?_)) (Finset.sum_nonneg (fun S _ => ?_))
  · split
    · exact div_nonneg (hd p.1) (by positivity)
    · exact le_rfl
  · split
    · exact hw S
    · exact le_rfl

/-- **The evaluation lemma.**  Every sum of the padded weighting over a subfamily of the padded
hypergraph splits into an explicit sum over pad indices and an explicit sum over real edges. -/
lemma sum_bigW_filter (P : Finset (W ⊕ (Fin k × Fin m)) → Prop) [DecidablePred P] :
    ∑ T ∈ (bigH H R k m).filter P, bigW H w R d k m T
      = (∑ p ∈ (padIdx R k m).filter (fun p => P (padEdge p.1 p.2)), d p.1 / (m : ℝ) ^ k)
        + ∑ S ∈ H.filter (fun S => P (S.map (inlEmb W k m))), w S := by
  classical
  simp only [bigW]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.sum_ite_eq' ((bigH H R k m).filter P) (padEdge p.1 p.2)]
    by_cases hP : P (padEdge p.1 p.2)
    · rw [if_pos (Finset.mem_filter.mpr ⟨padEdge_mem_bigH H R k m hp, hP⟩), if_pos hP]
    · rw [if_neg (fun hcon => hP (Finset.mem_filter.mp hcon).2), if_neg hP]
  · rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.sum_ite_eq' ((bigH H R k m).filter P) (S.map (inlEmb W k m))]
    by_cases hP : P (S.map (inlEmb W k m))
    · rw [if_pos (Finset.mem_filter.mpr ⟨map_mem_bigH H R k m hS, hP⟩), if_pos hP]
    · rw [if_neg (fun hcon => hP (Finset.mem_filter.mp hcon).2), if_neg hP]

/-! ### Evaluating the pad sums -/

lemma padSum_prod (R' : Finset W) (F : Finset (Fin k → Fin m)) :
    ∑ p ∈ R' ×ˢ F, d p.1 / (m : ℝ) ^ k = (∑ v ∈ R', d v) * (F.card : ℝ) / (m : ℝ) ^ k := by
  classical
  rw [Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_div]
  ring

lemma padIdx_filter_inl (x : W) :
    (padIdx R k m).filter (fun p => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2)
      = (R.filter (fun v => x = v)) ×ˢ (Finset.univ : Finset (Fin k → Fin m)) := by
  classical
  ext p
  simp [padIdx, Finset.mem_filter, Finset.mem_product, inl_mem_padEdge, and_comm]

lemma padIdx_filter_inr (j : Fin k) (a : Fin m) :
    (padIdx R k m).filter (fun p => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2)
      = R ×ˢ ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a)) := by
  classical
  ext p
  simp [padIdx, Finset.mem_filter, Finset.mem_product, inr_mem_padEdge]

lemma padIdx_filter_inl_inl (x z : W) (hxz : x ≠ z) :
    (padIdx R k m).filter (fun p => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2 ∧
        (Sum.inl z : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2) = ∅ := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ h
  rw [inl_mem_padEdge] at h
  rw [inl_mem_padEdge]
  intro h2
  exact hxz (h.trans h2.symm)

lemma padIdx_filter_inl_inr (x : W) (j : Fin k) (a : Fin m) :
    (padIdx R k m).filter (fun p => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2 ∧
        (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2)
      = (R.filter (fun v => x = v)) ×ˢ
          ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a)) := by
  classical
  ext p
  simp [padIdx, Finset.mem_filter, Finset.mem_product, inl_mem_padEdge, inr_mem_padEdge,
    and_assoc, and_comm, and_left_comm]

lemma padIdx_filter_inr_inr_same (j : Fin k) (a a' : Fin m) (h : a ≠ a') :
    (padIdx R k m).filter (fun p => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2 ∧
        (Sum.inr (j, a') : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2) = ∅ := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro _ h1
  rw [inr_mem_padEdge] at h1
  rw [inr_mem_padEdge]
  intro h2
  exact h (h1.symm.trans h2)

lemma padIdx_filter_inr_inr_diff (j j' : Fin k) (hj : j ≠ j') (a a' : Fin m) :
    (padIdx R k m).filter (fun p => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2 ∧
        (Sum.inr (j', a') : W ⊕ (Fin k × Fin m)) ∈ padEdge p.1 p.2)
      = R ×ˢ ((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a ∧ f j' = a')) := by
  classical
  ext p
  simp [padIdx, Finset.mem_filter, Finset.mem_product, inr_mem_padEdge, and_assoc]

/-! ### The loads and the weighted codegrees of the padded weighting -/

lemma card_univ_fun (k m : ℕ) :
    ((Finset.univ : Finset (Fin k → Fin m)).card : ℝ) = (m : ℝ) ^ k := by
  rw [Finset.card_univ]
  simp [Fintype.card_fun]

lemma bigW_total (hm : 0 < m) :
    ∑ T ∈ bigH H R k m, bigW H w R d k m T = (∑ v ∈ R, d v) + ∑ S ∈ H, w S := by
  classical
  have hmk : ((m : ℝ)) ^ k ≠ 0 := by positivity
  have h := sum_bigW_filter H w R d k m (fun _ => True)
  rw [Finset.filter_True] at h
  rw [h, Finset.filter_True, Finset.filter_True]
  congr 1
  rw [padIdx, padSum_prod, card_univ_fun]
  field_simp

lemma bigW_load_inl (hm : 0 < m) (x : W) :
    ∑ T ∈ (bigH H R k m).filter (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T),
        bigW H w R d k m T
      = (if x ∈ R then d x else 0) + ∑ S ∈ H.filter (fun S => x ∈ S), w S := by
  classical
  rw [sum_bigW_filter H w R d k m (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T)]
  congr 1
  · rw [padIdx_filter_inl, padSum_prod]
    have hc := card_univ_fun k m
    rw [hc, Finset.filter_eq]
    have hmk : ((m : ℝ)) ^ k ≠ 0 := by positivity
    by_cases hx : x ∈ R
    · rw [if_pos hx, if_pos hx, Finset.sum_singleton]
      field_simp
    · rw [if_neg hx, if_neg hx]
      simp
  · congr 1
    apply Finset.filter_congr
    intro S _
    simp [inlEmb]

lemma bigW_load_inr (hm : 0 < m) (j : Fin k) (a : Fin m) :
    ∑ T ∈ (bigH H R k m).filter (fun T => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T),
        bigW H w R d k m T
      = (∑ v ∈ R, d v) / (m : ℝ) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [sum_bigW_filter H w R d k m (fun T => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T)]
  have hreal : H.filter (fun S => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ S.map (inlEmb W k m))
      = ∅ := by
    ext S
    simp [inlEmb]
  rw [hreal, Finset.sum_empty, add_zero, padIdx_filter_inr, padSum_prod]
  have hcard : (((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a)).card : ℝ)
      * (m : ℝ) = (m : ℝ) ^ k := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (card_filter_one k m j a)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  rw [div_eq_div_iff (pow_ne_zero _ hmne) hmne, mul_assoc, hcard]

lemma bigW_codeg_inl_inl (x z : W) (hxz : x ≠ z) :
    ∑ T ∈ (bigH H R k m).filter (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T ∧
        (Sum.inl z : W ⊕ (Fin k × Fin m)) ∈ T), bigW H w R d k m T
      = ∑ S ∈ H.filter (fun S => x ∈ S ∧ z ∈ S), w S := by
  classical
  rw [sum_bigW_filter H w R d k m (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T ∧
    (Sum.inl z : W ⊕ (Fin k × Fin m)) ∈ T)]
  rw [padIdx_filter_inl_inl R k m x z hxz, Finset.sum_empty, zero_add]
  congr 1
  apply Finset.filter_congr
  intro S _
  simp [inlEmb]

lemma bigW_codeg_inl_inr (hm : 0 < m) (x : W) (j : Fin k) (a : Fin m) :
    ∑ T ∈ (bigH H R k m).filter (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T ∧
        (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T), bigW H w R d k m T
      = (if x ∈ R then d x else 0) / (m : ℝ) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [sum_bigW_filter H w R d k m (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T ∧
    (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T)]
  have hreal : H.filter (fun S => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ S.map (inlEmb W k m) ∧
      (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ S.map (inlEmb W k m)) = ∅ := by
    ext S
    simp [inlEmb]
  rw [hreal, Finset.sum_empty, add_zero, padIdx_filter_inl_inr, padSum_prod, Finset.filter_eq]
  have hcard : (((Finset.univ : Finset (Fin k → Fin m)).filter (fun f => f j = a)).card : ℝ)
      * (m : ℝ) = (m : ℝ) ^ k := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (card_filter_one k m j a)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  by_cases hx : x ∈ R
  · rw [if_pos hx, if_pos hx, Finset.sum_singleton,
      div_eq_div_iff (pow_ne_zero _ hmne) hmne, mul_assoc, hcard]
  · rw [if_neg hx, if_neg hx]
    simp

lemma bigW_codeg_inr_inr (hm : 0 < m) (j j' : Fin k) (a a' : Fin m) (hne : (j, a) ≠ (j', a'))
    (hd : ∀ v, 0 ≤ d v) :
    ∑ T ∈ (bigH H R k m).filter (fun T => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T ∧
        (Sum.inr (j', a') : W ⊕ (Fin k × Fin m)) ∈ T), bigW H w R d k m T
      ≤ (∑ v ∈ R, d v) / ((m : ℝ) * (m : ℝ)) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hΔ : 0 ≤ ∑ v ∈ R, d v := Finset.sum_nonneg (fun v _ => hd v)
  rw [sum_bigW_filter H w R d k m (fun T => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T ∧
    (Sum.inr (j', a') : W ⊕ (Fin k × Fin m)) ∈ T)]
  have hreal : H.filter (fun S => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ S.map (inlEmb W k m) ∧
      (Sum.inr (j', a') : W ⊕ (Fin k × Fin m)) ∈ S.map (inlEmb W k m)) = ∅ := by
    ext S
    simp [inlEmb]
  rw [hreal, Finset.sum_empty, add_zero]
  by_cases hj : j = j'
  · subst hj
    have ha : a ≠ a' := fun h => hne (by rw [h])
    rw [padIdx_filter_inr_inr_same R k m j a a' ha, Finset.sum_empty]
    positivity
  · rw [padIdx_filter_inr_inr_diff R k m j j' hj a a', padSum_prod]
    have hcard : ((((Finset.univ : Finset (Fin k → Fin m)).filter
        (fun f => f j = a ∧ f j' = a')).card : ℝ)) * (m : ℝ) * (m : ℝ) = (m : ℝ) ^ k := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (card_filter_two k m j j' hj a a')
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (∑ v ∈ R, d v) *
        ((((Finset.univ : Finset (Fin k → Fin m)).filter
          (fun f => f j = a ∧ f j' = a')).card : ℝ)) * ((m : ℝ) * (m : ℝ))
        = (∑ v ∈ R, d v) * (m : ℝ) ^ k := by
      rw [← hcard]; ring
    rw [this]

/-! ### Structure of the padded hypergraph -/

/-- The region carrying the padded hypergraph: the image of `R` together with all fresh vertices. -/
def bigR : Finset (W ⊕ (Fin k × Fin m)) :=
  R.image Sum.inl ∪ (Finset.univ : Finset (Fin k × Fin m)).image Sum.inr

lemma bigH_uniform {r : ℕ} (hr : k + 1 = r) (hunif : IsUniform H r) :
    IsUniform (bigH H R k m) r := by
  classical
  intro T hT
  rw [bigH, Finset.mem_union] at hT
  rcases hT with hT | hT
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    rw [Finset.card_map]
    exact hunif S hS
  · rw [padH, Finset.mem_image] at hT
    obtain ⟨p, _, rfl⟩ := hT
    rw [padEdge_card, hr]

lemma bigH_subset_bigR (hsub : ∀ S ∈ H, S ⊆ R) :
    ∀ T ∈ bigH H R k m, T ⊆ bigR R k m := by
  classical
  intro T hT
  rw [bigH, Finset.mem_union] at hT
  rcases hT with hT | hT
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hsub S hS hy, rfl⟩)
  · rw [padH, Finset.mem_image] at hT
    obtain ⟨p, hp, rfl⟩ := hT
    intro x hx
    rw [padEdge, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨j, _, rfl⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩)
      exact (Finset.mem_product.mp (by rw [padIdx] at hp; exact hp)).1
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)

/-- **Extracting a real matching.**  A matching of the padded hypergraph contains at most `m` pad
edges, because pad edges are pairwise disjoint and each meets the first fresh layer, which has `m`
vertices; all its other edges come from `H`. -/
lemma exists_real_matching (hk : 0 < k) {M' : Finset (Finset (W ⊕ (Fin k × Fin m)))}
    (hM' : IsMatching (bigH H R k m) M') :
    ∃ M : Finset (Finset W), IsMatching H M ∧ (M'.card : ℝ) - (m : ℝ) ≤ (M.card : ℝ) := by
  classical
  set j0 : Fin k := ⟨0, hk⟩ with hj0
  set L0 : Finset (W ⊕ (Fin k × Fin m)) :=
    (Finset.univ : Finset (Fin m)).image (fun a => Sum.inr (j0, a)) with hL0
  have hinj : Function.Injective (fun a : Fin m => (Sum.inr (j0, a) : W ⊕ (Fin k × Fin m))) := by
    intro a b hab
    have : (j0, a) = (j0, b) := by simpa using hab
    exact congrArg Prod.snd this
  have hL0card : L0.card = m := by
    rw [hL0, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set Mpad := M'.filter (fun T => (T ∩ L0).Nonempty) with hMpad
  set Mreal := M'.filter (fun T => ¬ (T ∩ L0).Nonempty) with hMreal
  have hsplit : Mpad.card + Mreal.card = M'.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  have hpadle : Mpad.card ≤ m := by
    have hdisj : ∀ T ∈ Mpad, ∀ T' ∈ Mpad, T ≠ T' → Disjoint (T ∩ L0) (T' ∩ L0) := by
      intro T hT T' hT' hne
      exact ((hM'.disjoint T (Finset.mem_filter.mp hT).1 T'
        (Finset.mem_filter.mp hT').1 hne).mono Finset.inter_subset_left Finset.inter_subset_left)
    have h1 : Mpad.card ≤ ∑ T ∈ Mpad, (T ∩ L0).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun T hT => Finset.card_pos.mpr (Finset.mem_filter.mp hT).2)
    have h2 : ∑ T ∈ Mpad, (T ∩ L0).card = (Mpad.biUnion (fun T => T ∩ L0)).card :=
      (Finset.card_biUnion hdisj).symm
    have h3 : (Mpad.biUnion (fun T => T ∩ L0)).card ≤ L0.card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr (fun T _ => Finset.inter_subset_right))
    omega
  set M := H.filter (fun S => S.map (inlEmb W k m) ∈ M') with hM
  have hMmatch : IsMatching H M := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro S hS S' hS' hne
    have h1 : S.map (inlEmb W k m) ∈ M' := (Finset.mem_filter.mp hS).2
    have h2 : S'.map (inlEmb W k m) ∈ M' := (Finset.mem_filter.mp hS').2
    have h3 : S.map (inlEmb W k m) ≠ S'.map (inlEmb W k m) := by
      intro hcon
      exact hne (Finset.map_injective _ hcon)
    exact (Finset.disjoint_map (inlEmb W k m)).mp (hM'.disjoint _ h1 _ h2 h3)
  have hreal_sub : Mreal ⊆ M.image (fun S => S.map (inlEmb W k m)) := by
    intro T hT
    rw [hMreal, Finset.mem_filter] at hT
    obtain ⟨hTM', hTL0⟩ := hT
    have hTbig := hM'.subset hTM'
    rw [bigH, Finset.mem_union] at hTbig
    rcases hTbig with h | h
    · obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, by rw [hSeq]; exact hTM'⟩, hSeq⟩
    · exfalso
      rw [padH, Finset.mem_image] at h
      obtain ⟨p, _, rfl⟩ := h
      refine hTL0 ⟨Sum.inr (j0, p.2 j0), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact (inr_mem_padEdge p.1 p.2 j0 (p.2 j0)).mpr rfl
      · exact Finset.mem_image.mpr ⟨p.2 j0, Finset.mem_univ _, rfl⟩
  have hcard : Mreal.card ≤ M.card := by
    refine le_trans (Finset.card_le_card hreal_sub) (le_of_eq ?_)
    exact Finset.card_image_of_injective _ (Finset.map_injective _)
  refine ⟨M, hMmatch, ?_⟩
  have : M'.card ≤ m + M.card := by omega
  have := (Nat.cast_le (α := ℝ)).mpr this
  push_cast at this
  linarith

end Construction

end DensePad

open DensePad in
/-- The total deficiency of the fractional matching `w` on the region `R`: how much weight would
have to be added to saturate every vertex of `R`. -/
noncomputable def defic {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W))
    (w : Finset W → ℝ) (R : Finset W) : ℝ :=
  ∑ v ∈ R, (1 - ∑ T ∈ H.filter (fun T => v ∈ T), w T)

open DensePad in
/-- **The padded weighted nibble.**  With no hypothesis on the distribution of the loads: if the
total deficiency `Δ` of `w` on `R` is at least `1/γ`, then `H` has a matching of size at least
`(1-β)(∑w + Δ) - (Δ+1)`.  The proof pads `w` up to a perfect fractional matching on `⌈Δ⌉` extra
layers of fresh vertices and applies `Nibble.fracNibble_weightedCodegree_on`; a matching of the
padded hypergraph uses at most `⌈Δ⌉ ≤ Δ+1` pad edges. -/
theorem fracNibble_weightedCodegree_pad (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : Finset (Finset W)) (w : Finset W → ℝ)
        (R : Finset W),
        IsUniform H r →
        (∀ T ∈ H, T ⊆ R) →
        (∀ T, 0 ≤ w T) →
        (∀ v : W, ∑ T ∈ H.filter (fun T => v ∈ T), w T ≤ 1) →
        (∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        1 / γ ≤ defic H w R →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * ((∑ T ∈ H, w T) + defic H w R) - (defic H w R + 1) ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η, hη, hmain⟩ := fracNibble_weightedCodegree_on r hr β hβ
  refine ⟨min γ₀ 1, lt_min hγ₀ one_pos, ?_⟩
  intro W _ _ H w R hunif hsub hwnn hload hcod hΔ
  have hγ₀' : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hcod₀ : ∀ x z : W, x ≠ z → ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ₀ :=
    fun x z hxz => le_trans (hcod x z hxz) hγ₀'
  -- the deficiency
  set L : W → ℝ := fun v => ∑ T ∈ H.filter (fun T => v ∈ T), w T with hL
  set d : W → ℝ := fun v => 1 - L v with hd
  have hdnn : ∀ v, 0 ≤ d v := fun v => by rw [hd]; simp only; linarith only [hload v]
  have hdle : ∀ v, d v ≤ 1 := by
    intro v
    have : 0 ≤ L v := Finset.sum_nonneg (fun T _ => hwnn T)
    rw [hd]; simp only; linarith
  set Δ : ℝ := defic H w R with hΔdef
  have hΔeq : Δ = ∑ v ∈ R, d v := by rw [hΔdef, defic, hd, hL]
  have hγinv : 1 / min γ₀ 1 ≤ Δ := hΔ
  have hmin_pos : (0 : ℝ) < min γ₀ 1 := lt_min hγ₀ one_pos
  have hΔpos : 0 < Δ := lt_of_lt_of_le (by positivity) hγinv
  have hΔγ : 1 / Δ ≤ γ₀ := by
    rw [div_le_iff₀ hΔpos]
    rw [div_le_iff₀ hmin_pos] at hγinv
    nlinarith [min_le_left γ₀ 1]
  -- the fresh layers
  set k : ℕ := r - 1 with hkdef
  have hk : 0 < k := by omega
  have hkr : k + 1 = r := by omega
  set m : ℕ := ⌈Δ⌉₊ with hmdef
  have hm : 0 < m := Nat.ceil_pos.mpr hΔpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hΔm : Δ ≤ (m : ℝ) := Nat.le_ceil Δ
  have hmΔ : (m : ℝ) ≤ Δ + 1 := le_of_lt (Nat.ceil_lt_add_one hΔpos.le)
  have hinvm : 1 / (m : ℝ) ≤ γ₀ := le_trans (by
    apply one_div_le_one_div_of_le hΔpos hΔm) hΔγ
  -- the padded data
  set H' := bigH H R k m with hH'
  set w' := bigW H w R d k m with hw'
  have hunif' : IsUniform H' r := bigH_uniform H R k m hkr hunif
  have hsub' : ∀ T ∈ H', T ⊆ bigR R k m := bigH_subset_bigR H R k m hsub
  have hwnn' : ∀ T, 0 ≤ w' T := bigW_nonneg H w R d k m hwnn hdnn
  -- loads
  have hload_inl : ∀ x : W, ∑ T ∈ H'.filter (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T), w' T
      = (if x ∈ R then d x else 0) + L x := bigW_load_inl H w R d k m hm
  have hload_inr : ∀ (j : Fin k) (a : Fin m),
      ∑ T ∈ H'.filter (fun T => (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T), w' T = Δ / (m : ℝ) := by
    intro j a
    rw [bigW_load_inr H w R d k m hm j a, hΔeq]
  have hload' : ∀ v : W ⊕ (Fin k × Fin m), ∑ T ∈ H'.filter (fun T => v ∈ T), w' T ≤ 1 := by
    rintro (x | ⟨j, a⟩)
    · rw [hload_inl x]
      by_cases hx : x ∈ R
      · rw [if_pos hx, hd]; simp
      · rw [if_neg hx, zero_add]; exact hload x
    · rw [hload_inr j a, div_le_one hmR]; exact hΔm
  have hloadlow : ∀ v : W ⊕ (Fin k × Fin m), v ∈ bigR R k m → v ∉ (∅ : Finset (W ⊕ (Fin k × Fin m)))
      → 1 - γ₀ ≤ ∑ T ∈ H'.filter (fun T => v ∈ T), w' T := by
    rintro (x | ⟨j, a⟩) hv _
    · have hx : x ∈ R := by
        rw [bigR, Finset.mem_union] at hv
        rcases hv with h | h
        · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
          cases hxy; exact hy
        · obtain ⟨y, _, hxy⟩ := Finset.mem_image.mp h
          exact absurd hxy (by simp)
      rw [hload_inl x, if_pos hx, hd]
      simp only
      linarith
    · rw [hload_inr j a, le_div_iff₀ hmR]
      have h1 : (1 : ℝ) ≤ γ₀ * (m : ℝ) := by
        have := hinvm
        rw [div_le_iff₀ hmR] at this
        linarith
      linarith
  -- codegrees
  have hcodeg' : ∀ x z : W ⊕ (Fin k × Fin m), x ≠ z →
      ∑ T ∈ H'.filter (fun T => x ∈ T ∧ z ∈ T), w' T ≤ γ₀ := by
    have hswap : ∀ (x z : W ⊕ (Fin k × Fin m)),
        ∑ T ∈ H'.filter (fun T => x ∈ T ∧ z ∈ T), w' T
          = ∑ T ∈ H'.filter (fun T => z ∈ T ∧ x ∈ T), w' T := by
      intro x z
      congr 1
      apply Finset.filter_congr
      intro T _
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have hmix : ∀ (x : W) (j : Fin k) (a : Fin m),
        ∑ T ∈ H'.filter (fun T => (Sum.inl x : W ⊕ (Fin k × Fin m)) ∈ T ∧
          (Sum.inr (j, a) : W ⊕ (Fin k × Fin m)) ∈ T), w' T ≤ γ₀ := by
      intro x j a
      rw [bigW_codeg_inl_inr H w R d k m hm x j a]
      have h1 : (if x ∈ R then d x else 0) ≤ 1 := by
        by_cases hx : x ∈ R
        · rw [if_pos hx]; exact hdle x
        · rw [if_neg hx]; norm_num
      have h2 : (0 : ℝ) ≤ (if x ∈ R then d x else 0) := by
        by_cases hx : x ∈ R
        · rw [if_pos hx]; exact hdnn x
        · rw [if_neg hx]
      calc (if x ∈ R then d x else 0) / (m : ℝ) ≤ 1 / (m : ℝ) :=
            div_le_div_of_nonneg_right h1 hmR.le
        _ ≤ γ₀ := hinvm
    rintro (x | ⟨j, a⟩) (z | ⟨j', a'⟩) hxz
    · rw [bigW_codeg_inl_inl H w R d k m x z (fun h => hxz (by rw [h]))]
      exact hcod₀ x z (fun h => hxz (by rw [h]))
    · exact hmix x j' a'
    · rw [hswap]
      exact hmix z j a
    · have hne : (j, a) ≠ (j', a') := fun h => hxz (by rw [h])
      refine le_trans (bigW_codeg_inr_inr H w R d k m hm j j' a a' hne hdnn) ?_
      rw [← hΔeq]
      have : Δ / ((m : ℝ) * (m : ℝ)) ≤ (m : ℝ) / ((m : ℝ) * (m : ℝ)) := by
        apply div_le_div_of_nonneg_right hΔm (by positivity) |>.trans_eq rfl
      refine le_trans this ?_
      rw [show (m : ℝ) / ((m : ℝ) * (m : ℝ)) = 1 / (m : ℝ) by field_simp]
      exact hinvm
  -- apply the near-perfect weighted nibble to the padded hypergraph
  obtain ⟨M', hM', -, hM'card⟩ := hmain H' w' (bigR R k m) ∅ hunif' hsub' hwnn' hload'
    hloadlow (by simp; positivity) hcodeg'
  obtain ⟨M, hM, hMcard⟩ := exists_real_matching H R k m hk hM'
  refine ⟨M, hM, ?_⟩
  have htot : ∑ T ∈ H', w' T = Δ + ∑ S ∈ H, w S := by
    rw [hH', hw', bigW_total H w R d k m hm, hΔeq]
  rw [htot] at hM'card
  have h1 : (1 - β) * (Δ + ∑ S ∈ H, w S) - (m : ℝ) ≤ (M.card : ℝ) := by linarith
  have h2 : (1 - β) * ((∑ T ∈ H, w T) + Δ) = (1 - β) * (Δ + ∑ S ∈ H, w S) := by ring
  rw [h2]
  linarith

end Nibble
