import Mathlib

/-!
# RC01: the token extension used to prove the marked-quota nibble gate

The marked-quota gate asks for a *single* matching which simultaneously keeps
the total fractional mass of an `r`-uniform system `H` and the fractional mass
of a marked subfamily `A ⊆ H`.  Paper III's near-perfect nibble only returns a
lower bound on the **cardinality** of the matching, so on its own it cannot see
the marked class.

The device implemented in this file converts the marked quota into a
cardinality statement.  Each edge of `H` is extended by exactly one extra
*token* vertex, drawn from a pool `Fin p` for the unmarked edges `H \ A` and
from a disjoint pool `Fin q` for the marked edges `A`, the weight of an edge
being spread uniformly over its pool.  Three things happen at once:

* the extended system is `(r+1)`-uniform and carries the *same* total mass and
  the *same* vertex loads on the old vertices;
* the token vertices have load `(∑_{H \ A} w)/p` resp. `(∑_A w)/q`, so choosing
  the pool sizes `p ≈ ∑_{H \ A} w`, `q ≈ ∑_A w` keeps the extended system
  near-perfect;
* every matching of the extended system uses each token at most once, so it
  contains **at most `p` unmarked edges**.

Hence a matching of the extended system of almost maximal cardinality must
contain almost all of the marked mass, which is exactly the marked quota.

This file contains only the combinatorics of the extension: the definitions,
the projection back to `W`, and the master reindexing lemma for sums over the
extended system.  The gate itself is proved in `PaperIV.MarkedQuotaGate`.
-/

namespace PaperIV.MarkedQuotaTokens

open Finset

variable {W : Type} [DecidableEq W]

/-- The vertex type of the token extension: the old vertices together with two
disjoint token pools. -/
abbrev Vtx (W : Type) (p q : ℕ) : Type := W ⊕ (Fin p ⊕ Fin q)

variable {p q : ℕ}

/-- The extension of an edge `T ⊆ W` by one token vertex `t`. -/
def ext (T : Finset W) (t : Fin p ⊕ Fin q) : Finset (Vtx W p q) :=
  insert (Sum.inr t) (T.image Sum.inl)

/-- The projection of an extended edge back to `W`. -/
noncomputable def proj (S : Finset (Vtx W p q)) : Finset W :=
  S.preimage Sum.inl Sum.inl_injective.injOn

omit [DecidableEq W] in
@[simp] lemma mem_proj {S : Finset (Vtx W p q)} {v : W} :
    v ∈ proj S ↔ (Sum.inl v : Vtx W p q) ∈ S := by
  simp [proj]

@[simp] lemma inl_mem_ext {T : Finset W} {t : Fin p ⊕ Fin q} {v : W} :
    (Sum.inl v : Vtx W p q) ∈ ext T t ↔ v ∈ T := by
  simp [ext]

@[simp] lemma inr_mem_ext {T : Finset W} {t s : Fin p ⊕ Fin q} :
    (Sum.inr s : Vtx W p q) ∈ ext T t ↔ s = t := by
  simp [ext]

@[simp] lemma proj_ext (T : Finset W) (t : Fin p ⊕ Fin q) :
    proj (ext T t) = T := by
  ext v; simp

lemma card_ext (T : Finset W) (t : Fin p ⊕ Fin q) :
    (ext T t).card = T.card + 1 := by
  rw [ext, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ Sum.inl_injective]

lemma ext_inj {T T' : Finset W} {t t' : Fin p ⊕ Fin q}
    (h : (ext T t : Finset (Vtx W p q)) = ext T' t') : T = T' ∧ t = t' := by
  constructor
  · have := congrArg (proj (p := p) (q := q)) h
    simpa using this
  · have ht : (Sum.inr t : Vtx W p q) ∈ ext T' t' := by
      rw [← h]; simp
    simpa using ht

/-- Whether an extended edge carries a token from the *unmarked* pool. -/
def hasPTok (S : Finset (Vtx W p q)) : Bool :=
  decide (∃ i : Fin p, (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S)

@[simp] lemma hasPTok_ext_inl (p q : ℕ) (T : Finset W) (i : Fin p) :
    hasPTok (ext T (Sum.inl i) : Finset (Vtx W p q)) = true := by
  simp [hasPTok]

@[simp] lemma hasPTok_ext_inr (p q : ℕ) (T : Finset W) (j : Fin q) :
    hasPTok (ext T (Sum.inr j) : Finset (Vtx W p q)) = false := by
  simp [hasPTok]

/-- The weight carried by an extended edge: the weight of its projection,
spread uniformly over the relevant token pool. -/
noncomputable def bigW (w : Finset W → ℝ) (p q : ℕ) (S : Finset (Vtx W p q)) : ℝ :=
  if hasPTok S then w (proj S) / (p : ℝ) else w (proj S) / (q : ℝ)

@[simp] lemma bigW_ext_inl (w : Finset W → ℝ) (p q : ℕ) (T : Finset W) (i : Fin p) :
    bigW w p q (ext T (Sum.inl i) : Finset (Vtx W p q)) = w T / (p : ℝ) := by
  simp [bigW]

@[simp] lemma bigW_ext_inr (w : Finset W → ℝ) (p q : ℕ) (T : Finset W) (j : Fin q) :
    bigW w p q (ext T (Sum.inr j) : Finset (Vtx W p q)) = w T / (q : ℝ) := by
  simp [bigW]

lemma bigW_nonneg {w : Finset W → ℝ} (hw : ∀ T, 0 ≤ w T) (p q : ℕ)
    (S : Finset (Vtx W p q)) : 0 ≤ bigW w p q S := by
  unfold bigW
  split <;> exact div_nonneg (hw _) (Nat.cast_nonneg _)

/-- The index set of the extended system: unmarked edges paired with unmarked
tokens, marked edges paired with marked tokens. -/
def idx (H A : Finset (Finset W)) (p q : ℕ) :
    Finset (Finset W × (Fin p ⊕ Fin q)) :=
  ((H \ A) ×ˢ ((Finset.univ : Finset (Fin p)).image Sum.inl)) ∪
    (A ×ˢ ((Finset.univ : Finset (Fin q)).image Sum.inr))

/-- The extended hypergraph. -/
def bigH (H A : Finset (Finset W)) (p q : ℕ) : Finset (Finset (Vtx W p q)) :=
  (idx H A p q).image (fun x => ext x.1 x.2)

lemma mem_idx {H A : Finset (Finset W)} {x : Finset W × (Fin p ⊕ Fin q)} :
    x ∈ idx H A p q ↔
      ((x.1 ∈ H ∧ x.1 ∉ A) ∧ ∃ i : Fin p, x.2 = Sum.inl i) ∨
        (x.1 ∈ A ∧ ∃ j : Fin q, x.2 = Sum.inr j) := by
  cases x with
  | mk T t =>
    simp [idx, Finset.mem_union, Finset.mem_product, Finset.mem_sdiff, eq_comm]

lemma mem_bigH {H A : Finset (Finset W)} {S : Finset (Vtx W p q)} :
    S ∈ bigH H A p q ↔
      (∃ T ∈ H, T ∉ A ∧ ∃ i : Fin p, S = ext T (Sum.inl i)) ∨
        (∃ T ∈ A, ∃ j : Fin q, S = ext T (Sum.inr j)) := by
  constructor
  · intro hS
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hS
    rcases mem_idx.1 hx with ⟨⟨hH, hA⟩, i, hi⟩ | ⟨hA, j, hj⟩
    · exact Or.inl ⟨x.1, hH, hA, i, by rw [hi]⟩
    · exact Or.inr ⟨x.1, hA, j, by rw [hj]⟩
  · rintro (⟨T, hH, hA, i, rfl⟩ | ⟨T, hA, j, rfl⟩)
    · exact Finset.mem_image.2 ⟨(T, Sum.inl i), mem_idx.2 (Or.inl ⟨⟨hH, hA⟩, i, rfl⟩), rfl⟩
    · exact Finset.mem_image.2 ⟨(T, Sum.inr j), mem_idx.2 (Or.inr ⟨hA, j, rfl⟩), rfl⟩

/-- Every extended edge projects into `H`, and its projection is marked exactly
when its token is marked. -/
lemma proj_mem_of_mem_bigH {H A : Finset (Finset W)} (hAH : A ⊆ H)
    {S : Finset (Vtx W p q)} (hS : S ∈ bigH H A p q) : proj S ∈ H := by
  rcases mem_bigH.1 hS with ⟨T, hH, _, i, rfl⟩ | ⟨T, hA, j, rfl⟩
  · simpa using hH
  · simpa using hAH hA

/-- The master reindexing lemma for sums over the extended system. -/
lemma sum_bigH (H A : Finset (Finset W)) (p q : ℕ) (g : Finset (Vtx W p q) → ℝ) :
    ∑ S ∈ bigH H A p q, g S
      = (∑ T ∈ H \ A, ∑ i : Fin p, g (ext T (Sum.inl i)))
        + ∑ T ∈ A, ∑ j : Fin q, g (ext T (Sum.inr j)) := by
  classical
  have hinj : ∀ x ∈ idx H A p q, ∀ y ∈ idx H A p q,
      (fun x : Finset W × (Fin p ⊕ Fin q) => ext x.1 x.2) x =
        (fun x : Finset W × (Fin p ⊕ Fin q) => ext x.1 x.2) y → x = y := by
    intro x _ y _ h
    obtain ⟨h1, h2⟩ := ext_inj h
    exact Prod.ext h1 h2
  rw [bigH, Finset.sum_image hinj]
  have hdisj : Disjoint ((H \ A) ×ˢ ((Finset.univ : Finset (Fin p)).image Sum.inl))
      (A ×ˢ ((Finset.univ : Finset (Fin q)).image Sum.inr)) := by
    rw [Finset.disjoint_left]
    rintro ⟨T, t⟩ h1 h2
    have hT1 : T ∈ H \ A := (Finset.mem_product.1 h1).1
    have hT2 : T ∈ A := (Finset.mem_product.1 h2).1
    exact (Finset.mem_sdiff.1 hT1).2 hT2
  rw [idx, Finset.sum_union hdisj, Finset.sum_product, Finset.sum_product]
  congr 1
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_image (fun i _ j _ h => Sum.inl_injective h)]
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_image (fun i _ j _ h => Sum.inr_injective h)]

/-- The extended system is `(r+1)`-uniform whenever `H` is `r`-uniform. -/
lemma card_of_mem_bigH {H A : Finset (Finset W)} {r : ℕ}
    (huni : ∀ T ∈ H, T.card = r) (hA : A ⊆ H) {S : Finset (Vtx W p q)}
    (hS : S ∈ bigH H A p q) : S.card = r + 1 := by
  rcases mem_bigH.1 hS with ⟨T, hH, _, i, rfl⟩ | ⟨T, hAT, j, rfl⟩
  · rw [card_ext, huni T hH]
  · rw [card_ext, huni T (hA hAT)]

/-! ## Masses, loads and codegrees of the extended system -/

section Analytic

variable (H A : Finset (Finset W)) (w : Finset W → ℝ) (p q : ℕ)

/-- Reindexing of a filtered sum over the extended system. -/
lemma sum_filter_bigH (P : Finset (Vtx W p q) → Prop) [DecidablePred P] :
    ∑ S ∈ (bigH H A p q).filter P, bigW w p q S
      = (∑ T ∈ H \ A, ∑ i : Fin p, if P (ext T (Sum.inl i)) then w T / (p : ℝ) else 0)
        + ∑ T ∈ A, ∑ j : Fin q, if P (ext T (Sum.inr j)) then w T / (q : ℝ) else 0 := by
  classical
  rw [Finset.sum_filter, sum_bigH H A p q (fun S => if P S then bigW w p q S else 0)]
  simp only [bigW_ext_inl, bigW_ext_inr]

private lemma sum_const_div (n : ℕ) (hn : n ≠ 0) (c : ℝ) :
    (∑ _i : Fin n, c / (n : ℝ)) = c := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma sum_const_div_ite (n : ℕ) (hn : n ≠ 0) (c : ℝ) (P : Prop) [Decidable P] :
    (∑ _i : Fin n, if P then c / (n : ℝ) else 0) = if P then c else 0 := by
  by_cases h : P <;> simp [h, sum_const_div n hn]

/-- The extension preserves the total mass. -/
lemma bigH_mass (hp : p ≠ 0) (hq : q ≠ 0) :
    ∑ S ∈ bigH H A p q, bigW w p q S = (∑ T ∈ H \ A, w T) + ∑ T ∈ A, w T := by
  rw [sum_bigH H A p q (bigW w p q)]
  congr 1
  · refine Finset.sum_congr rfl fun T _ => ?_
    simpa using sum_const_div p hp (w T)
  · refine Finset.sum_congr rfl fun T _ => ?_
    simpa using sum_const_div q hq (w T)

/-- The extension preserves the loads of the old vertices. -/
lemma bigH_load_inl (hAH : A ⊆ H) (hp : p ≠ 0) (hq : q ≠ 0) (v : W) :
    ∑ S ∈ (bigH H A p q).filter (fun S => (Sum.inl v : Vtx W p q) ∈ S), bigW w p q S
      = ∑ T ∈ H.filter (fun T => v ∈ T), w T := by
  classical
  rw [sum_filter_bigH H A w p q (fun S => (Sum.inl v : Vtx W p q) ∈ S), Finset.sum_filter]
  simp only [inl_mem_ext]
  rw [Finset.sum_congr rfl (fun T _ => sum_const_div_ite p hp (w T) (v ∈ T)),
    Finset.sum_congr rfl (fun T _ => sum_const_div_ite q hq (w T) (v ∈ T))]
  exact Finset.sum_sdiff hAH

/-- The extension preserves the weighted codegrees of the old vertices. -/
lemma bigH_codeg_inl_inl (hAH : A ⊆ H) (hp : p ≠ 0) (hq : q ≠ 0) (x z : W) :
    ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inl z : Vtx W p q) ∈ S), bigW w p q S
      = ∑ T ∈ H.filter (fun T => x ∈ T ∧ z ∈ T), w T := by
  classical
  rw [sum_filter_bigH H A w p q
      (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inl z : Vtx W p q) ∈ S), Finset.sum_filter]
  simp only [inl_mem_ext]
  rw [Finset.sum_congr rfl (fun T _ => sum_const_div_ite p hp (w T) (x ∈ T ∧ z ∈ T)),
    Finset.sum_congr rfl (fun T _ => sum_const_div_ite q hq (w T) (x ∈ T ∧ z ∈ T))]
  exact Finset.sum_sdiff hAH

/-- The load of an unmarked token vertex is the unmarked mass divided by the
size of the unmarked pool. -/
lemma bigH_load_tokP (i : Fin p) :
    ∑ S ∈ (bigH H A p q).filter (fun S => (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S),
        bigW w p q S = (∑ T ∈ H \ A, w T) / (p : ℝ) := by
  classical
  rw [sum_filter_bigH H A w p q (fun S => (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S)]
  have h1 : ∀ T : Finset W,
      (∑ i' : Fin p, if (Sum.inr (Sum.inl i) : Vtx W p q) ∈ ext T (Sum.inl i')
        then w T / (p : ℝ) else 0) = w T / (p : ℝ) := by
    intro T
    simp only [inr_mem_ext, Sum.inl.injEq]
    simp
  have h2 : ∀ T : Finset W,
      (∑ j : Fin q, if (Sum.inr (Sum.inl i) : Vtx W p q) ∈ ext T (Sum.inr j)
        then w T / (q : ℝ) else 0) = 0 := by
    intro T; simp
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_congr rfl (fun T _ => h2 T)]
  simp [Finset.sum_div]

/-- The load of a marked token vertex is the marked mass divided by the size of
the marked pool. -/
lemma bigH_load_tokQ (j : Fin q) :
    ∑ S ∈ (bigH H A p q).filter (fun S => (Sum.inr (Sum.inr j) : Vtx W p q) ∈ S),
        bigW w p q S = (∑ T ∈ A, w T) / (q : ℝ) := by
  classical
  rw [sum_filter_bigH H A w p q (fun S => (Sum.inr (Sum.inr j) : Vtx W p q) ∈ S)]
  have h1 : ∀ T : Finset W,
      (∑ i : Fin p, if (Sum.inr (Sum.inr j) : Vtx W p q) ∈ ext T (Sum.inl i)
        then w T / (p : ℝ) else 0) = 0 := by
    intro T; simp
  have h2 : ∀ T : Finset W,
      (∑ j' : Fin q, if (Sum.inr (Sum.inr j) : Vtx W p q) ∈ ext T (Sum.inr j')
        then w T / (q : ℝ) else 0) = w T / (q : ℝ) := by
    intro T
    simp only [inr_mem_ext, Sum.inr.injEq]
    simp
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_congr rfl (fun T _ => h2 T)]
  simp [Finset.sum_div]

/-- Mixed codegrees: an old vertex and an unmarked token. -/
lemma bigH_codeg_inl_tokP (i : Fin p) (x : W) :
    ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S),
        bigW w p q S = (∑ T ∈ (H \ A).filter (fun T => x ∈ T), w T) / (p : ℝ) := by
  classical
  rw [sum_filter_bigH H A w p q
      (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inl i) : Vtx W p q) ∈ S)]
  have h1 : ∀ T : Finset W,
      (∑ i' : Fin p, if (Sum.inl x : Vtx W p q) ∈ ext T (Sum.inl i') ∧
          (Sum.inr (Sum.inl i) : Vtx W p q) ∈ ext T (Sum.inl i')
        then w T / (p : ℝ) else 0) = if x ∈ T then w T / (p : ℝ) else 0 := by
    intro T
    simp only [inl_mem_ext, inr_mem_ext, Sum.inl.injEq]
    by_cases hx : x ∈ T
    · simp [hx]
    · simp [hx]
  have h2 : ∀ T : Finset W,
      (∑ j : Fin q, if (Sum.inl x : Vtx W p q) ∈ ext T (Sum.inr j) ∧
          (Sum.inr (Sum.inl i) : Vtx W p q) ∈ ext T (Sum.inr j)
        then w T / (q : ℝ) else 0) = 0 := by
    intro T; simp
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_congr rfl (fun T _ => h2 T),
    Finset.sum_filter, Finset.sum_div]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ T <;> simp [hx]

/-- Mixed codegrees: an old vertex and a marked token. -/
lemma bigH_codeg_inl_tokQ (j : Fin q) (x : W) :
    ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inr j) : Vtx W p q) ∈ S),
        bigW w p q S = (∑ T ∈ A.filter (fun T => x ∈ T), w T) / (q : ℝ) := by
  classical
  rw [sum_filter_bigH H A w p q
      (fun S => (Sum.inl x : Vtx W p q) ∈ S ∧ (Sum.inr (Sum.inr j) : Vtx W p q) ∈ S)]
  have h1 : ∀ T : Finset W,
      (∑ i : Fin p, if (Sum.inl x : Vtx W p q) ∈ ext T (Sum.inl i) ∧
          (Sum.inr (Sum.inr j) : Vtx W p q) ∈ ext T (Sum.inl i)
        then w T / (p : ℝ) else 0) = 0 := by
    intro T; simp
  have h2 : ∀ T : Finset W,
      (∑ j' : Fin q, if (Sum.inl x : Vtx W p q) ∈ ext T (Sum.inr j') ∧
          (Sum.inr (Sum.inr j) : Vtx W p q) ∈ ext T (Sum.inr j')
        then w T / (q : ℝ) else 0) = if x ∈ T then w T / (q : ℝ) else 0 := by
    intro T
    simp only [inl_mem_ext, inr_mem_ext, Sum.inr.injEq]
    by_cases hx : x ∈ T
    · simp [hx]
    · simp [hx]
  rw [Finset.sum_congr rfl (fun T _ => h1 T), Finset.sum_congr rfl (fun T _ => h2 T),
    Finset.sum_filter, Finset.sum_div]
  simp only [Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hx : x ∈ T <;> simp [hx]

/-- Two distinct token vertices never lie in a common extended edge. -/
lemma bigH_codeg_tok_tok (t t' : Fin p ⊕ Fin q) (htt : t ≠ t') :
    ∑ S ∈ (bigH H A p q).filter
        (fun S => (Sum.inr t : Vtx W p q) ∈ S ∧ (Sum.inr t' : Vtx W p q) ∈ S),
        bigW w p q S = 0 := by
  classical
  rw [sum_filter_bigH H A w p q
      (fun S => (Sum.inr t : Vtx W p q) ∈ S ∧ (Sum.inr t' : Vtx W p q) ∈ S)]
  simp only [inr_mem_ext]
  have h1 : ∀ u : Fin p ⊕ Fin q, (t = u ∧ t' = u) = False := by
    intro u
    simp only [eq_iff_iff, iff_false]
    rintro ⟨rfl, rfl⟩
    exact htt rfl
  simp [h1]

end Analytic

end PaperIV.MarkedQuotaTokens

