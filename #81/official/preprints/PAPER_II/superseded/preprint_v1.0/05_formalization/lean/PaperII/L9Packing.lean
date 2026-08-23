import PaperII.CompleteSplit
import PaperII.Model
import PaperII.L1
import Mathlib

/-!
# Paper II — L9 lower-bound packing infrastructure

Explicit fractional triangle packing for `S_{p,q}`, used to prove the LP lower bounds in `L9`.

Triangles of `S_{p,q}` split into two orbits:
* type A: three clique vertices `{inl a, inl b, inl c}` (present iff `p ≥ 3`);
* type B: two clique vertices + one independent vertex `{inl a, inl b, inr c}` (present iff
  `p ≥ 2, q ≥ 1`).

The packing puts weight `wA` on each type-A triangle and `wB` on each type-B triangle.  Its total
weight is `C(p,3)·wA + C(p,2)·q·wB`, and the weight through any clique edge is `(p-2)·wA + q·wB`,
through any radial edge `(p-1)·wB`.  Weak LP duality (`tauStar_ge_packing`) then yields the lower
bound.
-/

open scoped BigOperators
open Finset

namespace PaperII

/-- Non-diagonal unordered pairs inside `s` (the "edges" of the vertex set `s`). -/
def triEdges (p q : ℕ) (s : Finset (Fin p ⊕ Fin q)) : Finset (Sym2 (Fin p ⊕ Fin q)) :=
  s.sym2.filter (fun e => ¬ e.IsDiag)

theorem triEdges_eq_triangleEdges (p q : ℕ) (T : Triangle (completeSplit p q)) :
    triEdges p q T.1 = triangleEdges (completeSplit p q) T := rfl

/-- All triangles of `S_{p,q}`, as a finset of vertex sets. -/
def triFinset (p q : ℕ) : Finset (Finset (Fin p ⊕ Fin q)) :=
  Finset.univ.filter (IsTriangle (completeSplit p q))

/-- Type-A triangles: three clique vertices. -/
def triA (p q : ℕ) : Finset (Finset (Fin p ⊕ Fin q)) :=
  ((Finset.univ : Finset (Fin p)).powersetCard 3).image
    (fun t => t.image (Sum.inl : Fin p → Fin p ⊕ Fin q))

/-- Type-B triangles: two clique vertices + one independent vertex. -/
def triB (p q : ℕ) : Finset (Finset (Fin p ⊕ Fin q)) :=
  (((Finset.univ : Finset (Fin p)).powersetCard 2) ×ˢ (Finset.univ : Finset (Fin q))).image
    (fun x => insert (Sum.inr x.2) (x.1.image (Sum.inl : Fin p → Fin p ⊕ Fin q)))

/-- Packing weight of a triangle: `wA` if all-clique (no independent vertex), else `wB`. -/
noncomputable def packWeight (p q : ℕ) (wA wB : ℝ) (s : Finset (Fin p ⊕ Fin q)) : ℝ :=
  if (s.filter (fun v => v.isRight = true)).card = 0 then wA else wB

/-! ## Membership characterizations -/

theorem mem_triA_iff (p q : ℕ) (s : Finset (Fin p ⊕ Fin q)) :
    s ∈ triA p q ↔ ∃ t : Finset (Fin p), t.card = 3 ∧ s = t.image Sum.inl := by
  unfold triA; aesop;

theorem mem_triB_iff (p q : ℕ) (s : Finset (Fin p ⊕ Fin q)) :
    s ∈ triB p q ↔ ∃ (t : Finset (Fin p)) (c : Fin q),
      t.card = 2 ∧ s = insert (Sum.inr c) (t.image Sum.inl) := by
  constructor <;> intro h;
  · grind +locals;
  · rcases h with ⟨ t, c, ht, rfl ⟩ ; exact Finset.mem_image.mpr ⟨ ( t, c ), Finset.mem_product.mpr ⟨ Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, ht ⟩, Finset.mem_univ _ ⟩, rfl ⟩ ;

/-
Every triangle of `S_{p,q}` is type A or type B; conversely each such set is a triangle.
-/
theorem triFinset_eq_union (p q : ℕ) : triFinset p q = triA p q ∪ triB p q := by
  ext s; simp [triFinset, triA, triB];
  constructor <;> intro hs;
  · rcases Finset.card_eq_three.mp hs.2 with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; simp_all +decide [ IsTriangle ];
    rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> rcases z with ( z | z ) <;> simp_all +decide [ Finset.ext_iff, SimpleGraph.isNClique_iff ];
    · exact ⟨ { x, y, z }, by aesop ⟩;
    · exact ⟨ { x, y }, by aesop ⟩;
    · exact ⟨ { x, z }, by aesop ⟩;
    · exact ⟨ { y, z }, by aesop ⟩;
  · rcases hs with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, x, rfl ⟩ ) <;> simp_all +decide [ IsTriangle ];
    · rw [ Finset.card_eq_three ] at ha;
      rcases ha with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp +decide [ *, SimpleGraph.isNClique_iff ] ;
    · rw [ Finset.card_eq_two ] at ha;
      rcases ha with ⟨ x, y, hxy, rfl ⟩ ; simp +decide [ *, SimpleGraph.isNClique_iff ] ;

theorem disjoint_triA_triB (p q : ℕ) : Disjoint (triA p q) (triB p q) := by
  rw [ Finset.disjoint_left ] ; intro s hsA hsB ; rw [ mem_triA_iff ] at hsA ; rw [ mem_triB_iff ] at hsB ; obtain ⟨ t₁, ht₁, rfl ⟩ := hsA ; obtain ⟨ t₂, c, ht₂, hc ⟩ := hsB ; have := congr_arg ( fun s => Sum.inr c ∈ s ) hc ; simp +decide at this;

/-! ## Packing weight is constant on each orbit -/

theorem packWeight_of_mem_triA (p q : ℕ) (wA wB : ℝ) {s : Finset (Fin p ⊕ Fin q)}
    (hs : s ∈ triA p q) : packWeight p q wA wB s = wA := by
  convert if_pos _;
  rw [ mem_triA_iff ] at hs; obtain ⟨ t, ht, rfl ⟩ := hs; simp +decide [ Finset.filter_image ] ;

theorem packWeight_of_mem_triB (p q : ℕ) (wA wB : ℝ) {s : Finset (Fin p ⊕ Fin q)}
    (hs : s ∈ triB p q) : packWeight p q wA wB s = wB := by
  unfold packWeight;
  rw [ mem_triB_iff ] at hs;
  rcases hs with ⟨ t, c, ht, rfl ⟩ ; simp +decide [ Finset.filter_insert, Finset.filter_image ] ;

theorem packWeight_nonneg (p q : ℕ) {wA wB : ℝ} (hwA : 0 ≤ wA) (hwB : 0 ≤ wB)
    (s : Finset (Fin p ⊕ Fin q)) : 0 ≤ packWeight p q wA wB s := by
  unfold packWeight; split <;> assumption

/-! ## Cardinalities -/

theorem card_triA (p q : ℕ) : (triA p q).card = p.choose 3 := by
  rw [ triA, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
  intro a₁ a₂ h; ext x; replace h := Finset.ext_iff.mp h ( Sum.inl x ) ; aesop;

theorem card_triB (p q : ℕ) : (triB p q).card = p.choose 2 * q := by
  convert Finset.card_image_of_injOn _;
  · simp +decide [ Finset.card_univ, Finset.card_powersetCard ];
  · intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
    exact fun h₁ h₂ => Prod.ext ( Finset.ext h₁ ) h₂

/-! ## Counting subsets of `Fin p` containing fixed elements -/

theorem card_powersetCard2_through_one (p : ℕ) (a : Fin p) :
    (((Finset.univ : Finset (Fin p)).powersetCard 2).filter (fun t => a ∈ t)).card = p - 1 := by
  convert Finset.card_powersetCard 1 ( Finset.univ.erase a ) using 1;
  · refine' Finset.card_bij ( fun t ht => t.erase a ) _ _ _ <;> simp_all +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
    · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rw [ ← Finset.insert_erase ha₂, ← Finset.insert_erase ha₄, h ] ;
    · intro b hb hb'; obtain ⟨ x, hx ⟩ := Finset.card_eq_one.mp hb'; use Insert.insert a b; aesop;
  · simp +decide [ Finset.card_erase_of_mem ( Finset.mem_univ a ) ]

theorem card_powersetCard3_through_pair (p : ℕ) (a b : Fin p) (hab : a ≠ b) :
    (((Finset.univ : Finset (Fin p)).powersetCard 3).filter (fun t => a ∈ t ∧ b ∈ t)).card
      = p - 2 := by
  have h_bij : Finset.filter (fun t => a ∈ t ∧ b ∈ t) (Finset.powersetCard 3 (Finset.univ : Finset (Fin p))) = Finset.image (fun t => insert a (insert b t)) (Finset.powersetCard 1 (Finset.erase (Finset.erase (Finset.univ : Finset (Fin p)) a) b)) := by
    ext t;
    simp +zetaDelta at *;
    constructor <;> intro h;
    · use t.erase a |>.erase b;
      grind;
    · grind;
  rw [ h_bij, Finset.card_image_of_injOn ];
  · simp +decide [ Finset.card_erase_of_mem, Finset.mem_erase, hab ];
    rw [ Finset.card_erase_of_mem, Finset.card_erase_of_mem ] <;> aesop;
  · intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
    grind

/-! ## Cardinalities of triangles through a fixed edge -/

theorem card_triA_through_clique (p q : ℕ) (a b : Fin p) (hab : a ≠ b) :
    ((triA p q).filter (fun s => s(Sum.inl a, Sum.inl b) ∈ triEdges p q s)).card = p - 2 := by
  rw [ ← card_powersetCard3_through_pair p a b hab ];
  refine' Finset.card_bij ( fun s hs => Finset.filter ( fun x => Sum.inl x ∈ s ) Finset.univ ) _ _ _;
  · simp +contextual [ triA, triEdges ];
  · intro s₁ hs₁ s₂ hs₂ h; simp_all +decide [ Finset.ext_iff, triA ] ;
    grind +locals;
  · simp +decide [ triA, triEdges ];
    tauto

theorem card_triB_through_clique (p q : ℕ) (a b : Fin p) (hab : a ≠ b) :
    ((triB p q).filter (fun s => s(Sum.inl a, Sum.inl b) ∈ triEdges p q s)).card = q := by
  convert Finset.card_image_of_injOn _;
  rotate_left;
  convert rfl;
  convert Finset.card_fin q;
  exact fun c => insert ( Sum.inr c ) ( { a, b } |> Finset.image Sum.inl );
  infer_instance;
  · intro c hc d hd hcd; replace hcd := Finset.ext_iff.mp hcd ( Sum.inr c ) ; aesop;
  · ext; simp [triB, triEdges];
    constructor;
    · rintro ⟨ ⟨ t, ht, x, rfl ⟩, h, hab ⟩ ; use x; simp_all +decide [ Finset.ext_iff ] ;
      rw [ Finset.card_eq_two ] at ht ; aesop;
    · rintro ⟨ c, rfl ⟩ ; exact ⟨ ⟨ { a, b }, by aesop ⟩, by aesop ⟩ ;

theorem card_triA_through_radial (p q : ℕ) (a : Fin p) (c : Fin q) :
    ((triA p q).filter (fun s => s(Sum.inl a, Sum.inr c) ∈ triEdges p q s)).card = 0 := by
  simp +decide [ Finset.ext_iff, Fintype.elems ];
  intro s hs; rw [ mem_triA_iff ] at hs; obtain ⟨ t, ht, rfl ⟩ := hs; simp +decide [ triEdges ] ;

theorem card_triB_through_radial (p q : ℕ) (a : Fin p) (c : Fin q) :
    ((triB p q).filter (fun s => s(Sum.inl a, Sum.inr c) ∈ triEdges p q s)).card = p - 1 := by
  convert card_powersetCard2_through_one p a using 1;
  refine' Finset.card_bij ( fun s hs => s.image ( fun x => x.elim id ( fun _ => a ) ) ) _ _ _ <;> simp +decide [ triB ];
  · rintro s t ht c rfl hs; simp_all +decide [ triEdges ] ;
    rw [ Finset.card_image_of_injOn, Finset.card_image_of_injective ] <;> aesop_cat;
  · rintro a₁ x hx y rfl hy a₂ x' hx' y' rfl hy' h; simp_all +decide [ Finset.ext_iff, triEdges ] ;
  · intro b hb ha; use b; simp_all +decide [ triEdges ] ;
    ext x; aesop;

theorem card_triA_through_inr (p q : ℕ) (c₁ c₂ : Fin q) :
    ((triA p q).filter (fun s => s(Sum.inr c₁, Sum.inr c₂) ∈ triEdges p q s)).card = 0 := by
  simp +decide [ triEdges ];
  grind +suggestions

theorem card_triB_through_inr (p q : ℕ) (c₁ c₂ : Fin q) (h : c₁ ≠ c₂) :
    ((triB p q).filter (fun s => s(Sum.inr c₁, Sum.inr c₂) ∈ triEdges p q s)).card = 0 := by
  rw [ Finset.card_eq_zero, Finset.filter_eq_empty_iff ];
  intro s hs; rw [ mem_triB_iff ] at hs; obtain ⟨ t, c, ht, rfl ⟩ := hs; simp +decide [ triEdges ] ;
  aesop

/-! ## Sum conversions (subtype → finset) -/

theorem sum_over_triangles (p q : ℕ) (W : Finset (Fin p ⊕ Fin q) → ℝ) :
    (∑ k : Triangle (completeSplit p q), W k.1) = ∑ s ∈ triFinset p q, W s := by
  refine' Finset.sum_bij ( fun k hk => k.val ) _ _ _ _ <;> simp +decide [ triFinset ];
  · exact fun a => a.2;
  · grind +suggestions;
  · exact fun b hb => ⟨ ⟨ b, hb ⟩, rfl ⟩

theorem sum_over_triangles_through (p q : ℕ) (i : Sym2 (Fin p ⊕ Fin q))
    (W : Finset (Fin p ⊕ Fin q) → ℝ) :
    (∑ k ∈ Finset.univ.filter (fun k => i ∈ triangleEdges (completeSplit p q) k), W k.1)
      = ∑ s ∈ (triFinset p q).filter (fun s => i ∈ triEdges p q s), W s := by
  rw [Finset.sum_filter, Finset.sum_filter,
    ← sum_over_triangles p q (fun s => if i ∈ triEdges p q s then W s else 0)]
  rfl

/-
The packing sum over any subfamily of triangles, split by orbit.
-/
theorem sum_packWeight_filter (p q : ℕ) (wA wB : ℝ)
    (P : Finset (Fin p ⊕ Fin q) → Prop) [DecidablePred P] :
    (∑ s ∈ (triFinset p q).filter P, packWeight p q wA wB s)
      = wA * (((triA p q).filter P).card : ℝ) + wB * (((triB p q).filter P).card : ℝ) := by
  rw [ triFinset_eq_union ];
  rw [ Finset.sum_filter, Finset.sum_union ( disjoint_triA_triB p q ) ];
  congr! 1;
  · rw [ Finset.sum_congr rfl fun x hx => by rw [ packWeight_of_mem_triA p q wA wB hx ] ] ; simp +decide [ mul_comm, Finset.sum_ite ];
  · rw [ Finset.sum_ite ];
    rw [ Finset.sum_congr rfl fun x hx => packWeight_of_mem_triB p q wA wB <| Finset.mem_filter.mp hx |>.1 ] ; norm_num ; ring

/-- The total packing weight is `C(p,3)·wA + C(p,2)·q·wB`. -/
theorem sum_packWeight_total (p q : ℕ) (wA wB : ℝ) :
    (∑ s ∈ triFinset p q, packWeight p q wA wB s)
      = wA * (p.choose 3 : ℝ) + wB * ((p.choose 2 : ℝ) * (q : ℝ)) := by
  have h := sum_packWeight_filter p q wA wB (fun _ => True)
  rw [Finset.filter_true] at h
  rw [h, Finset.filter_true, Finset.filter_true, card_triA, card_triB]
  push_cast; ring

/-
The packing weight through any single coordinate is at most `1`.
-/
theorem packWeight_through_le_one (p q : ℕ) {wA wB : ℝ}
    (hclique : ((p - 2 : ℕ) : ℝ) * wA + (q : ℝ) * wB ≤ 1)
    (hradial : ((p - 1 : ℕ) : ℝ) * wB ≤ 1)
    (i : Sym2 (Fin p ⊕ Fin q)) :
    (∑ s ∈ (triFinset p q).filter (fun s => i ∈ triEdges p q s), packWeight p q wA wB s) ≤ 1 := by
  induction' i using Sym2.ind with a b;
  rcases a with ( a | a ) <;> rcases b with ( b | b );
  · by_cases hab : a = b;
    · simp +decide [ hab, triEdges ];
    · rw [ sum_packWeight_filter ];
      rw [ card_triA_through_clique p q a b hab, card_triB_through_clique p q a b hab ];
      linarith;
  · rw [ sum_packWeight_filter ];
    rw [ card_triA_through_radial, card_triB_through_radial ] ; norm_num ; nlinarith;
  · convert sum_packWeight_filter p q wA wB ( fun s => s(Sum.inl b, Sum.inr a) ∈ triEdges p q s ) |> fun h => h.trans_le _ using 1;
    · simp +decide [ Sym2.eq_swap ];
    · convert hradial using 1;
  