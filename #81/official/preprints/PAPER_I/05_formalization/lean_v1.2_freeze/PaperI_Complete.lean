/-
  Paper I — COMPLETE self-contained Lean proof (single file).
  Final result: `PaperI.Split.paperI_main_sharp` :  |E(G)| − 2·ν₃*(G) ≤ n²/6 + n/2.
  Also proves the v1.0 bound `PaperI.paperI_main` (≤ n²/6 + n).

  Auto-assembled by concatenating (in dependency order):
    FiniteLPDuality.lean  →  PaperI/PaperI_Statement.lean  →  Contrib/PaperISharp.lean,
  stripping the internal `import` lines and keeping a single `import Mathlib`.
  Compiles standalone under Lean 4 / Mathlib v4.28.0.
-/
import Mathlib


/- ====================================================================== -/
/- ===== FiniteLPDuality.lean -/
/- ====================================================================== -/

/-
  Finite linear-programming strong duality (covering / packing form).

  Self-contained development, `import Mathlib`.  The main export is
  `FiniteLP.covering_packing_duality`, a finite LP strong-duality theorem for a
  nonnegative incidence matrix `A` with nonnegative capacities `r`:

      max { ∑ t, w t : w ≥ 0, ∀ e, ∑ t A e t w t ≤ r e }
        =
      min { ∑ e, r e x e : x ≥ 0, ∀ t, ∑ e A e t x e ≥ 1 }

  and the maximum is attained.  It is proved from a finite Farkas lemma
  (`FiniteLP.farkas_ge`), which in turn rests on the closedness of a finitely
  generated cone (`FiniteLP.fg_cone_isClosed`) together with Mathlib's
  hyperplane-separation theorem for closed convex cones.
-/

open scoped BigOperators InnerProductSpace
open Finset

namespace FiniteLP

/-- The column vector `(N · j)` viewed as an element of `EuclideanSpace ℝ ι`. -/
noncomputable def col {ι κ : Type*} [Fintype ι] (N : ι → κ → ℝ) (j : κ) :
    EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => N i j)

/-- A generic vector of `EuclideanSpace ℝ ι` given by its coordinates. -/
noncomputable def toE {ι : Type*} [Fintype ι] (f : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm f

@[simp] lemma toE_apply {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) : toE f i = f i := rfl

lemma inner_toE {ι : Type*} [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, toE, mul_comm]

/-! ### Closedness of a finitely generated cone -/

/-- A simplicial cone (nonnegative combinations of a linearly independent finite family) is
closed: it is the image of the closed nonnegative orthant under an injective (hence closed)
linear map. -/
lemma simplicial_cone_isClosed {κ ι : Type*} [Fintype κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : EuclideanSpace ℝ ι |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
  classical
  set L : (s → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    ∑ k : s, LinearMap.smulRight (LinearMap.proj k) (v k) with hL_def
  have hLval : ∀ c : s → ℝ, L c = ∑ k : s, c k • v k := by
    intro c
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [hLval] at hm
    funext k; exact Fintype.linearIndependent_iff.mp hli m hm k
  have hclosedmap : IsClosedMap L :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {c : s → ℝ | ∀ k, 0 ≤ c k} := by
    have : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext c; simp
    rw [this]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨c, hc0, hcoff, rfl⟩
    refine ⟨fun k : s => c k, fun k => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach s (fun j => c j • v j)]
    rfl
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro k hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach s (fun j => (if h : j ∈ s then c ⟨j, h⟩ else 0) • v j)]
      apply Finset.sum_congr rfl
      intro k _
      simp [k.2]

/-
Conic Carathéodory: any nonnegative combination of a finite family can be rewritten as a
nonnegative combination of a linearly independent subfamily giving the same value.
-/
set_option maxHeartbeats 2000000 in
lemma conic_caratheodory {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → ℝ) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn ℝ v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by
  -- Among all finsets `s` and coefficient functions `d : κ → ℝ` with `d ≥ 0`, `d = 0` off `s`, and `∑ k ∈ s, d k • v k = ∑ k, c k • v k`, choose one whose support (as a finset) has minimal cardinality.
  obtain ⟨s, hs⟩ : ∃ s : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧ (∑ k ∈ s, d k • v k = ∑ k, c k • v k)) ∧ ∀ t : Finset κ, (∃ d : κ → ℝ, (∀ k, 0 ≤ d k) ∧ (∀ k ∉ t, d k = 0) ∧ (∑ k ∈ t, d k • v k = ∑ k, c k • v k)) → s.card ≤ t.card := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.toFinite _;
    · exact ⟨ Finset.univ, ⟨ c, hc, fun k hk => False.elim <| hk <| Finset.mem_univ _, by simp +decide ⟩ ⟩;
  by_cases h_lin_dep : ¬ LinearIndepOn ℝ v s;
  · obtain ⟨d, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨a, ha_nonzero, ha_support, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) ∧ (∃ k ∈ s, a k > 0) := by
      obtain ⟨a, ha_nonzero, ha_sum⟩ : ∃ a : κ → ℝ, (∃ k ∈ s, a k ≠ 0) ∧ (∀ k ∉ s, a k = 0) ∧ (∑ k ∈ s, a k • v k = 0) := by
        rw [ linearIndepOn_iff' ] at h_lin_dep;
        push_neg at h_lin_dep;
        obtain ⟨ t, g, ht, hg, i, hi, hi' ⟩ := h_lin_dep; use fun k => if k ∈ t then g k else 0; simp_all +decide [ Finset.sum_ite ] ;
        exact ⟨ ⟨ i, ht hi, hi, hi' ⟩, fun k hk₁ hk₂ => False.elim <| hk₁ <| ht hk₂, by rw [ Finset.inter_eq_right.mpr ht, hg ] ⟩;
      by_cases h_neg : ∀ k ∈ s, a k ≤ 0;
      · use fun k => -a k;
        simp_all +decide [ neg_smul ];
        exact ha_nonzero.imp fun k hk => ⟨ hk.1, lt_of_le_of_ne ( h_neg k hk.1 ) hk.2 ⟩;
      · exact ⟨ a, ha_nonzero, ha_sum.1, ha_sum.2, by push_neg at h_neg; exact h_neg ⟩;
    -- Choose $\theta > 0$ such that $d - \theta a$ is nonnegative and supported on a strictly smaller set than $s$.
    obtain ⟨θ, hθ_pos, hθ_min⟩ : ∃ θ > 0, (∀ k ∈ s, d k - θ * a k ≥ 0) ∧ (∃ k ∈ s, d k - θ * a k = 0) := by
      -- Choose $\theta$ to be the minimum of $d_k / a_k$ over all $k \in s$ where $a_k > 0$.
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ ∈ s, a k₀ > 0 ∧ ∀ k ∈ s, a k > 0 → d k / a k ≥ d k₀ / a k₀ := by
        have h_min : ∃ k₀ ∈ Finset.filter (fun k => a k > 0) s, ∀ k ∈ Finset.filter (fun k => a k > 0) s, d k / a k ≥ d k₀ / a k₀ := by
          exact Finset.exists_min_image _ _ ⟨ ha_sum.2.choose, Finset.mem_filter.mpr ⟨ ha_sum.2.choose_spec.1, ha_sum.2.choose_spec.2 ⟩ ⟩;
        exact ⟨ h_min.choose, Finset.mem_filter.mp h_min.choose_spec.1 |>.1, Finset.mem_filter.mp h_min.choose_spec.1 |>.2, fun k hk hk' => h_min.choose_spec.2 k ( Finset.mem_filter.mpr ⟨ hk, hk' ⟩ ) ⟩;
      refine' ⟨ d k₀ / a k₀, div_pos ( lt_of_le_of_ne ( hd_nonneg k₀ ) ( Ne.symm _ ) ) hk₀.2.1, _, k₀, hk₀.1, _ ⟩;
      · intro h; simp_all +decide [ ne_of_gt ] ;
        have := hs.2 ( s.erase k₀ ) ( fun k => if k = k₀ then 0 else d k ) ?_ ?_ ?_ <;> simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
        · exact Nat.not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ( Finset.card_pos.mpr ⟨ k₀, hk₀.1 ⟩ ) ) ) this;
        · exact fun k => by split_ifs <;> simp +decide [ * ] ;
      · intro k hk; by_cases hk' : a k > 0 <;> simp_all +decide [ div_mul_cancel₀ _ ( ne_of_gt _ ) ] ;
        · exact le_div_iff₀ hk' |>.1 ( hk₀.2.2 k hk hk' );
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( div_nonneg ( hd_nonneg _ ) hk₀.2.1.le ) hk' ) ( hd_nonneg _ );
      · rw [ div_mul_cancel₀ _ hk₀.2.1.ne', sub_self ];
    -- Let $t = s.filter (fun k => d k - θ * a k ≠ 0)$ be the support of $d - θ a$.
    set t := s.filter (fun k => d k - θ * a k ≠ 0) with ht_def;
    -- Then $d - \theta a$ is nonnegative, supported on $t$, and $\sum_{k \in t} (d k - \theta a k) • v k = \sum_{k \in s} d k • v k$.
    have h_t_support : ∀ k, 0 ≤ d k - θ * a k := by
      exact fun k => if hk : k ∈ s then hθ_min.1 k hk else by simp +decide [ hd_zero k hk, ha_support k hk ] ;
    have h_t_zero : ∀ k ∉ t, d k - θ * a k = 0 := by
      grind
    have h_t_sum : ∑ k ∈ t, (d k - θ * a k) • v k = ∑ k, c k • v k := by
      convert congr_arg ( fun x => x - θ • ∑ k ∈ s, a k • v k ) hd_sum using 1;
      · rw [ Finset.sum_filter_of_ne ];
        · simp +decide [ sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul ];
        · exact fun k hk hk' => fun hk'' => hk' <| by rw [ hk'', zero_smul ] ;
      · simp +decide [ ha_sum.1 ];
    contrapose! hs;
    refine' fun h => ⟨ t, ⟨ fun k => d k - θ * a k, h_t_support, h_t_zero, h_t_sum ⟩, _ ⟩;
    refine' Finset.card_lt_card _;
    grind;
  · exact ⟨ hs.1.choose, s, hs.1.choose_spec.1, hs.1.choose_spec.2.1, Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2 ⟩

/-- The finitely generated cone `{∑ k c k • v k : c ≥ 0}` is closed. -/
lemma fg_cone_isClosed {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) :
    IsClosed {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by
  have hset : {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y}
      = ⋃ s : Finset κ, ⋃ (_ : LinearIndepOn ℝ v s),
          {y : EuclideanSpace ℝ ι |
            ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨c, hc0, rfl⟩
      obtain ⟨d, s, hd0, hdoff, hindep, hsum⟩ := conic_caratheodory v c hc0
      exact ⟨s, hindep, d, hd0, hdoff, hsum⟩
    · rintro ⟨s, hindep, c, hc0, hcoff, rfl⟩
      refine ⟨c, hc0, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      intro k _ hks; rw [hcoff k hks, zero_smul]
  rw [hset]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_iUnion_of_finite fun h => simplicial_cone_isClosed v s h

/-! ### Finite Farkas lemma -/

/-- **Finite Farkas lemma (inequality form).**  If the primal system
`x ≥ 0, N x ≥ c` is infeasible, then there is a Farkas certificate `y ≥ 0` with
`Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`. -/
theorem farkas_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  classical
  set g : (κ ⊕ ι) → EuclideanSpace ℝ ι :=
    Sum.elim (fun j => toE (fun i => N i j)) (fun i => toE (fun i' => if i' = i then (-1:ℝ) else 0)) with hg
  have hind : ∀ a : κ ⊕ ι, ∑ k, (if k = a then (1:ℝ) else 0) • g k = g a := by
    intro a; simp [ite_smul]
  set S : Set (EuclideanSpace ℝ ι) := {y | ∃ coeff : (κ ⊕ ι) → ℝ, (∀ k, 0 ≤ coeff k) ∧ ∑ k, coeff k • g k = y} with hS
  have hSclosed : IsClosed S := fg_cone_isClosed g
  let K : ConvexCone ℝ (EuclideanSpace ℝ ι) :=
    { carrier := S
      smul_mem' := by
        rintro t ht x ⟨coeff, hcoeff, rfl⟩
        exact ⟨fun k => t * coeff k, fun k => mul_nonneg ht.le (hcoeff k), by
          rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_smul]⟩
      add_mem' := by
        rintro x ⟨c1, h1, rfl⟩ y ⟨c2, h2, rfl⟩
        exact ⟨fun k => c1 k + c2 k, fun k => add_nonneg (h1 k) (h2 k), by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [add_smul]⟩ }
  have hKne : (K : Set (EuclideanSpace ℝ ι)).Nonempty :=
    ⟨0, ⟨fun _ => 0, fun _ => le_refl 0, by simp⟩⟩
  have hcne : (toE c) ∉ K := by
    rintro ⟨coeff, hcoeff, hsum⟩
    apply hinfeas
    refine ⟨fun j => coeff (Sum.inl j), fun j => hcoeff _, ?_⟩
    intro i
    have hcoord := congrArg (fun z => z i) hsum
    simp only [toE_apply] at hcoord
    have hexp : (∑ k, coeff k • g k) i
        = (∑ j, coeff (Sum.inl j) * N i j) - coeff (Sum.inr i) := by
      rw [Fintype.sum_sum_type]
      simp [hg, EuclideanSpace, PiLp, Finset.sum_apply]
      ring
    have hcomm : ∑ j, N i j * coeff (Sum.inl j) = ∑ j, coeff (Sum.inl j) * N i j := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hcoord
    have hnn : 0 ≤ coeff (Sum.inr i) := hcoeff _
    linarith
  obtain ⟨y, hy1, hy2⟩ :=
    K.hyperplane_separation_of_nonempty_of_isClosed_of_notMem hKne hSclosed hcne
  refine ⟨fun i => -(y i), fun i => ?_, fun j => ?_, ?_⟩
  · have hmem : g (Sum.inr i) ∈ K := ⟨fun k => if k = Sum.inr i then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inr] at hh
    rw [inner_toE] at hh
    have hval : ∑ i', (if i' = i then (-1:ℝ) else 0) * y i' = - y i := by
      rw [Finset.sum_eq_single i] <;> simp +contextual
    rw [hval] at hh
    change 0 ≤ - y i; linarith
  · have hmem : g (Sum.inl j) ∈ K := ⟨fun k => if k = Sum.inl j then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inl] at hh
    rw [inner_toE] at hh
    have h2 : ∑ i, N i j * -(y i) = - ∑ i, (fun i => N i j) i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
  · rw [real_inner_comm] at hy2
    rw [inner_toE] at hy2
    have h2 : ∑ i, c i * -(y i) = - ∑ i, c i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith

/-! ### Strong duality -/

/-
**Finite LP strong duality (covering/packing).**  For a nonnegative incidence matrix `A`
with nonnegative capacities `r`, in which every column has a positive entry, there is a maximum
packing `w` whose value equals the covering optimum.
-/
theorem covering_packing_duality
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ)
    (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  by_contra h_no_wstar;
  -- By definition of $P$, we know that for any $w \in Q$, $\sum t, w t \leq Mr$.
  have hP_le_Mr : ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    intro w hw;
    refine' le_csInf _ _;
    · refine' ⟨ _, ⟨ fun e => ∑ t, 1 / A e t, _, _, rfl ⟩ ⟩;
      · exact fun e => Finset.sum_nonneg fun t _ => one_div_nonneg.2 ( hA e t );
      · intro t; obtain ⟨ e, he ⟩ := hcol t; refine' le_trans _ ( Finset.single_le_sum ( fun e _ => mul_nonneg ( hA e t ) ( Finset.sum_nonneg fun t _ => one_div_nonneg.mpr ( hA e t ) ) ) ( Finset.mem_univ e ) ) ; simp +decide [ he.ne', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
        exact le_trans ( by norm_num [ he.ne' ] ) ( Finset.single_le_sum ( fun i _ => mul_nonneg he.le ( inv_nonneg.2 ( hA e i ) ) ) ( Finset.mem_univ t ) );
    · rintro _ ⟨ x, hx₁, hx₂, rfl ⟩;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ t, w t * (∑ e, A e t * x e) = ∑ e, (∑ t, A e t * w t) * x e := by
        simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm;
      exact le_trans ( Finset.sum_le_sum fun t _ => le_mul_of_one_le_right ( hw.1 t ) ( hx₂ t ) ) ( h_fubini.le.trans ( Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ( hw.2 e ) ( hx₁ e ) ) );
  -- By definition of $P$, we know that there exists a maximum packing $w^* \in Q$ such that $\sum t, w^* t = P$.
  obtain ⟨w_star, hw_star⟩ : ∃ w_star : κ → ℝ, (∀ t, 0 ≤ w_star t) ∧ (∀ e, ∑ t, A e t * w_star t ≤ r e) ∧ ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ ∑ t, w_star t := by
    have h_compact : IsCompact {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)} := by
      refine' CompactIccSpace.isCompact_Icc.of_isClosed_subset _ _;
      exact fun t => 0;
      exact fun t => sInf { v | ∃ x : ι → ℝ, ( ∀ e, 0 ≤ x e ) ∧ ( ∀ t, 1 ≤ ∑ e, A e t * x e ) ∧ v = ∑ e, r e * x e };
      · simp +decide only [Set.setOf_and, Set.setOf_forall];
        exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( isClosed_iInter fun _ => isClosed_le ( continuous_finset_sum _ fun _ _ => continuous_const.mul <| continuous_apply _ ) continuous_const );
      · exact fun w hw => ⟨ hw.1, fun t => le_trans ( Finset.single_le_sum ( fun a _ => hw.1 a ) ( Finset.mem_univ t ) ) ( hP_le_Mr w hw ) ⟩;
    have h_nonempty : {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)}.Nonempty := by
      exact ⟨ fun _ => 0, fun _ => le_rfl, fun _ => by simp +decide [ hr ] ⟩;
    have := h_compact.exists_isMaxOn h_nonempty ( show ContinuousOn ( fun w : κ → ℝ => ∑ t, w t ) _ from Continuous.continuousOn <| continuous_finset_sum _ fun _ _ => continuous_apply _ );
    exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, fun w hw => this.choose_spec.2 hw ⟩;
  -- By definition of $P$, we know that $P < Mr$.
  have hP_lt_Mr : ∑ t, w_star t < sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    exact lt_of_le_of_ne ( hP_le_Mr w_star ⟨ hw_star.1, hw_star.2.1 ⟩ ) fun h => h_no_wstar ⟨ w_star, hw_star.1, hw_star.2.1, h ⟩;
  -- By definition of $P$, we know that there exists a Farkas certificate $y$ such that $y \geq 0$, $\sum_{e} N'_{ie} y_i \leq 0$ for all $e$, and $\sum_{i} c'_i y_i > 0$.
  obtain ⟨y, hy_nonneg, hy_row, hy_obj⟩ : ∃ y : κ ⊕ Unit → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ e, ∑ i, (Sum.elim (fun t e => A e t) (fun _ e => -r e) i e) * y i ≤ 0) ∧ 0 < ∑ i, (Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i) * y i := by
    have h_farkas : ¬∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ ∑ e, r e * x e ≤ ∑ t, w_star t := by
      contrapose! hP_lt_Mr;
      exact le_trans ( csInf_le ⟨ 0, by rintro v ⟨ x, hx₁, hx₂, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hr _ ) ( hx₁ _ ) ⟩ ⟨ hP_lt_Mr.choose, hP_lt_Mr.choose_spec.1, hP_lt_Mr.choose_spec.2.1, rfl ⟩ ) hP_lt_Mr.choose_spec.2.2;
    convert farkas_ge ( fun i e => Sum.elim ( fun t e => A e t ) ( fun _ e => -r e ) i e ) ( fun i => Sum.elim ( fun _ => 1 ) ( fun _ => -∑ t, w_star t ) i ) _ using 1;
    simp +zetaDelta at *;
    exact h_farkas;
  -- Let $lam t = y (Sum.inl t)$ and $mu = y (Sum.inr ())$.
  set lam : κ → ℝ := fun t => y (Sum.inl t)
  set mu : ℝ := y (Sum.inr ());
  -- By definition of $lam$ and $mu$, we have $\sum_{t} A_{et} lam_t \leq mu r_e$ for all $e$ and $\sum_{t} lam_t > mu P$.
  have hlam_mu : ∀ e, ∑ t, A e t * lam t ≤ mu * r e := by
    intro e; specialize hy_row e; simp +decide [ Finset.sum_add_distrib, mul_comm ] at hy_row ⊢;
    exact hy_row
  have hlam_mu_P : ∑ t, lam t > mu * ∑ t, w_star t := by
    simp +zetaDelta at *;
    linarith;
  -- If $mu = 0$, then from $hlam_mu$, we have $\sum_{t} A_{et} lam_t \leq 0$ for all $e$, which implies $lam_t = 0$ for all $t$.
  by_cases hmu_zero : mu = 0;
  · simp +zetaDelta at *;
    simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ];
    exact hy_obj.ne' ( Finset.sum_eq_zero fun t ht => le_antisymm ( le_of_not_gt fun h => by have := hy_row ( Classical.choose ( hcol t ) ) ; exact not_le_of_gt ( lt_of_lt_of_le ( mul_pos ( Classical.choose_spec ( hcol t ) ) h ) ( Finset.single_le_sum ( fun a _ => mul_nonneg ( hA _ a ) ( hy_nonneg a ) ) ht ) ) this ) ( hy_nonneg t ) );
  · -- Since $mu > 0$, we can divide both sides of $hlam_mu$ by $mu$ to get $\sum_{t} A_{et} (lam_t / mu) \leq r_e$ for all $e$.
    have hlam_mu_div : ∀ e, ∑ t, A e t * (lam t / mu) ≤ r e := by
      simp +decide only [← mul_div_assoc, ← sum_div];
      exact fun e => div_le_iff₀' ( lt_of_le_of_ne ( hy_nonneg _ ) ( Ne.symm hmu_zero ) ) |>.2 ( hlam_mu e );
    -- Since $mu > 0$, we can divide both sides of $hlam_mu_P$ by $mu$ to get $\sum_{t} (lam_t / mu) > \sum_{t} w_star t$.
    have hlam_mu_div_P : ∑ t, (lam t / mu) > ∑ t, w_star t := by
      rw [ ← Finset.sum_div _ _ _, gt_iff_lt, lt_div_iff₀ ] <;> cases lt_or_gt_of_ne hmu_zero <;> nlinarith [ hy_nonneg ( Sum.inr () ) ];
    exact not_le_of_gt hlam_mu_div_P ( hw_star.2.2 _ ⟨ fun t => div_nonneg ( hy_nonneg _ ) ( hy_nonneg _ ), hlam_mu_div ⟩ )

end FiniteLP

/- ====================================================================== -/
/- ===== PaperI/PaperI_Statement.lean -/
/- ====================================================================== -/

/-
  Paper I — M-MODEL: finite split model, edges, triangles, fractional triangle packing ν₃*,
  the functional Φ, and the main statement.

  Compiles standalone under `import Mathlib` (Lean/Mathlib v4.28.0).
  `PaperI_Arith` is imported only at T-MAIN, once the Lake lib is wired up.

  M-MODEL sorry-free targets: `nu3star`, `packing_le_card`, `nu3star_ge_of_feasible`.
  The strong-duality wall `residual_duality` is now proved (via the self-contained finite LP
  duality theory in `FiniteLPDuality.lean`), so the whole file — including `paperI_main` — is
  free of `sorry`.
-/

namespace PaperI
open scoped BigOperators
open Classical Finset

def Rq (p q : ℚ) : ℚ := (2*p^2 - 2*p*q - q^2)/12




/-- A finite split graph: clique `Fin p`, independent index `ι`, neighborhoods `N v ⊆ Fin p`. -/
structure Split where
  p : ℕ
  ι : Type
  fι : Fintype ι
  N : ι → Finset (Fin p)

attribute [instance] Split.fι

namespace Split
variable (G : Split)

/-- Vertex count: p clique vertices + |ι| independent vertices. -/
def n : ℕ := G.p + Fintype.card G.ι

/-- q = #{v : d_v ≥ 2}, b1 = #{v : d_v = 1}. -/
def q  : ℕ := (Finset.univ.filter (fun v => 2 ≤ (G.N v).card)).card
def b1 : ℕ := (Finset.univ.filter (fun v => (G.N v).card = 1)).card

/-- |E(G)| = C(p,2) + Σ_v |N v|  (paper (2.1)). -/
def edgeCount : ℕ := Nat.choose G.p 2 + ∑ v : G.ι, (G.N v).card

/-- Edges of a split graph: clique edges `{i<j} ⊆ Fin p`, and cross edges `(v,x)` with `x ∈ N v`. -/
abbrev Edge (G : Split) : Type :=
  {e : Fin G.p × Fin G.p // e.1 < e.2} ⊕ {e : G.ι × Fin G.p // e.2 ∈ G.N e.1}

/-- Triangles of a split graph: clique triples `{i<j<k}`, and mixed triangles `{v,x,y}`
    with `x<y` both neighbors of the independent vertex `v`. -/
abbrev Triangle (G : Split) : Type :=
  {t : Fin G.p × Fin G.p × Fin G.p // t.1 < t.2.1 ∧ t.2.1 < t.2.2} ⊕
  {t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1}

/-- Edge–triangle incidence. -/
def edgeMem : Edge G → Triangle G → Prop
  | Sum.inl ⟨(i, j), _⟩, Sum.inl ⟨(a, b, c), _⟩ =>
      (i = a ∧ j = b) ∨ (i = a ∧ j = c) ∨ (i = b ∧ j = c)
  | Sum.inl ⟨(i, j), _⟩, Sum.inr ⟨(_, x, y), _⟩ => i = x ∧ j = y
  | Sum.inr _,           Sum.inl _            => False
  | Sum.inr ⟨(v, x), _⟩, Sum.inr ⟨(w, y, z), _⟩ => v = w ∧ (x = y ∨ x = z)

/-- Every triangle contains at least one edge (namely its clique edge). -/
theorem triangle_has_edge (T : Triangle G) : ∃ e : Edge G, edgeMem G e T := by
  rcases T with ⟨⟨a, b, c⟩, hab, hbc⟩ | ⟨⟨v, x, y⟩, hxy, hx, hy⟩
  · exact ⟨Sum.inl ⟨(a, b), hab⟩, by simp [edgeMem]⟩
  · exact ⟨Sum.inl ⟨(x, y), hxy⟩, by simp [edgeMem]⟩

/-- A feasible fractional triangle packing: nonnegative weights whose per-edge load is ≤ 1. -/
def FeasiblePacking (w : Triangle G → ℝ) : Prop :=
  (∀ T, 0 ≤ w T) ∧
    ∀ e : Edge G, ∑ T ∈ Finset.univ.filter (fun T => edgeMem G e T), w T ≤ 1

/-- The set of achievable packing values. -/
def packingValues : Set ℝ := {s | ∃ w, FeasiblePacking G w ∧ s = ∑ T, w T}

theorem packingValues_nonempty : (packingValues G).Nonempty :=
  ⟨0, (fun _ => (0 : ℝ)), ⟨fun _ => le_refl 0, fun _ => by simp⟩, by simp⟩

/-- In a feasible packing every triangle weight is ≤ 1: it is one nonneg term of some edge's
    load, which is ≤ 1. -/
theorem weight_le_one {w : Triangle G → ℝ} (hw : FeasiblePacking G w) (T : Triangle G) :
    w T ≤ 1 := by
  obtain ⟨e, he⟩ := triangle_has_edge G T
  have hmem : T ∈ Finset.univ.filter (fun T => edgeMem G e T) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  have hle : w T ≤ ∑ T' ∈ Finset.univ.filter (fun T => edgeMem G e T), w T' :=
    Finset.single_le_sum (fun i _ => hw.1 i) hmem
  exact le_trans hle (hw.2 e)

/-- Packing total ≤ number of triangles. A crude bound (each weight ≤ 1) — all that is needed
    for `BddAbove`; the exact `≤ edgeCount` value is never used downstream. -/
theorem packing_le_card {w : Triangle G → ℝ} (hw : FeasiblePacking G w) :
    (∑ T, w T) ≤ (Fintype.card (Triangle G) : ℝ) := by
  calc (∑ T, w T) ≤ ∑ _T : Triangle G, (1 : ℝ) :=
        Finset.sum_le_sum (fun T _ => weight_le_one G hw T)
    _ = (Fintype.card (Triangle G) : ℝ) := by simp [Finset.card_univ]

theorem packingValues_bddAbove : BddAbove (packingValues G) := by
  refine ⟨(Fintype.card (Triangle G) : ℝ), ?_⟩
  rintro s ⟨w, hw, rfl⟩
  exact packing_le_card G hw

/-- ν₃*(G): the fractional triangle packing number, as a supremum of feasible packing values. -/
noncomputable def nu3star : ℝ := sSup (packingValues G)

/-- The only fact about ν₃* the main theorem uses: any feasible packing bounds it below
    (`le_csSup`). No LP is solved and no strong duality is invoked. -/
theorem nu3star_ge_of_feasible {w : Triangle G → ℝ} (hw : FeasiblePacking G w) :
    (∑ T, w T) ≤ nu3star G :=
  le_csSup (packingValues_bddAbove G) ⟨w, hw, rfl⟩

/-- The deficit functional Φ = |E| − 2 ν₃*. -/
noncomputable def Phi : ℝ := (G.edgeCount : ℝ) - 2 * nu3star G

/-! ### S-PHASE — clique-edge load and the load identity (Lemma 3.1, duality-free) -/

/-- Clique edges `{i<j} ⊆ Fin p` (the clique-edge summand of `Edge`). -/
abbrev CliqueEdge (G : Split) : Type := {e : Fin G.p × Fin G.p // e.1 < e.2}

/-- Aggregate clique-edge load `κ_e = Σ_{v : e ⊆ N v} 1/(d_v − 1)`  (paper (3.1)).
    Only vertices with both endpoints in `N v` contribute, which forces `d_v ≥ 2`. -/
noncomputable def kappa (e : CliqueEdge G) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => e.val.1 ∈ G.N v ∧ e.val.2 ∈ G.N v),
    (1 : ℝ) / (((G.N v).card : ℝ) - 1)

/-- `b_{≥2} = Σ_{v : d_v ≥ 2} d_v`. -/
def bge2 : ℕ := ∑ v ∈ Finset.univ.filter (fun v => 2 ≤ (G.N v).card), (G.N v).card

/-- Number of clique edges `{i<j}` with both endpoints in a finset `S` equals `C(|S|,2)`. -/
lemma card_cliqueEdges_in (S : Finset (Fin G.p)) :
    (Finset.univ.filter
        (fun e : CliqueEdge G => e.val.1 ∈ S ∧ e.val.2 ∈ S)).card
      = S.card.choose 2 := by
  have h_pairs : Finset.card (Finset.filter (fun e : Fin G.p × Fin G.p => e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S) (Finset.univ : Finset (Fin G.p × Fin G.p))) = Nat.choose (Finset.card S) 2 := by
    have h_pairs : Finset.card (Finset.filter (fun e : Fin G.p × Fin G.p => e.1 < e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S) (Finset.univ : Finset (Fin G.p × Fin G.p))) = Finset.card (Finset.powersetCard 2 S) := by
      refine' Finset.card_bij ( fun e he => { e.1, e.2 } ) _ _ _;
      · grind;
      · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        grind;
      · simp +decide [ Finset.mem_powersetCard ];
        intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
    rw [ h_pairs, Finset.card_powersetCard ];
  convert h_pairs using 1;
  rw [ ← Finset.card_image_of_injective _ ( show Function.Injective ( fun e : { e : Fin G.p × Fin G.p // e.1 < e.2 } => e.val ) from fun a b h => by aesop ) ] ; congr ; ext ; aesop;

/-- Fubini step: swap summation over clique edges and vertices; each vertex `v` contributes
    `C(d_v,2)/(d_v−1)`. -/
lemma load_fubini :
    (∑ e : CliqueEdge G, kappa G e)
      = ∑ v : G.ι, (((G.N v).card.choose 2 : ℝ) / (((G.N v).card : ℝ) - 1)) := by
  unfold Split.kappa;
  convert Finset.sum_comm using 2 ; simp +decide [ div_eq_mul_inv _ ];
  convert Finset.sum_filter ?_ ?_ using 1;
  rw [ Finset.sum_ite ] ; norm_num;
  erw [ card_cliqueEdges_in ] ; ring

/-- Arithmetic collapse: `C(d,2)/(d−1) = d/2` for `d ≥ 2`, `= 0` for `d < 2`. -/
lemma sum_term_eq :
    (∑ v : G.ι, (((G.N v).card.choose 2 : ℝ) / (((G.N v).card : ℝ) - 1)))
      = (bge2 G : ℝ) / 2 := by
  rw [ Split.bge2, Nat.cast_sum, Finset.sum_div _ _ _ ];
  rw [ Finset.sum_filter, ← Finset.sum_congr rfl ];
  intro v hv; split_ifs <;> simp_all +decide [ Nat.choose_two_right ] ;
  · rw [ Nat.cast_div, Nat.cast_mul, Nat.cast_sub ] <;> norm_num;
    · rw [ eq_div_iff ] <;> linarith [ show ( # ( G.N v ) : ℝ ) ≥ 2 by norm_cast ];
    · exact Finset.card_pos.mp ( pos_of_gt ‹_› );
    · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ );
  · interval_cases _ : # ( G.N v ) <;> norm_num

/-- **Lemma 3.1 (load identity).** `Σ_e κ_e = b_{≥2}/2`. Double counting: for each `v` with
    `d_v ≥ 2`, the `C(d_v,2)` clique edges inside `N v` each contribute `1/(d_v−1)`, totaling
    `d_v/2`; vertices with `d_v < 2` contribute nothing. -/
theorem load_identity :
    (∑ e : CliqueEdge G, kappa G e) = (bge2 G : ℝ) / 2 :=
  (load_fubini G).trans (sum_term_eq G)

/-! ### S-PHASE — Phase I packing (scaffold; proofs deferred, all duality-free) -/

/-- Phase-I edge scaling `λ_e` (paper §4.1): `1` if `κ_e = 0`, else `min{1, κ_e⁻¹}`,
    chosen so the clique-edge load is `λ_e·κ_e = min{κ_e, 1}`. -/
noncomputable def lambdaE (e : CliqueEdge G) : ℝ :=
  if kappa G e = 0 then 1 else min 1 (kappa G e)⁻¹

/-- Phase-I packing `w₁` (paper (4.1)): weight `λ_{xy}/(d_v−1)` on each mixed triangle
    `{v,x,y}`; clique triangles get weight `0`. -/
noncomputable def w1 : Triangle G → ℝ
  | Sum.inl _ => 0
  | Sum.inr ⟨(v, x, y), hxy, _, _⟩ => lambdaE G ⟨(x, y), hxy⟩ / (((G.N v).card : ℝ) - 1)

/-- Residual clique-edge capacity `r_e = max{1 − κ_e, 0}` (paper (4.4)). -/
noncomputable def residual (e : CliqueEdge G) : ℝ := max (1 - kappa G e) 0

/-- `κ_e ≥ 0`: only vertices with both endpoints in `N v` (hence `d_v ≥ 2`) contribute,
    and each term `1/(d_v−1)` is nonnegative. -/
lemma kappa_nonneg (e : CliqueEdge G) : 0 ≤ kappa G e := by
  apply Finset.sum_nonneg; intro v hv
  exact div_nonneg zero_le_one (sub_nonneg_of_le (by exact_mod_cast Finset.card_pos.mpr ⟨e.1.1, by aesop⟩))

/-- `λ_e ≥ 0`. -/
lemma lambdaE_nonneg (e : CliqueEdge G) : 0 ≤ lambdaE G e := by
  unfold Split.lambdaE
  split_ifs <;> norm_num [Split.kappa_nonneg]

/-- `λ_e ≤ 1`. -/
lemma lambdaE_le_one (e : CliqueEdge G) : lambdaE G e ≤ 1 := by
  unfold Split.lambdaE
  split_ifs <;> norm_num

/-- The defining property of `λ_e`: `λ_e · κ_e = min{κ_e, 1}` (using `κ_e ≥ 0`). -/
lemma lambdaE_mul_kappa (e : CliqueEdge G) :
    lambdaE G e * kappa G e = min (kappa G e) 1 := by
  by_cases h : G.kappa e = 0 <;> simp_all +decide [Split.lambdaE]
  cases min_cases (1 : ℝ) (G.kappa e)⁻¹ <;> cases min_cases (G.kappa e) 1 <;>
    nlinarith [inv_mul_cancel₀ h, show 0 ≤ G.kappa e from kappa_nonneg G e]

/-- `w₁` is nonnegative on every triangle. On mixed triangles `d_v ≥ 2` since `x < y` are two
    distinct neighbors, so `d_v − 1 ≥ 1 > 0`, and `λ_e ≥ 0`. -/
lemma w1_nonneg (T : Triangle G) : 0 ≤ w1 G T := by
  rcases T with ⟨⟨i, j, k⟩, hik, hjk⟩ | ⟨⟨v, i, j⟩, hij, hi, hj⟩
  · simp [Split.w1]
  · refine div_nonneg (lambdaE_nonneg G ⟨(i, j), hij⟩) (sub_nonneg_of_le ?_)
    exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩

/-
Clique-edge load identity: only mixed triangles `{v,x,y}` with `{x,y} = e` contribute
    (clique triangles have weight `0`), and reindexing by `v` gives
    `Σ_{v : e ⊆ N v} λ_e/(d_v−1) = λ_e · κ_e = min{κ_e, 1}`.
-/
lemma cliqueEdge_load_eq (e : CliqueEdge G) :
    (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inl e) T), w1 G T)
      = min (kappa G e) 1 := by
  -- By definition of `w1`, we can split the sum into clique-triangle and mixed-triangle parts.
  have h_split : ∑ T with G.edgeMem (Sum.inl e) T, G.w1 T = ∑ v ∈ Finset.univ.filter (fun v => e.val.1 ∈ G.N v ∧ e.val.2 ∈ G.N v), (G.lambdaE e) / (((G.N v).card : ℝ) - 1) := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun v : { v : G.ι // ( e.val.1 ∈ G.N v ∧ e.val.2 ∈ G.N v ) } => Sum.inr ⟨ ( v.val, e.val.1, e.val.2 ), by
      exact e.2, by
      exact v.2 ⟩ ) Finset.univ ) ) ];
    · rw [ Finset.sum_image ] <;> simp +decide [ Finset.sum_ite ];
      · refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide [ Split.edgeMem ];
        unfold Split.w1; aesop;
      · intro v w; aesop;
    · rintro ( x | x ) <;> simp +decide [ Split.edgeMem ];
      · exact fun h => rfl;
      · grind;
  rw [ h_split, ← lambdaE_mul_kappa ];
  simp +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _, Split.kappa ]

/-
Cross-edge load bound: the triangles containing cross edge `(v,x)` are mixed triangles
    `{v,x,y}` with `y ∈ N v`, `y ≠ x`; there are at most `d_v − 1` of them, each of weight
    at most `1/(d_v−1)`, so the total is `≤ 1`.
-/
lemma crossEdge_load_le (e : {e : G.ι × Fin G.p // e.2 ∈ G.N e.1}) :
    (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inr e) T), w1 G T) ≤ 1 := by
  rcases e with ⟨ ⟨ v, x ⟩, hx ⟩;
  -- Set `d := (G.N v).card`.
  set d := (G.N v).card;
  -- Termwise bound: each such term is `≤ if (v = w ∧ (x = y ∨ x = z)) then 1/((d:ℝ)-1) else 0`.
  have h_term_bound : ∀ T, edgeMem G (Sum.inr ⟨(v, x), hx⟩) T → w1 G T ≤ if edgeMem G (Sum.inr ⟨(v, x), hx⟩) T then 1 / (d - 1 : ℝ) else 0 := by
    intro T hT;
    rcases T with ( ⟨ ⟨ i, j, k ⟩, hij, hjk ⟩ | ⟨ ⟨ w, y, z ⟩, hyz, hy, hz ⟩ ) <;> simp_all +decide [ Split.w1 ];
    · exact Finset.card_pos.mpr ⟨ x, hx ⟩;
    · rcases hT with ⟨ rfl, rfl | rfl ⟩ <;> simp_all +decide;
      · exact mul_le_of_le_one_left ( inv_nonneg.mpr ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Finset.card_pos.mpr ⟨ x, hy ⟩ ) ) ) ) ( Split.lambdaE_le_one _ _ );
      · exact mul_le_of_le_one_left ( inv_nonneg.mpr ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Finset.card_pos.mpr ⟨ y, hy ⟩ ) ) ) ) ( Split.lambdaE_le_one G ⟨ ( y, x ), hyz ⟩ );
  -- So the mixed part `≤ ∑ t ∈ S, 1/((d:ℝ)-1)` where `S := Finset.univ.filter (fun t => v = t.val.1 ∧ (x = t.val.2.1 ∨ x = t.val.2.2))`.
  have h_sum_bound : (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inr ⟨(v, x), hx⟩) T), w1 G T) ≤ (Finset.univ.filter (fun t : {t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1} => v = t.val.1 ∧ (x = t.val.2.1 ∨ x = t.val.2.2))).card / (d - 1 : ℝ) := by
    refine' le_trans ( Finset.sum_le_sum fun T hT => h_term_bound T <| Finset.mem_filter.mp hT |>.2 ) _;
    simp +decide [ div_eq_mul_inv, Finset.sum_ite ];
    rw [ Finset.filter_true_of_mem ];
    · rw [ show ( Finset.univ.filter fun T : G.Triangle => G.edgeMem ( Sum.inr ⟨ ( v, x ), hx ⟩ ) T ) = Finset.image ( fun t : { t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1 } => Sum.inr t ) ( Finset.univ.filter fun t : { t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1 } => v = t.val.1 ∧ ( x = t.val.2.1 ∨ x = t.val.2.2 ) ) from ?_ ];
      · rw [ Finset.card_image_of_injective _ fun a b h => by aesop ];
      · ext T; cases T <;> simp +decide [ Split.edgeMem ] ;
    · aesop;
  refine le_trans h_sum_bound ?_;
  refine' div_le_one_of_le₀ _ _;
  · -- Define an injection from `S` into `(G.N v).erase x`.
    have h_inj : Finset.card (Finset.image (fun t : {t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1} => if x = t.val.2.1 then t.val.2.2 else t.val.2.1) (Finset.univ.filter (fun t : {t : G.ι × Fin G.p × Fin G.p // t.2.1 < t.2.2 ∧ t.2.1 ∈ G.N t.1 ∧ t.2.2 ∈ G.N t.1} => v = t.val.1 ∧ (x = t.val.2.1 ∨ x = t.val.2.2)))) ≤ d - 1 := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.erase ( G.N v ) x;
      · grind;
      · rw [ Finset.card_erase_of_mem hx ];
    rw [ Finset.card_image_of_injOn ] at h_inj;
    · exact le_trans ( Nat.cast_le.mpr h_inj ) ( by rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ x, hx ⟩ ) ] );
    · intro t ht t' ht' h_eq;
      grind;
  · exact sub_nonneg_of_le ( mod_cast Finset.card_pos.mpr ⟨ x, hx ⟩ )

/-- Phase I is feasible: nonneg weights, per-edge load ≤ 1 (clique edge load `= min{κ_e,1}`;
    a cross edge `vx` lies in ≤ `d_v−1` triangles each of weight ≤ `1/(d_v−1)`). ROADMAP. -/
theorem feasiblePacking_w1 : FeasiblePacking G (w1 G) := by
  refine ⟨w1_nonneg G, ?_⟩
  intro e
  cases e with
  | inl e => rw [cliqueEdge_load_eq G e]; exact min_le_right _ _
  | inr e => exact crossEdge_load_le G e

/-
Value of Phase I (paper (4.3)): `|w₁| = Σ_e min{κ_e, 1} = |H| + Σ_{e∈L} κ_e`,
    since every positive Phase-I triangle contains exactly one clique edge. ROADMAP.
-/
theorem w1_value :
    (∑ T, w1 G T) = ∑ e : CliqueEdge G, min (kappa G e) 1 := by
  rw [ ← Finset.sum_congr rfl fun e _ => cliqueEdge_load_eq G e ];
  have h_split_sum : ∑ T, G.w1 T = ∑ e : CliqueEdge G, ∑ T, if G.edgeMem (Sum.inl e) T then G.w1 T else 0 := by
    have h_split_sum : ∀ T : Triangle G, G.w1 T = ∑ e : CliqueEdge G, if G.edgeMem (Sum.inl e) T then G.w1 T else 0 := by
      intro T; rcases T with ( ⟨ ⟨ i, j, k ⟩, hij, hjk ⟩ | ⟨ ⟨ v, x, y ⟩, hxy, hx, hy ⟩ ) <;> simp +decide [ Split.w1, Split.edgeMem ] ;
      rw [ Finset.sum_eq_single ⟨ ( x, y ), hxy ⟩ ] <;> aesop;
    rw [ Finset.sum_congr rfl fun T _ => h_split_sum T, Finset.sum_comm ];
  simpa only [ Finset.sum_filter ] using h_split_sum

/-! ### S-PHASE — assembly interface (Mcov + edge count + deficit + uniform lower bound) -/

/-- Clique triangles `{a<b<c}` (the clique summand of `Triangle`). -/
abbrev CliqueTri (G : Split) : Type :=
  {t : Fin G.p × Fin G.p × Fin G.p // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

/-- Residual cover polytope `P_p` (paper (4.5)): `z ∈ [0,1]^{E(K)}` with, for every clique
    triangle `t`, total `z`-weight on its three edges `≥ 1`. -/
def ResidualCover (z : CliqueEdge G → ℝ) : Prop :=
  (∀ e, 0 ≤ z e ∧ z e ≤ 1) ∧
    ∀ t : CliqueTri G,
      1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), z e

/-- Residual-cover LP value for an arbitrary objective vector `c`. -/
noncomputable def McovObj (c : CliqueEdge G → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ z : CliqueEdge G → ℝ, ResidualCover G z ∧ v = ∑ e, c e * z e}

/-- `M(κ)` (paper (4.6)): the residual-cover LP value, objective `Σ_e (1−κ_e) z_e`. -/
noncomputable def Mcov : ℝ := McovObj G (fun e => 1 - kappa G e)

/-- `q ≤ |ι|`. -/
theorem q_le_card : G.q ≤ Fintype.card G.ι := by
  simpa [Split.q, Finset.card_univ] using
    Finset.card_filter_le (Finset.univ) (fun v => 2 ≤ (G.N v).card)

/-- `b₁ ≤ |ι|`. -/
theorem b1_le_card : G.b1 ≤ Fintype.card G.ι := by
  simpa [Split.b1, Finset.card_univ] using
    Finset.card_filter_le (Finset.univ) (fun v => (G.N v).card = 1)

/-- `n = p + |ι|` (definitional). -/
theorem n_eq : G.n = G.p + Fintype.card G.ι := rfl

/-- Degree-sum identity `Σ_v d_v = b≥2 + b₁` (per-vertex case split on `card ∈ {0,1,≥2}`). -/
theorem degree_sum_eq : ∑ v : G.ι, (G.N v).card = G.bge2 + G.b1 := by
  unfold Split.bge2 Split.b1;
  rw [ Finset.sum_filter, Finset.card_filter ];
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases Finset.card ( G.N x ) with ( _ | _ | n ) <;> simp +arith +decide

/-- **(L1) Edge count.** `|E| = C(p,2) + b≥2 + b₁`  (paper (2.1)). -/
theorem edgeCount_eq :
    (G.edgeCount : ℝ) = (Nat.choose G.p 2 : ℝ) + (G.bge2 : ℝ) + (G.b1 : ℝ) := by
  have h := G.degree_sum_eq
  unfold edgeCount
  push_cast [h]
  ring

-- (L25) S-DEFICIT `nu3star_ge_Vcom` is assembled at the END of this namespace (after the
-- deficit_algebra sub-tree + the w_com machinery). See below.

/-! #### Mcov_lower sub-tree (§5–7): affine reduction + pure profile + q=0 -/

/-- Pure-profile edge weight `a^S_e = 1_{e⊆S}/(|S|−1)` (paper (5.1)). -/
noncomputable def aS (S : Finset (Fin G.p)) (e : CliqueEdge G) : ℝ :=
  (if e.val.1 ∈ S ∧ e.val.2 ∈ S then (1 : ℝ) else 0) / ((S.card : ℝ) - 1)

/-- Number of active independent vertices whose neighborhood is exactly `S`. -/
def nS (S : Finset (Fin G.p)) : ℕ :=
  (Finset.univ.filter (fun v => 2 ≤ (G.N v).card ∧ G.N v = S)).card

/-- Pure-profile load `κ^S = q · a^S` (paper (6.1)). -/
noncomputable def kappaS (S : Finset (Fin G.p)) (e : CliqueEdge G) : ℝ :=
  (G.q : ℝ) * aS G S e

/-- Profile index: clique subsets `S` with `|S| ≥ 2`. -/
def Profiles (G : Split) : Finset (Finset (Fin G.p)) :=
  (Finset.univ : Finset (Fin G.p)).powerset.filter (fun S => 2 ≤ S.card)

/-
`z ≡ 1` is a feasible residual cover (each clique triangle has ≥ 1 edge).
-/
theorem residualCover_one : ResidualCover G (fun _ => 1) := by
  constructor <;> norm_num;
  intro a b c hab hbc; use ⟨ ( a, b ), hab ⟩ ; simp +decide [ Split.edgeMem ] ;

/-
**(ec. 5.3)** Profile convex combination (`q > 0`): `Σ_S λ_S = 1` and `κ = Σ_S λ_S κ^S`,
    with `λ_S = n_S/q ≥ 0`.
-/
theorem profile_convex_combo (hq : 0 < G.q) :
    (∑ S ∈ Profiles G, ((nS G S : ℝ) / (G.q : ℝ))) = 1 ∧
    (∀ e, kappa G e = ∑ S ∈ Profiles G, ((nS G S : ℝ) / (G.q : ℝ)) * kappaS G S e) := by
  constructor;
  · rw [ ← Finset.sum_div, div_eq_iff ] <;> norm_cast;
    · simp +decide [ Split.q, Split.nS ];
      rw [ ← Finset.card_biUnion ];
      · congr with v ; simp +decide [ Split.Profiles ];
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
    · omega;
  · intro e;
    -- By definition of $kappa$, we can rewrite the left-hand side as a sum over active vertices.
    have h_kappa_sum : G.kappa e = ∑ v ∈ Finset.univ.filter (fun v => 2 ≤ (G.N v).card ∧ e.val.1 ∈ G.N v ∧ e.val.2 ∈ G.N v), (1 : ℝ) / ((G.N v).card - 1) := by
      unfold Split.kappa;
      congr 1 with v ; simp +decide [ Finset.mem_filter ];
      exact fun h1 h2 => Finset.one_lt_card.2 ⟨ _, h1, _, h2, e.2.ne ⟩;
    -- By definition of $nS$, we can rewrite the right-hand side as a sum over profiles.
    have h_nS_sum : ∑ v ∈ Finset.univ.filter (fun v => 2 ≤ (G.N v).card ∧ e.val.1 ∈ G.N v ∧ e.val.2 ∈ G.N v), (1 : ℝ) / ((G.N v).card - 1) = ∑ S ∈ G.Profiles, ∑ v ∈ Finset.univ.filter (fun v => 2 ≤ (G.N v).card ∧ G.N v = S ∧ e.val.1 ∈ S ∧ e.val.2 ∈ S), (1 : ℝ) / ((S.card : ℝ) - 1) := by
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun v hv => ⟨ G.N v, v ⟩ ) _ _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_powerset ];
      · exact fun v hv₁ hv₂ hv₃ => Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr ( Finset.subset_univ _ ), hv₁ ⟩;
      · grind;
    convert h_nS_sum using 2;
    unfold Split.kappaS Split.aS Split.nS;
    split_ifs <;> simp_all +decide [ ← mul_assoc, ne_of_gt hq ]

/-
**(Lemma 5.1)** LP concavity in the objective: if `c = Σ_i λ_i c_i` with `λ_i ≥ 0` over the
    (nonempty) polytope `P_p`, then `Σ_i λ_i M(c_i) ≤ M(c)`.
-/
theorem McovObj_concave {ι' : Type*} (t : Finset ι') (lam : ι' → ℝ)
    (cs : ι' → CliqueEdge G → ℝ) (c : CliqueEdge G → ℝ)
    (hne : ∃ z, ResidualCover G z)
    (hlam : ∀ i ∈ t, 0 ≤ lam i)
    (hc : ∀ e, c e = ∑ i ∈ t, lam i * cs i e) :
    (∑ i ∈ t, lam i * McovObj G (cs i)) ≤ McovObj G c := by
  refine' le_csInf _ _;
  · exact ⟨ _, ⟨ hne.choose, hne.choose_spec, rfl ⟩ ⟩;
  · rintro _ ⟨ z, hz, rfl ⟩
    have h_bdd : ∀ i ∈ t, McovObj G (cs i) ≤ ∑ e, cs i e * z e := by
      exact fun i hi => csInf_le ⟨ ∑ e, Min.min ( cs i e ) 0, by rintro x ⟨ w, hw, rfl ⟩ ; exact Finset.sum_le_sum fun e _ => by cases le_or_gt 0 ( cs i e ) <;> nlinarith [ hw.1 e, min_le_left ( cs i e ) 0, min_le_right ( cs i e ) 0 ] ⟩ ⟨ z, hz, rfl ⟩
    generalize_proofs at *;
    convert Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( h_bdd i hi ) ( hlam i hi ) using 1;
    simp +decide only [hc, sum_mul, Finset.mul_sum _ _ _];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-- **Weak LP duality** for the cover LP `McovObj`: any dual-feasible `(y,w) ≥ 0` lower-bounds
    it. Citation-free (weak duality + Fubini + `z ≤ 1`). -/
theorem weak_cover_duality (c : CliqueEdge G → ℝ)
    (y : CliqueTri G → ℝ) (w : CliqueEdge G → ℝ)
    (hy : ∀ t, 0 ≤ y t) (hw : ∀ e, 0 ≤ w e)
    (hdf : ∀ e : CliqueEdge G,
        (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t)
          ≤ c e + w e) :
    (∑ t, y t) - (∑ e, w e) ≤ McovObj G c := by
  unfold McovObj
  apply le_csInf
  · exact ⟨_, (fun _ => (1 : ℝ)), residualCover_one G, rfl⟩
  · rintro v ⟨z, hz, rfl⟩
    obtain ⟨hz01, hzcov⟩ := hz
    -- Pointwise lower bound on the objective using dual feasibility.
    have h1 : ∑ e, ((∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t) - w e) * z e
                ≤ ∑ e, c e * z e := by
      apply Finset.sum_le_sum
      intro e _
      have hze : 0 ≤ z e := (hz01 e).1
      have hde := hdf e
      nlinarith [hde, hze]
    -- Distribute the subtraction.
    have h2 : ∑ e, ((∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t) - w e) * z e
               = (∑ e, (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t) * z e)
                 - (∑ e, w e * z e) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    -- Fibrewise swap of the double sum over the incidence relation.
    have h3 : (∑ e, (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t) * z e)
               = ∑ t : CliqueTri G, y t * (∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), z e) := by
      simp_rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : edgeMem G (Sum.inl e) (Sum.inl t) <;> simp [h, mul_comm]
    -- The cover constraint forces each triangle's row to dominate `y t`.
    have h4 : ∑ t : CliqueTri G, y t
               ≤ ∑ t : CliqueTri G, y t * (∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), z e) := by
      apply Finset.sum_le_sum
      intro t _
      nlinarith [hzcov t, hy t]
    -- The `z ≤ 1` bound controls the `w` contribution.
    have h5 : ∑ e, w e * z e ≤ ∑ e, w e := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith [hw e, (hz01 e).1, (hz01 e).2]
    linarith [h1, h2, h3, h4, h5]

/-
Real value of `C(n,3)` for `n ≥ 2`.
-/
lemma choose3_cast_real {n : ℕ} (hn : 2 ≤ n) :
    (Nat.choose n 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  rcases n with ( _ | _ | _ | n ) <;> norm_num at *;
  rw [ Nat.cast_choose ] <;> try linarith;
  rw [ div_eq_div_iff ] <;> first | positivity | push_cast [ Nat.factorial ] ; ring;

/-! #### `pure_profile_dual_cert`: orbit counting + régime construction -/

/-
Number of clique triangles fully inside `S` is `C(|S|,3)`.
-/
lemma card_triIn (S : Finset (Fin G.p)) :
    (Finset.univ.filter (fun t : CliqueTri G =>
        t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S)).card = S.card.choose 3 := by
  have h_card_triples : Finset.card (Finset.filter (fun t : Fin G.p × Fin G.p × Fin G.p => t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2) (Finset.univ : Finset (Fin G.p × Fin G.p × Fin G.p))) = Finset.card (Finset.powersetCard 3 S) := by
    refine' Finset.card_bij ( fun t ht => { t.1, t.2.1, t.2.2 } ) _ _ _ <;> simp +decide [ Finset.mem_powersetCard ];
    · grind;
    · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      grind;
    · intro b hb hb'; rw [ Finset.card_eq_three ] at hb'; obtain ⟨ a, b, c, ha, hb, hc, hab, hbc, hca ⟩ := hb'; simp_all +decide [ Finset.subset_iff ] ;
      grind +splitImp;
  convert h_card_triples using 1;
  · rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; aesop;
  · rw [ Finset.card_powersetCard ]

/-
Number of clique triangles through an `SS`-edge that are fully inside `S` is `|S|-2`.
-/
lemma card_triIn_through_edge (S : Finset (Fin G.p)) (e : CliqueEdge G)
    (he : e.val.1 ∈ S ∧ e.val.2 ∈ S) :
    (Finset.univ.filter (fun t : CliqueTri G =>
        edgeMem G (Sum.inl e) (Sum.inl t) ∧
          (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S))).card = S.card - 2 := by
  convert Finset.card_image_of_injOn _;
  rotate_left;
  rotate_left;
  exact { x : Fin G.p // x ∈ S \ { e.val.1, e.val.2 } };
  exact Finset.univ;
  use fun x => ⟨ ( if x.val < e.val.1 then ( x.val, e.val.1, e.val.2 ) else if x.val < e.val.2 then ( e.val.1, x.val, e.val.2 ) else ( e.val.1, e.val.2, x.val ) ), by
    grind +suggestions ⟩
  all_goals generalize_proofs at *;
  exact instDecidableEqOfLawfulBEq;
  · intro x hx y hy; simp +decide [ Fin.ext_iff ] at *;
    grind;
  · ext ⟨ t, ht ⟩ ; simp +decide [ Split.edgeMem ] ;
    grind;
  · simp +decide [ Finset.card_sdiff, * ];
    rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop

/-
A triangle through a non-`SS` edge cannot be fully inside `S`.
-/
lemma not_triIn_of_edge_not_subset (S : Finset (Fin G.p)) (e : CliqueEdge G)
    (he : ¬ (e.val.1 ∈ S ∧ e.val.2 ∈ S)) (t : CliqueTri G)
    (ht : edgeMem G (Sum.inl e) (Sum.inl t)) :
    ¬ (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S) := by
  intro h; rcases ht with ( ht | ht | ht ) <;> simp_all +decide ;

/-
Row value at an `SS`-edge for the 2-value multiplier `y = α·1_{t⊆S} + γ·1_{t⊄S}`.
-/
set_option maxHeartbeats 1600000 in
lemma row_SS (S : Finset (Fin G.p)) (α γ : ℝ) (e : CliqueEdge G)
    (he : e.val.1 ∈ S ∧ e.val.2 ∈ S) :
    (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)),
        (if (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S) then α else γ))
      = α * ((S.card : ℝ) - 2) + γ * ((G.p : ℝ) - S.card) := by
  -- By definition of $aS$, we know that
  have h_aS : (∑ t ∈ Finset.univ.filter (fun t : CliqueTri G => edgeMem G (Sum.inl e) (Sum.inl t) ∧ (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S)), 1) = S.card - 2 := by
    convert card_triIn_through_edge G S e he using 1;
    norm_num;
  have h_card : (Finset.univ.filter (fun t : CliqueTri G => edgeMem G (Sum.inl e) (Sum.inl t))).card = G.p - 2 := by
    -- Let's count the number of clique triangles containing the edge $e$.
    have h_count : Finset.card (Finset.filter (fun t : Fin G.p × Fin G.p × Fin G.p => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ (t.1 = e.val.1 ∧ t.2.1 = e.val.2 ∨ t.1 = e.val.1 ∧ t.2.2 = e.val.2 ∨ t.2.1 = e.val.1 ∧ t.2.2 = e.val.2)) (Finset.univ : Finset (Fin G.p × Fin G.p × Fin G.p))) = G.p - 2 := by
      rcases e with ⟨ ⟨ i, j ⟩, hij ⟩ ; simp +decide [ Finset.filter_or, Finset.filter_and, hij ] ;
      rw [ show ( Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.1 < a.2.1 ) Finset.univ ∩ ( Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.2.1 < a.2.2 ) Finset.univ ∩ ( Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.1 = i ) Finset.univ ∩ Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.2.1 = j ) Finset.univ ∪ ( Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.1 = i ) Finset.univ ∩ Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.2.2 = j ) Finset.univ ∪ Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.2.1 = i ) Finset.univ ∩ Finset.filter ( fun a : Fin G.p × Fin G.p × Fin G.p => a.2.2 = j ) Finset.univ ) ) ) ) = Finset.image ( fun k : Fin G.p => ( i, j, k ) ) ( Finset.Ioi j ) ∪ Finset.image ( fun k : Fin G.p => ( i, k, j ) ) ( Finset.Ioo i j ) ∪ Finset.image ( fun k : Fin G.p => ( k, i, j ) ) ( Finset.Iio i ) from ?_ ];
      · rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
        · grind +splitIndPred;
        · rw [ Finset.disjoint_left ] ; aesop;
        · constructor <;> rw [ Finset.disjoint_left ] <;> aesop;
      · grind;
    convert h_count using 1;
    refine' Finset.card_bij ( fun t ht => t.val ) _ _ _ <;> simp +decide [ edgeMem ]; all_goals grind;
  have h_card_S : S.card ≥ 2 := by
    exact Finset.one_lt_card.2 ⟨ _, he.1, _, he.2, ne_of_lt e.2 ⟩
  have h_card_G : S.card ≤ G.p := by
    exact le_trans ( Finset.card_le_univ _ ) ( by norm_num )
  have h_card_Gp : (G.p - 2 : ℕ) = (G.p : ℝ) - 2 := by
    rw [ Nat.cast_sub ] <;> norm_num ; linarith
  have h_card_Sp : (S.card - 2 : ℕ) = (S.card : ℝ) - 2 := by
    rw [ Nat.cast_sub ] <;> norm_num ; linarith;
  simp_all +decide [ Finset.sum_ite ];
  simp_all +decide [ Finset.filter_filter, mul_comm ];
  rw [ show ( Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ∧ ( ( t.val.1 ∈ S → t.val.2.1 ∈ S → t.val.2.2 ∉ S ) ) ) Finset.univ ) = Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ) Finset.univ \ Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ∧ ( t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S ) ) Finset.univ from ?_, Finset.card_sdiff ];
  · rw [ Nat.cast_sub ];
    · rw [ show ( Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ∧ ( t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S ) ) Finset.univ ∩ Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ) Finset.univ ) = Finset.filter ( fun t : CliqueTri G => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ∧ ( t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S ) ) Finset.univ from Finset.inter_eq_left.mpr fun x hx => by aesop ] ; aesop;
    · exact Finset.card_le_card fun x hx => by aesop;
  · grind

/-
Row value at a non-`SS` edge: every triangle through it is `⊄S`, so the row is `γ·(p-2)`.
-/
set_option maxHeartbeats 1600000 in
lemma row_nonSS (S : Finset (Fin G.p)) (α γ : ℝ) (e : CliqueEdge G)
    (he : ¬ (e.val.1 ∈ S ∧ e.val.2 ∈ S)) :
    (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)),
        (if (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S) then α else γ))
      = γ * ((G.p : ℝ) - 2) := by
  rw [ Finset.sum_congr rfl fun t ht => if_neg <| not_triIn_of_edge_not_subset G S e he t <| Finset.mem_filter.mp ht |>.2 ] ; norm_num [ mul_comm ];
  -- Apply the lemma that states the number of triangles containing a given edge is p-2.
  have h_card : (Finset.univ.filter (fun t : CliqueTri G => edgeMem G (Sum.inl e) (Sum.inl t))).card = G.p - 2 := by
    rcases e with ⟨ ⟨ i, j ⟩, hij ⟩;
    convert Finset.card_filter ( fun t : Fin G.p × Fin G.p × Fin G.p => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ ( i = t.1 ∧ j = t.2.1 ∨ i = t.1 ∧ j = t.2.2 ∨ i = t.2.1 ∧ j = t.2.2 ) ) Finset.univ using 1;
    · refine' Finset.card_bij ( fun t ht => ( t.val.1, t.val.2.1, t.val.2.2 ) ) _ _ _ <;> simp +decide [ Split.edgeMem ]; all_goals tauto;
    · rw [ Finset.sum_ite ];
      rw [ show ( Finset.filter ( fun x : Fin G.p × Fin G.p × Fin G.p => x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ ( i = x.1 ∧ j = x.2.1 ∨ i = x.1 ∧ j = x.2.2 ∨ i = x.2.1 ∧ j = x.2.2 ) ) Finset.univ ) = Finset.image ( fun k : Fin G.p => ( i, j, k ) ) ( Finset.Ioi j ) ∪ Finset.image ( fun k : Fin G.p => ( i, k, j ) ) ( Finset.Ioo i j ) ∪ Finset.image ( fun k : Fin G.p => ( k, i, j ) ) ( Finset.Iio i ) from ?_, Finset.sum_union, Finset.sum_union ] <;> norm_num;
      · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        grind;
      · rw [ Finset.disjoint_left ] ; aesop;
      · simp +decide [ Finset.disjoint_left ];
        grind;
      · grind
  rw [h_card]
  norm_cast;
  exact Or.inl ( by rw [ Int.subNatNat_of_le ] ; linarith [ show 2 ≤ G.p from by linarith [ Fin.is_lt e.val.1, Fin.is_lt e.val.2, show ( e.val.1 : ℕ ) < e.val.2 from e.2 ] ] )

/-
Total `y`-mass: `α·C(s,3) + γ·(C(p,3)-C(s,3))`.
-/
lemma sum_y_total (S : Finset (Fin G.p)) (α γ : ℝ) :
    (∑ t : CliqueTri G, (if (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S) then α else γ))
      = α * (S.card.choose 3 : ℝ) + γ * ((G.p.choose 3 : ℝ) - (S.card.choose 3 : ℝ)) := by
  rw [ ← card_triIn G S ] at * ; simp_all +decide [ Finset.sum_ite ];
  rw [ show ( Finset.univ.filter fun x : CliqueTri G => ( x.val.1 ∈ S → x.val.2.1 ∈ S → x.val.2.2 ∉ S ) ) = Finset.univ \ ( Finset.univ.filter fun x : CliqueTri G => ( x.val.1 ∈ S ∧ x.val.2.1 ∈ S ∧ x.val.2.2 ∈ S ) ) by ext; aesop, Finset.card_sdiff ] ; norm_num;
  rw [ Nat.cast_sub ];
  · rw [ show Fintype.card G.CliqueTri = Nat.choose G.p 3 from ?_ ] ; ring!;
    convert card_triIn G ( Finset.univ : Finset ( Fin G.p ) ) using 1;
    · simp +decide [ Fintype.card_subtype ];
    · simp +decide [ Finset.card_univ ];
  · exact Finset.card_le_univ _

/-
Total `w`-mass: `W·C(s,2)` (weight `W` on the `C(s,2)` `SS`-edges, `0` elsewhere).
-/
lemma sum_w_total (S : Finset (Fin G.p)) (W : ℝ) :
    (∑ e : CliqueEdge G, (if (e.val.1 ∈ S ∧ e.val.2 ∈ S) then W else (0:ℝ)))
      = W * (S.card.choose 2 : ℝ) := by
  convert congr_arg ( fun x : ℕ => W * x ) ( card_cliqueEdges_in G S ) using 1;
  simp +decide [ mul_comm, Finset.sum_ite ]

/-
Case-II core arithmetic fact `N_II ≥ 0`, split on `b = p-s = 0` vs `b ≥ 1`.
-/
lemma NII_nonneg (p s q : ℝ) (hs : 2 ≤ s) (hsp : s ≤ p) (hq : 0 ≤ q)
    (H : (s-1)*(s-2) ≤ q*(p-2)) (hb : p = s ∨ s + 1 ≤ p) :
    0 ≤ 2*p^2*q + 4*p^2 + p*q^2 - 6*p*q*s - 4*p*q - 8*p - 2*q^2 + 12*q*s
          + 4*s^3 - 12*s^2 + 8*s := by
  cases hb;
  · subst_vars; nlinarith [ sq_nonneg ( q - 2 * s ) ] ;
  · by_contra h_neg;
    have h_nonneg : 0 ≤ (p - 2) * (2 * p ^ 2 * q + 4 * p ^ 2 + p * q ^ 2 - 6 * p * q * s - 4 * p * q - 8 * p - 2 * q ^ 2 + 12 * q * s + 4 * s ^ 3 - 12 * s ^ 2 + 8 * s) := by
      by_cases hq2 : q ≥ 2 * s - p;
      · have h_nonneg : 0 ≤ (p - 2) * (q - (3 * s - p)) ^ 2 := by
          exact mul_nonneg ( by linarith ) ( sq_nonneg _ );
        nlinarith [ mul_le_mul_of_nonneg_left hq2 ( sub_nonneg.mpr hsp ), mul_le_mul_of_nonneg_left hq2 ( sub_nonneg.mpr hs ), mul_le_mul_of_nonneg_left hq2 ( sub_nonneg.mpr ‹s + 1 ≤ p› ), mul_le_mul_of_nonneg_left ‹s + 1 ≤ p› ( sub_nonneg.mpr hs ), mul_le_mul_of_nonneg_left ‹s + 1 ≤ p› ( sub_nonneg.mpr ‹s + 1 ≤ p› ) ];
      · nlinarith [ sq_nonneg ( p - 2 ), sq_nonneg ( q - ( 3 * s - p ) ) ];
    exact h_neg ( by nlinarith )

/-
Case-I value equals `(p(p-1) - q s)/6`, which dominates `R(p,q) - p/2`.
-/
lemma dualcert_caseI (p s q : ℝ) (hs : 3 ≤ s) (hsp : s ≤ p) (hp : 3 ≤ p) (hq : 0 ≤ q) :
    ((2*p^2 - 2*p*q - q^2)/12) - p/2
      ≤ (((1 - q/(s-1)) - (p-s)/(p-2))/(s-2)) * (s*(s-1)*(s-2)/6)
          + (1/(p-2)) * ((p*(p-1)*(p-2) - s*(s-1)*(s-2))/6) := by
  have hrhs : (((1 - q/(s-1)) - (p-s)/(p-2))/(s-2)) * (s*(s-1)*(s-2)/6) + (1/(p-2)) * ((p*(p-1)*(p-2) - s*(s-1)*(s-2))/6) = (p*(p-1) - q*s)/6 := by
    grind;
  nlinarith [ mul_nonneg hq ( sub_nonneg.mpr hsp ), sq_nonneg q ]

/-
Case-II value dominates `R(p,q) - p/2`.
-/
lemma dualcert_caseII (p s q : ℝ) (hs : 2 ≤ s) (hsp : s ≤ p) (hp : 3 ≤ p) (hq : 0 ≤ q)
    (H : (s-1)*(s-2) ≤ q*(p-2)) (hb : p = s ∨ s + 1 ≤ p) :
    ((2*p^2 - 2*p*q - q^2)/12) - p/2
      ≤ (1/(p-2)) * ((p*(p-1)*(p-2) - s*(s-1)*(s-2))/6)
          - ((p-s)/(p-2) - (1 - q/(s-1))) * (s*(s-1)/2) := by
  have hs1 : s - 1 ≠ 0 := by
    linarith
  have hp2 : p - 2 ≠ 0 := by
    linarith
  field_simp at *;
  rw [ le_div_iff₀ ] <;> nlinarith [ NII_nonneg p s q hs hsp hq H hb ]

/-
**Pure-profile dual certificate** (DELICATE, régimen-dependent witness): an explicit
    dual-feasible `(y,w)` with dual value `≥ R(p,q) − p/2`. Citation-free (∃ witness).
-/
theorem pure_profile_dual_cert (S : Finset (Fin G.p)) (hS : S ∈ Profiles G) :
    ∃ (y : CliqueTri G → ℝ) (w : CliqueEdge G → ℝ),
      (∀ t, 0 ≤ y t) ∧ (∀ e, 0 ≤ w e) ∧
      (∀ e : CliqueEdge G,
        (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t)
          ≤ (1 - kappaS G S e) + w e) ∧
      ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2 ≤ (∑ t, y t) - (∑ e, w e) := by
  classical
  have h2S : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
  have hSp : S.card ≤ G.p := by
    simpa [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ S)
  have hp2N : 2 ≤ G.p := le_trans h2S hSp
  have hsR2 : (2:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast h2S
  have hspR : (S.card:ℝ) ≤ (G.p:ℝ) := by exact_mod_cast hSp
  have hqR0 : (0:ℝ) ≤ (G.q:ℝ) := by positivity
  have hpR2 : (2:ℝ) ≤ (G.p:ℝ) := by exact_mod_cast hp2N
  have hRq : ((Rq (G.p:ℚ) (G.q:ℚ):ℚ):ℝ)
      = (2*(G.p:ℝ)^2 - 2*(G.p:ℝ)*(G.q:ℝ) - (G.q:ℝ)^2)/12 := by
    simp only [Rq]; push_cast; ring
  have main : ∀ (α γ W : ℝ), 0 ≤ α → 0 ≤ γ → 0 ≤ W →
      (α * ((S.card:ℝ) - 2) + γ * ((G.p:ℝ) - (S.card:ℝ)) ≤ (1 - (G.q:ℝ)/((S.card:ℝ) - 1)) + W) →
      (γ * ((G.p:ℝ) - 2) ≤ 1) →
      ((2*(G.p:ℝ)^2 - 2*(G.p:ℝ)*(G.q:ℝ) - (G.q:ℝ)^2)/12 - (G.p:ℝ)/2
          ≤ α * ((S.card:ℝ)*((S.card:ℝ)-1)*((S.card:ℝ)-2)/6)
            + γ * ((G.p:ℝ)*((G.p:ℝ)-1)*((G.p:ℝ)-2)/6
                    - (S.card:ℝ)*((S.card:ℝ)-1)*((S.card:ℝ)-2)/6)
            - W * ((S.card:ℝ)*((S.card:ℝ)-1)/2)) →
      (∃ (y : CliqueTri G → ℝ) (w : CliqueEdge G → ℝ),
        (∀ t, 0 ≤ y t) ∧ (∀ e, 0 ≤ w e) ∧
        (∀ e : CliqueEdge G,
          (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), y t)
            ≤ (1 - kappaS G S e) + w e) ∧
        ((Rq (G.p:ℚ) (G.q:ℚ):ℚ):ℝ) - (G.p:ℝ)/2 ≤ (∑ t, y t) - (∑ e, w e)) := by
    intro α γ W hα hγ hW hfSS hfnon hval
    refine ⟨fun t => if (t.val.1 ∈ S ∧ t.val.2.1 ∈ S ∧ t.val.2.2 ∈ S) then α else γ,
            fun e => if (e.val.1 ∈ S ∧ e.val.2 ∈ S) then W else 0, ?_, ?_, ?_, ?_⟩
    · intro t; dsimp only; split_ifs <;> assumption
    · intro e; dsimp only; split_ifs with h
      · exact hW
      · exact le_refl 0
    · intro e
      by_cases he : e.val.1 ∈ S ∧ e.val.2 ∈ S
      · have hk : (1:ℝ) - kappaS G S e = 1 - (G.q:ℝ)/((S.card:ℝ) - 1) := by
          unfold kappaS aS; rw [if_pos he]; ring
        simp only [row_SS G S α γ e he, if_pos he, hk]
        exact hfSS
      · have hk : (1:ℝ) - kappaS G S e = 1 := by
          unfold kappaS aS; rw [if_neg he]; ring
        simp only [row_nonSS G S α γ e he, if_neg he, hk]
        linarith [hfnon]
    · simp only [sum_y_total G S α γ, sum_w_total G S W, hRq,
                 choose3_cast_real h2S, choose3_cast_real hp2N, Nat.cast_choose_two]
      exact hval
  by_cases hp3 : 3 ≤ G.p
  · have hp3R : (3:ℝ) ≤ (G.p:ℝ) := by exact_mod_cast hp3
    have hp2ne : (G.p:ℝ) - 2 ≠ 0 := by linarith
    by_cases hcase : 3 ≤ S.card ∧ G.q * (G.p - 2) ≤ (S.card - 1) * (S.card - 2)
    · have hs3R : (3:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast hcase.1
      have hs1ne : (S.card:ℝ) - 1 ≠ 0 := by linarith
      have hs2ne : (S.card:ℝ) - 2 ≠ 0 := by linarith
      have hcaseR : (G.q:ℝ) * ((G.p:ℝ) - 2) ≤ ((S.card:ℝ) - 1) * ((S.card:ℝ) - 2) := by
        have h := (Nat.cast_le (α := ℝ)).mpr hcase.2
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp2N, Nat.cast_sub (by omega : 1 ≤ S.card),
            Nat.cast_sub h2S] at h
        push_cast at h; linarith
      refine main (((1 - (G.q:ℝ)/((S.card:ℝ) - 1)) - ((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2))/((S.card:ℝ) - 2))
                  (1/((G.p:ℝ) - 2)) 0 ?_ ?_ (le_refl 0) ?_ ?_ ?_
      · apply div_nonneg _ (by linarith)
        rw [show (1 - (G.q:ℝ)/((S.card:ℝ) - 1)) - ((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2)
              = (((S.card:ℝ) - 1)*((S.card:ℝ) - 2) - (G.q:ℝ)*((G.p:ℝ) - 2))/(((S.card:ℝ) - 1)*((G.p:ℝ) - 2)) from by
              field_simp; ring]
        exact div_nonneg (by linarith [hcaseR]) (mul_nonneg (by linarith) (by linarith))
      · exact div_nonneg zero_le_one (by linarith)
      · rw [show (((1 - (G.q:ℝ)/((S.card:ℝ) - 1)) - ((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2))/((S.card:ℝ) - 2)) * ((S.card:ℝ) - 2)
              + (1/((G.p:ℝ) - 2)) * ((G.p:ℝ) - (S.card:ℝ)) = 1 - (G.q:ℝ)/((S.card:ℝ) - 1) from by
              field_simp; ring]
        linarith
      · rw [show (1/((G.p:ℝ) - 2)) * ((G.p:ℝ) - 2) = 1 from by field_simp]
      · rw [zero_mul, sub_zero]
        exact (dualcert_caseI (G.p:ℝ) (S.card:ℝ) (G.q:ℝ) hs3R hspR hp3R hqR0).trans (le_of_eq (by ring))
    · have hs1ne : (S.card:ℝ) - 1 ≠ 0 := by
        have : (1:ℝ) ≤ (S.card:ℝ) := by exact_mod_cast (by omega : 1 ≤ S.card)
        linarith
      have Hnat : (S.card - 1) * (S.card - 2) ≤ G.q * (G.p - 2) := by
        by_cases h3 : 3 ≤ S.card
        · exact le_of_lt (not_le.mp (not_and.mp hcase h3))
        · have he2 : S.card = 2 := by omega
          rw [he2]; simp
      have HR : ((S.card:ℝ) - 1) * ((S.card:ℝ) - 2) ≤ (G.q:ℝ) * ((G.p:ℝ) - 2) := by
        have h := (Nat.cast_le (α := ℝ)).mpr Hnat
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ S.card), Nat.cast_sub h2S,
            Nat.cast_sub hp2N] at h
        push_cast at h; linarith
      have hb : (G.p:ℝ) = (S.card:ℝ) ∨ (S.card:ℝ) + 1 ≤ (G.p:ℝ) := by
        rcases Nat.eq_or_lt_of_le hSp with h | h
        · left; exact_mod_cast h.symm
        · right; have : S.card + 1 ≤ G.p := h; exact_mod_cast this
      refine main 0 (1/((G.p:ℝ) - 2))
                  (((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2) - (1 - (G.q:ℝ)/((S.card:ℝ) - 1)))
                  (le_refl 0) ?_ ?_ ?_ ?_ ?_
      · exact div_nonneg zero_le_one (by linarith)
      · rw [show ((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2) - (1 - (G.q:ℝ)/((S.card:ℝ) - 1))
              = ((G.q:ℝ)*((G.p:ℝ) - 2) - ((S.card:ℝ) - 1)*((S.card:ℝ) - 2))/(((S.card:ℝ) - 1)*((G.p:ℝ) - 2)) from by
              field_simp; ring]
        exact div_nonneg (by linarith [HR]) (mul_nonneg (by linarith) (by linarith))
      · rw [show (0:ℝ) * ((S.card:ℝ) - 2) + (1/((G.p:ℝ) - 2)) * ((G.p:ℝ) - (S.card:ℝ))
              = (1 - (G.q:ℝ)/((S.card:ℝ) - 1)) + (((G.p:ℝ) - (S.card:ℝ))/((G.p:ℝ) - 2) - (1 - (G.q:ℝ)/((S.card:ℝ) - 1))) from by
              field_simp; ring]
      · rw [show (1/((G.p:ℝ) - 2)) * ((G.p:ℝ) - 2) = 1 from by field_simp]
      · rw [zero_mul, zero_add]
        exact (dualcert_caseII (G.p:ℝ) (S.card:ℝ) (G.q:ℝ) hsR2 hspR hp3R hqR0 HR hb).trans (le_of_eq (by ring))
  · have hpeqN : G.p = 2 := by omega
    have hseqN : S.card = 2 := by omega
    have hpeq : (G.p:ℝ) = 2 := by exact_mod_cast hpeqN
    have hseq : (S.card:ℝ) = 2 := by exact_mod_cast hseqN
    refine main 0 0 (max ((G.q:ℝ) - 1) 0) (le_refl 0) (le_refl 0) (le_max_right _ _) ?_ ?_ ?_
    · rw [hseq, hpeq]; norm_num
      nlinarith [le_max_left ((G.q:ℝ) - 1) 0, le_max_right ((G.q:ℝ) - 1) 0]
    · rw [hpeq]; norm_num
    · rw [hpeq, hseq]
      rcases le_total ((G.q:ℝ) - 1) 0 with h | h
      · rw [max_eq_right h]; norm_num; nlinarith [sq_nonneg ((G.q:ℝ) + 2)]
      · rw [max_eq_left h]; norm_num; nlinarith [sq_nonneg ((G.q:ℝ) - 4)]

/-- **Uniform pure-profile bound** `R(p,q) − p/2 ≤ M(κ^S)`, assembled from the dual certificate
    via weak duality (citation-free). -/
theorem pure_profile_ge (S : Finset (Fin G.p)) (hS : S ∈ Profiles G) :
    ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2
      ≤ McovObj G (fun e => 1 - kappaS G S e) := by
  obtain ⟨y, w, hy, hw, hdf, hval⟩ := pure_profile_dual_cert G S hS
  exact hval.trans (weak_cover_duality G (fun e => 1 - kappaS G S e) y w hy hw hdf)

/-
When `q = 0` there are no active vertices, so every clique-edge load vanishes.
-/
lemma kappa_eq_zero_of_q_zero (hq : G.q = 0) (e : CliqueEdge G) : kappa G e = 0 := by
  convert Finset.sum_eq_zero _;
  simp_all +decide [ Split.q ];
  intro x hx₁ hx₂; specialize hq; have := @hq x; interval_cases _ : # ( G.N x ) <;> simp_all +decide ;

/-
The number of clique triangles is `C(p,3)`.
-/
lemma card_cliqueTri : Fintype.card (CliqueTri G) = Nat.choose G.p 3 := by
  convert Finset.card_powersetCard 3 ( Finset.univ : Finset ( Fin G.p ) ) using 1;
  · refine' Finset.card_bij _ _ _ _;
    use fun a _ => { a.val.1, a.val.2.1, a.val.2.2 };
    · grind;
    · simp +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      grind;
    · intro b hb; rw [ Finset.mem_powersetCard ] at hb; obtain ⟨ a, b, c, hab, hbc, hac ⟩ := Finset.card_eq_three.mp hb.2; simp_all +decide [ Finset.ext_iff ] ;
      cases lt_or_gt_of_ne hab <;> cases lt_or_gt_of_ne hbc <;> cases lt_or_gt_of_ne hac.1 <;> first | exact ⟨ _, _, _, ⟨ by assumption, by assumption ⟩, by tauto ⟩ | skip;
      · grind +extAll;
      · grind;
      · exact ⟨ c, a, b, ⟨ by assumption, by assumption ⟩, by tauto ⟩;
      · exact ⟨ b, a, c, ⟨ by assumption, by assumption ⟩, by tauto ⟩;
  · rw [ Finset.card_univ, Fintype.card_fin ]

/-
Each clique edge lies in exactly `p − 2` clique triangles.
-/
lemma card_triangles_through_edge (e : CliqueEdge G) :
    (Finset.univ.filter (fun T : CliqueTri G => edgeMem G (Sum.inl e) (Sum.inl T))).card
      = G.p - 2 := by
  convert Set.ncard_eq_toFinset_card' ( { T : Fin G.p × Fin G.p × Fin G.p | ( e.val.1 ∈ ({ T.1, T.2.1, T.2.2 } : Finset ( Fin G.p )) ∧ e.val.2 ∈ ({ T.1, T.2.1, T.2.2 } : Finset ( Fin G.p )))
        ∧ T.1 < T.2.1 ∧ T.2.1 < T.2.2 } ) using 1;
  · rw [ ← Set.ncard_coe_finset ];
    fapply Set.ncard_congr;
    use fun a ha => a.val;
    · unfold Split.edgeMem; aesop;
    · exact fun a b _ _ h => Subtype.ext h;
    · simp +decide [ Split.edgeMem ];
      grind;
  · rw [ eq_comm ];
    convert Finset.card_image_of_injective _ ( show Function.Injective ( fun k : Fin G.p => if k < e.val.1 then ( k, e.val.1, e.val.2 ) else if k < e.val.2 then ( e.val.1, k, e.val.2 ) else ( e.val.1, e.val.2, k ) ) from ?_ ) using 2;
    any_goals exact Finset.univ \ { e.val.1, e.val.2 };
    · grind;
    · simp +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ, e.2.ne ];
    · intro a b; aesop


/-
Double counting: summing the residual-cover constraint over all clique triangles gives
    `(p−2)·Σ_e z_e ≥ C(p,3)`.
-/
lemma cover_double_count (hp : 3 ≤ G.p) {z : CliqueEdge G → ℝ} (hz : ResidualCover G z) :
    (Nat.choose G.p 3 : ℝ) ≤ ((G.p : ℝ) - 2) * ∑ e, z e := by
  have h_sum_inequality : ∑ T : CliqueTri G, 1 ≤ ∑ T : CliqueTri G, ∑ e : CliqueEdge G, if edgeMem G (Sum.inl e) (Sum.inl T) then z e else 0 := by
    apply Finset.sum_le_sum;
    intro T hT; specialize hz; have := hz.2 T; simp_all +decide [ Finset.sum_ite ] ;
  -- By reindexing the double sum, we can rewrite it as a single sum over edges.
  have h_reindex : ∑ T : CliqueTri G, ∑ e : CliqueEdge G, (if edgeMem G (Sum.inl e) (Sum.inl T) then z e else 0) = ∑ e : CliqueEdge G, ∑ T : CliqueTri G, (if edgeMem G (Sum.inl e) (Sum.inl T) then z e else 0) := by
    exact Finset.sum_comm;
  convert h_sum_inequality.trans_eq h_reindex using 1;
  · norm_num [ card_cliqueTri G ];
  · rw [ Finset.mul_sum _ _ _ ];
    refine' Finset.sum_congr rfl fun e he => _;
    rw [ Finset.sum_ite ] ; norm_num;
    exact Or.inl ( by rw [ card_triangles_through_edge G e ] ; rw [ Nat.cast_sub ( by linarith ) ] ; push_cast; ring )

/-- **(§7 tail)** `q = 0` branch: `κ = 0`, `M(0) = 0` (p≤2) or `p(p−1)/6` (p≥3), both `≥ R(p,0)−p/2`. -/
theorem q0_branch (hq : G.q = 0) :
    (Rq (G.p : ℚ) 0 : ℝ) - (G.p : ℝ) / 2 ≤ G.Mcov := by
  have hk : ∀ e, kappa G e = 0 := kappa_eq_zero_of_q_zero G hq
  have hRq : (Rq (G.p : ℚ) 0 : ℝ) = (G.p : ℝ) ^ 2 / 6 := by
    simp only [Rq]; push_cast; ring
  unfold Split.Mcov Split.McovObj
  apply le_csInf
  · exact ⟨∑ e, (1 - kappa G e) * (1 : ℝ), fun _ => (1 : ℝ), residualCover_one G, by simp⟩
  · rintro v ⟨z, hz, rfl⟩
    have hz1 : ∀ e, 0 ≤ z e := fun e => (hz.1 e).1
    have hsum : ∑ e, (1 - kappa G e) * z e = ∑ e, z e := by
      refine Finset.sum_congr rfl (fun e _ => ?_); rw [hk e]; ring
    rw [hsum]
    have hp0 : (0 : ℝ) ≤ (G.p : ℝ) := by positivity
    rcases Nat.lt_or_ge G.p 3 with hp | hp
    · have hnn : 0 ≤ ∑ e, z e := Finset.sum_nonneg (fun e _ => hz1 e)
      have hple : (G.p : ℝ) ≤ 2 := by exact_mod_cast (show G.p ≤ 2 by omega)
      rw [hRq]; nlinarith
    · have hdc := cover_double_count G hp hz
      have hC3 : (Nat.choose G.p 3 : ℝ)
          = (G.p : ℝ) * ((G.p : ℝ) - 1) * ((G.p : ℝ) - 2) / 6 :=
        choose3_cast_real (by omega)
      have hp2 : (0 : ℝ) < (G.p : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (G.p : ℝ) := by exact_mod_cast hp
        linarith
      rw [hRq]
      rw [hC3] at hdc
      nlinarith [hdc, hp2, mul_nonneg hp0 (le_of_lt hp2)]

/-- **(L55) Uniform lower bound.** `M(κ) ≥ R(p,q) − p/2`. Assembles §5–7 from the sub-tree. -/
theorem Mcov_lower :
    ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2 ≤ G.Mcov := by
  rcases Nat.eq_zero_or_pos G.q with hq0 | hqpos
  · have hqQ : (G.q : ℚ) = 0 := by exact_mod_cast hq0
    rw [hqQ]; exact q0_branch G hq0
  · obtain ⟨hsum, hcombo⟩ := profile_convex_combo G hqpos
    set lam : Finset (Fin G.p) → ℝ := fun S => (nS G S : ℝ) / (G.q : ℝ) with hlamdef
    -- objective convex combination: 1 − κ = Σ_S λ_S (1 − κ^S)
    have hc : ∀ e, (1 - kappa G e) = ∑ S ∈ Profiles G, lam S * (1 - kappaS G S e) := by
      intro e
      have hcomboe := hcombo e
      rw [show (∑ S ∈ Profiles G, lam S * (1 - kappaS G S e))
            = (∑ S ∈ Profiles G, lam S) - (∑ S ∈ Profiles G, lam S * kappaS G S e) from by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun S _ => by ring)]
      rw [hsum, ← hcomboe]
    -- concavity ⇒ Σ λ_S M(1−κ^S) ≤ M(1−κ) = Mcov
    have hconc := McovObj_concave G (Profiles G) lam (fun S e => 1 - kappaS G S e)
      (fun e => 1 - kappa G e) ⟨_, residualCover_one G⟩ (fun S _ => by positivity) hc
    -- each pure profile ≥ R − p/2, weighted by λ (Σλ = 1) ⇒ average ≥ R − p/2
    have hlow : ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2
        ≤ ∑ S ∈ Profiles G, lam S * McovObj G (fun e => 1 - kappaS G S e) := by
      have hRsum : ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2
          = ∑ S ∈ Profiles G, lam S * (((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2) := by
        rw [← Finset.sum_mul, hsum, one_mul]
      rw [hRsum]
      exact Finset.sum_le_sum
        (fun S hS => mul_le_mul_of_nonneg_left (pure_profile_ge G S hS) (by positivity))
    calc ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2
        ≤ ∑ S ∈ Profiles G, lam S * McovObj G (fun e => 1 - kappaS G S e) := hlow
      _ ≤ McovObj G (fun e => 1 - kappa G e) := hconc
      _ = G.Mcov := rfl

/-! #### deficit_algebra sub-tree (§4.2): M_r ↔ Mcov substitution + H/L split -/

/-- `H = {e : κ_e ≥ 1}` (paper §4.2). -/
noncomputable def Hi (G : Split) : Finset (CliqueEdge G) :=
  Finset.univ.filter (fun e => 1 ≤ kappa G e)

/-- **(paso 1)** `M_r`: residual-cover LP value (objective `Σ r_e x_e`, `x ≥ 0`, covers `≥ 1`). -/
noncomputable def Mr : ℝ :=
  sInf {v : ℝ | ∃ x : CliqueEdge G → ℝ, (∀ e, 0 ≤ x e) ∧
    (∀ t : CliqueTri G,
      1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e) ∧
    v = ∑ e, residual G e * x e}

/-- On `H` the residual capacity vanishes: `κ_e ≥ 1 ⟹ r_e = max(1-κ_e,0) = 0`. -/
lemma residual_of_mem_Hi (e : CliqueEdge G) (he : e ∈ Hi G) : residual G e = 0 := by
  have h1 : (1 : ℝ) ≤ kappa G e := by simpa [Hi] using he
  simp only [residual]
  exact max_eq_right (by linarith)

/-- Off `H` the residual capacity is exactly `1-κ_e` (since `κ_e < 1`). -/
lemma residual_of_not_mem_Hi (e : CliqueEdge G) (he : e ∉ Hi G) :
    residual G e = 1 - kappa G e := by
  have h1 : kappa G e < 1 := by
    by_contra h
    exact he (by simp only [Hi, Finset.mem_filter, Finset.mem_univ, true_and]; linarith [not_lt.mp h])
  simp only [residual]
  exact max_eq_left (by linarith)

/-
Capping a cover to `[0,1]` keeps it a cover, triangle-by-triangle.
-/
lemma cover_min_one {x : CliqueEdge G → ℝ} (hx0 : ∀ e, 0 ≤ x e)
    (hcov : ∀ t : CliqueTri G,
      1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e)
    (t : CliqueTri G) :
    1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)),
        min (x e) 1 := by
  by_cases h : ∃ e ∈ Finset.univ.filter ( fun e => G.edgeMem ( Sum.inl e ) ( Sum.inl t ) ), 1 ≤ x e;
  · obtain ⟨ e, he₁, he₂ ⟩ := h;
    exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun a _ => le_min ( hx0 a ) zero_le_one ) he₁ );
  · exact hcov t |> le_trans <| Finset.sum_le_sum fun e he => by rw [ min_eq_left ] ; exact le_of_not_ge fun he' => h ⟨ e, he, he' ⟩ ;

/-
The feasible-value set of `M_r` is bounded below by `0`.
-/
lemma Mr_set_bddBelow :
    BddBelow {v : ℝ | ∃ x : CliqueEdge G → ℝ, (∀ e, 0 ≤ x e) ∧
      (∀ t : CliqueTri G,
        1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e) ∧
      v = ∑ e, residual G e * x e} := by
  exact ⟨ 0, by rintro v ⟨ x, hx, _, rfl ⟩ ; exact Finset.sum_nonneg fun e _ => mul_nonneg ( le_max_right _ _ ) ( hx e ) ⟩

/-
The feasible-value set of `Mcov = McovObj (1-κ)` is bounded below.
-/
lemma Mcov_set_bddBelow :
    BddBelow {v : ℝ | ∃ z : CliqueEdge G → ℝ, ResidualCover G z ∧
      v = ∑ e, (1 - kappa G e) * z e} := by
  refine' ⟨ ∑ e : CliqueEdge G, Min.min ( 1 - G.kappa e ) 0, fun v hv => _ ⟩;
  rcases hv with ⟨ z, hz, rfl ⟩ ; exact Finset.sum_le_sum fun e _ => by cases le_or_gt 0 ( 1 - G.kappa e ) <;> nlinarith [ hz.1 e, min_le_left ( 1 - G.kappa e ) 0, min_le_right ( 1 - G.kappa e ) 0 ] ;

/-
Easy direction: `M_r ≤ Mcov − Σ_{e∈H}(1−κ_e)`. Take `x = z` for any residual cover `z`;
    then `Σ r_e z_e ≤ Σ(1−κ_e)z_e − Σ_{e∈H}(1−κ_e)` since on `H` `r_e = 0` and `(1−κ)(z−1)≥0`.
-/
lemma mr_le_mcov_sub :
    G.Mr ≤ G.Mcov - ∑ e ∈ Hi G, (1 - kappa G e) := by
  refine' le_sub_iff_add_le.mpr ( le_csInf _ _ );
  · exact ⟨ _, ⟨ fun _ => 1, residualCover_one G, rfl ⟩ ⟩;
  · rintro _ ⟨ z, hz, rfl ⟩;
    refine' add_le_of_le_sub_right _;
    refine' le_trans ( csInf_le _ ⟨ z, _, _, rfl ⟩ ) _;
    · exact Mr_set_bddBelow G;
    · exact fun e => hz.1 e |>.1;
    · exact hz.2;
    · have h_split_sum : ∑ e, (1 - G.kappa e) * z e - ∑ e, G.residual e * z e = ∑ e ∈ G.Hi, (1 - G.kappa e) * z e := by
        rw [ ← Finset.sum_sub_distrib ];
        rw [ ← Finset.sum_subset ( Finset.subset_univ G.Hi ) ];
        · exact Finset.sum_congr rfl fun x hx => by rw [ residual_of_mem_Hi G x hx ] ; ring;
        · simp +contextual [ residual_of_not_mem_Hi ];
      linarith [ show ∑ e ∈ G.Hi, ( 1 - G.kappa e ) ≤ ∑ e ∈ G.Hi, ( 1 - G.kappa e ) * z e from Finset.sum_le_sum fun e he => by nlinarith [ hz.1 e, hz.2, Finset.mem_filter.mp he, G.kappa_nonneg e ] ]

/-
Hard direction: `Mcov − Σ_{e∈H}(1−κ_e) ≤ M_r`. Given a feasible `x` for `M_r`,
    cap it and raise it to `1` on `H` to get a residual cover `z`; then
    `Σ(1−κ_e)z_e ≤ Σ r_e x_e + Σ_{e∈H}(1−κ_e)`.
-/
lemma mcov_sub_le_mr :
    G.Mcov - ∑ e ∈ Hi G, (1 - kappa G e) ≤ G.Mr := by
  -- Let `a = ∑ e, residual G e * x e`, `hx0 : ∀ e, 0 ≤ x e`, `hcov` the cover.
  have h_all_x : ∀ x : CliqueEdge G → ℝ, (∀ e, 0 ≤ x e) → (∀ t : CliqueTri G, 1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e) → G.Mcov - ∑ e ∈ Hi G, (1 - kappa G e) ≤ ∑ e, residual G e * x e := by
    intro x hx_nonneg hx_cover
    set z : CliqueEdge G → ℝ := fun e => if e ∈ Hi G then 1 else min (x e) 1;
    -- Show that `z` is a residual cover.
    have hz_cover : ResidualCover G z := by
      constructor;
      · aesop;
      · intro t;
        refine' le_trans _ ( Finset.sum_le_sum fun e he => show z e ≥ min ( x e ) 1 from _ );
        · convert cover_min_one G hx_nonneg hx_cover t using 1;
        · grind;
    -- Then `Mcov ≤ ∑ e, (1 - kappa G e) * z e` by `csInf_le` (use `Mcov_set_bddBelow G`).
    have hMcov_le : G.Mcov ≤ ∑ e, (1 - kappa G e) * z e := by
      exact csInf_le ( Mcov_set_bddBelow G ) ⟨ z, hz_cover, rfl ⟩;
    -- Split `∑ e, (1 - kappa G e) * z e` over `Hi G` and complement.
    have h_split : ∑ e, (1 - kappa G e) * z e = ∑ e ∈ Hi G, (1 - kappa G e) + ∑ e ∈ Finset.univ \ Hi G, (1 - kappa G e) * min (x e) 1 := by
      simp +zetaDelta at *;
      simp +decide [ Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
    -- Also `a = ∑ e, residual G e * x e`; split over `Hi G`: on `e ∈ Hi G` residual = 0, on `e ∉ Hi G` residual = `1 - kappa G e`.
    have h_split_x : ∑ e, residual G e * x e = ∑ e ∈ Finset.univ \ Hi G, (1 - kappa G e) * x e := by
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ \ G.Hi ) ) ];
      · exact Finset.sum_congr rfl fun e he => by rw [ residual_of_not_mem_Hi G e ( Finset.mem_sdiff.mp he |>.2 ) ] ;
      · simp +contextual [ residual_of_mem_Hi ];
    linarith [ show ∑ e ∈ Finset.univ \ G.Hi, ( 1 - G.kappa e ) * min ( x e ) 1 ≤ ∑ e ∈ Finset.univ \ G.Hi, ( 1 - G.kappa e ) * x e from Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left ( min_le_left _ _ ) ( sub_nonneg.mpr <| le_of_not_ge fun h => Finset.mem_sdiff.mp he |>.2 <| Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h ⟩ ) ];
  refine' le_csInf _ _;
  · refine' ⟨ _, ⟨ fun _ => 1, _, _, rfl ⟩ ⟩ <;> norm_num;
    intro a b c hab hbc; use ⟨ ( a, b ), hab ⟩ ; simp +decide [ edgeMem ] ;
  · rintro _ ⟨ x, hx₁, hx₂, rfl ⟩ ; exact h_all_x x hx₁ hx₂;

/-- **(pasos 2–4, DELICATE)** substitution core: `M_r = Mcov − Σ_{e∈H}(1−κ_e)`. Capping `x ≤ 1`
    (per-triangle case split, `r_e ≥ 0`) + bijections `y=1−x`, `z=1−y` (→ P_p) + drop of H
    (uses `1−κ ≤ 0` on H). Preservation of an LP optimum under an affine bijection. -/
theorem mr_eq : G.Mr = G.Mcov - ∑ e ∈ Hi G, (1 - kappa G e) :=
  le_antisymm (mr_le_mcov_sub G) (mcov_sub_le_mr G)

/-- **(paso 5)** H/L split (elementary): `Σ min{κ,1} − Σ_{e∈H}(1−κ) = Σ_e κ`. -/
theorem deficit_split :
    (∑ e : CliqueEdge G, min (kappa G e) 1) - (∑ e ∈ Hi G, (1 - kappa G e))
      = ∑ e : CliqueEdge G, kappa G e := by
  have hsplit_min := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e => 1 ≤ kappa G e) (fun e => min (kappa G e) 1)
  have hsplit_k := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e => 1 ≤ kappa G e) (fun e => kappa G e)
  have hHi : ∑ e ∈ Finset.univ.filter (fun e => 1 ≤ kappa G e), min (kappa G e) 1
      = ∑ e ∈ Finset.univ.filter (fun e => 1 ≤ kappa G e), (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    exact min_eq_right he.2
  have hOff : ∑ e ∈ Finset.univ.filter (fun e => ¬ 1 ≤ kappa G e), min (kappa G e) 1
      = ∑ e ∈ Finset.univ.filter (fun e => ¬ 1 ≤ kappa G e), kappa G e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    exact min_eq_left (le_of_lt (not_le.mp he.2))
  rw [hHi, hOff] at hsplit_min
  unfold Hi
  rw [Finset.sum_sub_distrib]
  linarith [hsplit_min, hsplit_k]

/-- **`deficit_algebra`** (paper (4.7), duality-free): `Σ min{κ,1} + M_r = b≥2/2 + Mcov`.
    Assembled from `mr_eq`, `deficit_split`, `load_identity`. -/
theorem deficit_algebra :
    (∑ e : CliqueEdge G, min (kappa G e) 1) + G.Mr = (G.bge2 : ℝ) / 2 + G.Mcov := by
  rw [mr_eq G, ← load_identity G]
  linarith [deficit_split G]

/-! #### S-DEFICIT: combined packing w_com = w₁ + w₂ ⇒ ν₃* ≥ b≥2/2 + M(κ) -/

/-- Residual clique-triangle packing: nonneg weights, per clique-edge load ≤ `r_e`. -/
def ResidualPacking (w : CliqueTri G → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e : CliqueEdge G,
    (∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), w t)
      ≤ residual G e

/-- **Prop B.1 (strong duality — TO PROVE, no external citation).** THE remaining wall. -/
theorem residual_duality :
    ∃ w2 : CliqueTri G → ℝ, ResidualPacking G w2 ∧ (∑ t, w2 t) = G.Mr := by
  classical
  -- incidence matrix of the clique-edge / clique-triangle system
  set A : CliqueEdge G → CliqueTri G → ℝ :=
    fun e t => if edgeMem G (Sum.inl e) (Sum.inl t) then (1 : ℝ) else 0 with hA_def
  -- rewriting a full sum against `A` as a sum over the incident indices
  have hrow_t : ∀ (e : CliqueEdge G) (w : CliqueTri G → ℝ),
      ∑ t ∈ Finset.univ.filter (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), w t
        = ∑ t, A e t * w t := by
    intro e w
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : edgeMem G (Sum.inl e) (Sum.inl t) <;> simp [hA_def, h]
  have hrow_e : ∀ (t : CliqueTri G) (x : CliqueEdge G → ℝ),
      ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e
        = ∑ e, A e t * x e := by
    intro t x
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : edgeMem G (Sum.inl e) (Sum.inl t) <;> simp [hA_def, h]
  have hA : ∀ e t, 0 ≤ A e t := by
    intro e t; rw [hA_def]; dsimp only; split <;> norm_num
  have hr : ∀ e, 0 ≤ residual G e := fun e => le_max_right _ _
  have hcol : ∀ t : CliqueTri G, ∃ e, 0 < A e t := by
    intro t
    refine ⟨⟨(t.val.1, t.val.2.1), t.property.1⟩, ?_⟩
    have hmem : edgeMem G (Sum.inl ⟨(t.val.1, t.val.2.1), t.property.1⟩) (Sum.inl t) := by
      simp only [edgeMem]; tauto
    rw [hA_def]; simp [hmem]
  obtain ⟨w, hw0, hwpack, hwval⟩ :=
    FiniteLP.covering_packing_duality A (residual G) hA hr hcol
  refine ⟨w, ⟨hw0, ?_⟩, ?_⟩
  · intro e
    rw [hrow_t e w]
    exact hwpack e
  · -- the covering value set coincides with the one defining `Mr`
    have hset :
        {v : ℝ | ∃ x : CliqueEdge G → ℝ, (∀ e, 0 ≤ x e) ∧
            (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, residual G e * x e}
          = {v : ℝ | ∃ x : CliqueEdge G → ℝ, (∀ e, 0 ≤ x e) ∧
            (∀ t : CliqueTri G,
              1 ≤ ∑ e ∈ Finset.univ.filter (fun e => edgeMem G (Sum.inl e) (Sum.inl t)), x e) ∧
            v = ∑ e, residual G e * x e} := by
      apply Set.ext; intro v; constructor
      · rintro ⟨x, hx0, hxc, rfl⟩
        exact ⟨x, hx0, fun t => by rw [hrow_e t x]; exact hxc t, rfl⟩
      · rintro ⟨x, hx0, hxc, rfl⟩
        exact ⟨x, hx0, fun t => by rw [← hrow_e t x]; exact hxc t, rfl⟩
    rw [hwval, hset]
    rfl

/-- Combined packing: `w₂` on clique triangles, `w₁` on mixed triangles. -/
noncomputable def wcom (w2 : CliqueTri G → ℝ) : Triangle G → ℝ :=
  fun T => match T with
    | Sum.inl t => w2 t
    | Sum.inr _ => w1 G T

/-- Combined feasibility (duality-free). -/
theorem wcom_feasible (w2 : CliqueTri G → ℝ) (h2 : ResidualPacking G w2) :
    FeasiblePacking G (wcom G w2) := by
  refine ⟨?_, ?_⟩
  · intro T
    cases T with
    | inl t => exact h2.1 t
    | inr T => exact w1_nonneg G (Sum.inr T)
  · intro e
    cases e with
    | inl e =>
      have hsplit :
          (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inl e) T), wcom G w2 T)
            = (∑ t ∈ Finset.univ.filter
                  (fun t => edgeMem G (Sum.inl e) (Sum.inl t)), w2 t)
              + (∑ b ∈ Finset.univ.filter
                  (fun b => edgeMem G (Sum.inl e) (Sum.inr b)), w1 G (Sum.inr b)) := by
        simp only [Finset.sum_filter, Fintype.sum_sum_type, wcom]
      have hfull :
          (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inl e) T), w1 G T)
            = (∑ b ∈ Finset.univ.filter
                  (fun b => edgeMem G (Sum.inl e) (Sum.inr b)), w1 G (Sum.inr b)) := by
        simp only [Finset.sum_filter, Fintype.sum_sum_type, w1, ite_self,
          Finset.sum_const_zero, zero_add]
      have hmix :
          (∑ b ∈ Finset.univ.filter
              (fun b => edgeMem G (Sum.inl e) (Sum.inr b)), w1 G (Sum.inr b))
            = min (kappa G e) 1 := hfull.symm.trans (cliqueEdge_load_eq G e)
      have hkey : min (kappa G e) 1 + max (1 - kappa G e) 0 = 1 := by
        have hk := kappa_nonneg G e
        rcases le_total (kappa G e) 1 with h | h
        · rw [min_eq_left h, max_eq_left (by linarith)]; ring
        · rw [min_eq_right h, max_eq_right (by linarith)]; ring
      have h22 := h2.2 e
      have hres : residual G e = max (1 - kappa G e) 0 := rfl
      rw [hres] at h22
      rw [hsplit, hmix]
      linarith [hkey, h22]
    | inr e =>
      have hcongr :
          (∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inr e) T), wcom G w2 T)
            = ∑ T ∈ Finset.univ.filter (fun T => edgeMem G (Sum.inr e) T), w1 G T := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.mem_filter] at hT
        cases T with
        | inl a => exact absurd hT.2 (by simp [edgeMem])
        | inr b => rfl
      rw [hcongr]
      exact crossEdge_load_le G e

/-- Sum split: `Σ w_com = Σ w₂ + |w₁|`. -/
theorem wcom_sum_split (w2 : CliqueTri G → ℝ) :
    (∑ T, wcom G w2 T) = (∑ t, w2 t) + (∑ T, w1 G T) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [wcom, w1, Finset.sum_const_zero, zero_add]

/-- **(L25) S-DEFICIT.** `ν₃* ≥ b≥2/2 + M(κ)`, assembled from residual_duality (B.1),
    wcom_feasible, wcom_sum_split, w1_value, deficit_algebra, nu3star_ge_of_feasible. -/
theorem nu3star_ge_Vcom :
    (G.bge2 : ℝ) / 2 + G.Mcov ≤ G.nu3star := by
  obtain ⟨w2, hw2, hw2val⟩ := residual_duality G
  have hval : (∑ T, wcom G w2 T) = (G.bge2 : ℝ) / 2 + G.Mcov := by
    rw [wcom_sum_split G w2, hw2val, w1_value]
    linarith [deficit_algebra G]
  calc (G.bge2 : ℝ) / 2 + G.Mcov = ∑ T, wcom G w2 T := hval.symm
    _ ≤ G.nu3star := nu3star_ge_of_feasible G (wcom_feasible G w2 hw2)

end Split

/-! ### Main theorem -/

/-- **Paper I, Theorem 1.1.** For every split graph `G`, `|E| − 2 ν₃* ≤ n²/6 + n`. -/
theorem paperI_main (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) := by
  have h1 := G.nu3star_ge_Vcom
  have h2 := G.Mcov_lower
  have h3 := G.edgeCount_eq
  have hq  : (G.q : ℝ)  ≤ (Fintype.card G.ι : ℝ) := by exact_mod_cast G.q_le_card
  have hb1 : (G.b1 : ℝ) ≤ (Fintype.card G.ι : ℝ) := by exact_mod_cast G.b1_le_card
  have hn  : (G.n : ℝ)  = (G.p : ℝ) + (Fintype.card G.ι : ℝ) := by exact_mod_cast G.n_eq
  have hp0 : (0 : ℝ) ≤ (G.p : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (G.q : ℝ) := by positivity
  -- ℝ-value of R(p,q)
  have hRq : ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ)
      = (2 * (G.p : ℝ) ^ 2 - 2 * (G.p : ℝ) * (G.q : ℝ) - (G.q : ℝ) ^ 2) / 12 := by
    simp only [Rq]; push_cast; ring
  -- C(p,2) = p(p-1)/2 in ℝ
  have hchoose : (Nat.choose G.p 2 : ℝ) = (G.p : ℝ) * ((G.p : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  -- deficit chain (pure linear in the opaque atoms ν₃*, M, |E|, C(p,2), R):
  have hPhi : G.Phi ≤ (Nat.choose G.p 2 : ℝ) + (G.b1 : ℝ)
      - 2 * (((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2) := by
    have hd : G.Phi = (G.edgeCount : ℝ) - 2 * G.nu3star := rfl
    linarith [h1, h2, h3, hd]
  -- arithmetic close
  rw [hchoose, hRq] at hPhi
  rw [hn]
  have hcq : (0 : ℝ) ≤ (Fintype.card G.ι : ℝ) - (G.q : ℝ) := sub_nonneg.mpr hq
  have hcb : (0 : ℝ) ≤ (Fintype.card G.ι : ℝ) - (G.b1 : ℝ) := sub_nonneg.mpr hb1
  nlinarith [hPhi, hcq, hcb, hp0, hq0,
    mul_nonneg hcq (by positivity : (0 : ℝ) ≤ 2 * (G.p : ℝ) + (G.q : ℝ) + (Fintype.card G.ι : ℝ))]

end PaperI

-- ===== M-MODEL sorry-free audit (reporting protocol) =====
#print axioms PaperI.Split.nu3star
#print axioms PaperI.Split.packing_le_card
#print axioms PaperI.Split.nu3star_ge_of_feasible
#print axioms PaperI.Split.card_cliqueEdges_in
#print axioms PaperI.Split.load_fubini
#print axioms PaperI.Split.sum_term_eq
#print axioms PaperI.Split.load_identity
#print axioms PaperI.Split.kappa_nonneg
#print axioms PaperI.Split.lambdaE_nonneg
#print axioms PaperI.Split.lambdaE_le_one
#print axioms PaperI.Split.lambdaE_mul_kappa
#print axioms PaperI.Split.w1_nonneg
#print axioms PaperI.Split.cliqueEdge_load_eq
#print axioms PaperI.Split.crossEdge_load_le
#print axioms PaperI.Split.feasiblePacking_w1
#print axioms PaperI.Split.w1_value
-- ===== S-PHASE assembly: open obligations + the assembled theorem =====
#print axioms PaperI.Split.degree_sum_eq
#print axioms PaperI.Split.edgeCount_eq
-- Mcov_lower sub-tree (Aristotle batch)
#print axioms PaperI.Split.residualCover_one
#print axioms PaperI.Split.profile_convex_combo
#print axioms PaperI.Split.McovObj_concave
#print axioms PaperI.Split.q0_branch
#print axioms PaperI.Split.kappa_eq_zero_of_q_zero
#print axioms PaperI.Split.card_cliqueTri
#print axioms PaperI.Split.card_triangles_through_edge
#print axioms PaperI.Split.choose3_cast_real
#print axioms PaperI.Split.cover_double_count
#print axioms PaperI.Split.Mcov_lower
-- pure_profile_ge sub-tree (B1) + deficit_algebra sub-tree
#print axioms PaperI.Split.weak_cover_duality
#print axioms PaperI.Split.pure_profile_dual_cert
#print axioms PaperI.Split.pure_profile_ge
#print axioms PaperI.Split.mr_eq
#print axioms PaperI.Split.deficit_split
#print axioms PaperI.Split.deficit_algebra
-- S-DEFICIT w_com machinery
#print axioms PaperI.Split.residual_duality
#print axioms PaperI.Split.wcom_feasible
#print axioms PaperI.Split.wcom_sum_split
#print axioms PaperI.Split.nu3star_ge_Vcom
#print axioms PaperI.paperI_main



/- ====================================================================== -/
/- ===== Contrib/PaperISharp.lean -/
/- ====================================================================== -/

/-
  Paper I v1.1 candidate — the sharpened bound  Φ ≤ n²/6 + n/2.

  `paperI_main` (the frozen v1.0 artifact) proves the weaker `Φ ≤ n²/6 + n`. The proof
  actually yields `n²/6 + n/2`: (8.3) already gives `Φ ≤ (p+q)²/6 + p/2 + b₁`, and the
  final step of §8 discards quadratic slack in `b₁ + |I₀|` that pays for the linear term.

  This file adds the sharpened statement WITHOUT touching the frozen `PaperI` development;
  it re-uses the public lemmas `nu3star_ge_Vcom`, `Mcov_lower`, `edgeCount_eq`.
-/

namespace PaperI

open scoped BigOperators

/-- The sharp assembly arithmetic. The side hypothesis `1 ≤ b₁ → 1 ≤ p` is forced by the
model (a degree-one independent vertex has its neighbour in `K`). Over `ℝ` with only
`b₁ ≥ 0` the inequality is false, so `b₁` must be a natural. -/
lemma assembly_sharp (p q b i : ℕ) (hside : 1 ≤ b → 1 ≤ p) :
    ((p : ℝ) + q) ^ 2 / 6 + (p : ℝ) / 2 + (b : ℝ)
      ≤ ((p : ℝ) + q + b + i) ^ 2 / 6 + ((p : ℝ) + q + b + i) / 2 := by
  have hp : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hq : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hbn : (0:ℝ) ≤ (b:ℝ) := by positivity
  have hi : (0:ℝ) ≤ (i:ℝ) := by positivity
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    nlinarith [sq_nonneg (i:ℝ), mul_nonneg (add_nonneg hp hq) hi, hq, hi]
  · have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hside hb1
    have hbR : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
    have hkey : (0:ℝ) ≤ (b:ℝ) + 2*(p:ℝ) + 2*(q:ℝ) - 3 := by nlinarith
    nlinarith [mul_nonneg hbn hkey, sq_nonneg (i:ℝ),
      mul_nonneg (add_nonneg hp hq) hi, mul_nonneg hbn hi, hq, hi]

namespace Split
variable (G : Split)

/-- `q + b₁ ≤ |I|`: the degree-≥2 and degree-1 independent vertices are disjoint subsets. -/
theorem q_add_b1_le_card : G.q + G.b1 ≤ Fintype.card G.ι := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun v : G.ι => 2 ≤ (G.N v).card))
      (Finset.univ.filter (fun v : G.ι => (G.N v).card = 1)) := by
    simp only [Finset.disjoint_left, Finset.mem_filter]
    rintro v ⟨_, h2⟩ ⟨_, h1⟩; omega
  have h := Finset.card_union_of_disjoint hdisj
  have hqb : G.q + G.b1 =
      ((Finset.univ.filter (fun v : G.ι => 2 ≤ (G.N v).card)) ∪
        (Finset.univ.filter (fun v : G.ι => (G.N v).card = 1))).card := by
    rw [h]; rfl
  rw [hqb, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- A degree-one independent vertex forces the clique to be nonempty: `1 ≤ b₁ → 1 ≤ p`. -/
theorem one_le_p_of_one_le_b1 : 1 ≤ G.b1 → 1 ≤ G.p := by
  intro hb
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by simpa [Split.b1] using hb)
  rw [Finset.mem_filter] at hv
  have hne : (G.N v).Nonempty := Finset.card_pos.mp (by rw [hv.2]; norm_num)
  obtain ⟨x, _⟩ := hne
  have := x.isLt; omega

/-- **Paper I v1.1, sharpened.** `Φ ≤ n²/6 + n/2`. -/
theorem paperI_main_sharp : G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ) / 2 := by
  have h1 := G.nu3star_ge_Vcom
  have h2 := G.Mcov_lower
  have h3 := G.edgeCount_eq
  have hRq : ((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ)
      = (2 * (G.p : ℝ) ^ 2 - 2 * (G.p : ℝ) * (G.q : ℝ) - (G.q : ℝ) ^ 2) / 12 := by
    simp only [Rq]; push_cast; ring
  have hchoose : (Nat.choose G.p 2 : ℝ) = (G.p : ℝ) * ((G.p : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hPhi : G.Phi ≤ (Nat.choose G.p 2 : ℝ) + (G.b1 : ℝ)
      - 2 * (((Rq (G.p : ℚ) (G.q : ℚ) : ℚ) : ℝ) - (G.p : ℝ) / 2) := by
    have hd : G.Phi = (G.edgeCount : ℝ) - 2 * G.nu3star := rfl
    linarith [h1, h2, h3, hd]
  rw [hchoose, hRq] at hPhi
  -- (8.3): hPhi now says  Φ ≤ (p+q)²/6 + p/2 + b₁  (up to `ring`)
  have hqb1 := G.q_add_b1_le_card
  have hkey := assembly_sharp G.p G.q G.b1 (Fintype.card G.ι - G.q - G.b1)
    G.one_le_p_of_one_le_b1
  have hsum : G.p + G.q + G.b1 + (Fintype.card G.ι - G.q - G.b1) = G.n := by
    rw [G.n_eq]; omega
  have hcast : (G.p : ℝ) + (G.q : ℝ) + (G.b1 : ℝ)
      + ((Fintype.card G.ι - G.q - G.b1 : ℕ) : ℝ) = (G.n : ℝ) := by exact_mod_cast hsum
  rw [hcast] at hkey
  nlinarith [hPhi, hkey]

end Split
end PaperI


/- ==================== axiom footprint (self-check) ==================== -/
#print axioms PaperI.Split.paperI_main_sharp
#print axioms PaperI.paperI_main
