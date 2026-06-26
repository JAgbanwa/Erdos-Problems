import RequestProject.Defs

set_option maxHeartbeats 4000000

/-!
# Excluding infinite cliques (Section 3)

* `two_dist_diff_finite` — Lemma 3.1: for non-collinear `P, Q, R` and fixed reals `a, b`,
  the set of `X` with `|X-P| - |X-Q| = a` and `|X-P| - |X-R| = b` is finite.
* `no_infinite_clique` — Theorem 1.3: `Γ(A)` contains no infinite clique.
-/

open scoped BigOperators
open EuclideanGeometry

/-
**Lemma 3.1.** Let `P, Q, R` be non-collinear. For fixed real numbers `a, b`, the set of
points `X` satisfying `|X - P| - |X - Q| = a` and `|X - P| - |X - R| = b` is finite.
-/
lemma two_dist_diff_finite (P Q R : Plane)
    (hPQR : ¬ Collinear ℝ ({P, Q, R} : Set Plane)) (a b : ℝ) :
    {X : Plane | dist X P - dist X Q = a ∧ dist X P - dist X R = b}.Finite := by
  -- Let $w := X - P$ (in the underlying vector space), $q := Q - P$, $r := R - P$. Non-collinearity of $\{P,Q,R\}$ means $q$ and $r$ are linearly independent in $\mathbb{R}^2$.
  set w : Plane → EuclideanSpace ℝ (Fin 2) := fun X => X - P
  set q : EuclideanSpace ℝ (Fin 2) := Q - P
  set r : EuclideanSpace ℝ (Fin 2) := R - P
  have hq_r_lin_ind : LinearIndependent ℝ ![q, r] := by
    refine' linearIndependent_fin2.mpr ⟨ _, _ ⟩;
    · exact sub_ne_zero_of_ne <| by rintro rfl; exact hPQR <| by simp +decide [ collinear_pair ] ;
    · intro a ha; contrapose! hPQR; simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ] ;
      use P, r; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact ⟨ ⟨ a, by rw [ ha, sub_add_cancel ] ⟩, ⟨ 1, by rw [ one_smul, sub_add_cancel ] ⟩ ⟩;
  -- Because $q, r$ are linearly independent, the linear map $w \mapsto (\langle w, q \rangle, \langle w, r \rangle)$ from $\mathbb{R}^2$ to $\mathbb{R}^2$ is a linear isomorphism. Hence $w$ is an affine function of the single scalar $s$: there are fixed vectors $u, c$ (determined by $P,Q,R,a,b$) with $w = s \cdot u + c$, where $u$ solves $\langle u, q \rangle = a, \langle u, r \rangle = b$ and $c$ solves $\langle c, q \rangle = \frac{\|q\|^2 - a^2}{2}, \langle c, r \rangle = \frac{\|r\|^2 - b^2}{2}$.
  obtain ⟨u, c, hu, hc⟩ : ∃ u c : EuclideanSpace ℝ (Fin 2), (∀ X : Plane, dist X P - dist X Q = a ∧ dist X P - dist X R = b → w X = (dist X P) • u + c) ∧ (inner ℝ u q = a ∧ inner ℝ u r = b) ∧ (inner ℝ c q = (‖q‖^2 - a^2) / 2 ∧ inner ℝ c r = (‖r‖^2 - b^2) / 2) := by
    -- By definition of $u$ and $c$, we know that they satisfy the required conditions.
    obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin 2), inner ℝ u q = a ∧ inner ℝ u r = b := by
      -- Since $q$ and $r$ are linearly independent, the matrix $A = \begin{pmatrix} q_1 & q_2 \\ r_1 & r_2 \end{pmatrix}$ is invertible.
      have hA_inv : Invertible (Matrix.of ![![q 0, q 1], ![r 0, r 1]]) := by
        have h_det : q 0 * r 1 - q 1 * r 0 ≠ 0 := by
          contrapose! hq_r_lin_ind;
          rw [ Fintype.not_linearIndependent_iff ];
          by_cases hq : q = 0 <;> by_cases hr : r = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
          · exact ⟨ fun _ => 1, by norm_num ⟩;
          · exact ⟨ fun i => if i = 0 then 1 else 0, rfl, by norm_num ⟩;
          · exact False.elim <| hPQR <| by rw [ sub_eq_zero.mp hr ] ; norm_num [ collinear_pair ] ;
          · by_cases hq0 : q 0 = 0 <;> by_cases hr0 : r 0 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
            · refine' ⟨ fun i => if i = 0 then -r 1 else q 1, _, _ ⟩ <;> simp_all +decide [ funext_iff, Fin.forall_fin_two ];
              · ext i ; fin_cases i <;> simp_all +decide [ sub_eq_iff_eq_add ];
                ring;
              · exact not_and_or.mp fun h => hr <| by ext i; fin_cases i <;> aesop;
            · exact False.elim <| hq <| by ext i; fin_cases i <;> aesop;
            · exact False.elim <| hr <| by ext i; fin_cases i <;> aesop;
            · refine' ⟨ fun i => if i = 0 then -r.ofLp 0 else q.ofLp 0, _, _ ⟩ <;> simp_all +decide [ funext_iff, Fin.forall_fin_two ];
              ext i; fin_cases i <;> simp_all +decide [ mul_comm ] ;
        convert Matrix.invertibleOfDetInvertible _;
        exact invertibleOfNonzero ( by simpa [ Matrix.det_fin_two ] using h_det );
      obtain ⟨u, hu⟩ : ∃ u : Fin 2 → ℝ, (Matrix.of ![![q 0, q 1], ![r 0, r 1]]).mulVec u = ![a, b] := by
        exact ⟨ hA_inv.1.mulVec ( Matrix.vecCons a ( Matrix.vecCons b 0 ) ), by simp +decide ⟩;
      simp_all +decide [ ← List.ofFn_inj, Matrix.mulVec ];
      simp_all +decide [ mul_comm, inner ];
      exact ⟨ EuclideanSpace.single 0 ( u 0 ) + EuclideanSpace.single 1 ( u 1 ), by simpa using hu ⟩
    obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin 2), inner ℝ c q = (‖q‖^2 - a^2) / 2 ∧ inner ℝ c r = (‖r‖^2 - b^2) / 2 := by
      -- Since $q$ and $r$ are linearly independent, the system of equations has a unique solution.
      have h_unique : ∃ x y : ℝ, x * inner ℝ q q + y * inner ℝ r q = (‖q‖^2 - a^2) / 2 ∧ x * inner ℝ q r + y * inner ℝ r r = (‖r‖^2 - b^2) / 2 := by
        have h_unique : inner ℝ q q * inner ℝ r r - inner ℝ q r * inner ℝ r q ≠ 0 := by
          have h_det : (‖q‖^2) * (‖r‖^2) - (inner ℝ q r)^2 ≠ 0 := by
            have h_lin_ind : ¬(∃ (c : ℝ), q = c • r) := by
              intro h; obtain ⟨ c, hc ⟩ := h; have := hq_r_lin_ind.ne_zero 0; simp_all +decide [ linearIndependent_fin2 ] ;
              exact hq_r_lin_ind.2 c rfl
            contrapose! h_lin_ind;
            have h_lin_ind : ‖q - (inner ℝ q r / ‖r‖^2) • r‖^2 = 0 := by
              rw [ @norm_sub_sq ℝ ];
              by_cases hr : r = 0 <;> simp_all +decide [ norm_smul, inner_smul_right ];
              · exact absurd ( hq_r_lin_ind.ne_zero 1 ) ( by norm_num );
              · field_simp;
                norm_num ; linarith;
            exact ⟨ inner ℝ q r / ‖r‖ ^ 2, sub_eq_zero.mp <| norm_eq_zero.mp <| sq_eq_zero_iff.mp h_lin_ind ⟩;
          simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
          simpa only [ sq ] using h_det;
        use ((‖q‖^2 - a^2) / 2 * inner ℝ r r - (‖r‖^2 - b^2) / 2 * inner ℝ r q) / (inner ℝ q q * inner ℝ r r - inner ℝ q r * inner ℝ r q), ((‖r‖^2 - b^2) / 2 * inner ℝ q q - (‖q‖^2 - a^2) / 2 * inner ℝ q r) / (inner ℝ q q * inner ℝ r r - inner ℝ q r * inner ℝ r q);
        grind;
      obtain ⟨ x, y, hx, hy ⟩ := h_unique; use x • q + y • r; simp_all +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ] ;
    refine' ⟨ u, c, _, hu, hc ⟩;
    intro X hX
    have h_eq : inner ℝ (w X - (dist X P) • u - c) q = 0 ∧ inner ℝ (w X - (dist X P) • u - c) r = 0 := by
      have h_eq : ‖w X - q‖^2 = (dist X P - a)^2 ∧ ‖w X - r‖^2 = (dist X P - b)^2 := by
        simp +zetaDelta at *;
        simp +decide [ ← hX, dist_eq_norm ];
      simp_all +decide [ norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ];
      constructor <;> linarith [ show ‖w X‖ ^ 2 = dist X P ^ 2 by rw [ dist_eq_norm ] ];
    have h_eq_zero : ∀ v : EuclideanSpace ℝ (Fin 2), inner ℝ v q = 0 ∧ inner ℝ v r = 0 → v = 0 := by
      intro v hv
      have h_span : Submodule.span ℝ (Set.range ![q, r]) = ⊤ := by
        refine' Submodule.eq_top_of_finrank_eq _;
        rw [ finrank_span_eq_card ] <;> aesop;
      have h_eq_zero : ∀ w ∈ Submodule.span ℝ (Set.range ![q, r]), inner ℝ v w = 0 := by
        intro w hw; rw [ Submodule.mem_span_range_iff_exists_fun ] at hw; obtain ⟨ f, rfl ⟩ := hw; simp_all +decide [ inner_add_right, inner_smul_right ] ;
      exact by simpa [ h_span ] using h_eq_zero v ( h_span.symm ▸ Submodule.mem_top ) ;
    exact eq_of_sub_eq_zero ( h_eq_zero _ h_eq ) ▸ by abel1;
  -- Now the constraint $s^2 = \|w\|^2 = \|s \cdot u + c\|^2 = s^2 \|u\|^2 + 2 s \langle u, c \rangle + \|c\|^2$ becomes the quadratic in $s$:
  -- $(1 - \|u\|^2) s^2 - 2 \langle u, c \rangle s - \|c\|^2 = 0$.    (★)
  have h_quad : ∀ X : Plane, dist X P - dist X Q = a ∧ dist X P - dist X R = b → (1 - ‖u‖^2) * (dist X P)^2 - 2 * inner ℝ u c * (dist X P) - ‖c‖^2 = 0 := by
    intro X hX
    have h_norm : ‖w X‖^2 = (dist X P)^2 := by
      simp [w, dist_eq_norm]
    have h_expand : ‖w X‖^2 = (dist X P)^2 * ‖u‖^2 + 2 * (dist X P) * inner ℝ u c + ‖c‖^2 := by
      rw [ hu X hX, norm_add_sq_real ] ; ring;
      norm_num [ norm_smul, inner_smul_left ] ; ring
    rw [h_expand] at h_norm
    linarith [h_norm];
  -- Claim this quadratic is not the zero polynomial. If it were, the constant term gives $\|c\|^2 = 0$, so $c = 0$; then $\langle c, q \rangle = 0$ forces $\|q\|^2 = a^2$, i.e. $\|q\| = |a|$. The leading coefficient gives $\|u\|^2 = 1$. From $\langle u, q \rangle = a$ with $\|u\| = 1$ and $\|q\| = |a|$, the Cauchy–Schwarz inequality $|\langle u, q \rangle| \leq \|u\| \|q\| = |a|$ is an equality, so $u$ and $q$ are parallel. Likewise from $c = 0$ we get $\|r\| = |b|$ and $u$ parallel to $r$. But $q, r$ are linearly independent and $u \neq 0$ ($\|u\|=1$), so $u$ cannot be parallel to both — contradiction. Hence (★) is a genuine (nonzero) quadratic.
  have h_nonzero_quad : (1 - ‖u‖^2) ≠ 0 ∨ (2 * inner ℝ u c) ≠ 0 ∨ (‖c‖^2) ≠ 0 := by
    by_contra h_contra
    push_neg at h_contra
    have h_c_zero : c = 0 := by
      exact norm_eq_zero.mp ( sq_eq_zero_iff.mp h_contra.2.2 )
    have h_q_norm : ‖q‖ = |a| := by
      rw [ ← sq_eq_sq₀ ] <;> norm_num [ h_c_zero ] at * ; linarith
    have h_r_norm : ‖r‖ = |b| := by
      simp_all +decide [ inner_self_eq_norm_sq_to_K ];
      rw [ ← sq_eq_sq₀ ] <;> norm_num ; nlinarith [ norm_nonneg r ]
    have h_u_q_parallel : ∃ k : ℝ, u = k • q := by
      have h_u_q_parallel : ‖u - (inner ℝ u q / ‖q‖^2) • q‖^2 = 0 := by
        rw [ @norm_sub_sq ℝ ] ; norm_num [ inner_smul_right, inner_smul_left ] ; ring;
        by_cases ha : a = 0 <;> simp_all +decide [ norm_smul, mul_pow ];
        · exact False.elim <| hq_r_lin_ind.ne_zero 0 rfl;
        · grind;
      exact ⟨ inner ℝ u q / ‖q‖ ^ 2, sub_eq_zero.mp <| norm_eq_zero.mp <| sq_eq_zero_iff.mp h_u_q_parallel ⟩
    have h_u_r_parallel : ∃ k : ℝ, u = k • r := by
      have h_u_r_parallel : ‖u - (b / ‖r‖^2) • r‖^2 = 0 := by
        rw [ @norm_sub_sq ℝ ] ; norm_num [ hc, h_contra ] ; ring;
        simp_all +decide [ norm_smul, inner_smul_right ] ; ring;
        by_cases hb : b = 0 <;> simp_all +decide [ show |b|^4 = ( |b|^2 ) ^2 by ring, show |b|^2 = b^2 by rw [ sq_abs ] ];
        · exact False.elim <| hq_r_lin_ind.ne_zero 1 rfl;
        · grind;
      exact ⟨ b / ‖r‖ ^ 2, sub_eq_zero.mp <| norm_eq_zero.mp <| sq_eq_zero_iff.mp h_u_r_parallel ⟩
    have h_q_r_parallel : ∃ k : ℝ, q = k • r := by
      obtain ⟨ k₁, hk₁ ⟩ := h_u_q_parallel
      obtain ⟨ k₂, hk₂ ⟩ := h_u_r_parallel
      use k₂ / k₁
      have h_k₁_ne_zero : k₁ ≠ 0 := by
        intro h; simp_all +decide [ norm_smul ] ;
        norm_num [ ← hc.1, ← hc.2 ] at *
      field_simp [h_k₁_ne_zero] at *;
      rw [ div_eq_inv_mul, ← smul_smul, ← hk₂, hk₁, smul_smul, inv_mul_cancel₀ h_k₁_ne_zero, one_smul ]
    have h_contra_lin_ind : ¬LinearIndependent ℝ ![q, r] := by
      rw [ Fintype.not_linearIndependent_iff ];
      obtain ⟨ k, hk ⟩ := h_q_r_parallel; use fun i => if i = 0 then 1 else -k; simp +decide [ hk, Fin.sum_univ_succ ] ;
    contradiction;
  -- Finiteness: the map $X \mapsto s = dist X P$ sends the solution set into the root set of the nonzero quadratic (★), which has at most two real roots (`Set.Finite`).
  have h_finite_roots : Set.Finite {s : ℝ | (1 - ‖u‖^2) * s^2 - 2 * inner ℝ u c * s - ‖c‖^2 = 0} := by
    by_cases h : 1 - ‖u‖ ^ 2 = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · by_cases h' : inner ℝ u c = 0 <;> simp_all +decide [ neg_eq_iff_eq_neg ];
      · exact Set.finite_empty.subset fun x hx => h_nonzero_quad <| norm_eq_zero.mp <| by simpa [ sq ] using hx.symm;
      · exact Set.Finite.subset ( Set.finite_singleton ( -‖c‖ ^ 2 / ( 2 * inner ℝ u c ) ) ) fun x hx => eq_div_of_mul_eq ( mul_ne_zero two_ne_zero h' ) <| by linarith [ hx.symm ] ;
    · refine' Set.Finite.subset ( Set.toFinite { ( 2 * inner ℝ u c + Real.sqrt ( ( 2 * inner ℝ u c ) ^ 2 + 4 * ( 1 - ‖u‖ ^ 2 ) * ‖c‖ ^ 2 ) ) / ( 2 * ( 1 - ‖u‖ ^ 2 ) ), ( 2 * inner ℝ u c - Real.sqrt ( ( 2 * inner ℝ u c ) ^ 2 + 4 * ( 1 - ‖u‖ ^ 2 ) * ‖c‖ ^ 2 ) ) / ( 2 * ( 1 - ‖u‖ ^ 2 ) ) } ) _;
      intro s hs; simp_all +decide [ mul_comm ] ;
      rw [ eq_div_iff, eq_div_iff ] <;> cases lt_or_gt_of_ne h <;> first | nlinarith | exact Classical.or_iff_not_imp_left.2 fun h' => mul_left_cancel₀ ( sub_ne_zero_of_ne h' ) <| by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( 2 * inner ℝ u c ) ^ 2 + 4 * ( 1 - ‖u‖ ^ 2 ) * ‖c‖ ^ 2 by nlinarith [ sq_nonneg ( s * ( 1 - ‖u‖ ^ 2 ) - inner ℝ u c ) ] ) ] ;
  have h_inj : ∀ X Y : Plane, dist X P - dist X Q = a ∧ dist X P - dist X R = b → dist Y P - dist Y Q = a ∧ dist Y P - dist Y R = b → dist X P = dist Y P → X = Y := by
    grind;
  have h_finite_image : Set.Finite (Set.image (fun X : Plane => dist X P) {X : Plane | dist X P - dist X Q = a ∧ dist X P - dist X R = b}) := by
    exact h_finite_roots.subset fun x hx => by obtain ⟨ X, hX, rfl ⟩ := hx; exact h_quad X hX;
  convert h_finite_image.of_finite_image _;
  exact fun X hX Y hY hXY => h_inj X Y hX hY hXY

/-
**Theorem 1.3 (No infinite clique).** If `A` has no three collinear points, then there is
no infinite subset `B ⊆ A` all of whose pairs are at integer distance.
-/
theorem no_infinite_clique {A : Set Plane} (hA3 : NoThreeCollinear A) :
    ¬ ∃ B : Set Plane, B ⊆ A ∧ B.Infinite ∧
        ∀ P ∈ B, ∀ Q ∈ B, P ≠ Q → IsIntDist P Q := by
  rintro ⟨ B, hB₁, hB₂, hB₃ ⟩;
  obtain ⟨ P, Q, R, hP, hQ, hR, hPQR ⟩ : ∃ P Q R : Plane, P ∈ B ∧ Q ∈ B ∧ R ∈ B ∧ P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ ¬ Collinear ℝ ({P, Q, R} : Set Plane) := by
    obtain ⟨ P, hP ⟩ := hB₂.nonempty;
    obtain ⟨ Q, hQ, hPQ ⟩ := hB₂.exists_notMem_finset { P } ; obtain ⟨ R, hR, hPR ⟩ := hB₂.exists_notMem_finset { P, Q } ; use P, Q, R; simp_all +decide ;
    have := hA3 { P, Q, R } ; simp_all +decide [ Set.insert_subset_iff ] ;
    grind;
  -- Consider `B' := B \ {P, Q, R}`, still infinite.
  set B' := B \ {P, Q, R} with hB'_def
  have hB'_inf : B'.Infinite := by
    exact Set.Infinite.diff hB₂ ( Set.toFinite { P, Q, R } );
  -- Define `g : Plane → ℤ × ℤ` by `g X = (⌊dist X P - dist X Q⌋, ⌊dist X P - dist X R⌋)`; on `B'` these are exact integers (difference of two natural-number distances) with `|dist X P - dist X Q| ≤ dist P Q` and `|dist X P - dist X R| ≤ dist P R` by the triangle inequality (`abs_dist_sub_le`).
  have h_g_finite : Set.Finite (Set.image (fun X : Plane => (⌊dist X P - dist X Q⌋, ⌊dist X P - dist X R⌋)) B') := by
    have h_g_finite : ∀ X ∈ B', ⌊dist X P - dist X Q⌋ ∈ Set.Icc (-⌈dist P Q⌉₊ : ℤ) ⌈dist P Q⌉₊ ∧ ⌊dist X P - dist X R⌋ ∈ Set.Icc (-⌈dist P R⌉₊ : ℤ) ⌈dist P R⌉₊ := by
      intros X hX
      have h_dist_PQ : |dist X P - dist X Q| ≤ dist P Q := by
        simpa [ dist_comm ] using abs_dist_sub_le P Q X
      have h_dist_PR : |dist X P - dist X R| ≤ dist P R := by
        simpa [ dist_comm ] using abs_dist_sub_le P R X;
      exact ⟨ ⟨ Int.le_floor.2 <| by push_cast; linarith [ abs_le.mp h_dist_PQ, Nat.le_ceil ( dist P Q ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by push_cast; linarith [ abs_le.mp h_dist_PQ, Nat.le_ceil ( dist P Q ) ] ⟩, ⟨ Int.le_floor.2 <| by push_cast; linarith [ abs_le.mp h_dist_PR, Nat.le_ceil ( dist P R ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by push_cast; linarith [ abs_le.mp h_dist_PR, Nat.le_ceil ( dist P R ) ] ⟩ ⟩;
    exact Set.Finite.subset ( Set.Finite.prod ( Set.finite_Icc _ _ ) ( Set.finite_Icc _ _ ) ) ( Set.image_subset_iff.mpr fun X hX => h_g_finite X hX );
  -- Since `B'` is infinite and `g` has finite range on it, by pigeonhole there exist fixed integers `(a, b)` and an infinite subset `B'' ⊆ B'` with `dist X P - dist X Q = a` and `dist X P - dist X R = b` for all `X ∈ B''`.
  obtain ⟨a, b, hB''⟩ : ∃ a b : ℤ, Set.Infinite {X ∈ B' | ⌊dist X P - dist X Q⌋ = a ∧ ⌊dist X P - dist X R⌋ = b} := by
    contrapose! hB'_inf;
    exact Set.Finite.subset ( h_g_finite.biUnion fun x hx => hB'_inf x.1 x.2 ) fun x hx => by aesop;
  -- Then `B'' ⊆ {X | dist X P - dist X Q = (a:ℝ) ∧ dist X P - dist X R = (b:ℝ)}`, which is finite by `two_dist_diff_finite P Q R (the non-collinearity above) (a:ℝ) (b:ℝ)`.
  have hB''_finite : Set.Finite {X : Plane | dist X P - dist X Q = a ∧ dist X P - dist X R = b} := by
    convert two_dist_diff_finite P Q R _ a b using 1;
    exact hPQR.2.2.2;
  refine hB'' <| hB''_finite.subset fun x hx => ?_;
  obtain ⟨ n, hn ⟩ := hB₃ x ( hx.1.1 ) P hP ( by aesop ) ; obtain ⟨ m, hm ⟩ := hB₃ x ( hx.1.1 ) Q hQ ( by aesop ) ; obtain ⟨ k, hk ⟩ := hB₃ x ( hx.1.1 ) R hR ( by aesop ) ; simp_all +decide [ Int.floor_eq_iff ] ;
  exact ⟨ by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith ), by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith ) ⟩

/-
The graph-theoretic form of Theorem 1.3: every clique of `Γ(A)` is finite.
-/
theorem isClique_finite {A : Set Plane} (hA3 : NoThreeCollinear A)
    (s : Set A) (hs : (IntDistGraph A).IsClique s) : s.Finite := by
  contrapose! hA3;
  have h_inf_clique : ∃ B : Set Plane, B ⊆ A ∧ B.Infinite ∧ ∀ P ∈ B, ∀ Q ∈ B, P ≠ Q → IsIntDist P Q := by
    use s.image Subtype.val;
    simp_all +decide [ Set.Infinite.image, SimpleGraph.IsClique ];
    exact fun P hP hP' Q hQ hQ' hne => hs hP' hQ' ( by aesop ) |>.2;
  exact fun h => no_infinite_clique h h_inf_clique
