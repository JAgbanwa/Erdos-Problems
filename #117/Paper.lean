import Mathlib
/- ============================================================
   Source file: RequestProject/Defs.lean
   ============================================================ -/
/-!
# Abelian subgroup covers under a bound on pairwise noncommuting sets
This file sets up the basic definitions used throughout the formalization of the paper
*Abelian Subgroup Covers Under a Bound on Pairwise Noncommuting Sets*.
For a group `G`:
* `Erdos.PNC X`  : the set `X ⊆ G` is *pairwise noncommuting*.
* `Erdos.wnc G`  : the *noncommuting number* `ωnc(G)`, the supremum of cardinalities of finite
  pairwise noncommuting subsets, valued in `ℕ∞`.
* `Erdos.IsAbelianCover 𝒜` : `𝒜` is a family of abelian subgroups whose union is `G`.
* `Erdos.ac G`   : the *abelian covering number* `ac(G)`, the least cardinality of an abelian
  cover, valued in `ℕ∞`.
* `Erdos.U`      : the elementary recurrence `U₁ = U₂ = 1`, `Uₙ = n·Uₙ₋₂`.
* `Erdos.h n`    : `h(n) = sup { ac(G) : ωnc(G) ≤ n }`, valued in `ℕ∞`.
Since we bound `ac(G) ≤ U_n` for *every* group with `ωnc(G) ≤ n` and realise the extremal
values by groups living in `Type`, the supremum defining `h` may faithfully be taken over
`Type`-valued groups.
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-- A subset `X ⊆ G` is *pairwise noncommuting* if distinct elements never commute. -/
def PNC (X : Set G) : Prop := X.Pairwise (fun x y => x * y ≠ y * x)
/-- A subgroup is abelian (as a predicate). -/
def Subgroup.abelian (A : Subgroup G) : Prop := ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
/-- The *noncommuting number* `ωnc(G)`, the supremum of cardinalities of finite pairwise
noncommuting subsets, valued in `ℕ∞`. -/
noncomputable def wnc (G : Type*) [Group G] : ℕ∞ :=
  ⨆ (X : Finset G) (_ : PNC (↑X : Set G)), (X.card : ℕ∞)
/-- A family `𝒜` of subgroups is an *abelian cover* of `G` if every member is abelian and the
union of the members is all of `G`. -/
def IsAbelianCover (𝒜 : Set (Subgroup G)) : Prop :=
  (∀ A ∈ 𝒜, Subgroup.abelian A) ∧ ∀ g : G, ∃ A ∈ 𝒜, g ∈ A
/-- The *abelian covering number* `ac(G)`, the least cardinality of an abelian cover of `G`,
valued in `ℕ∞`. -/
noncomputable def ac (G : Type*) [Group G] : ℕ∞ :=
  ⨅ (𝒜 : Set (Subgroup G)) (_ : IsAbelianCover 𝒜), 𝒜.encard
/-- The elementary recurrence `U₁ = U₂ = 1`, `Uₙ = n·Uₙ₋₂` for `n ≥ 3` (with `U₀ = 1`). -/
def U : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | (n + 3) => (n + 3) * U (n + 1)
/-- `h(n) = sup { ac(G) : ωnc(G) ≤ n }`, valued in `ℕ∞`. -/
noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨆ (G : Type) (inst : Group G) (_ : @wnc G inst ≤ (n : ℕ∞)), @ac G inst
end Erdos
/- ============================================================
   Source file: RequestProject/Basic.lean
   ============================================================ -/
/-!
# Basic characterizations of `wnc` and `ac`
Convenient interface lemmas turning the `iSup`/`iInf` definitions of `wnc` and `ac` into the
elementary statements used in the paper.
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-- A finite pairwise noncommuting set has cardinality at most `wnc G`. -/
lemma le_wnc {X : Finset G} (hX : PNC (↑X : Set G)) : (X.card : ℕ∞) ≤ wnc G := by
  refine le_trans ?_ (le_iSup (fun X : Finset G => ⨆ _ : PNC (↑X : Set G), (X.card : ℕ∞)) X)
  exact le_iSup (fun _ : PNC (↑X : Set G) => (X.card : ℕ∞)) hX
/-- `wnc G ≤ n` iff every finite pairwise noncommuting set has at most `n` elements. -/
lemma wnc_le_iff {n : ℕ∞} :
    wnc G ≤ n ↔ ∀ X : Finset G, PNC (↑X : Set G) → (X.card : ℕ∞) ≤ n := by
  unfold wnc
  simp only [iSup_le_iff]
/-- `wnc G ≤ n` for a natural `n` iff every finite pairwise noncommuting set has at most `n`
elements. -/
lemma wnc_le_nat_iff {n : ℕ} :
    wnc G ≤ (n : ℕ∞) ↔ ∀ X : Finset G, PNC (↑X : Set G) → X.card ≤ n := by
  rw [wnc_le_iff]
  constructor
  · intro h X hX
    have := h X hX
    exact_mod_cast this
  · intro h X hX
    exact_mod_cast h X hX
/-- If `G` admits an abelian cover `𝒜`, then `ac G ≤ |𝒜|`. -/
lemma ac_le_encard {𝒜 : Set (Subgroup G)} (h𝒜 : IsAbelianCover 𝒜) :
    ac G ≤ 𝒜.encard := by
  unfold ac
  refine le_trans (iInf_le _ 𝒜) ?_
  exact iInf_le _ h𝒜
/-- To bound `ac G` below by `c`, it suffices to show every abelian cover has cardinality
at least `c`. -/
lemma le_ac {c : ℕ∞} (h : ∀ 𝒜 : Set (Subgroup G), IsAbelianCover 𝒜 → c ≤ 𝒜.encard) :
    c ≤ ac G := by
  unfold ac
  refine le_iInf fun 𝒜 => ?_
  refine le_iInf fun h𝒜 => ?_
  exact h 𝒜 h𝒜
/-- If `G` is covered by a finite family (indexed by `Fin k`) of abelian subgroups, then
`ac G ≤ k`. -/
lemma ac_le_of_fin_cover {k : ℕ} (A : Fin k → Subgroup G)
    (habel : ∀ i, Subgroup.abelian (A i)) (hcov : ∀ g : G, ∃ i, g ∈ A i) :
    ac G ≤ (k : ℕ∞) := by
  refine le_trans (ac_le_encard (𝒜 := Set.range A) ?_) ?_
  · constructor
    · rintro B ⟨i, rfl⟩
      exact habel i
    · intro g
      obtain ⟨i, hi⟩ := hcov g
      exact ⟨A i, ⟨i, rfl⟩, hi⟩
  · rw [← Set.image_univ]
    refine le_trans (Set.encard_image_le _ _) ?_
    rw [Set.encard_univ]
    simp [ENat.card_eq_coe_fintype_card]
/-- The family of all cyclic subgroups is an abelian cover, so an abelian cover always exists. -/
lemma exists_abelianCover : ∃ 𝒜 : Set (Subgroup G), IsAbelianCover 𝒜 := by
  refine ⟨Set.range (fun g : G => Subgroup.zpowers g), ?_, ?_⟩
  · rintro B ⟨g, rfl⟩
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (zpow_mul_comm g m n)
  · intro g
    exact ⟨Subgroup.zpowers g, ⟨g, rfl⟩, Subgroup.mem_zpowers g⟩
/-- `ac G ≤ N` (for a natural `N`) iff `G` has an abelian cover of cardinality at most `N`. -/
lemma ac_le_nat_iff {N : ℕ} :
    ac G ≤ (N : ℕ∞) ↔ ∃ 𝒜 : Set (Subgroup G), IsAbelianCover 𝒜 ∧ 𝒜.encard ≤ (N : ℕ∞) := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hge : ((N : ℕ∞) + 1) ≤ ac G := by
      apply le_ac
      intro 𝒜 h𝒜
      exact Order.add_one_le_of_lt (hcon 𝒜 h𝒜)
    have hcontra : ((N : ℕ∞) + 1) ≤ (N : ℕ∞) := le_trans hge h
    have hcast : (((N + 1 : ℕ) : ℕ∞)) ≤ ((N : ℕ) : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]; exact hcontra
    have : N + 1 ≤ N := by exact_mod_cast hcast
    omega
  · rintro ⟨𝒜, h𝒜, hcard⟩
    exact le_trans (ac_le_encard h𝒜) hcard
end Erdos
/- ============================================================
   Source file: RequestProject/Recurrence.lean
   ============================================================ -/
/-!
# Closed forms and monotonicity of the recurrence `U` (Lemma 4.1)
* `Erdos.U_even`  : `U₍₂ᵣ₎ = 2^(r-1)·r!` for `r ≥ 1`.
* `Erdos.U_odd`   : `U₍₂ᵣ₊₁₎ = (2r+1)!!`.
* `Erdos.U_mono`  : the sequence `U` is monotone.
-/
namespace Erdos
/-- The defining recurrence in usable form: `Uₘ = m·U₍ₘ₋₂₎` for `m ≥ 3`. -/
lemma U_step (n : ℕ) : U (n + 3) = (n + 3) * U (n + 1) := rfl
/-
Closed form for even indices: `U₍₂ᵣ₎ = 2^(r-1)·r!` for `r ≥ 1`.
-/
lemma U_even (r : ℕ) (hr : 1 ≤ r) : U (2 * r) = 2 ^ (r - 1) * r.factorial := by
  induction hr <;> simp_all +decide [ Nat.factorial ];
  rename_i k hk ih;
  rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
  erw [ show U ( 2 * k + 4 ) = ( 2 * k + 4 ) * U ( 2 * k + 2 ) from U_step ( 2 * k + 1 ) ] ; rw [ ih ] ; ring
/-
Closed form for odd indices: `U₍₂ᵣ₊₁₎ = (2r+1)!!`.
-/
lemma U_odd (r : ℕ) : U (2 * r + 1) = Nat.doubleFactorial (2 * r + 1) := by
  induction' r with r ih;
  · decide +revert;
  · rw [ Nat.mul_succ, U_step, ih, Nat.doubleFactorial ]
/-
The sequence `U` is monotone.
-/
lemma U_mono : Monotone U := by
  refine' monotone_nat_of_le_succ _;
  intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | _ | n ) <;> simp +arith +decide [ * ] ;
  exact Nat.mul_le_mul ( by linarith ) ( ih _ <| by linarith )
end Erdos
/- ============================================================
   Source file: RequestProject/Chromatic.lean
   ============================================================ -/
/-!
# `ωnc(G) ≤ ac(G)` (the easy direction of Proposition 2.2)
A pairwise noncommuting set is a clique in the noncommuting graph, and each abelian subgroup can
contain at most one vertex of any clique.  Hence the noncommuting number never exceeds the
abelian covering number.  This gives all the lower bounds `ac(G) ≥ ωnc(G)` for free.
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-- A pairwise noncommuting finite set injects into any abelian cover, one element per subgroup. -/
lemma card_pnc_le_encard_cover {X : Finset G} (hX : PNC (↑X : Set G))
    {𝒜 : Set (Subgroup G)} (h𝒜 : IsAbelianCover 𝒜) :
    (X.card : ℕ∞) ≤ 𝒜.encard := by
  -- choose, for each element, a covering subgroup
  choose A hAmem hAin using h𝒜.2
  have hinj : Set.InjOn A (↑X : Set G) := by
    intro x hx y hy hxy
    by_contra hne
    have hxA : x ∈ A x := hAin x
    have hyA : y ∈ A x := hxy ▸ hAin y
    have hcomm := h𝒜.1 (A x) (hAmem x) x hxA y hyA
    exact hX hx hy hne hcomm
  have hsub : (↑(X.image A) : Set (Subgroup G)) ⊆ 𝒜 := by
    intro B hB
    rw [Finset.coe_image, Set.mem_image] at hB
    obtain ⟨x, _, rfl⟩ := hB
    exact hAmem x
  have hcard : (X.image A).card = X.card := Finset.card_image_of_injOn hinj
  calc (X.card : ℕ∞) = ((X.image A).card : ℕ∞) := by rw [hcard]
    _ = (↑(X.image A) : Set (Subgroup G)).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ 𝒜.encard := Set.encard_le_encard hsub
/-- **Proposition 2.2 (`≤` direction).** `ωnc(G) ≤ ac(G)`. -/
theorem wnc_le_ac : wnc G ≤ ac G := by
  refine iSup_le fun X => iSup_le fun hX => ?_
  exact le_ac fun 𝒜 h𝒜 => card_pnc_le_encard_cover hX h𝒜
end Erdos
/- ============================================================
   Source file: RequestProject/Cover.lean
   ============================================================ -/
/-!
# Finite abelian covers and transport across a subgroup cover
Interface lemmas letting us work with *finite* abelian covers (as `Finset (Subgroup G)`), plus
the key transport lemma: if `G` is covered by finitely many subgroups, each of which has abelian
covering number at most `N`, then `ac G` is at most (number of subgroups)·`N`.
-/
open scoped Classical
open scoped BigOperators
namespace Erdos
variable {G : Type*} [Group G]
/-- From a finite family of abelian subgroups covering `G`, we get `ac G ≤ card`. -/
lemma ac_le_finset_cover {𝒜 : Finset (Subgroup G)}
    (habel : ∀ A ∈ 𝒜, Subgroup.abelian A) (hcov : ∀ g : G, ∃ A ∈ 𝒜, g ∈ A) :
    ac G ≤ (𝒜.card : ℕ∞) := by
  refine le_trans (ac_le_encard (𝒜 := (↑𝒜 : Set (Subgroup G))) ?_) ?_
  · exact ⟨fun A hA => habel A (by simpa using hA), fun g => by
      obtain ⟨A, hA, hgA⟩ := hcov g; exact ⟨A, by simpa using hA, hgA⟩⟩
  · rw [Set.encard_coe_eq_coe_finsetCard]
/-- `ac G ≤ N` yields a *finite* abelian cover of size at most `N`. -/
lemma exists_finset_cover_of_ac_le {N : ℕ} (h : ac G ≤ (N : ℕ∞)) :
    ∃ 𝒜 : Finset (Subgroup G),
      (∀ A ∈ 𝒜, Subgroup.abelian A) ∧ (∀ g : G, ∃ A ∈ 𝒜, g ∈ A) ∧ 𝒜.card ≤ N := by
  obtain ⟨𝒜, h𝒜, hcard⟩ := ac_le_nat_iff.1 h
  have hfin : 𝒜.Finite := Set.finite_of_encard_le_coe hcard
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro A hA
    exact h𝒜.1 A (by simpa using hA)
  · intro g
    obtain ⟨A, hA, hgA⟩ := h𝒜.2 g
    exact ⟨A, by simpa using hA, hgA⟩
  · have : (hfin.toFinset.card : ℕ∞) = 𝒜.encard := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
    exact_mod_cast le_trans (le_of_eq this) hcard
/-- The image of an abelian subgroup under an injective homomorphism is abelian. -/
lemma abelian_map {K : Type*} [Group K] (f : K →* G)
    {A : Subgroup K} (hA : Subgroup.abelian A) : Subgroup.abelian (A.map f) := by
  intro x hx y hy
  rw [Subgroup.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, hA a ha b hb]
/-- **Transport lemma.** If `G` is covered by the subgroups `H i` for `i` in a finite set `s`,
and each `H i` (as a group) has abelian covering number at most `N`, then
`ac G ≤ (s.card)·N`. -/
lemma ac_le_subgroup_cover {ι : Type*} (s : Finset ι) (H : ι → Subgroup G)
    (hcov : ∀ g : G, ∃ i ∈ s, g ∈ H i) {N : ℕ}
    (hN : ∀ i ∈ s, ac (H i) ≤ (N : ℕ∞)) :
    ac G ≤ ((s.card * N : ℕ) : ℕ∞) := by
  -- For each `i ∈ s`, choose a finite abelian cover of the subgroup `H i`.
  choose! 𝒜 h𝒜abel h𝒜cov h𝒜card using
    fun i (hi : i ∈ s) => exists_finset_cover_of_ac_le (hN i hi)
  -- Push these covers into `G` via the (injective) inclusions.
  classical
  set 𝒞 : Finset (Subgroup G) :=
    s.biUnion (fun i => (𝒜 i).image (fun A => A.map (H i).subtype)) with h𝒞
  refine le_trans (ac_le_finset_cover (𝒜 := 𝒞) ?_ ?_) ?_
  · -- every member is abelian
    intro B hB
    rw [h𝒞, Finset.mem_biUnion] at hB
    obtain ⟨i, hi, hB⟩ := hB
    rw [Finset.mem_image] at hB
    obtain ⟨A, hA, rfl⟩ := hB
    exact abelian_map (H i).subtype (h𝒜abel i hi A hA)
  · -- the family covers `G`
    intro g
    obtain ⟨i, hi, hgi⟩ := hcov g
    obtain ⟨A, hA, hgA⟩ := h𝒜cov i hi ⟨g, hgi⟩
    refine ⟨A.map (H i).subtype, ?_, ?_⟩
    · rw [h𝒞, Finset.mem_biUnion]
      exact ⟨i, hi, Finset.mem_image.2 ⟨A, hA, rfl⟩⟩
    · rw [Subgroup.mem_map]
      exact ⟨⟨g, hgi⟩, hgA, rfl⟩
  · -- cardinality bound
    have hcard : 𝒞.card ≤ ∑ i ∈ s, (𝒜 i).card := by
      refine le_trans (Finset.card_biUnion_le) ?_
      exact Finset.sum_le_sum (fun i _ => Finset.card_image_le)
    have hsum : ∑ i ∈ s, (𝒜 i).card ≤ s.card * N := by
      refine le_trans (Finset.sum_le_sum (fun i hi => h𝒜card i hi)) ?_
      rw [Finset.sum_const, smul_eq_mul]
    exact_mod_cast le_trans hcard hsum
end Erdos
/- ============================================================
   Source file: RequestProject/Centralizer.lean
   ============================================================ -/
/-!
# Centralizer lemmas (Section 3 of the paper)
* `Erdos.pnc_triple` : a noncommuting pair `x, y` yields the pairwise noncommuting triple
  `x, y, xy` (Lemma 3.1).
* `Erdos.abelian_of_wnc_le_two` : if `ωnc(G) ≤ 2` then `G` is abelian (Lemma 3.1).
* `Erdos.wnc_subgroup_le` : bridge between pairwise noncommuting subsets of a subgroup and of `G`.
* `Erdos.wnc_centralizer_le` : the centralizer of a noncentral element drops the noncommuting
  number by two (Lemma 3.2).
* `Erdos.cover_by_centralizers` : a maximum pairwise noncommuting set covers `G` by centralizers
  (Lemma 3.3).
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-
**Lemma 3.1 (triple).** If `x` and `y` do not commute, then `x, y, xy` are pairwise
noncommuting.
-/
lemma pnc_triple {x y : G} (h : x * y ≠ y * x) :
    PNC ({x, y, x * y} : Set G) := by
  simp +decide [ PNC ];
  simp +decide [ Set.Pairwise, h ];
  simp +decide [ mul_assoc, h ];
  simp +decide [ ← mul_assoc, h, eq_comm ]
/-
**Lemma 3.1.** If `ωnc(G) ≤ 2` then `G` is abelian.
-/
lemma abelian_of_wnc_le_two (h : wnc G ≤ (2 : ℕ∞)) (a b : G) : a * b = b * a := by
  contrapose h;
  refine' not_le_of_gt ( lt_of_lt_of_le _ ( le_wnc _ ) );
  any_goals exact { a, b, a * b };
  · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide;
    · aesop;
    · grind;
  · convert pnc_triple h using 1;
    simp +decide
/-
Bridge: to bound the noncommuting number of a subgroup `H` (as a group), it suffices to
bound the size of pairwise noncommuting finite subsets of `G` contained in `H`.
-/
lemma wnc_subgroup_le {H : Subgroup G} {n : ℕ}
    (h : ∀ T : Finset G, (↑T : Set G) ⊆ (H : Set G) → PNC (↑T : Set G) → T.card ≤ n) :
    wnc H ≤ (n : ℕ∞) := by
  convert wnc_le_nat_iff.mpr _;
  intro X hX; specialize h ( X.image Subtype.val ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
  convert h ( fun x hx => x.2 ) _;
  intro x hx y hy hxy; obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, rfl ⟩ := hy; specialize hX ha hb; aesop;
/-- Auxiliary map used in Lemma 3.2: `t ↦ x·t` if `t` commutes with `y0`, else `t ↦ t`.
The point is that the result never commutes with `y0` (when `x` does not commute with `y0`). -/
noncomputable def dropMap (x y0 t : G) : G := if t * y0 = y0 * t then x * t else t
/-
The auxiliary element commutes with `x` whenever `t` does.
-/
lemma dropMap_comm_x {x y0 t : G} (ht : t * x = x * t) :
    dropMap x y0 t * x = x * dropMap x y0 t := by
  unfold dropMap; split_ifs <;> simp_all +decide [ mul_assoc ] ;
/-
The auxiliary element never commutes with `y0` (given `x` does not).
-/
lemma dropMap_noncomm_y0 {x y0 t : G} (hy0 : x * y0 ≠ y0 * x) :
    dropMap x y0 t * y0 ≠ y0 * dropMap x y0 t := by
  unfold dropMap;
  split_ifs <;> simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc ]
/-
Distinct noncommuting `s, t` (both commuting with `x`) give noncommuting auxiliary elements.
-/
lemma dropMap_noncomm_pair {x y0 s t : G} (hs : s * x = x * s) (ht : t * x = x * t)
    (hst : s * t ≠ t * s) :
    dropMap x y0 s * dropMap x y0 t ≠ dropMap x y0 t * dropMap x y0 s := by
  unfold dropMap; split_ifs <;> simp_all +decide [ ← mul_assoc ] ;
  · simp_all +decide [ mul_assoc ];
  · simp_all +decide [ mul_assoc ];
  · simp_all +decide [ mul_assoc ]
/-
The auxiliary element never commutes with `x·y0`.
-/
lemma dropMap_noncomm_xy0 {x y0 t : G} (ht : t * x = x * t) (hy0 : x * y0 ≠ y0 * x) :
    dropMap x y0 t * (x * y0) ≠ (x * y0) * dropMap x y0 t := by
  unfold dropMap;
  split_ifs <;> simp_all +decide [ ← mul_assoc ];
  · simp_all +decide [ mul_assoc ];
    simp_all +decide [ ← mul_assoc ];
  · simp_all +decide [ mul_assoc ]
/-
`y0` and `x·y0` do not commute.
-/
lemma y0_noncomm_xy0 {x y0 : G} (hy0 : x * y0 ≠ y0 * x) :
    y0 * (x * y0) ≠ (x * y0) * y0 := by
  contrapose! hy0; simp_all +decide [ ← mul_assoc ] ;
/-- **Lemma 3.2 (centralizer drop by two).** If `ωnc(G) ≤ m` and `x` is not central (some `y`
does not commute with `x`), then any pairwise noncommuting subset of `C_G(x)` has at most
`m - 2` elements. -/
lemma centralizer_pnc_card_le {m : ℕ} (hm : wnc G ≤ (m : ℕ∞))
    {x : G} {y0 : G} (hy0 : x * y0 ≠ y0 * x)
    (T : Finset G) (hTsub : (↑T : Set G) ⊆ (Subgroup.centralizer {x} : Set G))
    (hTpnc : PNC (↑T : Set G)) : T.card + 2 ≤ m := by
  -- All elements of `T` commute with `x`.
  have hcx : ∀ t ∈ T, t * x = x * t := by
    intro t ht
    have hmem : t ∈ (↑T : Set G) := by simpa using ht
    have hc := hTsub hmem
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc
    have hx := hc x (by simp)
    exact hx.symm
  set S : Finset G := insert y0 (insert (x * y0) (T.image (dropMap x y0))) with hS
  have hginj : Set.InjOn (dropMap x y0) (↑T : Set G) := by
    intro s hs t ht hst
    by_contra hne
    exact dropMap_noncomm_pair (hcx s hs) (hcx t ht)
      (hTpnc hs ht hne) (by rw [hst])
  have hy0_notmem : y0 ∉ insert (x * y0) (T.image (dropMap x y0)) := by
    simp only [Finset.mem_insert, Finset.mem_image, not_or]
    refine ⟨?_, ?_⟩
    · intro h
      exact y0_noncomm_xy0 hy0 (by rw [← h])
    · rintro ⟨t, ht, hgt⟩
      exact dropMap_noncomm_y0 hy0 (by rw [hgt])
  have hxy0_notmem : x * y0 ∉ T.image (dropMap x y0) := by
    simp only [Finset.mem_image, not_exists]
    rintro t ⟨ht, hgt⟩
    exact dropMap_noncomm_xy0 (hcx t (by simpa using ht)) hy0 (by rw [hgt])
  have hcard : S.card = T.card + 2 := by
    rw [hS, Finset.card_insert_of_notMem hy0_notmem,
      Finset.card_insert_of_notMem hxy0_notmem,
      Finset.card_image_of_injOn hginj]
  have hpnc : PNC (↑S : Set G) := by
    rw [hS]
    have himg : ∀ a ∈ T.image (dropMap x y0), ∀ b ∈ T.image (dropMap x y0), a ≠ b → a * b ≠ b * a := by
      intro a ha b hb hab
      simp only [Finset.mem_image] at ha hb
      obtain ⟨s, hs, rfl⟩ := ha
      obtain ⟨t, ht, rfl⟩ := hb
      have hsne : s ≠ t := by rintro rfl; exact hab rfl
      have hst : s * t ≠ t * s :=
        hTpnc (by simpa using hs) (by simpa using ht) hsne
      exact dropMap_noncomm_pair (hcx s hs) (hcx t ht) hst
    -- assemble pairwise noncommuting over the three-way insert
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at ha hb
    have key : ∀ t ∈ T, y0 * dropMap x y0 t ≠ dropMap x y0 t * y0 ∧
        (x*y0) * dropMap x y0 t ≠ dropMap x y0 t * (x*y0) := by
      intro t ht
      exact ⟨fun h => dropMap_noncomm_y0 hy0 h.symm,
        fun h => dropMap_noncomm_xy0 (hcx t ht) hy0 h.symm⟩
    rcases ha with rfl | rfl | ⟨s, hs, rfl⟩ <;>
      rcases hb with rfl | rfl | ⟨t, ht, rfl⟩
    · exact absurd rfl hab
    · exact y0_noncomm_xy0 hy0
    · exact ((key t (by simpa using ht)).1)
    · exact (y0_noncomm_xy0 hy0).symm
    · exact absurd rfl hab
    · exact ((key t (by simpa using ht)).2)
    · exact fun h => (key s (by simpa using hs)).1 h.symm
    · exact fun h => (key s (by simpa using hs)).2 h.symm
    · exact himg _ (Finset.mem_image.2 ⟨s, (by simpa using hs), rfl⟩) _
        (Finset.mem_image.2 ⟨t, (by simpa using ht), rfl⟩) hab
  have := le_wnc hpnc
  rw [hcard] at this
  have hle : ((T.card + 2 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans this hm
  exact_mod_cast hle
/-- **Lemma 3.2.** The centralizer of a noncentral element has noncommuting number at most
`m - 2`. -/
lemma wnc_centralizer_le {m : ℕ} (hm : wnc G ≤ (m : ℕ∞))
    {x : G} {y0 : G} (hy0 : x * y0 ≠ y0 * x) :
    wnc (Subgroup.centralizer {x}) ≤ ((m - 2 : ℕ) : ℕ∞) := by
  apply wnc_subgroup_le
  intro T hTsub hTpnc
  have := centralizer_pnc_card_le hm hy0 T hTsub hTpnc
  omega
/-
Any element of a pairwise noncommuting set of size at least `2` is noncentral.
-/
lemma pnc_mem_noncentral {X : Finset G} (hpnc : PNC (↑X : Set G)) (hcard : 2 ≤ X.card)
    {x : G} (hx : x ∈ X) : ∃ y, x * y ≠ y * x := by
  obtain ⟨ y, hy, hy' ⟩ := Finset.exists_mem_ne hcard x;
  exact ⟨ y, by have := hpnc hy hx ( by tauto ) ; tauto ⟩
/-
**Lemma 3.3.** If `ωnc(G) ≤ m`, there is a maximum pairwise noncommuting finite set `X`
whose centralizers cover `G`.
-/
lemma exists_centralizer_cover {m : ℕ} (hm : wnc G ≤ (m : ℕ∞)) :
    ∃ X : Finset G, PNC (↑X : Set G) ∧
      (∀ g : G, ∃ x ∈ X, g ∈ Subgroup.centralizer ({x} : Set G)) ∧
      (∀ Y : Finset G, PNC (↑Y : Set G) → Y.card ≤ X.card) := by
  obtain ⟨X, hX⟩ : ∃ X : Finset G, PNC (↑X : Set G) ∧ ∀ Y : Finset G, PNC (↑Y : Set G) → Y.card ≤ X.card := by
    have h_max : ∃ k, (∃ X : Finset G, PNC (↑X : Set G) ∧ X.card = k) ∧ ∀ l, (∃ X : Finset G, PNC (↑X : Set G) ∧ X.card = l) → l ≤ k := by
      apply_rules [ Set.exists_max_image ];
      · exact Set.finite_iff_bddAbove.mpr ⟨ m, fun n hn => by rcases hn with ⟨ X, hX, rfl ⟩ ; exact_mod_cast le_trans ( le_wnc hX ) hm ⟩;
      · exact ⟨ 0, ⟨ ∅, by simp +decide [ PNC ] ⟩ ⟩;
    grind;
  refine' ⟨ X, hX.1, fun g => _, hX.2 ⟩;
  by_cases hg : g ∈ X;
  · exact ⟨ g, hg, by simp +decide [ Subgroup.mem_centralizer_iff ] ⟩;
  · contrapose! hX;
    refine' fun h => ⟨ Insert.insert g X, _, _ ⟩ <;> simp_all +decide [ PNC ];
    simp_all +decide [ Set.Pairwise, Subgroup.mem_centralizer_iff ];
    exact fun x hx hx' => Ne.symm ( hX x hx )
end Erdos
/- ============================================================
   Source file: RequestProject/UpperBound.lean
   ============================================================ -/
/-!
# The elementary upper bound (Section 4 of the paper)
* `Erdos.U_rec`, `Erdos.U_pos` : basic properties of the recurrence.
* `Erdos.ac_le_one_of_abelian` : an abelian group is covered by a single abelian subgroup.
* `Erdos.ac_le_U` : **Theorem 4.2**, if `ωnc(G) = m < ∞` then `ac(G) ≤ Uₘ`.
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-- The defining recurrence in usable form: `Uₘ = m·U₍ₘ₋₂₎` for `m ≥ 3`. -/
lemma U_rec {m : ℕ} (hm : 3 ≤ m) : U m = m * U (m - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  have h2 : n + 3 - 2 = n + 1 := by omega
  rw [h2]
  simp only [U]
/-- Every term of the recurrence is positive. -/
lemma U_pos : ∀ m : ℕ, 1 ≤ U m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simp [U]
    | 1 => simp [U]
    | 2 => simp [U]
    | (n + 3) =>
      rw [U_rec (by omega)]
      have : 1 ≤ U (n + 3 - 2) := ih (n + 3 - 2) (by omega)
      calc 1 ≤ (n + 3) * 1 := by omega
        _ ≤ (n + 3) * U (n + 3 - 2) := by
              exact Nat.mul_le_mul_left _ this
/-- An abelian group is covered by the single abelian subgroup `⊤`. -/
lemma ac_le_one_of_abelian (h : ∀ a b : G, a * b = b * a) : ac G ≤ 1 := by
  have hcov : ac G ≤ (({⊤} : Finset (Subgroup G)).card : ℕ∞) := by
    apply ac_le_finset_cover
    · intro A hA
      rw [Finset.mem_singleton] at hA
      subst hA
      intro x _ y _
      exact h x y
    · intro g
      exact ⟨⊤, by simp, Subgroup.mem_top g⟩
  simpa using hcov
/-- A noncommuting pair yields a pairwise noncommuting finset of size 3. -/
lemma exists_pnc_finset_three {x y : G} (h : x * y ≠ y * x) :
    ∃ Y : Finset G, PNC (↑Y : Set G) ∧ Y.card = 3 := by
  refine ⟨{x, y, x * y}, ?_, ?_⟩
  · have hp := pnc_triple h
    have : (↑({x, y, x * y} : Finset G) : Set G) = ({x, y, x * y} : Set G) := by
      simp
    rw [this]; exact hp
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · -- `y ∉ {x*y}`
      simp only [Finset.mem_singleton]
      intro hc
      apply h
      have hx1 : x = 1 := by
        have hcy : (1 : G) * y = x * y := by rw [one_mul]; exact hc
        exact (mul_right_cancel hcy).symm
      rw [hx1]; group
    · -- `x ∉ {y, x*y}`
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun hc => h (by rw [hc]), ?_⟩
      intro hc
      apply h
      have hy1 : y = 1 := by
        have hcx : x * y = x * 1 := by rw [mul_one]; exact hc.symm
        exact mul_left_cancel hcx
      rw [hy1]; group
/-- **Theorem 4.2 (Elementary covering theorem).** If `ωnc(G) ≤ m` (finite), then
`ac(G) ≤ Uₘ`. -/
theorem ac_le_U : ∀ (m : ℕ) (G : Type*) [Group G], wnc G ≤ (m : ℕ∞) → ac G ≤ (U m : ℕ∞) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G _ hwnc
    by_cases habelian : ∀ a b : G, a * b = b * a
    · -- Abelian case: `ac G ≤ 1 ≤ Uₘ`.
      refine le_trans (ac_le_one_of_abelian habelian) ?_
      exact_mod_cast U_pos m
    · -- Nonabelian case.
      push_neg at habelian
      obtain ⟨a, b, hab⟩ := habelian
      obtain ⟨X, hXpnc, hXcov, hXmax⟩ := exists_centralizer_cover hwnc
      -- `X` has size at least 3, and at most `m`.
      obtain ⟨Y, hYpnc, hYcard⟩ := exists_pnc_finset_three hab
      have hcard3 : 3 ≤ X.card := by rw [← hYcard]; exact hXmax Y hYpnc
      have hcard2 : 2 ≤ X.card := by omega
      have hcardm : X.card ≤ m := by
        have := le_wnc hXpnc
        have h2 := le_trans this hwnc
        exact_mod_cast h2
      have hm3 : 3 ≤ m := le_trans hcard3 hcardm
      -- Each centralizer has abelian covering number `≤ U₍ₘ₋₂₎`.
      have hcent : ∀ x ∈ X, ac (Subgroup.centralizer ({x} : Set G)) ≤ (U (m - 2) : ℕ∞) := by
        intro x hx
        obtain ⟨y, hy⟩ := pnc_mem_noncentral hXpnc hcard2 hx
        have hwc : wnc (Subgroup.centralizer ({x} : Set G)) ≤ ((m - 2 : ℕ) : ℕ∞) :=
          wnc_centralizer_le hwnc hy
        exact ih (m - 2) (by omega) _ hwc
      -- Transport the cover.
      have htrans : ac G ≤ ((X.card * U (m - 2) : ℕ) : ℕ∞) :=
        ac_le_subgroup_cover X (fun x => Subgroup.centralizer ({x} : Set G)) hXcov hcent
      refine le_trans htrans ?_
      have : X.card * U (m - 2) ≤ U m := by
        rw [U_rec hm3]
        exact Nat.mul_le_mul_right _ hcardm
      exact_mod_cast this
end Erdos
/- ============================================================
   Source file: RequestProject/MainBounds.lean
   ============================================================ -/
/-!
# The upper bound on `h`
`Erdos.h_le_U` : `h(n) ≤ Uₙ`, so the supremum defining `h(n)` is a finite integer.
`Erdos.le_h`   : a way to bound `h(n)` from below by exhibiting a witnessing group.
-/
open scoped Classical
namespace Erdos
/-- **Theorem 4.2 for `h`.** `h(n) ≤ Uₙ`; in particular `h(n)` is finite. -/
theorem h_le_U (n : ℕ) : h n ≤ (U n : ℕ∞) := by
  refine iSup_le fun G => iSup_le fun inst => iSup_le fun hwnc => ?_
  exact ac_le_U n G hwnc
/-- To bound `h(n)` from below, exhibit a group `G` (on `Type`) with `ωnc(G) ≤ n` and a lower
bound on `ac(G)`. -/
theorem le_h {n : ℕ} {c : ℕ∞} (G : Type) [inst : Group G] (hwnc : wnc G ≤ (n : ℕ∞))
    (hac : c ≤ ac G) : c ≤ h n := by
  refine le_iSup_of_le G ?_
  refine le_iSup_of_le inst ?_
  refine le_iSup_of_le hwnc ?_
  exact hac
end Erdos
/- ============================================================
   Source file: RequestProject/Neumann.lean
   ============================================================ -/
/-!
# The sharp exponential order (Section 9 of the paper)
The elementary recurrence gives a superexponential upper bound `h(n) ≤ Uₙ`.  The sharp order
`h(n) = 2^{Θ(n)}` uses two external structural results:
* **Neumann (Theorem 9.1):** `ωnc(G) < ∞ ⟹ [G : Z(G)] < ∞`;
* **Pyber (Theorem 9.2):** finite `Q` satisfies `[Q : Z(Q)] ≤ C^{ωnc(Q)}`.
The reduction from these to arbitrary groups is Corollary 9.6, which we take here as a single
hypothesis (`hQ`) — a *quantitative centre theorem in the required form*.  The remaining input,
**Lemma 9.7** (`ac(G) ≤ [G : Z(G)]`), is entirely elementary and is proved here.  Combining the two
yields **Theorem 9.8**: `h(n) ≤ Cⁿ`.
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-
**Lemma 9.7.** If the centre has finite index, then `ac(G) ≤ [G : Z(G)]`.
-/
theorem ac_le_index_center [Finite (G ⧸ Subgroup.center G)] :
    ac G ≤ (Nat.card (G ⧸ Subgroup.center G) : ℕ∞) := by
  have h_fintype : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite (G ⧸ Subgroup.center G);
  refine' le_trans ( ac_le_finset_cover _ _ ) _;
  exact Finset.image ( fun c : G ⧸ Subgroup.center G => Subgroup.zpowers ( Quotient.out c ) ⊔ Subgroup.center G ) Finset.univ;
  · simp +decide [ Subgroup.abelian ];
    intro a x hx y hy;
    rw [ Subgroup.sup_eq_closure ] at hx hy;
    refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ hx;
    · refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ hy;
      · rcases hx with ( hx | hx ) <;> simp_all +decide [ Subgroup.mem_center_iff ];
        rcases ‹ ( _ : G ) ∈ Subgroup.zpowers ( Quotient.out a ) ∨ _› with ( h | h ) <;> simp_all +decide [ Subgroup.mem_zpowers_iff ];
        rcases hx with ⟨ k, rfl ⟩ ; rcases h with ⟨ l, rfl ⟩ ; group;
      · simp +decide;
      · grind;
      · simp +contextual [ mul_inv_eq_iff_eq_mul ];
        simp +contextual [ mul_assoc ];
    · simp +decide;
    · grind;
    · simp +contextual [ inv_mul_eq_iff_eq_mul ];
      simp +contextual [ ← mul_assoc ];
  · intro g
    obtain ⟨c, hc⟩ : ∃ c : G ⧸ Subgroup.center G, g ∈ Subgroup.zpowers (Quotient.out c) ⊔ Subgroup.center G := by
      obtain ⟨c, hc⟩ : ∃ c : G ⧸ Subgroup.center G, g ∈ (Subgroup.zpowers (Quotient.out c) ⊔ Subgroup.center G) := by
        have h_coset : ∃ c : G ⧸ Subgroup.center G, g * (Quotient.out c)⁻¹ ∈ Subgroup.center G := by
          use QuotientGroup.mk g;
          rw [ ← QuotientGroup.eq_one_iff ] ; simp +decide ;
        obtain ⟨ c, hc ⟩ := h_coset;
        use c;
        rw [ Subgroup.sup_eq_closure ];
        rw [ Subgroup.mem_closure ];
        intro K hK; have := hK ( Set.mem_union_right _ hc ) ; simp_all +decide [ mul_mem_cancel_right ] ;
      use c
    use Subgroup.zpowers (Quotient.out c) ⊔ Subgroup.center G
    simp [hc];
  · exact_mod_cast Finset.card_image_le.trans ( by simp +decide [ Nat.card_eq_fintype_card ] )
/-- **Theorem 9.8.** Given the quantitative centre theorem in the form `hQ` (the finite bound
`[G : Z(G)] ≤ Cⁿ` for every group with `ωnc(G) ≤ n`, which encapsulates the cited theorems of
Neumann and Pyber), one has `h(n) ≤ Cⁿ`. -/
theorem h_le_pow {n C : ℕ}
    (hQ : ∀ (G : Type) [Group G], wnc G ≤ (n : ℕ∞) →
        Finite (G ⧸ Subgroup.center G) ∧ Nat.card (G ⧸ Subgroup.center G) ≤ C ^ n) :
    h n ≤ ((C ^ n : ℕ) : ℕ∞) := by
  refine iSup_le fun G => iSup_le fun inst => iSup_le fun hwnc => ?_
  obtain ⟨hfin, hbound⟩ := hQ G hwnc
  haveI := hfin
  refine le_trans ac_le_index_center ?_
  exact_mod_cast hbound
end Erdos
/- ============================================================
   Source file: RequestProject/Dihedral.lean
   ============================================================ -/
/-!
# The dihedral lower bound (Section 7 of the paper)
For odd `q ≥ 3`, the dihedral group `D₂q` (Mathlib's `DihedralGroup q`, of order `2q`) satisfies
`ωnc = q + 1` and `ac = q + 1` (Proposition 7.1).  Consequently `h(n) ≥ n` for every even
`n ≥ 4` (Corollary 7.2).
-/
open scoped Classical
open DihedralGroup
namespace Erdos
variable {q : ℕ}
/-
In `ZMod q` with `q` odd, doubling is injective at `0`.
-/
lemma zmod_add_self_eq_zero (hq : Odd q) {x : ZMod q} (h : x + x = 0) : x = 0 := by
  obtain ⟨ k, hk ⟩ := hq;
  have h_two_unit : IsUnit (2 : ZMod q) := by
    convert ( ZMod.isUnit_iff_coprime 2 q ).mpr _;
    norm_num [ hk ];
  exact h_two_unit.mul_right_eq_zero.mp ( by linear_combination' h )
/-
Distinct reflections do not commute.
-/
lemma sr_sr_noncomm (hq : Odd q) {i j : ZMod q} (hij : i ≠ j) :
    sr i * sr j ≠ sr j * sr i := by
  contrapose! hij with h;
  simp_all +decide;
  have := zmod_add_self_eq_zero hq ( show ( j - i ) + ( j - i ) = 0 from ?_ );
  · exact Eq.symm ( sub_eq_zero.mp this );
  · grind
/-
A nonidentity rotation does not commute with any reflection.
-/
lemma r_sr_noncomm (hq : Odd q) {k j : ZMod q} (hk : k ≠ 0) :
    r k * sr j ≠ sr j * r k := by
  simp_all +decide [ sub_eq_add_neg ];
  exact fun h => hk ( by rw [ neg_eq_iff_add_eq_zero ] at h; exact zmod_add_self_eq_zero hq h )
/-
`q + 1 ≤ ωnc(D₂q)`: the `q` reflections together with one nonidentity rotation are pairwise
noncommuting.
-/
lemma wnc_dihedral_ge (hq : Odd q) (hq3 : 3 ≤ q) :
    ((q + 1 : ℕ) : ℕ∞) ≤ wnc (DihedralGroup q) := by
  obtain ⟨ k, hk ⟩ := hq;
  subst hk;
  convert Erdos.le_wnc _;
  rotate_left;
  exact Finset.image ( fun j : ZMod ( 2 * k + 1 ) => sr j ) Finset.univ ∪ { r 1 };
  · intro x hx y hy hxy;
    by_cases hx' : x = r 1 <;> by_cases hy' : y = r 1 <;> simp_all +decide;
    · obtain ⟨ j, rfl ⟩ := hy;
      convert r_sr_noncomm ( show Odd ( 2 * k + 1 ) from by simp +decide [ parity_simps ] ) ( show ( 1 : ZMod ( 2 * k + 1 ) ) ≠ 0 from by haveI := Fact.mk ( by linarith : 1 < 2 * k + 1 ) ; exact one_ne_zero ) using 1;
    · obtain ⟨ y, rfl ⟩ := hx;
      convert r_sr_noncomm ( show Odd ( 2 * k + 1 ) from by simp +decide [ parity_simps ] ) ( show ( 1 : ZMod ( 2 * k + 1 ) ) ≠ 0 from by haveI := Fact.mk ( by linarith : 1 < 2 * k + 1 ) ; exact one_ne_zero ) using 1;
      exact eq_comm;
    · rcases hx with ⟨ i, rfl ⟩ ; rcases hy with ⟨ j, rfl ⟩ ; exact sr_sr_noncomm ( by simp +decide [ parity_simps ] ) ( by aesop );
  · rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
    exact fun x => by rintro ⟨ ⟩ ;
/-
`ωnc(D₂q) ≤ q + 1`: a pairwise noncommuting set has at most one rotation and at most `q`
reflections.
-/
lemma wnc_dihedral_le (hq : Odd q) :
    wnc (DihedralGroup q) ≤ ((q + 1 : ℕ) : ℕ∞) := by
  obtain ⟨ k, hk ⟩ := hq;
  have h_card : ∀ T : Finset (DihedralGroup (2 * k + 1)), PNC (T : Set (DihedralGroup (2 * k + 1))) → T.card ≤ 2 * k + 2 := by
    intro T hT
    have h_rotations : (T.filter (fun g => ∃ i, g = r i)).card ≤ 1 := by
      rw [ Finset.card_le_one_iff ];
      simp +zetaDelta at *;
      intro a b ha x hx hb y hy; have := hT ha hb; simp_all +decide [ PNC ] ;
      exact Classical.not_not.1 fun h => this h <| add_comm _ _;
    have h_reflections : (T.filter (fun g => ∃ i, g = sr i)).card ≤ 2 * k + 1 := by
      exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun g => ∃ i, g = sr i ) T ⊆ Finset.image ( fun i : ZMod ( 2 * k + 1 ) => sr i ) Finset.univ from fun x hx => by aesop ) ) ( Finset.card_image_le.trans ( by simp +decide [ Finset.card_univ ] ) );
    have h_union : T = (T.filter (fun g => ∃ i, g = r i)) ∪ (T.filter (fun g => ∃ i, g = sr i)) := by
      ext g; cases g <;> aesop;
    grind +extAll;
  convert wnc_le_nat_iff.mpr _;
  aesop
/-- **Proposition 7.1 (noncommuting number).** `ωnc(D₂q) = q + 1` for odd `q ≥ 3`. -/
theorem wnc_dihedral (hq : Odd q) (hq3 : 3 ≤ q) :
    wnc (DihedralGroup q) = ((q + 1 : ℕ) : ℕ∞) :=
  le_antisymm (wnc_dihedral_le hq) (wnc_dihedral_ge hq hq3)
/-
`ac(D₂q) ≤ q + 1`: cover by the rotation subgroup together with the `q` order-two reflection
subgroups `⟨sr i⟩`.
-/
lemma ac_dihedral_le (hq : Odd q) (hq3 : 3 ≤ q) :
    ac (DihedralGroup q) ≤ ((q + 1 : ℕ) : ℕ∞) := by
  obtain ⟨ k, hk ⟩ := hq;
  subst hk;
  have h_cover : ∀ g : DihedralGroup (2 * k + 1), ∃ A ∈ Finset.image (fun i : ZMod (2 * k + 1) => Subgroup.zpowers (sr i)) (Finset.univ : Finset (ZMod (2 * k + 1))) ∪ {Subgroup.zpowers (r 1)}, g ∈ A := by
    rintro ( g | g ) <;> simp +decide [ Subgroup.mem_zpowers_iff ];
    · exact Or.inl ⟨ g.val, by simp +decide ⟩;
    · exact ⟨ g, 1, by simp +decide ⟩;
  refine' le_trans ( Erdos.ac_le_finset_cover _ _ ) _;
  exact Finset.image ( fun i : ZMod ( 2 * k + 1 ) => Subgroup.zpowers ( sr i ) ) Finset.univ ∪ { Subgroup.zpowers ( r 1 ) };
  · simp +decide [ Subgroup.abelian ];
    simp +decide [ Subgroup.mem_zpowers_iff ];
    simp +decide [ ← zpow_add, add_comm ];
  · assumption;
  · exact_mod_cast le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_image_le.trans ( by norm_num ) ) ( Finset.card_singleton _ |> le_of_eq ) )
/-- **Proposition 7.1 (abelian covering number).** `ac(D₂q) = q + 1` for odd `q ≥ 3`. -/
theorem ac_dihedral (hq : Odd q) (hq3 : 3 ≤ q) :
    ac (DihedralGroup q) = ((q + 1 : ℕ) : ℕ∞) :=
  le_antisymm (ac_dihedral_le hq hq3)
    (le_trans (le_of_eq (wnc_dihedral hq hq3).symm) wnc_le_ac)
/-- **Corollary 7.2.** For every even `n ≥ 4`, `h(n) ≥ n`. -/
theorem le_h_of_even {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) : (n : ℕ∞) ≤ h n := by
  obtain ⟨q, hq, rfl⟩ : ∃ q, Odd q ∧ n = q + 1 := by
    refine ⟨n - 1, Nat.Even.sub_odd (by omega) hn odd_one, by omega⟩
  have hq3 : 3 ≤ q := by omega
  have hac : ((q + 1 : ℕ) : ℕ∞) ≤ ac (DihedralGroup q) :=
    le_trans (le_of_eq (wnc_dihedral hq hq3).symm) wnc_le_ac
  exact le_h (DihedralGroup q) (le_of_eq (wnc_dihedral hq hq3)) hac
end Erdos
/- ============================================================
   Source file: RequestProject/HThree.lean
   ============================================================ -/
/-!
# `h(3) = 3` (part of Theorem 8.1)
The dihedral group `D₈ = DihedralGroup 4` of order `8` has `ωnc = 3` and hence (via
`wnc ≤ ac`) `ac ≥ 3`.  Together with `h(3) ≤ U₃ = 3` this gives `h(3) = 3`.
(For `r = 1` the extraspecial group `E₁` of the paper is exactly such an order-`8` group, and
`2^r + 1 = 2r + 1 = 3`, so no symplectic machinery is needed for this value.)
-/
open scoped Classical
open DihedralGroup
namespace Erdos
/-- Bridge from a `Finset`-level pairwise condition to `PNC`. -/
lemma pnc_of_finset_pairwise {G : Type*} [Group G] {X : Finset G}
    (h : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → a * b ≠ b * a) : PNC (↑X : Set G) := by
  intro a ha b hb hab
  exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
/-- `ωnc(D₈) ≤ 3`, checked by finite enumeration. -/
lemma wnc_D8_le : wnc (DihedralGroup 4) ≤ ((3 : ℕ) : ℕ∞) := by
  rw [wnc_le_nat_iff]
  intro X hX
  have hdec : ∀ Y : Finset (DihedralGroup 4),
      (∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → a * b ≠ b * a) → Y.card ≤ 3 := by
    native_decide
  exact hdec X (fun a ha b hb hab => hX (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)
/-- `3 ≤ ωnc(D₈)`: the set `{r 1, sr 0, sr 1}` is pairwise noncommuting. -/
lemma wnc_D8_ge : ((3 : ℕ) : ℕ∞) ≤ wnc (DihedralGroup 4) := by
  have hpnc : PNC (↑({r 1, sr 0, sr 1} : Finset (DihedralGroup 4)) : Set (DihedralGroup 4)) := by
    apply pnc_of_finset_pairwise
    decide
  have hcard : ({r 1, sr 0, sr 1} : Finset (DihedralGroup 4)).card = 3 := by decide
  have := le_wnc hpnc
  rw [hcard] at this
  exact_mod_cast this
/-- `ωnc(D₈) = 3`. -/
theorem wnc_D8 : wnc (DihedralGroup 4) = ((3 : ℕ) : ℕ∞) :=
  le_antisymm wnc_D8_le wnc_D8_ge
/-- `h(3) = 3` (part of Theorem 8.1). -/
theorem h_three : h 3 = 3 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (h_le_U 3) ?_
    simp [U]
  · have hac : ((3 : ℕ) : ℕ∞) ≤ ac (DihedralGroup 4) :=
      le_trans wnc_D8_ge wnc_le_ac
    have := le_h (DihedralGroup 4) wnc_D8_le hac
    exact_mod_cast this
end Erdos
/- ============================================================
   Source file: RequestProject/SmallValues.lean
   ============================================================ -/
/-!
# Small values of `h` and the trivial lower bound
* `Erdos.one_le_ac`      : every group needs at least one abelian subgroup to be covered.
* `Erdos.wnc_le_one_of_subsingleton` : a subsingleton group has `ωnc ≤ 1`.
* `Erdos.one_le_h`       : `1 ≤ h(n)` for every `n ≥ 1`.
* `Erdos.h_one`, `Erdos.h_two` : `h(1) = h(2) = 1` (part of **Theorem 8.1**).
-/
open scoped Classical
namespace Erdos
variable {G : Type*} [Group G]
/-- Any abelian cover has at least one member (it must cover the identity), so `1 ≤ ac G`. -/
lemma one_le_ac : 1 ≤ ac G := by
  apply le_ac
  intro 𝒜 h𝒜
  rw [Set.one_le_encard_iff_nonempty]
  obtain ⟨A, hA, _⟩ := h𝒜.2 1
  exact ⟨A, hA⟩
/-- A subsingleton (in particular trivial) group has noncommuting number at most `1`. -/
lemma wnc_le_one_of_subsingleton [Subsingleton G] : wnc G ≤ ((1 : ℕ) : ℕ∞) := by
  rw [wnc_le_nat_iff]
  intro X _
  exact Finset.card_le_one_of_subsingleton X
/-- `1 ≤ h(n)` for every `n ≥ 1`, witnessed by the trivial group. -/
theorem one_le_h {n : ℕ} (hn : 1 ≤ n) : 1 ≤ h n := by
  refine le_h (PUnit) ?_ one_le_ac
  refine le_trans wnc_le_one_of_subsingleton ?_
  exact_mod_cast hn
/-- `h(1) = 1` (part of Theorem 8.1). -/
theorem h_one : h 1 = 1 := by
  refine le_antisymm ?_ (one_le_h (le_refl 1))
  refine le_trans (h_le_U 1) ?_
  simp [U]
/-- `h(2) = 1` (part of Theorem 8.1). -/
theorem h_two : h 2 = 1 := by
  refine le_antisymm ?_ (one_le_h (by norm_num))
  refine le_trans (h_le_U 2) ?_
  simp [U]
end Erdos
/- ============================================================
   Source file: RequestProject/Results.lean
   ============================================================ -/
/-!
# Collected results
This file collects the main theorems that have been proved from first principles, following the
paper *Abelian Subgroup Covers Under a Bound on Pairwise Noncommuting Sets*.
Recall (`Erdos.Defs`):
* `wnc G` is the noncommuting number `ωnc(G)` (a `ℕ∞`);
* `ac G`  is the abelian covering number `ac(G)` (a `ℕ∞`);
* `h n`   is `sup { ac(G) : ωnc(G) ≤ n }` (a `ℕ∞`).
## What is proved here
* Upper bound (Theorem 4.2 / 1.2(i)): `h n ≤ U n`.
* General inequality (Prop 2.2, `≤`): `ωnc(G) ≤ ac(G)`.
* Closed forms and monotonicity of `U` (Lemma 4.1 / 1.2(ii)).
* Dihedral lower bound (Cor 7.2 / 1.2(iii)): `h n ≥ n` for even `n ≥ 4`.
* Small values (Theorem 8.1 / 1.2(iv)): `h 1 = h 2 = 1`, `h 3 = 3`, `h 4 = 4`.
-/
open scoped Classical
namespace Erdos
/-- `h(4) = 4` (part of Theorem 8.1): upper bound `U₄ = 4` and dihedral lower bound. -/
theorem h_four : h 4 = 4 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (h_le_U 4) ?_
    simp [U]
  · have := le_h_of_even (n := 4) (by decide) (by norm_num)
    exact_mod_cast this
/-- **Theorem 1.2(iv) / 8.1.** The first four values of `h`. -/
theorem first_four_values : h 1 = 1 ∧ h 2 = 1 ∧ h 3 = 3 ∧ h 4 = 4 :=
  ⟨h_one, h_two, h_three, h_four⟩
/-- **Theorem 1.2(i), upper half.** `h(n) ≤ Uₙ` for all `n`. -/
theorem h_upper_bound (n : ℕ) : h n ≤ (U n : ℕ∞) := h_le_U n
/-- **Theorem 1.2(iii).** For every even `n ≥ 4`, `h(n) ≥ n`. -/
theorem h_ge_even {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) : (n : ℕ∞) ≤ h n :=
  le_h_of_even hn hn4
end Erdos
/- ============================================================
   Source file: RequestProject/Extraspecial/Group.lean
   ============================================================ -/
/-!
# The extraspecial 2-group `E r` (Section 6.1 of the paper)
`E r = (F₂^r) × (F₂^r) × F₂` with the twisted multiplication
`(a,b,ε)(c,d,η) = (a+c, b+d, ε+η+a·d)`.  This is a group of order `2^(2r+1)`, with centre
`{(0,0,ε)}`, and two elements commute iff the symplectic form `B((a,b),(c,d)) = a·d + c·b`
vanishes.
-/
open scoped Classical BigOperators
namespace Erdos
namespace Extraspecial
/-- The `F₂`-vector `F₂^r`. -/
abbrev Vec (r : ℕ) := Fin r → ZMod 2
/-- The standard dot product over `F₂`. -/
def dotp {r : ℕ} (a d : Vec r) : ZMod 2 := ∑ i, a i * d i
variable {r : ℕ}
lemma dotp_add_left (a c d : Vec r) : dotp (a + c) d = dotp a d + dotp c d := by
  simp only [dotp, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma dotp_add_right (a d f : Vec r) : dotp a (d + f) = dotp a d + dotp a f := by
  simp only [dotp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
@[simp] lemma dotp_zero_left (d : Vec r) : dotp 0 d = 0 := by simp [dotp]
@[simp] lemma dotp_zero_right (a : Vec r) : dotp a 0 = 0 := by simp [dotp]
lemma vec_add_self (v : Vec r) : v + v = 0 := by
  funext i; simp [CharTwo.add_self_eq_zero]
/-- Elements of the extraspecial group `E r`, written as triples `(a, b, ε)`. -/
@[ext] structure E (r : ℕ) where
  a : Vec r
  b : Vec r
  e : ZMod 2
instance : Mul (E r) :=
  ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.e + y.e + dotp x.a y.b⟩⟩
instance : One (E r) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (E r) := ⟨fun x => ⟨x.a, x.b, x.e + dotp x.a x.b⟩⟩
@[simp] lemma mul_a (x y : E r) : (x * y).a = x.a + y.a := rfl
@[simp] lemma mul_b (x y : E r) : (x * y).b = x.b + y.b := rfl
@[simp] lemma mul_e (x y : E r) : (x * y).e = x.e + y.e + dotp x.a y.b := rfl
@[simp] lemma one_a : (1 : E r).a = 0 := rfl
@[simp] lemma one_b : (1 : E r).b = 0 := rfl
@[simp] lemma one_e : (1 : E r).e = 0 := rfl
@[simp] lemma inv_a (x : E r) : x⁻¹.a = x.a := rfl
@[simp] lemma inv_b (x : E r) : x⁻¹.b = x.b := rfl
@[simp] lemma inv_e (x : E r) : x⁻¹.e = x.e + dotp x.a x.b := rfl
instance : Group (E r) :=
  Group.ofLeftAxioms
    (by
      intro x y z
      refine E.ext ?_ ?_ ?_
      · simp only [mul_a]; abel
      · simp only [mul_b]; abel
      · simp only [mul_e, mul_a, mul_b, dotp_add_left, dotp_add_right]; ring)
    (by
      intro x
      refine E.ext ?_ ?_ ?_
      · simp only [mul_a, one_a, zero_add]
      · simp only [mul_b, one_b, zero_add]
      · simp only [mul_e, one_e, one_a, dotp_zero_left, add_zero, zero_add])
    (by
      intro x
      refine E.ext ?_ ?_ ?_
      · simp only [mul_a, inv_a, one_a, vec_add_self]
      · simp only [mul_b, inv_b, one_b, vec_add_self]
      · simp only [mul_e, inv_e, inv_a, one_e]
        have h2 : ∀ z : ZMod 2, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
        rw [show x.e + dotp x.a x.b + x.e + dotp x.a x.b
          = (x.e + x.e) + (dotp x.a x.b + dotp x.a x.b) by ring, h2, h2, add_zero])
/-- The symplectic form `B((a,b),(c,d)) = a·d + c·b` on `V = F₂^r × F₂^r`, valued in `F₂`. -/
def B (x y : E r) : ZMod 2 := dotp x.a y.b + dotp y.a x.b
/-- Two elements commute iff the symplectic form of their projections vanishes. -/
lemma mul_comm_iff (x y : E r) : x * y = y * x ↔ B x y = 0 := by
  have hkey : dotp x.a y.b = dotp y.a x.b ↔ B x y = 0 := by
    unfold B
    constructor
    · intro hd; rw [hd]; exact CharTwo.add_self_eq_zero _
    · intro h
      have := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this
  constructor
  · intro h
    have he := congrArg E.e h
    simp only [mul_e] at he
    rw [add_comm y.e x.e] at he
    exact hkey.1 (add_left_cancel he)
  · intro h
    refine E.ext ?_ ?_ ?_
    · simp [add_comm]
    · simp [add_comm]
    · simp only [mul_e]
      rw [add_comm x.e y.e, hkey.2 h]
end Extraspecial
end Erdos
/- ============================================================
   Source file: RequestProject/Extraspecial/Bounds.lean
   ============================================================ -/
/-!
# The extraspecial family and the exponential lower bound (Section 6)
We record the two exact computations for the extraspecial group `E r`:
* `wnc_E` : `ωnc(E r) = 2r + 1` (Theorem 6.2);
* `ac_E`  : `ac(E r) = 2^r + 1` (Theorem 6.5).
*Remark.* The abstract of the paper prints `ac(E_r) = 2r + 1`, but this is a typo: the proof of
Theorem 6.5 (and Proposition 6.4, giving `2^r + 1` totally isotropic subspaces) yields
`ac(E_r) = 2^r + 1`, which is what makes the lower bound exponential.
From these we deduce the exponential lower bounds on `h` (Corollary 6.6):
`h(n) ≥ 2^⌊(n-1)/2⌋ + 1`.
-/
open scoped Classical
namespace Erdos
namespace Extraspecial
variable {r : ℕ}
/-- **Theorem 6.2 (upper bound).** `ωnc(E r) ≤ 2r + 1`. -/
theorem wnc_E_le : wnc (E r) ≤ ((2 * r + 1 : ℕ) : ℕ∞) := by
  sorry
/-- **Theorem 6.2 (lower bound).** `2r + 1 ≤ ωnc(E r)` for `r ≥ 1`. -/
theorem wnc_E_ge (hr : 1 ≤ r) : ((2 * r + 1 : ℕ) : ℕ∞) ≤ wnc (E r) := by
  sorry
/-- **Theorem 6.2.** `ωnc(E r) = 2r + 1`. -/
theorem wnc_E (hr : 1 ≤ r) : wnc (E r) = ((2 * r + 1 : ℕ) : ℕ∞) :=
  le_antisymm wnc_E_le (wnc_E_ge hr)
/-- **Theorem 6.5 (lower bound).** `2^r + 1 ≤ ac(E r)`: each abelian subgroup projects to a
totally isotropic subspace, covering at most `2^r - 1` nonzero vectors of `V`. -/
theorem ac_E_ge : ((2 ^ r + 1 : ℕ) : ℕ∞) ≤ ac (E r) := by
  sorry
/-- **Theorem 6.5 (upper bound).** `ac(E r) ≤ 2^r + 1`, using a symplectic spread. -/
theorem ac_E_le : ac (E r) ≤ ((2 ^ r + 1 : ℕ) : ℕ∞) := by
  sorry
/-- **Theorem 6.5.** `ac(E r) = 2^r + 1`. -/
theorem ac_E : ac (E r) = ((2 ^ r + 1 : ℕ) : ℕ∞) :=
  le_antisymm ac_E_le ac_E_ge
/-- The exponential lower bound realised at `n = 2r + 1`: `h(2r+1) ≥ 2^r + 1`. -/
theorem le_h_pow : ((2 ^ r + 1 : ℕ) : ℕ∞) ≤ h (2 * r + 1) :=
  le_h (E r) wnc_E_le ac_E_ge
/-- **Corollary 6.6.** For `n ≥ 3`, `h(n) ≥ 2^⌊(n-1)/2⌋ + 1`. -/
theorem le_h_floor {n : ℕ} (hn : 3 ≤ n) :
    ((2 ^ ((n - 1) / 2) + 1 : ℕ) : ℕ∞) ≤ h n := by
  have h2r : 2 * ((n - 1) / 2) + 1 ≤ n := by omega
  refine le_h (E ((n - 1) / 2)) (le_trans wnc_E_le ?_) ac_E_ge
  exact_mod_cast h2r
end Extraspecial
end Erdos
