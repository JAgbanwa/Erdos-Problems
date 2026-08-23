/-
# The parity counterexample to the cover-down input, at every ratio `K ≥ 3`.

This file builds, for every ratio `K ≥ 3` and every size threshold `n₀`, a configuration
`W'' ⊆ W' ⊆ W` with `K|W'| ≤ |W| ≤ K²|W'|` and `K|W''| ≤ |W'|`, and a triangle-divisible edge set
`F` spanned by `W` of minimum degree `> (91/100)|W|`, for which the conclusion of
`BKLO.CoverDownK3` fails at `K`.

The configuration is the complete graph on `W = Fin n` **minus the complete bipartite graph between
`W''` and `W' \ W''`**, with

  `|W''| = p = 6q`,  `|W'| = m = 6Kq`,  `|W| = n = 6K³q - 3`.

Take `v₀ ∈ W''`.  All its edges inside `W'` go to `W''`, and those may not be touched by the
triangle family; all its other edges must be covered.  So the covered set has degree
`deg_F(v₀) - (p - 1)` at `v₀`, which is odd because `deg_F(v₀)` is even and `p - 1 = 6q - 1` is
odd — while the edges of an edge-disjoint triangle family have even degree everywhere.  This is
`BKLO.cover_parity_obstruction`.

The size window is what makes the configuration legal: `|W'| = |W|/K²` up to rounding is small
enough that a vertex of `W''` can have almost all of its `> (91/100)|W|` neighbours outside `W'`,
and `|W''| = |W'|/K` is large enough to supply the odd number `p - 1` of neighbours inside `W''`.

Everything here is `sorry`-free.
-/
import BKLO.CoverDownObstruction

open Finset

namespace BKLO

namespace RefutationB

/-- The first `k` vertices of `Fin n`. -/
def lowB (n k : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < k)

/-- The middle layer `W' \ W''`. -/
def midB (n p m : ℕ) : Finset (Fin n) := univ.filter (fun i => p ≤ i.val ∧ i.val < m)

/-- The complete bipartite graph between `W''` and `W' \ W''`: the edges that are *absent*. -/
def bipB (n p m : ℕ) : Finset (Sym2 (Fin n)) :=
  ((lowB n p) ×ˢ (midB n p m)).image (fun z => s(z.1, z.2))

/-- The complete graph on `Fin n` minus the bipartite graph between `W''` and `W' \ W''`. -/
def edgesB (n p m : ℕ) : Finset (Sym2 (Fin n)) := cliqueEdges (univ : Finset (Fin n)) \ bipB n p m

theorem mem_lowB {n k : ℕ} {i : Fin n} : i ∈ lowB n k ↔ i.val < k := by simp [lowB]

theorem mem_midB {n p m : ℕ} {i : Fin n} : i ∈ midB n p m ↔ (p ≤ i.val ∧ i.val < m) := by
  simp [midB]

theorem lowB_subset {n k l : ℕ} (h : k ≤ l) : lowB n k ⊆ lowB n l := by
  intro i hi; rw [mem_lowB] at *; omega

theorem card_lowB {n k : ℕ} (h : k ≤ n) : (lowB n k).card = k := by
  classical
  have hEq : lowB n k = (Finset.range k).attachFin (by intro x hx; simp at hx; omega) := by
    ext i; simp [lowB, Finset.mem_attachFin]
  rw [hEq, Finset.card_attachFin, Finset.card_range]

theorem card_midB {n p m : ℕ} (hpm : p ≤ m) (hm : m ≤ n) : (midB n p m).card = m - p := by
  classical
  have hEq : midB n p m = lowB n m \ lowB n p := by
    ext i
    simp only [mem_midB, mem_lowB, Finset.mem_sdiff]
    omega
  rw [hEq, Finset.card_sdiff_of_subset (lowB_subset hpm), card_lowB hm,
    card_lowB (le_trans hpm hm)]

theorem mem_bipB {n p m : ℕ} {x y : Fin n} :
    s(x, y) ∈ bipB n p m ↔
      (x.val < p ∧ p ≤ y.val ∧ y.val < m) ∨ (y.val < p ∧ p ≤ x.val ∧ x.val < m) := by
  constructor
  · intro he
    obtain ⟨⟨a, b⟩, hab, hEq⟩ := Finset.mem_image.1 he
    simp only [Finset.mem_product, mem_lowB, mem_midB] at hab
    simp only [Sym2.eq_iff] at hEq
    rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hab.1, hab.2⟩
    · exact Or.inr ⟨hab.1, hab.2⟩
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Finset.mem_image.2 ⟨(x, y), ?_, rfl⟩
      simp only [Finset.mem_product, mem_lowB, mem_midB]
      exact ⟨h1, h2⟩
    · refine Finset.mem_image.2 ⟨(y, x), ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_product, mem_lowB, mem_midB]
      exact ⟨h1, h2⟩

theorem bipB_subset (n p m : ℕ) : bipB n p m ⊆ cliqueEdges (univ : Finset (Fin n)) := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    refine mem_cliqueEdgesV.2 ⟨fun z _ => Finset.mem_univ z, ?_⟩
    simp only [Sym2.isDiag_iff_proj_eq]
    intro hxy
    rcases mem_bipB.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hxy] at * <;> omega

theorem card_bipB {n p m : ℕ} (hpm : p ≤ m) (hm : m ≤ n) :
    (bipB n p m).card = p * (m - p) := by
  classical
  unfold bipB
  rw [Finset.card_image_of_injOn, Finset.card_product, card_lowB (le_trans hpm hm),
    card_midB hpm hm]
  rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' heq
  simp only [Finset.mem_coe, Finset.mem_product, mem_lowB, mem_midB] at hxy hxy'
  simp only [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · omega

theorem inj_sym2 {n : ℕ} (v : Fin n) :
    Set.InjOn (fun u : Fin n => s(v, u)) (univ : Finset (Fin n)) := by
  intro a _ b _ hab
  simp only [Sym2.eq_iff] at hab
  rcases hab with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact h
  · exact h2.trans h1

/-! ### Degrees -/

theorem edeg_bipB_low {n p m : ℕ} {v : Fin n} (hv : v.val < p) (hpm : p ≤ m) (hm : m ≤ n) :
    edeg (bipB n p m) v = m - p := by
  classical
  have hfil : (bipB n p m).filter (fun e => v ∈ e) = (midB n p m).image (fun u => s(v, u)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he, hve⟩
      induction e using Sym2.ind with
      | _ x y =>
        rcases mem_bipB.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact ⟨y, mem_midB.2 h2, rfl⟩
          · omega
        · rcases Sym2.mem_iff.1 hve with rfl | rfl
          · omega
          · exact ⟨x, mem_midB.2 h2, Sym2.eq_swap⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mem_bipB.2 (Or.inl ⟨hv, mem_midB.1 hu⟩), by simp⟩
  unfold edeg
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ h => inj_sym2 v (by simp) (by simp) h),
    card_midB hpm hm]

theorem edeg_bipB_mid {n p m : ℕ} {v : Fin n} (hv1 : p ≤ v.val) (hv2 : v.val < m) (hpm : p ≤ m)
    (hm : m ≤ n) : edeg (bipB n p m) v = p := by
  classical
  have hfil : (bipB n p m).filter (fun e => v ∈ e) = (lowB n p).image (fun u => s(v, u)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨he, hve⟩
      induction e using Sym2.ind with
      | _ x y =>
        rcases mem_bipB.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases Sym2.mem_iff.1 hve with rfl | rfl
          · omega
          · exact ⟨x, mem_lowB.2 h1, Sym2.eq_swap⟩
        · rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact ⟨y, mem_lowB.2 h1, rfl⟩
          · omega
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mem_bipB.2 (Or.inr ⟨mem_lowB.1 hu, hv1, hv2⟩), by simp⟩
  unfold edeg
  rw [hfil, Finset.card_image_of_injOn (fun a _ b _ h => inj_sym2 v (by simp) (by simp) h),
    card_lowB (le_trans hpm hm)]

theorem edeg_bipB_high {n p m : ℕ} {v : Fin n} (hv : m ≤ v.val) : edeg (bipB n p m) v = 0 := by
  classical
  have hfil : (bipB n p m).filter (fun e => v ∈ e) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 ?_
    intro e he hve
    induction e using Sym2.ind with
    | _ x y =>
      rcases mem_bipB.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases Sym2.mem_iff.1 hve with rfl | rfl <;> omega
  unfold edeg
  rw [hfil, Finset.card_empty]

theorem edeg_edgesB_add {n p m : ℕ} (v : Fin n) :
    edeg (bipB n p m) v + edeg (edgesB n p m) v = n - 1 := by
  have h1 : edeg (bipB n p m) v + edeg (edgesB n p m) v
      = edeg (cliqueEdges (univ : Finset (Fin n))) v :=
    edeg_sdiff_add (bipB_subset n p m) v
  rw [h1, edeg_cliqueEdges_of_mem (Finset.mem_univ v)]
  simp

theorem edgesB_subset (n p m : ℕ) : edgesB n p m ⊆ cliqueEdges (univ : Finset (Fin n)) :=
  Finset.sdiff_subset

/-! ### The bottom level is untouched by the missing edges -/

theorem cliqueEdges_lowB_subset_edgesB {n p m : ℕ} :
    cliqueEdges (lowB n p) ⊆ edgesB n p m := by
  intro e he
  refine Finset.mem_sdiff.2 ⟨cliqueEdges_mono (Finset.subset_univ _) he, ?_⟩
  intro hbip
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x.val < p := mem_lowB.1 ((mem_cliqueEdgesV.1 he).1 x (by simp))
    have hy : y.val < p := mem_lowB.1 ((mem_cliqueEdgesV.1 he).1 y (by simp))
    rcases mem_bipB.1 hbip with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem inter_cliqueEdges_lowB {n p m : ℕ} :
    edgesB n p m ∩ cliqueEdges (lowB n p) = cliqueEdges (lowB n p) :=
  Finset.inter_eq_right.2 cliqueEdges_lowB_subset_edgesB

/-- At a vertex of `W''`, every edge of `F` inside `W'` lies inside `W''`. -/
theorem link_lowB {n p m : ℕ} {v₀ : Fin n} (hv₀ : v₀.val < p) :
    ∀ e ∈ edgesB n p m, v₀ ∈ e → e ∈ cliqueEdges (lowB n m) → e ∈ cliqueEdges (lowB n p) := by
  intro e he hv hem
  induction e using Sym2.ind with
  | _ x y =>
    have hx : x.val < m := mem_lowB.1 ((mem_cliqueEdgesV.1 hem).1 x (by simp))
    have hy : y.val < m := mem_lowB.1 ((mem_cliqueEdgesV.1 hem).1 y (by simp))
    have hnbip : s(x, y) ∉ bipB n p m := (Finset.mem_sdiff.1 he).2
    have hxp : x.val < p ∧ y.val < p := by
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · by_contra hcon
        exact hnbip (mem_bipB.2 (Or.inl ⟨hv₀, by omega⟩))
      · by_contra hcon
        exact hnbip (mem_bipB.2 (Or.inr ⟨hv₀, by omega⟩))
    refine mem_cliqueEdgesV.2 ⟨?_, (mem_cliqueEdgesV.1 hem).2⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    exacts [mem_lowB.2 hxp.1, mem_lowB.2 hxp.2]

end RefutationB

open RefutationB in
/-- **The cover-down conclusion fails at every ratio `K ≥ 3`**, for the density `c = 91/100 > 9/10`
and the damage tolerance `γ = 1/20`: at a vertex of `W''` whose only edges inside `W'` go to `W''`,
the covered edge set would have odd degree. -/
theorem not_coverDownK3At_ge_three {K : ℕ} (hK : 3 ≤ K) (n₀ : ℕ) :
    ¬ CoverDownK3At (91 / 100) (1 / 20) K n₀ := by
  classical
  intro h
  -- the sizes
  set q : ℕ := n₀ + 1 with hq
  set B : ℕ := K * q with hB
  set C : ℕ := K * B with hC
  set A : ℕ := K * C with hA
  set p : ℕ := 6 * q with hp
  set m : ℕ := 6 * B with hm
  set n : ℕ := 6 * A - 3 with hn
  have hq1 : 1 ≤ q := by omega
  have hBq : 3 * q ≤ B := by
    rw [hB]; exact Nat.mul_le_mul_right q hK
  have hCB : 3 * B ≤ C := by
    rw [hC]; exact Nat.mul_le_mul_right B hK
  have hAC : 3 * C ≤ A := by
    rw [hA]; exact Nat.mul_le_mul_right C hK
  have hpm : p ≤ m := by omega
  have hmn : m ≤ n := by omega
  have hAkey : 600 * B + 127 ≤ 54 * A + 600 * q := by
    have hAK : A = K ^ 3 * q := by rw [hA, hC, hB]; ring
    have hBK : B = K * q := hB
    rw [hAK, hBK]
    nlinarith only [Nat.mul_le_mul_right q hK, sq_nonneg K, hq1, hK]
  have hcardW : (univ : Finset (Fin n)).card = n := by simp
  -- the degree of a vertex is at least `6A - 4 - 6B + 6q`
  have hdeg : ∀ v : Fin n, 6 * A - 4 - (6 * B - 6 * q) ≤ edeg (edgesB n p m) v := by
    intro v
    have hsum := edeg_edgesB_add (n := n) (p := p) (m := m) v
    rcases lt_or_ge v.val p with hlt | hge
    · rw [edeg_bipB_low hlt hpm hmn] at hsum; omega
    · rcases lt_or_ge v.val m with hlt2 | hge2
      · rw [edeg_bipB_mid hge hlt2 hpm hmn] at hsum; omega
      · rw [edeg_bipB_high hge2] at hsum; omega
  -- triangle divisibility
  have hdiv : TriDivisible (edgesB n p m) := by
    constructor
    · intro v
      show Even (edeg (edgesB n p m) v)
      have hsum := edeg_edgesB_add (n := n) (p := p) (m := m) v
      rw [Nat.even_iff]
      rcases lt_or_ge v.val p with hlt | hge
      · rw [edeg_bipB_low hlt hpm hmn] at hsum; omega
      · rcases lt_or_ge v.val m with hlt2 | hge2
        · rw [edeg_bipB_mid hge hlt2 hpm hmn] at hsum; omega
        · rw [edeg_bipB_high hge2] at hsum; omega
    · show 3 ∣ (edgesB n p m).card
      have hcard : (edgesB n p m).card = n.choose 2 - p * (m - p) := by
        unfold edgesB
        rw [Finset.card_sdiff_of_subset (bipB_subset n p m), card_cliqueEdges, hcardW,
          card_bipB hpm hmn]
      rw [hcard]
      refine Nat.dvd_sub ?_ ?_
      · -- `3 ∣ C(n,2)` because `n = 6A - 3` and `n - 1 = 6A - 4`
        obtain ⟨A', hA'⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
        have h2 : 2 * (n.choose 2) = n * (n - 1) := two_mul_choose_two n
        have hnv : n = 6 * A' + 3 := by omega
        have hnv1 : n - 1 = 6 * A' + 2 := by omega
        rw [hnv1] at h2
        rw [hnv] at h2 ⊢
        have e1 : (6 * A' + 3) * (6 * A' + 2) = 36 * A' ^ 2 + 30 * A' + 6 := by ring
        rw [e1] at h2
        omega
      · exact Dvd.dvd.mul_right ⟨2 * q, by omega⟩ (m - p)
  -- apply the cover-down conclusion
  obtain ⟨P, hP, hleft, huntouched, -⟩ :=
    h (V := Fin n) (univ : Finset (Fin n)) (lowB n m) (lowB n p) (edgesB n p m)
      (by rw [hcardW]; omega)
      (Finset.subset_univ _) (lowB_subset hpm)
      (by rw [hcardW, card_lowB hmn, hm]
          have hKm : K * (6 * B) = 6 * C := by rw [hC]; ring
          omega)
      (by rw [hcardW, card_lowB hmn, hm]
          have : K * K * (6 * B) = 6 * A := by rw [hA, hC]; ring
          omega)
      (by rw [card_lowB hmn, card_lowB (le_trans hpm hmn), hp, hm]
          have : K * (6 * q) = 6 * B := by rw [hB]; ring
          omega)
      (edgesB_subset n p m) hdiv
      (by
        intro v _
        rw [hcardW]
        have h1 : 91 * n ≤ 100 * (6 * A - 4 - (6 * B - 6 * q)) := by omega
        have h2 : (6 * A - 4 - (6 * B - 6 * q) : ℕ) ≤ edeg (edgesB n p m) v := hdeg v
        have h3 : (91 : ℝ) * (n : ℝ) ≤ 100 * ((6 * A - 4 - (6 * B - 6 * q) : ℕ) : ℝ) := by
          exact_mod_cast h1
        have h4 : ((6 * A - 4 - (6 * B - 6 * q) : ℕ) : ℝ) ≤ (edeg (edgesB n p m) v : ℝ) := by
          exact_mod_cast h2
        linarith)
  -- the parity contradiction at the vertex `0`
  have hnpos : 0 < n := by omega
  set v₀ : Fin n := ⟨0, hnpos⟩ with hv₀
  have hv₀p : v₀.val < p := by simp [hv₀]; omega
  have heven : Even (edeg (edgesB n p m) v₀) := hdiv.1 v₀
  have hpar := cover_parity_obstruction (W' := lowB n m) (W'' := lowB n p) hP hleft huntouched
    (link_lowB hv₀p) heven
  rw [inter_cliqueEdges_lowB] at hpar
  rw [edeg_cliqueEdges_of_mem (mem_lowB.2 hv₀p), card_lowB (le_trans hpm hmn)] at hpar
  rw [Nat.even_iff] at hpar
  omega

end BKLO
