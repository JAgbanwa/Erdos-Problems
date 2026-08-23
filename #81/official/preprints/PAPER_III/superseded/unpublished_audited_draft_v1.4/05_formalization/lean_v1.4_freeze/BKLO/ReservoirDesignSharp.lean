/-
# The sharp grid design.

`BKLO.IsGridCleanReservoir` (`BKLO/ReservoirDesignClean.lean`) is obtained from the grid design of
`BKLO.exists_reservoir_full_structured` by *deleting* the protected level `W''` from the classes.
That deletion is what costs the design its two-sided balance:

* the classes end up of unequal sizes anywhere in `[3t/4, t]`, which
  `BKLO.not_gridPairingResidualClean` turns into an outright refutation of the pairing demand;
* even after the sizes are equalized (`BKLO.exists_reservoir_equitable_structured`) the balance
  `classBalanced` is still measured against the *nominal* size `t`, so a class of `3t/4` places may
  miss a third of itself at a given vertex of `W`, and the resulting link is exactly — with no
  margin at all — at Dirac's threshold.

This file removes the deletion: the classes are extracted from the pool `W' \ W''` in the first
place, so they avoid the protected level by construction, they all have the one common size
`t₁ = ⌊|W' \ W''| / (10h²)⌋`, and the balance `BKLO.IsGridSharpReservoir.classBalancedSharp` is
against *their own* size — every vertex of `W` misses at most a quarter of every class.  The room
is there because the protected level is a `1/800`-th of `W'` (`K|W''| ≤ |W'|` and `8 ≤ εK` with
`ε ≤ 1/100`), so `t₁` is within a `1/200`-th of the nominal `t`.

The construction repeats `BKLO.exists_reservoir_full_structured` with the pool `W' \ W''` and the
class size `t₁`; the apexes are exported at the perturbation scale `BKLO.cleanEta` of the clean
design.  In the sharp design the reserved link of an outer vertex has, at each of its vertices,
`|link|/2 + Θ(h t)` neighbours inside itself, so Dirac's threshold is met with a margin
proportional to the link itself.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignEquitable

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **A sharp grid reservoir**: an equitable clean grid design whose classes are balanced against
their *own* size — every vertex of `W` misses at most a quarter of every class. -/
structure IsGridSharpReservoir (ε : ℝ) (K : ℕ) (W W' W'' : Finset V) (F R : Finset (Sym2 V))
    (C : ℕ → Finset V) (x y : V → ℕ)
    : Prop extends IsGridEquitableReservoir ε K W W' W'' F R C x y where
  /-- **every vertex of `W` misses at most a quarter of each class.** -/
  classBalancedSharp : ∀ v ∈ W, ∀ i < gridSize ε K * gridSize ε K,
    4 * ((nonNbrs F W' v ∩ C i).card) ≤ (C i).card

/-! ### The construction -/

set_option maxHeartbeats 4000000 in
/-- **The sharp grid design.**  The construction of `BKLO.exists_reservoir_full_structured`, run on
the pool `W' \ W''`: the classes avoid the protected level by construction, have one common size,
and are balanced against that size. -/
theorem exists_reservoir_sharp_structured
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
    {W W' W'' : Finset V} {F : Finset (Sym2 V)}
    (hW''W' : W'' ⊆ W')
    (hKW' : K * W'.card ≤ W.card) (hW'K : W.card ≤ K * K * W'.card)
    (hKW'' : K * W''.card ≤ W'.card)
    (hres : ∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ))
    (hN : reservoirThreshold ε K ≤ W.card) :
    ∃ (R : Finset (Sym2 V)) (C : ℕ → Finset V) (x y : V → ℕ),
      R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * cleanEta ε K * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) ∧
      IsGridSharpReservoir ε K W W' W'' F R C x y := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set N : ℕ := W.card with hNdef
  set m : ℕ := W'.card with hmdef
  set t : ℕ := m / (10 * h * h) with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hεh : (64 : ℝ) * (K : ℝ) ^ 2 ≤ ε * (h : ℝ) := by
    have h1 := le_gridSize ε K
    have h2 : (64 : ℝ) * (K : ℝ) ^ 2 / ε * ε ≤ (h : ℝ) * ε :=
      mul_le_mul_of_nonneg_right h1 hε.le
    rw [div_mul_cancel₀] at h2
    · linarith
    · exact ne_of_gt hε
  have hεK : (8 : ℝ) ≤ ε * (K : ℝ) := by
    have h2 : (8 : ℝ) / ε * ε ≤ (K : ℝ) * ε := mul_le_mul_of_nonneg_right hKε hε.le
    rw [div_mul_cancel₀] at h2
    · linarith
    · exact ne_of_gt hε
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · exfalso; rw [hK0] at hεK; norm_num at hεK
    · exact hK0
  have hh1 : 1 ≤ h := hhpos
  have hK1 : 1 ≤ K := hKpos
  have hK1r : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  -- ### the numerical facts
  set Q : ℕ := K * K * h * h with hQdef
  have hQpos : 0 < Q := by positivity
  have hhhQ : h * h ≤ Q := by
    have : 1 * 1 * (h * h) ≤ K * K * (h * h) :=
      Nat.mul_le_mul (Nat.mul_le_mul hK1 hK1) le_rfl
    simpa [hQdef, Nat.mul_assoc] using this
  have hKKQ : K * K ≤ Q := by
    have : K * K * (1 * 1) ≤ K * K * (h * h) :=
      Nat.mul_le_mul le_rfl (Nat.mul_le_mul hh1 hh1)
    simpa [hQdef, Nat.mul_assoc] using this
  have hNbig : 10 ^ 9 * (Q * Q) ≤ N := by
    have : reservoirThreshold ε K = 10 ^ 9 * (Q * Q) := by
      simp only [reservoirThreshold, hQdef, hhdef]; ring
    omega
  have hmQ : Q * m ≥ N := by
    calc N ≤ K * K * m := hW'K
      _ ≤ Q * m := Nat.mul_le_mul_right _ hKKQ
  have hmbig : 10 ^ 9 * Q ≤ m := by
    by_contra hcon
    push_neg at hcon
    have hlt : Q * m < 10 ^ 9 * (Q * Q) := by
      calc Q * m < Q * (10 ^ 9 * Q) := (Nat.mul_lt_mul_left hQpos).2 hcon
        _ = 10 ^ 9 * (Q * Q) := by ring
    omega
  have ht1 : 1 ≤ t := by
    rw [htdef]
    refine (Nat.one_le_div_iff (by positivity)).2 ?_
    calc 10 * h * h ≤ 10 ^ 9 * Q := by nlinarith only [hhhQ, hQpos]
      _ ≤ m := hmbig
  have hvolt : 10 * ((h * h) * t) ≤ m := by
    have := Nat.div_mul_le_self m (10 * h * h)
    calc 10 * ((h * h) * t) = t * (10 * h * h) := by ring
      _ ≤ m := this
  have hmt : m ≤ 10 * h * h * t + 10 * h * h := by
    have key : ∀ d : ℕ, 0 < d → m ≤ d * (m / d) + d := by
      intro d hd
      have h1 := Nat.div_add_mod m d
      have h2 := Nat.mod_lt m hd
      linarith
    have := key (10 * h * h) (by positivity)
    rw [← htdef] at this
    exact this
  have hNt : N ≤ 20 * Q * t := by
    calc N ≤ K * K * m := hW'K
      _ ≤ K * K * (10 * h * h * t + 10 * h * h) := Nat.mul_le_mul le_rfl hmt
      _ ≤ 20 * Q * t := by
          simp only [hQdef]
          nlinarith only [Nat.mul_le_mul (le_refl (K * K * h * h * 10)) ht1]
  -- ### the classes
  have hW''m : ((W''.card : ℝ)) * 8 ≤ ε * (m : ℝ) := by
    have h1 : ((K : ℝ)) * (W''.card : ℝ) ≤ (m : ℝ) := by
      have : ((K * W''.card : ℕ) : ℝ) ≤ ((W'.card : ℕ) : ℝ) := by exact_mod_cast hKW''
      push_cast at this
      simpa [hmdef] using this
    have h2 : (0 : ℝ) ≤ (W''.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hεK, h1, h2, hε.le]
  -- ### the pool, the protected level and the sharp class size
  set w : ℕ := W''.card with hwdef
  have hwm : 800 * w ≤ m := by
    have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h1 : (800 : ℝ) * (w : ℝ) ≤ (m : ℝ) := by nlinarith only [hW''m, hε', hmr]
    exact_mod_cast h1
  set P : Finset V := W' \ W'' with hPdef
  have hPcard : P.card = m - w := by
    rw [hPdef, Finset.card_sdiff_of_subset hW''W']
  have hwle : w ≤ m := by omega
  have hPm : P.card + w = m := by omega
  set A : ℕ := 10 * h * h with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set t₁ : ℕ := P.card / A with ht₁def
  have ht₁vol : 10 * ((h * h) * t₁) ≤ P.card := by
    have h1 : t₁ * A ≤ P.card := by rw [ht₁def]; exact Nat.div_mul_le_self P.card A
    have h2 : 10 * ((h * h) * t₁) = t₁ * A := by rw [hAdef]; ring
    omega
  have hAm : 100 * A ≤ m := by
    have h1 : 1000 * (h * h) ≤ 10 ^ 9 * Q := by nlinarith only [hhhQ, hQpos]
    have h2 : 100 * A = 1000 * (h * h) := by rw [hAdef]; ring
    omega
  have hAt : t * A ≤ m := by rw [htdef]; exact Nat.div_mul_le_self m A
  have hAt₁ : t₁ * A ≤ P.card := by rw [ht₁def]; exact Nat.div_mul_le_self P.card A
  have hlt₁ : P.card < t₁ * A + A := by
    have hdm : A * t₁ + P.card % A = P.card := by
      rw [ht₁def]; exact Nat.div_add_mod P.card A
    have hmod : P.card % A < A := Nat.mod_lt _ hApos
    have hcomm : A * t₁ = t₁ * A := Nat.mul_comm _ _
    omega
  have h3t : 3 * t ≤ 4 * t₁ := by
    have hkey : (3 * t) * A ≤ (4 * t₁) * A := by
      have e1 : (3 * t) * A = 3 * (t * A) := by ring
      have e2 : (4 * t₁) * A = 4 * (t₁ * A) := by ring
      rw [e1, e2]
      linarith
    exact Nat.le_of_mul_le_mul_right hkey hApos
  have ht₁1 : 1 ≤ t₁ := by omega
  have ht2 : t ≤ 2 * t₁ := by omega
  have hNt₁ : N ≤ 40 * Q * t₁ := by
    calc N ≤ 20 * Q * t := hNt
      _ ≤ 20 * Q * (2 * t₁) := Nat.mul_le_mul_left _ ht2
      _ = 40 * Q * t₁ := by ring
  have hnonbd : ∀ v ∈ W, (10 : ℝ) * ((nonNbrs F W' v).card : ℝ) ≤ (m : ℝ) - 5 / 2 * ε * (m : ℝ) := by
    intro v hv
    have hsub : resLink F W' v ⊆ W' := fun a ha => (mem_resLink.1 ha).1
    have hcard : (nonNbrs F W' v).card = m - (resLink F W' v).card := by
      simpa [nonNbrs, hmdef] using Finset.card_sdiff_of_subset hsub
    have hle : (resLink F W' v).card ≤ m := Finset.card_le_card hsub
    have hR := hres v hv
    rw [hcard]
    have hcast : (((m - (resLink F W' v).card : ℕ)) : ℝ)
        = (m : ℝ) - ((resLink F W' v).card : ℝ) := by
      push_cast [Nat.cast_sub hle]; ring
    rw [hcast]
    nlinarith only [hR, hε]
  have hTcard1 : ∀ v ∈ W, 10 * ((nonNbrs F W' v).card) ≤ P.card := by
    intro v hv
    have hPr : ((P.card : ℕ) : ℝ) = (m : ℝ) - (w : ℝ) := by
      rw [hPcard]; push_cast [Nat.cast_sub hwle]; ring
    have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h1 : (10 : ℝ) * ((nonNbrs F W' v).card : ℝ) ≤ ((P.card : ℕ) : ℝ) := by
      rw [hPr]
      nlinarith only [hnonbd v hv, hW''m, hε, hmr]
    exact_mod_cast h1
  have hsmall1 : (W.card : ℝ) * (9 / 10 : ℝ) ^ (2 * (t₁ / 32)) < 1 := by
    refine union_bound_of_sq ?_
    rw [← hNdef]
    set s : ℕ := t₁ / 32 with hsdef
    have hts : t₁ ≤ 32 * s + 31 := by rw [hsdef]; omega
    have h1 : N ≤ 1280 * Q * s + 1240 * Q := by
      calc N ≤ 40 * Q * t₁ := hNt₁
        _ ≤ 40 * Q * (32 * s + 31) := Nat.mul_le_mul le_rfl hts
        _ = 1280 * Q * s + 1240 * Q := by ring
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · exfalso
        rw [hs0] at h1
        nlinarith only [hNbig, h1, hQpos]
      · exact hs0
    have hA' : N ≤ 2560 * Q * s := by nlinarith only [h1, hs1, hQpos]
    have hsq : N * N ≤ (2560 * Q * s) * (2560 * Q * s) := Nat.mul_le_mul hA' hA'
    have hNN : 10 ^ 9 * (Q * Q) * N ≤ N * N := Nat.mul_le_mul_right N hNbig
    have hQQ : 0 < Q * Q := by positivity
    have hstep : (Q * Q) * (10 ^ 9 * N) ≤ (Q * Q) * (6553600 * (s * s)) := by
      nlinarith only [hsq, hNN]
    have hfin : 10 ^ 9 * N ≤ 6553600 * (s * s) := Nat.le_of_mul_le_mul_left hstep hQQ
    have hNpos : 0 < N := by nlinarith only [hNbig, hQQ]
    linarith
  obtain ⟨C, hCP, hCcard, hCdisj, hCbal⟩ :=
    exists_balanced_classes (W := W) (P := P) (T := fun v => nonNbrs F W' v) (g := h * h)
      (t := t₁) hTcard1 ht₁vol ht₁1 hsmall1
  have hCW' : ∀ i < h * h, C i ⊆ W' := by
    intro i hi
    exact (hCP i hi).trans (by rw [hPdef]; exact Finset.sdiff_subset)
  have hCavoid : ∀ i < h * h, Disjoint (C i) W'' := by
    intro i hi
    exact Finset.disjoint_of_subset_left (hCP i hi) (by rw [hPdef]; exact Finset.sdiff_disjoint)
  have hCbal' : ∀ v ∈ W, ∀ i < h * h, 4 * ((nonNbrs F W' v ∩ C i).card) ≤ t₁ := hCbal
  -- ### the grid labelling
  obtain ⟨x, y, hx, hy, hxfib, hyfib, hcellfib⟩ := exists_grid_labelling_cells (W \ W') hhpos
  -- ### the reservoir
  set region : V → Finset V := fun u =>
    ((Finset.range h).biUnion (fun q => C (x u * h + q))) ∪
      ((Finset.range h).biUnion (fun p => C (p * h + y u))) with hregdef
  set S : V → Finset V := fun u => resLink F W' u ∩ region u with hSdef
  set R : Finset (Sym2 V) := (W \ W').biUnion (fun u => (S u).image (fun a => s(u, a)))
    with hRdef
  have hSW' : ∀ u, S u ⊆ W' := by
    intro u a ha
    exact (mem_resLink.1 (Finset.mem_inter.1 ha).1).1
  have hSF : ∀ u, ∀ a ∈ S u, s(u, a) ∈ F := by
    intro u a ha
    exact (mem_resLink.1 (Finset.mem_inter.1 ha).1).2
  have hmemR : ∀ e : Sym2 V, e ∈ R ↔ ∃ u ∈ W \ W', ∃ a ∈ S u, e = s(u, a) := by
    intro e
    simp only [hRdef, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
    · rintro ⟨u, hu, a, ha, rfl⟩; exact ⟨u, hu, a, ha, rfl⟩
  have hclass_mem : ∀ i < h * h, C i ⊆ W' := hCW'
  have hinner : ∀ v : V, v ∈ W' → edeg R v * h ≤ 2 * N + 2 * (h * h) := by
    intro v hvW'
    have hcls : ∀ u : V, u ∈ W \ W' → v ∈ S u →
        ∃ i < h * h, v ∈ C i := by
      intro u hu hv
      have hvr : v ∈ region u := (Finset.mem_inter.1 hv).2
      rcases Finset.mem_union.1 hvr with hrow | hcol
      · obtain ⟨q, hq, hvq⟩ := Finset.mem_biUnion.1 hrow
        exact ⟨x u * h + q, by
          have hxu := hx u hu
          have hq' := Finset.mem_range.1 hq
          calc x u * h + q < x u * h + h := by omega
            _ = (x u + 1) * h := by ring
            _ ≤ h * h := by
                have : x u + 1 ≤ h := by omega
                exact Nat.mul_le_mul_right _ this, hvq⟩
      · obtain ⟨p, hp, hvp⟩ := Finset.mem_biUnion.1 hcol
        exact ⟨p * h + y u, by
          have hyu := hy u hu
          have hp' := Finset.mem_range.1 hp
          calc p * h + y u < p * h + h := by omega
            _ = (p + 1) * h := by ring
            _ ≤ h * h := by
                have : p + 1 ≤ h := by omega
                exact Nat.mul_le_mul_right _ this, hvp⟩
    by_cases hex : ∃ i, i < h * h ∧ v ∈ C i
    · obtain ⟨i, hi, hvi⟩ := hex
      have huniq : ∀ j, j < h * h → v ∈ C j → j = i := by
        intro j hj hvj
        by_contra hne
        exact (Finset.disjoint_left.1 (hCdisj j hj i hi hne)) hvj hvi
      have hsubfib : (W \ W').filter (fun u => v ∈ S u) ⊆
          ((W \ W').filter (fun u => x u = i / h)) ∪ ((W \ W').filter (fun u => y u = i % h)) := by
        intro u hu
        obtain ⟨huD, hvS⟩ := Finset.mem_filter.1 hu
        have hvr : v ∈ region u := (Finset.mem_inter.1 hvS).2
        rcases Finset.mem_union.1 hvr with hrow | hcol
        · obtain ⟨q, hq, hvq⟩ := Finset.mem_biUnion.1 hrow
          have hq' := Finset.mem_range.1 hq
          have hxu := hx u huD
          have hlt : x u * h + q < h * h := by
            calc x u * h + q < x u * h + h := by omega
              _ = (x u + 1) * h := by ring
              _ ≤ h * h := Nat.mul_le_mul_right _ (by omega)
          have heq := huniq _ hlt hvq
          refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨huD, ?_⟩)
          have hdiv : i / h = x u := by
            rw [← heq, Nat.add_comm, Nat.add_mul_div_right _ _ hhpos,
              Nat.div_eq_of_lt hq', Nat.zero_add]
          omega
        · obtain ⟨p, hp, hvp⟩ := Finset.mem_biUnion.1 hcol
          have hp' := Finset.mem_range.1 hp
          have hyu := hy u huD
          have hlt : p * h + y u < h * h := by
            calc p * h + y u < p * h + h := by omega
              _ = (p + 1) * h := by ring
              _ ≤ h * h := Nat.mul_le_mul_right _ (by omega)
          have heq := huniq _ hlt hvp
          refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨huD, ?_⟩)
          have hmod : i % h = y u := by
            rw [← heq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hyu]
          omega
      have hedge : R.filter (fun e => v ∈ e) ⊆
          ((W \ W').filter (fun u => v ∈ S u)).image (fun u => s(u, v)) := by
        intro e he
        obtain ⟨heR, hve⟩ := Finset.mem_filter.1 he
        obtain ⟨u, hu, a, ha, rfl⟩ := (hmemR e).1 heR
        have huW' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
        have hav : a = v := by
          rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact absurd hvW' huW'
          · rfl
        subst hav
        exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, ha⟩, rfl⟩
      have hcard1 : edeg R v ≤ ((W \ W').filter (fun u => x u = i / h)).card
          + ((W \ W').filter (fun u => y u = i % h)).card := by
        calc edeg R v ≤ (((W \ W').filter (fun u => v ∈ S u)).image (fun u => s(u, v))).card :=
              Finset.card_le_card hedge
          _ ≤ ((W \ W').filter (fun u => v ∈ S u)).card := Finset.card_image_le
          _ ≤ (((W \ W').filter (fun u => x u = i / h)) ∪
                ((W \ W').filter (fun u => y u = i % h))).card := Finset.card_le_card hsubfib
          _ ≤ _ := Finset.card_union_le _ _
      -- the two fibres are small
      have hDN : (W \ W').card ≤ N := Finset.card_le_card Finset.sdiff_subset
      have hfib1 := hxfib (i / h)
      have hfib2 := hyfib (i % h)
      have hnat : edeg R v * h ≤ 2 * N + 2 * (h * h) := by
        have := Nat.mul_le_mul hcard1 (le_refl h)
        nlinarith only [hfib1, hfib2, hDN, this]
      exact hnat
    · -- `v` lies in no class of the design, so nothing is reserved at `v`
      have hempty : R.filter (fun e => v ∈ e) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro e he
        obtain ⟨heR, hve⟩ := Finset.mem_filter.1 he
        obtain ⟨u, hu, a, ha, rfl⟩ := (hmemR e).1 heR
        have huW' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
        have hav : a = v := by
          rcases Sym2.mem_iff.1 hve with rfl | rfl
          · exact absurd hvW' huW'
          · rfl
        subst hav
        exact hex (hcls u hu ha)
      have hz : edeg R v = 0 := by
        simp only [edeg, hempty, Finset.card_empty]
      simp [hz]
  have houter : ∀ v : V, v ∉ W' → edeg R v ≤ m := by
    intro v hvW'
    have hedge : R.filter (fun e => v ∈ e) ⊆ (S v).image (fun a => s(v, a)) := by
      intro e he
      obtain ⟨heR, hve⟩ := Finset.mem_filter.1 he
      obtain ⟨u, hu, a, ha, rfl⟩ := (hmemR e).1 heR
      have haW' : a ∈ W' := hSW' u ha
      have huv : u = v := by
        rcases Sym2.mem_iff.1 hve with rfl | rfl
        · rfl
        · exact absurd haW' hvW'
      subst huv
      exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    have hcard1 : edeg R v ≤ m := by
      calc edeg R v ≤ ((S v).image (fun a => s(v, a))).card := Finset.card_le_card hedge
        _ ≤ (S v).card := Finset.card_image_le
        _ ≤ m := Finset.card_le_card (hSW' v)
    exact hcard1
  -- the reservoir link of an outer vertex is exactly the designed set `S u`
  have hlink : ∀ u ∈ W \ W', resLink R W' u = resLink F W' u ∩ region u := by
    intro u hu
    have huW' : u ∉ W' := (Finset.mem_sdiff.1 hu).2
    ext v
    rw [mem_resLink]
    constructor
    · rintro ⟨hvW', hvR⟩
      obtain ⟨u', hu', a, ha, heq⟩ := (hmemR _).1 hvR
      have haW' : a ∈ W' := hSW' u' ha
      have hu'W' : u' ∉ W' := (Finset.mem_sdiff.1 hu').2
      rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; exact ha
      · exact absurd (h1 ▸ haW') huW'
    · intro hv
      exact ⟨hSW' u hv, (hmemR _).2 ⟨u, hu, v, hv, rfl⟩⟩
  refine ⟨R, C, x, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `R ⊆ F`
    intro e he
    obtain ⟨u, -, a, ha, rfl⟩ := (hmemR e).1 he
    exact hSF u a ha
  · -- `R` is crossing
    intro e he
    obtain ⟨u, hu, a, ha, rfl⟩ := (hmemR e).1 he
    exact ⟨u, hu, a, hSW' u ha, rfl⟩
  · -- ### (a) sparsity
    intro v
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
    have hNr : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have he0 : (0 : ℝ) ≤ (edeg R v : ℝ) := Nat.cast_nonneg _
    have hhN : ((h : ℝ) * (h : ℝ)) ≤ (N : ℝ) := by
      have hle : h * h ≤ N := by
        calc h * h ≤ Q := hhhQ
          _ ≤ N := by nlinarith only [hNbig, hQpos]
      exact_mod_cast hle
    by_cases hvW' : v ∈ W'
    · have hcast : (edeg R v : ℝ) * (h : ℝ) ≤ 2 * (N : ℝ) + 2 * ((h : ℝ) * (h : ℝ)) := by
        exact_mod_cast hinner v hvW'
      have h64 : (64 : ℝ) ≤ ε * (h : ℝ) := by nlinarith only [hεh, hK1r]
      have h1 : (edeg R v : ℝ) * 64 ≤ (edeg R v : ℝ) * (ε * (h : ℝ)) :=
        mul_le_mul_of_nonneg_left h64 he0
      have h2 := mul_le_mul_of_nonneg_left hcast hε.le
      have h3 := mul_le_mul_of_nonneg_left hhN hε.le
      nlinarith only [h1, h2, h3, mul_nonneg hε.le hNr]
    · have hKm : (K : ℝ) * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKW'
      have hmr : (edeg R v : ℝ) ≤ (m : ℝ) := by exact_mod_cast houter v hvW'
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have h2 := mul_le_mul_of_nonneg_left hKm hε.le
      have h3 := mul_le_mul_of_nonneg_right hεK hm0
      nlinarith only [hmr, h2, h3]
  · -- ### (b) apex abundance
    intro u hu v hv
    have hxu := hx u hu
    have hyv := hy v hv
    set i : ℕ := x u * h + y v with hidef
    have hi : i < h * h := by
      calc i < x u * h + h := by omega
        _ = (x u + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right _ (by omega)
    have hCi : C i ⊆ W' := hCW' i hi
    -- the class of the cell `(x u, y v)` is shared by `u` and `v`
    have hrow : C i ⊆ region u := by
      intro a ha
      exact Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨y v, Finset.mem_range.2 hyv, ha⟩)
    have hcol : C i ⊆ region v := by
      intro a ha
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨x u, Finset.mem_range.2 hxu, ha⟩)
    have hsub : (C i ∩ resLink F W' u) ∩ resLink F W' v ⊆ apexes R W' u v := by
      intro a ha
      obtain ⟨ha1, ha3⟩ := Finset.mem_inter.1 ha
      obtain ⟨hai, ha2⟩ := Finset.mem_inter.1 ha1
      refine mem_apexes.2 ⟨hCi hai, ?_, ?_⟩
      · exact (hmemR _).2 ⟨u, hu, a, Finset.mem_inter.2 ⟨ha2, hrow hai⟩, rfl⟩
      · exact (hmemR _).2 ⟨v, hv, a, Finset.mem_inter.2 ⟨ha3, hcol hai⟩, rfl⟩
    -- most of the class survives
    have hbalu : 4 * ((nonNbrs F W' u ∩ C i).card) ≤ t₁ :=
      hCbal' u (Finset.mem_sdiff.1 hu).1 i hi
    have hbalv : 4 * ((nonNbrs F W' v ∩ C i).card) ≤ t₁ :=
      hCbal' v (Finset.mem_sdiff.1 hv).1 i hi
    have hcover : C i ⊆ ((C i ∩ resLink F W' u) ∩ resLink F W' v)
        ∪ (nonNbrs F W' u ∩ C i) ∪ (nonNbrs F W' v ∩ C i) := by
      intro a ha
      by_cases h1 : a ∈ resLink F W' u
      · by_cases h2 : a ∈ resLink F W' v
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.2 ⟨Finset.mem_inter.2 ⟨ha, h1⟩, h2⟩))
        · exact Finset.mem_union_right _
            (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hCi ha, h2⟩, ha⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hCi ha, h1⟩, ha⟩))
    have hcard : t₁ ≤ ((C i ∩ resLink F W' u) ∩ resLink F W' v).card
        + (nonNbrs F W' u ∩ C i).card + (nonNbrs F W' v ∩ C i).card := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_union_le
        (((C i ∩ resLink F W' u) ∩ resLink F W' v) ∪ (nonNbrs F W' u ∩ C i))
        (nonNbrs F W' v ∩ C i)
      have h3 := Finset.card_union_le ((C i ∩ resLink F W' u) ∩ resLink F W' v)
        (nonNbrs F W' u ∩ C i)
      rw [hCcard i hi] at h1
      omega
    have hhalf : 2 * ((C i ∩ resLink F W' u) ∩ resLink F W' v).card ≥ t₁ := by omega
    have hfinal : 2 * (apexes R W' u v).card ≥ t₁ := by
      have := Finset.card_le_card hsub
      omega
    -- the numerical bound
    have hcastf : (t₁ : ℝ) ≤ 2 * ((apexes R W' u v).card : ℝ) := by exact_mod_cast hfinal
    have hNt' : (N : ℝ) ≤ 40 * (Q : ℝ) * (t₁ : ℝ) := by exact_mod_cast hNt₁
    have hQr : (Q : ℝ) = (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by
      simp only [hQdef]; push_cast; ring
    have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
    have hηdef : cleanEta ε K = 1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      rw [cleanEta, reservoirEta, ← hhdef]
      field_simp
      ring
    rw [hηdef]
    rw [hQr] at hNt'
    have hden : (0 : ℝ) < 160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
    have hmul : 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 * (t₁ : ℝ)
        ≤ 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 * (2 * ((apexes R W' u v).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcastf (by positivity)
    have key : 2 * (N : ℝ)
        ≤ ((apexes R W' u v).card : ℝ) * (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      nlinarith only [hNt', hmul]
    calc 2 * (1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (N : ℝ)
        = (2 * (N : ℝ)) / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
          field_simp
      _ ≤ ((apexes R W' u v).card : ℝ) := by rw [div_le_iff₀ hden]; exact key
  · -- ### the reservoir is sparse at the scale of `W'` too
    intro a ha
    have he0 : (0 : ℝ) ≤ (edeg R a : ℝ) := Nat.cast_nonneg _
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hcast : (edeg R a : ℝ) * (h : ℝ) ≤ 2 * (N : ℝ) + 2 * ((h : ℝ) * (h : ℝ)) := by
      exact_mod_cast hinner a ha
    have hNmN : N ≤ K ^ 2 * m := by rw [pow_two]; exact hW'K
    have hNm : (N : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) := by exact_mod_cast hNmN
    have hhmN : h * h ≤ K ^ 2 * m := by
      have h1 : h * h ≤ m := by nlinarith only [hhhQ, hmbig]
      have h2 : 1 * m ≤ K ^ 2 * m := Nat.mul_le_mul (by nlinarith only [hK1]) le_rfl
      omega
    have hhm : (h : ℝ) * (h : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) := by exact_mod_cast hhmN
    have hK2pos : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
    have hstep : (K : ℝ) ^ 2 * (64 * (edeg R a : ℝ)) ≤ (K : ℝ) ^ 2 * (4 * ε * (m : ℝ)) := by
      nlinarith only [mul_le_mul_of_nonneg_left hcast hε.le,
        mul_le_mul_of_nonneg_left hNm hε.le,
        mul_le_mul_of_nonneg_left hhm hε.le,
        mul_le_mul_of_nonneg_left hεh he0]
    have hfin := le_of_mul_le_mul_left hstep hK2pos
    linarith

  · -- ### the grid structure of the sharp design
    have ht₁t : t₁ ≤ t := by
      rw [ht₁def, htdef]
      exact Nat.div_le_div_right (by omega)
    refine
      { classSubset := ?_, classAvoid := ?_, classCardLe := ?_, classCardGe := ?_,
        classDisjoint := ?_, classBalanced := ?_, rowLt := hx, colLt := hy,
        rowFibre := hxfib, colFibre := hyfib, cellFibre := ?_, link := ?_,
        classPos := ht1, classVolume := hvolt, outerVolume := hNt,
        classCardEq := ?_, classBalancedSharp := ?_ }
    · intro i hi
      exact hCW' i (by rw [hhdef]; exact hi)
    · intro i hi
      exact hCavoid i (by rw [hhdef]; exact hi)
    · intro i hi
      rw [hCcard i (by rw [hhdef]; exact hi)]
      exact ht₁t
    · intro i hi
      rw [hCcard i (by rw [hhdef]; exact hi)]
      exact h3t
    · intro i hi j hj hij
      exact hCdisj i (by rw [hhdef]; exact hi) j (by rw [hhdef]; exact hj) hij
    · intro v hv i hi
      exact le_trans (hCbal' v hv i (by rw [hhdef]; exact hi)) ht₁t
    · intro p q
      simpa [← hhdef] using hcellfib p q
    · intro u hu
      rw [hlink u hu]
      rfl
    · intro i hi j hj
      rw [hCcard i (by rw [hhdef]; exact hi), hCcard j (by rw [hhdef]; exact hj)]
    · intro v hv i hi
      rw [hCcard i (by rw [hhdef]; exact hi)]
      exact hCbal' v hv i (by rw [hhdef]; exact hi)

end BKLO
