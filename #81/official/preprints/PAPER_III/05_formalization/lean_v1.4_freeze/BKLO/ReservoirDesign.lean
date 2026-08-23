/-
# A sparse, apex-abundant reservoir: clauses (a) and (b) of `BKLO.ReservoirClauseR`, proved.

The reservoir clause asks for a crossing `R ⊆ F` which is

* **(a) vertex-sparse** — `edeg R v ≤ (ε/8)|W|` for every vertex, and
* **(b) apex-abundant** — any two outer vertices `u, v ∈ W \ W'` have at least `2η|W|` reserved
  common neighbours inside `W'`,

and (c) has all its perturbed link systems coverable.  This file proves (a) and (b), with an
explicit `η = η(ε, K) > 0` and an explicit size threshold, by an explicit construction — no
appeal to (c), to the vortex, or to the main theorem.  It proves one bound more than (a) asks:
the reservoir is also sparse *at the scale of `W'`*, `edeg R a ≤ (ε/16)|W'|` for `a ∈ W'`.  That
is the bound clause (c) needs and (a) does not supply: a link cover of a perturbed link system
spends one edge of `W'` at `a` for each outer vertex whose link contains `a`, and its damage
budget at `a` is `(ε/8)|W'|`, so a reservoir that is merely `(ε/8)|W|`-sparse is already
over budget by a factor `K`.  The reservoir built here is therefore load-feasible for (c).

The construction is a **grid design**.  Fix `h ≈ 64K²/ε`.  Inside `W'` choose `h²` pairwise
disjoint *balanced classes* `C_{ph+q}` of a common size `t ≈ |W'|/(10h²)`, in each of which every
vertex of `W` has at most a quarter of its non-neighbours (`BKLO.exists_balanced_classes`); label
each outer vertex `u` by a cell `(x u, y u)` of the grid so that all row and column fibres are
small (`BKLO.exists_grid_labelling`); and reserve for `u` its `F`-neighbours inside the classes of
its row and of its column.

* Sparsity: a vertex of the class `C_{ph+q}` is reserved only for the outer vertices with
  `x u = p` or `y u = q`, of which there are at most `2(|W|/h + h)`; since `|W| ≤ K²|W'|` and
  `h ≥ 64K²/ε` this is at most `(ε/16)|W'| ≤ (ε/8)|W|`.  An outer vertex reserves at most
  `|W'| ≤ |W|/K ≤ (ε/8)|W|` vertices, because `K ≥ 8/ε`.
* Abundance: the cell `(x u, y v)` lies in the row of `u` and in the column of `v`, so `u` and `v`
  share the whole class `C_{x u·h + y v}` bar their non-neighbours, at least `t/2 ≥ 2η|W|`
  vertices, with `η = 1/(80K²h²)`.

So the residual `BKLO.ReservoirPairingResidual` is missing only its pairing clause: reservoirs
satisfying its first two demands — and the load bound that its third demand needs — exist, in
every configuration of the clause that is large enough.

Everything here is `sorry`-free.
-/import BKLO.BalancedClasses
import BKLO.GridLabelling
import BKLO.ReservoirRepaired

open Finset

namespace BKLO

/-! ### The parameters of the design -/

/-- The side of the grid of classes: `h ≈ 64K²/ε`.  The factor `K²` is what makes the reservoir
sparse *at the scale of `W'`*, which is the scale at which a link cover must pay for it. -/
noncomputable def gridSize (ε : ℝ) (K : ℕ) : ℕ := ⌈(64 : ℝ) * (K : ℝ) ^ 2 / ε⌉₊ + 1

theorem gridSize_pos (ε : ℝ) (K : ℕ) : 0 < gridSize ε K := Nat.succ_pos _

theorem le_gridSize (ε : ℝ) (K : ℕ) : (64 : ℝ) * (K : ℝ) ^ 2 / ε ≤ (gridSize ε K : ℝ) := by
  have h := Nat.le_ceil ((64 : ℝ) * (K : ℝ) ^ 2 / ε)
  have h2 : ((⌈(64 : ℝ) * (K : ℝ) ^ 2 / ε⌉₊ : ℕ) : ℝ) ≤ (gridSize ε K : ℝ) := by
    unfold gridSize
    push_cast
    linarith only []
  linarith only [h, h2]

/-- The perturbation scale delivered by the grid design. -/
noncomputable def reservoirEta (ε : ℝ) (K : ℕ) : ℝ :=
  1 / (80 * (K : ℝ) ^ 2 * (gridSize ε K : ℝ) ^ 2)

theorem reservoirEta_pos {ε : ℝ} {K : ℕ} (hK : 0 < K) : 0 < reservoirEta ε K := by
  have h1 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < (gridSize ε K : ℝ) := by exact_mod_cast gridSize_pos ε K
  unfold reservoirEta
  positivity

/-- The size threshold above which the grid design runs. -/
noncomputable def reservoirThreshold (ε : ℝ) (K : ℕ) : ℕ :=
  10 ^ 9 * (K * K * gridSize ε K * gridSize ε K) ^ 2

/-! ### The union bound -/

/-- A convenient sufficient condition for the union bound of `BKLO.exists_balanced_classes`:
`(10/9)^s ≥ s/9` by Bernoulli, so `n < s²/81` already forces `n(9/10)^{2s} < 1`. -/
theorem union_bound_of_sq {n s : ℕ} (h : 81 * n < s * s) :
    (n : ℝ) * (9 / 10 : ℝ) ^ (2 * s) < 1 := by
  have hb := one_add_mul_le_pow (a := (1 : ℝ) / 9) (by norm_num) s
  have hpow : ((1 : ℝ) + 1 / 9) ^ s = (10 / 9 : ℝ) ^ s := by norm_num
  rw [hpow] at hb
  have hA : ((s : ℝ) / 9) ≤ (10 / 9 : ℝ) ^ s := by linarith only [hb]
  have hApos : (0 : ℝ) < (10 / 9 : ℝ) ^ s := by positivity
  have hBpos : (0 : ℝ) < (9 / 10 : ℝ) ^ s := by positivity
  have hs0 : (0 : ℝ) ≤ (s : ℝ) / 9 := by positivity
  have hn : (n : ℝ) < ((s : ℝ) / 9) ^ 2 := by
    have hc : (81 : ℝ) * (n : ℝ) < (s : ℝ) * (s : ℝ) := by exact_mod_cast h
    linarith only [hc]
  have hkey : (n : ℝ) < ((10 / 9 : ℝ) ^ s) ^ 2 := by nlinarith only [hA, hs0, hn]
  have hid : ((9 / 10 : ℝ) ^ s) * ((10 / 9 : ℝ) ^ s) = 1 := by
    rw [← mul_pow]; norm_num
  have hsplit : (9 / 10 : ℝ) ^ (2 * s) = ((9 / 10 : ℝ) ^ s) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  have hprod : ((10 / 9 : ℝ) ^ s) ^ 2 * ((9 / 10 : ℝ) ^ s) ^ 2 = 1 := by
    rw [← mul_pow, mul_comm, hid, one_pow]
  have hB2 : (0 : ℝ) < ((9 / 10 : ℝ) ^ s) ^ 2 := by positivity
  rw [hsplit]
  calc (n : ℝ) * ((9 / 10 : ℝ) ^ s) ^ 2
      < ((10 / 9 : ℝ) ^ s) ^ 2 * ((9 / 10 : ℝ) ^ s) ^ 2 := mul_lt_mul_of_pos_right hkey hB2
    _ = 1 := hprod

/-! ### The construction -/

variable {V : Type*} [DecidableEq V]

set_option maxHeartbeats 2000000 in
/-- **Clauses (a) and (b) of the reservoir clause, proved.**  In every configuration of
`BKLO.ReservoirClauseR` whose scale exceeds `BKLO.reservoirThreshold ε K`, there is a crossing
reservoir inside `F` that is vertex-sparse and apex-abundant at the scale
`BKLO.reservoirEta ε K > 0` — and, beyond what clause (a) asks, sparse at the scale of `W'`:
every `a ∈ W'` carries at most `(ε/16)|W'|` reserved edges.  That last bound is exactly the
budget a link cover has at `a`, so the reservoir produced here is *load-feasible* for clause
(c) as well. -/
theorem exists_reservoir_sparse_apexAbundant
    {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
    {W W' : Finset V} {F : Finset (Sym2 V)}
    (hKW' : K * W'.card ≤ W.card) (hW'K : W.card ≤ K * K * W'.card)
    (hres : ∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ))
    (hN : reservoirThreshold ε K ≤ W.card) :
    ∃ R : Finset (Sym2 V), R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * reservoirEta ε K * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) := by
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
    · linarith only [h2]
    · exact ne_of_gt hε
  have hεK : (8 : ℝ) ≤ ε * (K : ℝ) := by
    have h2 : (8 : ℝ) / ε * ε ≤ (K : ℝ) * ε := mul_le_mul_of_nonneg_right hKε hε.le
    rw [div_mul_cancel₀] at h2
    · linarith only [h2]
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
    calc 10 * h * h ≤ 10 ^ 9 * Q := by linarith only [hhhQ, hQpos]
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
      linarith only [h1, h2]
    have := key (10 * h * h) (by positivity)
    rw [← htdef] at this
    exact this
  have hNt : N ≤ 20 * Q * t := by
    calc N ≤ K * K * m := hW'K
      _ ≤ K * K * (10 * h * h * t + 10 * h * h) := Nat.mul_le_mul le_rfl hmt
      _ ≤ 20 * Q * t := by
          simp only [hQdef]
          linarith only [Nat.mul_le_mul (le_refl (K * K * h * h * 10)) ht1]
  -- ### the classes
  have hTcard : ∀ v ∈ W, 10 * (nonNbrs F W' v).card ≤ m := by
    intro v hv
    have hsub : resLink F W' v ⊆ W' := fun a ha => (mem_resLink.1 ha).1
    have hcard : (nonNbrs F W' v).card = m - (resLink F W' v).card := by
      simpa [nonNbrs, hmdef] using Finset.card_sdiff_of_subset hsub
    have hle : (resLink F W' v).card ≤ m := Finset.card_le_card hsub
    have hR := hres v hv
    have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have : (10 : ℝ) * ((nonNbrs F W' v).card : ℝ) ≤ (m : ℝ) := by
      rw [hcard]
      have hcast : (((m - (resLink F W' v).card : ℕ)) : ℝ)
          = (m : ℝ) - ((resLink F W' v).card : ℝ) := by
        push_cast [Nat.cast_sub hle]; ring
      rw [hcast]
      nlinarith only [hR, hε]
    exact_mod_cast this
  have hsmall : (W.card : ℝ) * (9 / 10 : ℝ) ^ (2 * (t / 32)) < 1 := by
    refine union_bound_of_sq ?_
    rw [← hNdef]
    set s : ℕ := t / 32 with hsdef
    have hts : t ≤ 32 * s + 31 := by rw [hsdef]; omega
    have h1 : N ≤ 640 * Q * s + 620 * Q := by
      calc N ≤ 20 * Q * t := hNt
        _ ≤ 20 * Q * (32 * s + 31) := Nat.mul_le_mul le_rfl hts
        _ = 640 * Q * s + 620 * Q := by ring
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · exfalso
        rw [hs0] at h1
        nlinarith only [hNbig, h1, hQpos]
      · exact hs0
    have hA : N ≤ 1280 * Q * s := by nlinarith only [h1, hs1, hQpos]
    have hsq : N * N ≤ (1280 * Q * s) * (1280 * Q * s) := Nat.mul_le_mul hA hA
    have hNN : 10 ^ 9 * (Q * Q) * N ≤ N * N := Nat.mul_le_mul_right N hNbig
    have hQQ : 0 < Q * Q := by positivity
    have hstep : (Q * Q) * (10 ^ 9 * N) ≤ (Q * Q) * (1638400 * (s * s)) := by
      linarith only [hsq, hNN]
    have hfin : 10 ^ 9 * N ≤ 1638400 * (s * s) := Nat.le_of_mul_le_mul_left hstep hQQ
    have hNpos : 0 < N := by linarith only [hNbig, hQQ]
    linarith only [hfin, hNpos]
  obtain ⟨C, hCP, hCcard, hCdisj, hCbal⟩ :=
    exists_balanced_classes (W := W) (P := W') (T := fun v => nonNbrs F W' v) (g := h * h)
      (t := t) hTcard hvolt ht1 hsmall
  -- ### the grid labelling
  obtain ⟨x, y, hx, hy, hxfib, hyfib⟩ := exists_grid_labelling (W \ W') hhpos
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
  have hclass_mem : ∀ i < h * h, C i ⊆ W' := hCP
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
        nlinarith [hfib1, hfib2, hDN]
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
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
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
      linarith only [h1, h2, h3, mul_nonneg hε.le hNr]
    · have hKm : (K : ℝ) * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKW'
      have hmr : (edeg R v : ℝ) ≤ (m : ℝ) := by exact_mod_cast houter v hvW'
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have h2 := mul_le_mul_of_nonneg_left hKm hε.le
      have h3 := mul_le_mul_of_nonneg_right hεK hm0
      linarith only [hmr, h2, h3]
  · -- ### (b) apex abundance
    intro u hu v hv
    have hxu := hx u hu
    have hyv := hy v hv
    set i : ℕ := x u * h + y v with hidef
    have hi : i < h * h := by
      calc i < x u * h + h := by omega
        _ = (x u + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right _ (by omega)
    have hCi : C i ⊆ W' := hCP i hi
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
    have hbalu : 4 * ((nonNbrs F W' u ∩ C i).card) ≤ t :=
      hCbal u (Finset.mem_sdiff.1 hu).1 i hi
    have hbalv : 4 * ((nonNbrs F W' v ∩ C i).card) ≤ t :=
      hCbal v (Finset.mem_sdiff.1 hv).1 i hi
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
    have hcard : t ≤ ((C i ∩ resLink F W' u) ∩ resLink F W' v).card
        + (nonNbrs F W' u ∩ C i).card + (nonNbrs F W' v ∩ C i).card := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_union_le
        (((C i ∩ resLink F W' u) ∩ resLink F W' v) ∪ (nonNbrs F W' u ∩ C i))
        (nonNbrs F W' v ∩ C i)
      have h3 := Finset.card_union_le ((C i ∩ resLink F W' u) ∩ resLink F W' v)
        (nonNbrs F W' u ∩ C i)
      rw [hCcard i hi] at h1
      omega
    have hhalf : 2 * ((C i ∩ resLink F W' u) ∩ resLink F W' v).card ≥ t := by omega
    have hfinal : 2 * (apexes R W' u v).card ≥ t := by
      have := Finset.card_le_card hsub
      omega
    -- the numerical bound
    have hcastf : (t : ℝ) ≤ 2 * ((apexes R W' u v).card : ℝ) := by exact_mod_cast hfinal
    have hNt' : (N : ℝ) ≤ 20 * (Q : ℝ) * (t : ℝ) := by exact_mod_cast hNt
    have hQr : (Q : ℝ) = (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by
      simp only [hQdef]; push_cast; ring
    have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
    have hηdef : reservoirEta ε K = 1 / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      simp only [reservoirEta, hhdef]
    rw [hηdef]
    rw [hQr] at hNt'
    have hden : (0 : ℝ) < 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
    have hmul : 40 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 * (t : ℝ)
        ≤ 40 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 * (2 * ((apexes R W' u v).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcastf (by positivity)
    have key : 2 * (N : ℝ)
        ≤ ((apexes R W' u v).card : ℝ) * (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
      linarith only [hNt', hmul]
    calc 2 * (1 / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (N : ℝ)
        = (2 * (N : ℝ)) / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
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
      have h1 : h * h ≤ m := by linarith only [hhhQ, hmbig]
      have h2 : 1 * m ≤ K ^ 2 * m := Nat.mul_le_mul (by nlinarith only [hK1]) le_rfl
      omega
    have hhm : (h : ℝ) * (h : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) := by exact_mod_cast hhmN
    have hK2pos : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
    have hstep : (K : ℝ) ^ 2 * (64 * (edeg R a : ℝ)) ≤ (K : ℝ) ^ 2 * (4 * ε * (m : ℝ)) := by
      linarith only [mul_le_mul_of_nonneg_left hcast hε.le,
        mul_le_mul_of_nonneg_left hNm hε.le,
        mul_le_mul_of_nonneg_left hhm hε.le,
        mul_le_mul_of_nonneg_left hεh he0]
    have hfin := le_of_mul_le_mul_left hstep hK2pos
    linarith only [hfin]

end BKLO
