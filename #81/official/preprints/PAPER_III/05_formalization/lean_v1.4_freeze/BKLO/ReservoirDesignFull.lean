/-
# The grid design, exported with its cells **and its behaviour at the protected level**.

`BKLO.IsGridReservoir` (`BKLO/ReservoirDesignStructured.lean`) exports the row and the column
fibres of the grid labelling, and nothing about the protected level `W''`.  Both gaps are fatal
for the pairing step of §10, and `BKLO.not_gridPairingResidual` (`BKLO/GridPairingRefutation.lean`)
turns the second one into an outright refutation of the residual as stated: if `W''` may be the
designed region of an outer vertex, that vertex has no admissible pair at all.

This file repeats the construction of `BKLO.exists_reservoir_structured` and exports two more
properties of it, in the structure `BKLO.IsGridFullReservoir`:

* `cellFibre` — a cell of the labelling holds at most `|D|/h² + 1` outer vertices.  All the outer
  vertices of a cell share one designed region of `(2h-1)t` vertices and have to pair their links
  inside it with pairwise distinct edges, so this is exactly the bound the pairing needs;
  `BKLO.exists_grid_labelling_cells` supplies it.
* `protectedBalanced` — the protected level takes up at most a quarter of every class.  This comes
  for free from `BKLO.exists_balanced_classes` by adding `W''` to the bad sets: the room is there
  because `K|W''| ≤ |W'|` and `8 ≤ εK`.

Nothing in `BKLO/ReservoirDesignStructured.lean` is changed; the statement here is strictly
stronger than the one there.

Everything here is `sorry`-free.
-/
import BKLO.GridLabellingCells
import BKLO.ReservoirDesignStructured

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- **A grid reservoir with small cells, avoiding the protected level.**  `BKLO.IsGridReservoir`
together with the size of the cells of the labelling and the balance of the protected level
against the classes. -/
structure IsGridFullReservoir (ε : ℝ) (K : ℕ) (W W' W'' : Finset V) (F R : Finset (Sym2 V))
    (C : ℕ → Finset V) (x y : V → ℕ) extends IsGridReservoir ε K W W' F R C x y where
  /-- the cells are small: at most `|D|/h² + 1` outer vertices share a designed region. -/
  cellFibre : ∀ p q : ℕ, (((W \ W').filter (fun u => x u = p ∧ y u = q)).card)
    * (gridSize ε K * gridSize ε K) ≤ (W \ W').card + gridSize ε K * gridSize ε K
  /-- the protected level occupies at most a quarter of each class. -/
  protectedBalanced : ∀ i < gridSize ε K * gridSize ε K,
    4 * ((W'' ∩ C i).card) ≤ gridClassSize ε K W'.card

/-! ### The construction -/

set_option maxHeartbeats 2000000 in
/-- **The grid design, with its structure.**  The reservoir of
`BKLO.exists_reservoir_sparse_apexAbundant`, exported together with the class family, the grid
labelling, the identity between the reservoir links and the designed regions, **and the size of
the cells of the labelling**. -/
theorem exists_reservoir_full_structured
    {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hKε : (8 : ℝ) / ε ≤ (K : ℝ))
    {W W' W'' : Finset V} {F : Finset (Sym2 V)}
    (hKW' : K * W'.card ≤ W.card) (hW'K : W.card ≤ K * K * W'.card)
    (hKW'' : K * W''.card ≤ W'.card)
    (hres : ∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ))
    (hN : reservoirThreshold ε K ≤ W.card) :
    ∃ (R : Finset (Sym2 V)) (C : ℕ → Finset V) (x y : V → ℕ),
      R ⊆ F ∧ IsCrossing W W' R ∧
      (∀ v : V, (edeg R v : ℝ) ≤ ε / 8 * (W.card : ℝ)) ∧
      (∀ u ∈ W \ W', ∀ v ∈ W \ W',
        2 * reservoirEta ε K * (W.card : ℝ) ≤ ((apexes R W' u v).card : ℝ)) ∧
      (∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ)) ∧
      IsGridFullReservoir ε K W W' W'' F R C x y := by
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
  have hW''m : ((W''.card : ℝ)) * 8 ≤ ε * (m : ℝ) := by
    have h1 : ((K : ℝ)) * (W''.card : ℝ) ≤ (m : ℝ) := by
      have : ((K * W''.card : ℕ) : ℝ) ≤ ((W'.card : ℕ) : ℝ) := by exact_mod_cast hKW''
      push_cast at this
      simpa [hmdef] using this
    have h2 : (0 : ℝ) ≤ (W''.card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hεK, h1, h2, hε.le]
  have hTcard : ∀ v ∈ W, 10 * ((nonNbrs F W' v ∪ W'').card) ≤ m := by
    intro v hv
    have hsub : resLink F W' v ⊆ W' := fun a ha => (mem_resLink.1 ha).1
    have hcard : (nonNbrs F W' v).card = m - (resLink F W' v).card := by
      simpa [nonNbrs, hmdef] using Finset.card_sdiff_of_subset hsub
    have hle : (resLink F W' v).card ≤ m := Finset.card_le_card hsub
    have hR := hres v hv
    have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hun : (nonNbrs F W' v ∪ W'').card ≤ (nonNbrs F W' v).card + W''.card :=
      Finset.card_union_le _ _
    have hnon : (10 : ℝ) * ((nonNbrs F W' v).card : ℝ) ≤ (m : ℝ) - 5 / 2 * ε * (m : ℝ) := by
      rw [hcard]
      have hcast : (((m - (resLink F W' v).card : ℕ)) : ℝ)
          = (m : ℝ) - ((resLink F W' v).card : ℝ) := by
        push_cast [Nat.cast_sub hle]; ring
      rw [hcast]
      linarith only [hR, hε]
    have hunr : (((nonNbrs F W' v ∪ W'').card : ℕ) : ℝ)
        ≤ ((nonNbrs F W' v).card : ℝ) + (W''.card : ℝ) := by exact_mod_cast hun
    have : (10 : ℝ) * (((nonNbrs F W' v ∪ W'').card : ℕ) : ℝ) ≤ (m : ℝ) := by
      linarith only [hnon, hunr, hW''m, hε]
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
    exists_balanced_classes (W := W) (P := W') (T := fun v => nonNbrs F W' v ∪ W'') (g := h * h)
      (t := t) hTcard hvolt ht1 hsmall
  have hCbal' : ∀ v ∈ W, ∀ i < h * h, 4 * ((nonNbrs F W' v ∩ C i).card) ≤ t := by
    intro v hv i hi
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_)) (hCbal v hv i hi)
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
    exact Finset.mem_inter.2 ⟨Finset.mem_union_left _ ha1, ha2⟩
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
      hCbal' u (Finset.mem_sdiff.1 hu).1 i hi
    have hbalv : 4 * ((nonNbrs F W' v ∩ C i).card) ≤ t :=
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
    linarith

  · -- ### the grid structure of the design, with the cells
    refine ⟨⟨hCP, hCcard, hCdisj, ?_, hx, hy, hxfib, hyfib, ?_, ht1, ?_, ?_⟩, ?_, ?_⟩
    · intro v hv i hi; exact hCbal' v hv i hi
    · intro u hu
      rw [hlink u hu]
      rfl
    · exact hvolt
    · exact hNt
    · intro p q
      simpa [← hhdef] using hcellfib p q
    · -- the protected level occupies at most a quarter of each class
      intro i hi
      obtain ⟨v₀, hv₀⟩ : W.Nonempty := by
        rw [← Finset.card_pos, ← hNdef]
        nlinarith only [hNbig, hQpos]
      refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
        (hCbal v₀ hv₀ i (by rw [hhdef]; exact hi))
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
      exact Finset.mem_inter.2 ⟨Finset.mem_union_right _ ha1, ha2⟩

end BKLO
