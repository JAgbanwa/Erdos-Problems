/-
# The links of the two-sided design meet Dirac's threshold with a margin.

At the two-sided grid design (`BKLO.IsGridTwoSidedReservoir`,
`BKLO/ReservoirDesignTwoSided.lean`) the reserved link of an outer vertex `u` meets each of the
`2h - 1` classes of its region in exactly `c` places, and `c` is at least three quarters of the
common class size `q`.  Two counts follow, exactly as at the sharp design:

* `BKLO.card_resLink_twoSided` — the link has exactly `(2h-1)c` vertices;
* `BKLO.card_nonNbrs_inter_gridRegion_twoSided_le` — every vertex of `W` misses at most a quarter
  of the region, hence at most `(2h-1)q/4` of the link.

Since `3q ≤ 4c`, the second is at most a third of the first, so every vertex of the link has
`|link|·2/3 ≥ |link|/2 + |link|/6` neighbours inside it: Dirac's threshold with a margin
proportional to the link.  The margin survives both the adversary's perturbation of the link and
the deletion of the edges already used by a sweep, which is
`BKLO.twoSided_perturbed_link_dirac_avoiding`, and — given Dirac's theorem — produces one pairing
of each perturbed link avoiding the used edges
(`BKLO.exists_pairing_of_twoSided_link_avoiding`).

The budget of the sweep is the same arithmetic as at the sharp design
(`BKLO/SharpSweepBudget.lean`), transported to the units of the two-sided design.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesignTwoSided

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {q c : ℕ}

/-! ### The two sizes of a two-sided design -/

/-- **The two sizes of a two-sided design**: the common class size `q` and the common number `c` of
places the reserved links keep in each class of their region, with `3q ≤ 4c ≤ 4q`. -/
theorem IsGridTwoSidedReservoir.exists_sizes
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) :
    ∃ q c : ℕ, (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) ∧
      (∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
        (resLink R W' u ∩ C i).card = c) ∧ 3 * q ≤ 4 * c ∧ c ≤ q := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hqcard : ∀ i < h * h, (C i).card = (C 0).card := fun i hi =>
    hgrid.classCardEq i hi 0 hhh
  by_cases hD : (W \ W').Nonempty
  · obtain ⟨u₀, hu₀⟩ := hD
    have hx₀ : x u₀ < h := hgrid.rowLt u₀ hu₀
    have hy₀ : y u₀ < h := hgrid.colLt u₀ hu₀
    set i₀ : ℕ := x u₀ * h + y u₀ with hi₀def
    have hi₀ : i₀ ∈ gridIdx h (x u₀) (y u₀) := mem_gridIdx.2 (Or.inl ⟨y u₀, hy₀, rfl⟩)
    refine ⟨(C 0).card, (resLink R W' u₀ ∩ C i₀).card, hqcard, ?_, ?_, ?_⟩
    · intro u hu i hi
      exact (hgrid.linkClassEq u hu i hi u₀ hu₀ i₀ hi₀)
    · have h1 := hgrid.linkClassGe u₀ hu₀ i₀ hi₀
      rwa [hqcard i₀ (gridIdx_lt hx₀ hy₀ hi₀)] at h1
    · have h1 : (resLink R W' u₀ ∩ C i₀).card ≤ (C i₀).card :=
        Finset.card_le_card Finset.inter_subset_right
      rwa [hqcard i₀ (gridIdx_lt hx₀ hy₀ hi₀)] at h1
  · refine ⟨(C 0).card, (C 0).card, hqcard, ?_, by omega, le_rfl⟩
    intro u hu
    exact absurd ⟨u, hu⟩ hD

/-! ### The two counts -/

/-- Every vertex of `W` misses at most a quarter of the region of an outer vertex. -/
theorem card_nonNbrs_inter_gridRegion_twoSided_le
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {a : V} (ha : a ∈ W) :
    4 * ((nonNbrs F W' a ∩ gridRegion (gridSize ε K) C (x u) (y u)).card)
      ≤ (2 * gridSize ε K - 1) * q := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  have hxu : x u < h := hgrid.rowLt u hu
  have hyu : y u < h := hgrid.colLt u hu
  set I : Finset ℕ := gridIdx h (x u) (y u) with hIdef
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j) := fun i hi j hj hij =>
    hgrid.region_disjoint hu hi hj hij
  rw [gridRegion_eq_biUnion, ← hIdef, card_inter_biUnion_eq_sum _ hdisj, Finset.mul_sum]
  calc ∑ i ∈ I, 4 * ((nonNbrs F W' a ∩ C i).card)
      ≤ ∑ _i ∈ I, q := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hgrid.classBalancedSharp a ha i (gridIdx_lt hxu hyu hi) |>.trans_eq
          (hq i (gridIdx_lt hxu hyu hi))
    _ = I.card * q := by rw [Finset.sum_const, smul_eq_mul]
    _ = (2 * h - 1) * q := by rw [card_gridIdx hxu hyu]

/-- The reserved link of an outer vertex of a two-sided design has exactly `(2h-1)c` vertices. -/
theorem card_resLink_twoSided
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hc : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (resLink R W' u ∩ C i).card = c)
    {u : V} (hu : u ∈ W \ W') :
    (resLink R W' u).card = (2 * gridSize ε K - 1) * c :=
  hgrid.card_resLink hu (hc u hu)

/-! ### Dirac's threshold, with the perturbation and the used edges -/

/-- **Dirac's hypothesis for the perturbed link, after the used edges are deleted.**  At a
two-sided grid design, an admissible perturbation `X` of the reserved link of an outer vertex still
has every vertex joined to at least half of it by edges outside a set `U` of small degree. -/
theorem twoSided_perturbed_link_dirac_avoiding
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    (hc : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (resLink R W' u ∩ C i).card = c)
    (hqc : 3 * q ≤ 4 * c)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W')
    {n m : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    {U : Finset (Sym2 V)} (hU : ∀ a ∈ X, (resLink U X a).card ≤ m)
    (hmargin : 12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c)
    {a : V} (ha : a ∈ X) :
    X.card ≤ 2 * edeg ((F \ U) ∩ cliqueEdges X) a := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set S : Finset V := resLink R W' u with hSdef
  have haW : a ∈ W := hW'W (hXW' ha)
  have hSW' : S ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  have hSreg : S ⊆ gridRegion h C (x u) (y u) := fun z hz =>
    (Finset.mem_inter.1 (hgrid.linkSubset u hu hz)).2
  have hnd' : ∀ e ∈ F \ U, ¬ e.IsDiag := fun e he => hnd e (Finset.mem_sdiff.1 he).1
  -- the degree inside the perturbed link, after the deletion
  have hdeg : edeg ((F \ U) ∩ cliqueEdges X) a = (resLink F X a \ resLink U X a).card := by
    rw [edeg_inter_cliqueEdges_eq_card_resLink ha hnd', resLink_sdiff]
  have hdeg' : (X \ nonNbrs F W' a).card ≤ (resLink F X a \ resLink U X a).card + m := by
    have h1 : (resLink F X a).card = (X \ nonNbrs F W' a).card := by
      rw [resLink_eq_sdiff_nonNbrs hXW' a]
    have h2 : (resLink F X a \ resLink U X a).card + (resLink F X a ∩ resLink U X a).card
        = (resLink F X a).card := Finset.card_sdiff_add_card_inter _ _
    have h2' : (resLink F X a ∩ resLink U X a).card ≤ (resLink U X a).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h3 := hU a ha
    omega
  have hsplit : (X \ nonNbrs F W' a).card + (nonNbrs F W' a ∩ X).card = X.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter _ _
  have hsub : nonNbrs F W' a ∩ X ⊆ (nonNbrs F W' a ∩ S) ∪ (X \ S) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz1, hzS⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hz2, hzS⟩)
  have hnon : (nonNbrs F W' a ∩ X).card ≤ (nonNbrs F W' a ∩ S).card + (X \ S).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- the two counts at the two-sided design
  have hupper : 4 * ((nonNbrs F W' a ∩ S).card) ≤ (2 * h - 1) * q := by
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      (card_nonNbrs_inter_gridRegion_twoSided_le hgrid hq hu haW)
    exact Finset.inter_subset_inter_left hSreg
  have hSc : S.card = (2 * h - 1) * c := card_resLink_twoSided hgrid hc hu
  have hqc' : 3 * ((2 * h - 1) * q) ≤ 4 * ((2 * h - 1) * c) := by
    calc 3 * ((2 * h - 1) * q) = (2 * h - 1) * (3 * q) := by ring
      _ ≤ (2 * h - 1) * (4 * c) := Nat.mul_le_mul_left _ hqc
      _ = 4 * ((2 * h - 1) * c) := by ring
  -- the link is not much larger than its perturbation
  have hSX : S.card ≤ X.card + n := by
    have h1 : S.card ≤ (S ∩ X).card + (S \ X).card := by
      rw [Finset.card_inter_add_card_sdiff]
    have h2 : (S ∩ X).card ≤ X.card := Finset.card_le_card Finset.inter_subset_right
    omega
  rw [hdeg]
  omega

section Dirac

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Every link of a two-sided design is paired up avoiding a small used-edge set.**  The step of
a sweep: given the pairs already placed (an edge set `U` of degree at most `m` inside the link),
the next link is still paired up, by edges of `F` that `U` does not contain. -/
theorem exists_pairing_of_twoSided_link_avoiding (hDirac : PerfectMatchingDirac)
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q c : ℕ}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    (hc : ∀ u ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x u) (y u),
      (resLink R W' u ∩ C i).card = c)
    (hqc : 3 * q ≤ 4 * c)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W') (hXeven : Even X.card)
    {n m : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    {U : Finset (Sym2 V)} (hU : ∀ a ∈ X, (resLink U X a).card ≤ m)
    (hmargin : 12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c) :
    ∃ g : V → V, (∀ a ∈ X, g a ∈ X) ∧ (∀ a ∈ X, g (g a) = a) ∧ (∀ a ∈ X, g a ≠ a) ∧
      ∀ a ∈ X, s(a, g a) ∈ F ∧ s(a, g a) ∉ U := by
  obtain ⟨g, h1, h2, h3, h4⟩ :=
    exists_pairing_of_dirac hDirac hXeven
      (fun _ ha => twoSided_perturbed_link_dirac_avoiding hgrid hnd hW'W hq hc hqc hu hXW'
        hadd hdel hU hmargin ha)
  exact ⟨g, h1, h2, h3, fun a ha => ⟨(Finset.mem_sdiff.1 (h4 a ha)).1,
    (Finset.mem_sdiff.1 (h4 a ha)).2⟩⟩

end Dirac

/-! ### The budget of a sweep, in the units of the two-sided design -/

/-- **The two budgets of a sweep at a two-sided design.**  With `t` the nominal class size, an
adversarial perturbation of size `n ≤ t/4` and an already-used edge set of degree `m ≤ h t / 32`
inside the link leave Dirac's hypothesis intact. -/
theorem twoSided_sweep_margin {h t q c n m : ℕ} (hh : 5 ≤ h) (hn : 4 * n ≤ t)
    (hm : 32 * m ≤ h * t) (hq3 : 3 * t ≤ 4 * q) (hqc : 3 * q ≤ 4 * c) :
    12 * n + 8 * m ≤ (2 * h - 1) * c := by
  have h16 : 9 * t ≤ 16 * c := by omega
  have key : 144 * (12 * n + 8 * m) ≤ 144 * ((2 * h - 1) * c) := by
    calc 144 * (12 * n + 8 * m) = 432 * (4 * n) + 36 * (32 * m) := by ring
      _ ≤ 432 * t + 36 * (h * t) := Nat.add_le_add (Nat.mul_le_mul_left _ hn)
            (Nat.mul_le_mul_left _ hm)
      _ = (4 * h + 48) * (9 * t) := by ring
      _ ≤ (4 * h + 48) * (16 * c) := Nat.mul_le_mul_left _ h16
      _ ≤ (9 * (2 * h - 1)) * (16 * c) := Nat.mul_le_mul_right _ (by omega)
      _ = 144 * ((2 * h - 1) * c) := by ring
  exact Nat.le_of_mul_le_mul_left key (by norm_num)

/-- **The budget closes at a two-sided design.**  If the used-edge degree inside the link being
processed splits into the competition of one cell and a spread contribution, and the two halves of
the budget cover them, then Dirac's hypothesis of
`BKLO.twoSided_perturbed_link_dirac_avoiding` holds. -/
theorem twoSided_sweep_budget_of_spread {h t q c n m Ncell s : ℕ} (hh : 5 ≤ h)
    (hn : 4 * n ≤ t) (hm : m ≤ Ncell + s)
    (hcell : 64 * Ncell ≤ h * t) (hspread : 64 * s ≤ h * t)
    (hq3 : 3 * t ≤ 4 * q) (hqc : 3 * q ≤ 4 * c) :
    12 * n + 8 * m ≤ (2 * h - 1) * c := by
  refine twoSided_sweep_margin hh hn ?_ hq3 hqc
  have key : 2 * (32 * m) ≤ 2 * (h * t) := by
    calc 2 * (32 * m) = 64 * m := by ring
      _ ≤ 64 * (Ncell + s) := Nat.mul_le_mul_left _ hm
      _ = 64 * Ncell + 64 * s := by ring
      _ ≤ h * t + h * t := Nat.add_le_add hcell hspread
      _ = 2 * (h * t) := by ring
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-! ### The two contributions, at a two-sided design -/

/-- The adversary's perturbation is at most a quarter of a class: `8η|W| ≤ t`. -/
theorem eight_cleanEta_mul_card_le_twoSided
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hK : 0 < K) :
    8 * cleanEta ε K * (W.card : ℝ) ≤ (gridClassSize ε K W'.card : ℝ) := by
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hvol : (W.card : ℝ) ≤ 20 * ((K : ℝ) * K * h * h) * (t : ℝ) := by
    have h1 := hgrid.outerVolume
    rw [← hhdef, ← htdef] at h1
    exact_mod_cast h1
  have heta : cleanEta ε K = 1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
    rw [cleanEta, reservoirEta, ← hhdef]
    field_simp
    ring
  rw [heta,
    show 8 * (1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (W.card : ℝ)
      = (W.card : ℝ) / (20 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) by field_simp; ring,
    div_le_iff₀ (by positivity)]
  nlinarith only [hvol]

/-- The adversary's perturbation fits in the first budget of `BKLO.twoSided_sweep_margin`. -/
theorem twoSided_perturbation_quarter
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y) (hK : 0 < K)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) :
    4 * n ≤ gridClassSize ε K W'.card := by
  have h1 := eight_cleanEta_mul_card_le_twoSided hgrid hK
  have h2 : ((4 * n : ℕ) : ℝ) ≤ ((gridClassSize ε K W'.card : ℕ) : ℝ) := by push_cast; linarith only [hn, h1]
  exact_mod_cast h2

/-- **The competition of one cell is free** at a two-sided design too: the number of outer vertices
of a single cell of the grid is at most `h t / 64`. -/
theorem twoSided_cell_fibre_budget
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K) (p₀ q₀ : ℕ) :
    64 * (((W \ W').filter (fun u => x u = p₀ ∧ y u = q₀)).card)
      ≤ gridSize ε K * gridClassSize ε K W'.card := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set Nc : ℕ := ((W \ W').filter (fun u => x u = p₀ ∧ y u = q₀)).card with hNdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have htpos : 0 < t := hgrid.classPos
  have hcell : Nc * (h * h) ≤ (W \ W').card + h * h := hgrid.cellFibre p₀ q₀
  have hDW : (W \ W').card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
  have hvol : W.card ≤ 20 * (K * K * h * h) * t := hgrid.outerVolume
  have hstep : Nc * (h * h) ≤ (20 * (K * K) * t + 1) * (h * h) := by
    calc Nc * (h * h) ≤ (W \ W').card + h * h := hcell
      _ ≤ 20 * (K * K * h * h) * t + h * h := Nat.add_le_add_right (le_trans hDW hvol) _
      _ = (20 * (K * K) * t + 1) * (h * h) := by ring
  have hN : Nc ≤ 20 * (K * K) * t + 1 := Nat.le_of_mul_le_mul_right hstep hhh
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKt : 1 ≤ K * K * t := Nat.mul_pos (Nat.mul_pos hK hK) htpos
  calc 64 * Nc ≤ 64 * (20 * (K * K) * t + 1) := Nat.mul_le_mul_left _ hN
    _ = 1280 * (K * K * t) + 64 := by ring
    _ ≤ 1280 * (K * K * t) + 64 * (K * K * t) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right 64 hKt) _
    _ = 1344 * (K * K) * t := by ring
    _ ≤ 6400 * (K * K) * t := Nat.mul_le_mul_right _ (by omega)
    _ ≤ h * t := Nat.mul_le_mul_right _ hwide

/-- **The total number of links a vertex belongs to** at a two-sided design. -/
theorem twoSided_link_multiplicity_le
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε' : ε ≤ 1 / 100) (hK : 0 < K)
    {X : V → Finset V} {a : V} (ha : a ∈ W')
    (hsparse : (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ))
    (hmult : ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℕ) : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ)) :
    160 * ((((W \ W').filter (fun u => a ∈ X u)).card : ℕ))
      ≤ gridSize ε K * gridSize ε K * (gridClassSize ε K W'.card + 1)
        + 40 * gridClassSize ε K W'.card := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < 10 * h * h := by positivity
  have hDW' : ∀ u ∈ W \ W', u ∉ W' := fun u hu => (Finset.mem_sdiff.1 hu).2
  have hT := card_filter_mem_link_le (D := W \ W') (W' := W') (R := R) (X := X) hDW' ha hsparse
    hmult
  have hteq : t = W'.card / (10 * h * h) := by rw [htdef, hhdef]; rfl
  have hpool : W'.card < 10 * h * h * (t + 1) := by
    have hd := Nat.div_add_mod W'.card (10 * h * h)
    have hm := Nat.mod_lt W'.card hhh
    rw [hteq]
    nlinarith only [hd, hm]
  have hpoolr : (W'.card : ℝ) ≤ 10 * (h : ℝ) * h * ((t : ℝ) + 1) := by
    have hcast : ((W'.card : ℕ) : ℝ) ≤ ((10 * h * h * (t + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_lt hpool
    push_cast at hcast
    linarith only [hcast]
  have hperturb := eight_cleanEta_mul_card_le_twoSided hgrid hK
  rw [← htdef] at hperturb
  have hW'0 : (0 : ℝ) ≤ (W'.card : ℝ) := Nat.cast_nonneg _
  have h2 : (160 : ℝ) * (ε / 16 * (W'.card : ℝ)) ≤ (h : ℝ) * h * ((t : ℝ) + 1) := by
    have hA : (10 : ℝ) * ε * (W'.card : ℝ) ≤ (W'.card : ℝ) / 10 := by nlinarith only [hε']
    have hB : (W'.card : ℝ) / 10 ≤ (h : ℝ) * h * ((t : ℝ) + 1) := by linarith only [hpoolr]
    linarith only [hpoolr, hA]
  have hfinal : (160 : ℝ) * ((((W \ W').filter (fun u => a ∈ X u)).card : ℕ) : ℝ)
      ≤ (h : ℝ) * h * ((t : ℝ) + 1) + 40 * (t : ℝ) := by linarith only [hT, hperturb, h2]
  have hcast : ((160 * ((((W \ W').filter (fun u => a ∈ X u)).card : ℕ)) : ℕ) : ℝ)
      ≤ ((h * h * (t + 1) + 40 * t : ℕ) : ℝ) := by push_cast; linarith only [hfinal]
  exact_mod_cast hcast

end BKLO
