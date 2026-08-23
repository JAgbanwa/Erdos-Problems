/-
# The budget of a sweep at the sharp grid design.

`BKLO/SharpLinkMargin.lean` pairs up *one* link of the sharp grid design: every vertex of the
perturbed link `X` has at least `|X|/2 + (2h-1)q/8` neighbours inside it, so Dirac's theorem
applies.  A *system* of pairings has to do more — the pairs of different outer vertices must be
different edges (`IsPairedLinkCore.distinct`) — and the natural route is a sweep over the outer
vertices which deletes the already-used edges before applying Dirac to the next link.

This file is the arithmetic of that sweep.

* `BKLO.sharp_perturbed_link_dirac_avoiding` — Dirac's hypothesis survives the deletion of *any*
  edge set `U` of degree at most `m` inside the link, as long as `12n + 8m ≤ (2h-1)q`
  (`n` is the size of the adversary's perturbation);
* `BKLO.exists_pairing_of_sharp_link_avoiding` — hence one pairing of the link by edges of `F \ U`;
* `BKLO.sharp_sweep_margin` — the two budgets in the design's own units: `4n ≤ t` and `32m ≤ h t`
  suffice, where `t` is the nominal class size;
* `BKLO.sharp_cell_fibre_budget` — **the first half of the budget is free**: the number of outer
  vertices of a single cell is at most `h t / 64`, so if the pairs at a vertex `a` coming from the
  links of one cell were the only competition, the sweep would go through;
* `BKLO.sharp_link_multiplicity_le` — the total number of links a vertex `a ∈ W'` belongs to is at
  most `ε|W'|/16 + 2η|W|`;
* `BKLO.sharp_spread_budget` — **the second half of the budget is what the ledger must deliver**:
  if the used edges at `a` are spread over the `h` cells of a row (or a column) of the grid to
  within a factor two of the average, their contribution is also at most `h t / 64`.

Together (`BKLO.sharp_sweep_budget_of_spread`) the two halves close the budget of
`BKLO.sharp_sweep_margin`, so the only thing between the sharp design and
`BKLO.GridPairingResidualSharp` is the construction of a pairing rule realising that spread.

Everything here is `sorry`-free.
-/
import BKLO.SharpLinkMargin
import BKLO.GridCompetition

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Deleting the used edges -/

/-- The link inside a deleted edge set is the link minus the deleted link. -/
theorem resLink_sdiff (F U : Finset (Sym2 V)) (S : Finset V) (a : V) :
    resLink (F \ U) S a = resLink F S a \ resLink U S a := by
  ext z
  simp only [Finset.mem_sdiff, mem_resLink, not_and]
  constructor
  · rintro ⟨hz, hzF, hzU⟩
    exact ⟨⟨hz, hzF⟩, fun _ => hzU⟩
  · rintro ⟨⟨hz, hzF⟩, hzU⟩
    exact ⟨hz, hzF, hzU hz⟩

variable {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
  {x y : V → ℕ} {q : ℕ}

/-- **Dirac's hypothesis for the perturbed link, after the used edges are deleted.**  At a sharp
grid design, an admissible perturbation `X` of the reserved link of an outer vertex still has every
vertex joined to at least half of it by edges outside a set `U` of small degree. -/
theorem sharp_perturbed_link_dirac_avoiding
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W')
    {n m : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    {U : Finset (Sym2 V)} (hU : ∀ a ∈ X, (resLink U X a).card ≤ m)
    (hmargin : 12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * q)
    {a : V} (ha : a ∈ X) :
    X.card ≤ 2 * edeg ((F \ U) ∩ cliqueEdges X) a := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set S : Finset V := resLink R W' u with hSdef
  have haW : a ∈ W := hW'W (hXW' ha)
  have hSW' : S ⊆ W' := fun z hz => (mem_resLink.1 hz).1
  have hSreg : S ⊆ gridRegion h C (x u) (y u) := by
    rw [hSdef, hgrid.link u hu]
    exact Finset.inter_subset_right
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
  -- the non-neighbours inside `X` are those inside the link, plus the perturbation
  have hsub : nonNbrs F W' a ∩ X ⊆ (nonNbrs F W' a ∩ S) ∪ (X \ S) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hz1, hzS⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hz2, hzS⟩)
  have hnon : (nonNbrs F W' a ∩ X).card ≤ (nonNbrs F W' a ∩ S).card + (X \ S).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- the two counts at the sharp design
  have hupper : 4 * ((nonNbrs F W' a ∩ S).card) ≤ (2 * h - 1) * q := by
    refine le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      (card_nonNbrs_inter_gridRegion_sharp_le hgrid hq hu haW)
    exact Finset.inter_subset_inter_left hSreg
  have hlower : 3 * ((2 * h - 1) * q) ≤ 4 * S.card := card_resLink_sharp_ge hgrid hq hu
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

/-- **Every link of a sharp design is paired up avoiding a small used-edge set.**  The step of a
sweep: given the pairs already placed (an edge set `U` of degree at most `m` inside the link), the
next link is still paired up, by edges of `F` that `U` does not contain. -/
theorem exists_pairing_of_sharp_link_avoiding (hDirac : PerfectMatchingDirac)
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q : ℕ}
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hW'W : W' ⊆ W)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    {u : V} (hu : u ∈ W \ W') {X : Finset V} (hXW' : X ⊆ W') (hXeven : Even X.card)
    {n m : ℕ} (hadd : (X \ resLink R W' u).card ≤ n) (hdel : (resLink R W' u \ X).card ≤ n)
    {U : Finset (Sym2 V)} (hU : ∀ a ∈ X, (resLink U X a).card ≤ m)
    (hmargin : 12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * q) :
    ∃ g : V → V, (∀ a ∈ X, g a ∈ X) ∧ (∀ a ∈ X, g (g a) = a) ∧ (∀ a ∈ X, g a ≠ a) ∧
      ∀ a ∈ X, s(a, g a) ∈ F ∧ s(a, g a) ∉ U := by
  obtain ⟨g, h1, h2, h3, h4⟩ :=
    exists_pairing_of_dirac hDirac hXeven
      (fun _ ha => sharp_perturbed_link_dirac_avoiding hgrid hnd hW'W hq hu hXW' hadd hdel hU
        hmargin ha)
  exact ⟨g, h1, h2, h3, fun a ha => ⟨(Finset.mem_sdiff.1 (h4 a ha)).1,
    (Finset.mem_sdiff.1 (h4 a ha)).2⟩⟩

end Dirac

/-! ### The budget in the design's own units -/

/-- At `ε ≤ 1/100` the grid is at least `6400K²` wide. -/
theorem gridSize_ge_of_eps_small {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (K : ℕ) :
    6400 * (K * K) ≤ gridSize ε K := by
  have h1 := le_gridSize ε K
  have hKr : (0 : ℝ) ≤ (K : ℝ) ^ 2 := sq_nonneg _
  have h2 : (6400 : ℝ) * (K : ℝ) ^ 2 ≤ 64 * (K : ℝ) ^ 2 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have h3 : (6400 : ℝ) * (K : ℝ) ^ 2 ≤ (gridSize ε K : ℝ) := le_trans h2 h1
  have h4 : ((6400 * (K * K) : ℕ) : ℝ) ≤ ((gridSize ε K : ℕ) : ℝ) := by push_cast; nlinarith
  exact_mod_cast h4

/-- **The two budgets of a sweep.**  With `t` the nominal class size, an adversarial perturbation
of size `n ≤ t/4` and an already-used edge set of degree `m ≤ h t / 32` inside the link leave
Dirac's hypothesis intact: this is exactly the hypothesis of
`BKLO.sharp_perturbed_link_dirac_avoiding`. -/
theorem sharp_sweep_margin {h t q n m : ℕ} (hh : 3 ≤ h) (hn : 4 * n ≤ t)
    (hm : 32 * m ≤ h * t) (hq3 : 3 * t ≤ 4 * q) :
    12 * n + 8 * m ≤ (2 * h - 1) * q := by
  have key : 4 * (12 * n + 8 * m) ≤ 4 * ((2 * h - 1) * q) := by
    calc 4 * (12 * n + 8 * m) = 12 * (4 * n) + 32 * m := by ring
      _ ≤ 12 * t + h * t := Nat.add_le_add (Nat.mul_le_mul_left _ hn) hm
      _ = (12 + h) * t := by ring
      _ ≤ (3 * (2 * h - 1)) * t := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * h - 1) * (3 * t) := by ring
      _ ≤ (2 * h - 1) * (4 * q) := Nat.mul_le_mul_left _ hq3
      _ = 4 * ((2 * h - 1) * q) := by ring
  omega

/-- **The spread budget.**  If the used edges at a vertex are spread over the `h` cells of a row of
the grid to within a factor two of the average, their contribution to a single link is at most
`h t / 64` — half of the budget of `BKLO.sharp_sweep_margin`. -/
theorem sharp_spread_budget {h t T s : ℕ} (hh : 80 ≤ h) (ht : 16 ≤ t)
    (hT : 160 * T ≤ h * h * (t + 1) + 40 * t) (hs : h * s ≤ 2 * T + h) :
    64 * s ≤ h * t := by
  have core : 128 * (h * h) + 5120 * t + 10240 * h ≤ 32 * (h * h * t) := by
    have hA : 128 * (h * h) ≤ 8 * (h * h * t) := by
      calc 128 * (h * h) = 8 * (h * h * 16) := by ring
        _ ≤ 8 * (h * h * t) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ht)
    have hB : 10240 * h ≤ 8 * (h * h * t) := by
      calc 10240 * h = 8 * (80 * 16 * h) := by ring
        _ ≤ 8 * (h * t * h) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul hh ht))
        _ = 8 * (h * h * t) := by ring
    have hC : 5120 * t ≤ 16 * (h * h * t) := by
      calc 5120 * t = 16 * (320 * t) := by ring
        _ ≤ 16 * ((h * h) * t) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by nlinarith))
        _ = 16 * (h * h * t) := by ring
    calc 128 * (h * h) + 5120 * t + 10240 * h
        ≤ 8 * (h * h * t) + 16 * (h * h * t) + 8 * (h * h * t) :=
          Nat.add_le_add (Nat.add_le_add hA hC) hB
      _ = 32 * (h * h * t) := by ring
  have key : (160 * h) * (64 * s) ≤ (160 * h) * (h * t) := by
    calc (160 * h) * (64 * s) = 64 * (160 * (h * s)) := by ring
      _ ≤ 64 * (160 * (2 * T + h)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hs)
      _ = 64 * (2 * (160 * T) + 160 * h) := by ring
      _ ≤ 64 * (2 * (h * h * (t + 1) + 40 * t) + 160 * h) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 128 * (h * h * t) + (128 * (h * h) + 5120 * t + 10240 * h) := by ring
      _ ≤ 128 * (h * h * t) + 32 * (h * h * t) := Nat.add_le_add_left core _
      _ = (160 * h) * (h * t) := by ring
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- **The budget closes.**  If the used-edge degree inside the link being processed splits into the
competition of one cell and a spread contribution, and the two halves of the budget cover them,
then Dirac's hypothesis of `BKLO.sharp_perturbed_link_dirac_avoiding` holds. -/
theorem sharp_sweep_budget_of_spread {h t q n m Ncell s : ℕ} (hh : 3 ≤ h)
    (hn : 4 * n ≤ t) (hm : m ≤ Ncell + s)
    (hcell : 64 * Ncell ≤ h * t) (hspread : 64 * s ≤ h * t) (hq3 : 3 * t ≤ 4 * q) :
    12 * n + 8 * m ≤ (2 * h - 1) * q := by
  refine sharp_sweep_margin hh hn ?_ hq3
  have key : 2 * (32 * m) ≤ 2 * (h * t) := by
    calc 2 * (32 * m) = 64 * m := by ring
      _ ≤ 64 * (Ncell + s) := Nat.mul_le_mul_left _ hm
      _ = 64 * Ncell + 64 * s := by ring
      _ ≤ h * t + h * t := Nat.add_le_add hcell hspread
      _ = 2 * (h * t) := by ring
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-! ### The two contributions, at a sharp design -/

/-- The adversary's perturbation is at most a quarter of a class: `8η|W| ≤ t`. -/
theorem eight_cleanEta_mul_card_le
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y) (hK : 0 < K) :
    8 * cleanEta ε K * (W.card : ℝ) ≤ (gridClassSize ε K W'.card : ℝ) := by
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hvol : (W.card : ℝ) ≤ 20 * ((K : ℝ) * K * h * h) * (t : ℝ) := by
    have := hgrid.outerVolume
    rw [← hhdef, ← htdef] at this
    exact_mod_cast this
  have heta : cleanEta ε K = 1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
    rw [cleanEta, reservoirEta, ← hhdef]
    field_simp
    ring
  rw [heta,
    show 8 * (1 / (160 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (W.card : ℝ)
      = (W.card : ℝ) / (20 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) by field_simp; ring,
    div_le_iff₀ (by positivity)]
  nlinarith only [hvol]

/-- The adversary's perturbation fits in the first budget of `BKLO.sharp_sweep_margin`. -/
theorem sharp_perturbation_quarter
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y) (hK : 0 < K)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ)) :
    4 * n ≤ gridClassSize ε K W'.card := by
  have h1 := eight_cleanEta_mul_card_le hgrid hK
  have h2 : ((4 * n : ℕ) : ℝ) ≤ ((gridClassSize ε K W'.card : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h2

/-- **The competition of one cell is free.**  The number of outer vertices of a single cell of the
grid is at most `h t / 64`: even if every one of them used an edge at the same vertex of the link
being processed, half of the budget of `BKLO.sharp_sweep_margin` would still be unspent. -/
theorem sharp_cell_fibre_budget
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 0 < K) (p₀ q₀ : ℕ) :
    64 * (((W \ W').filter (fun u => x u = p₀ ∧ y u = q₀)).card)
      ≤ gridSize ε K * gridClassSize ε K W'.card := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set N : ℕ := ((W \ W').filter (fun u => x u = p₀ ∧ y u = q₀)).card with hNdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have htpos : 0 < t := hgrid.classPos
  have hcell : N * (h * h) ≤ (W \ W').card + h * h := hgrid.cellFibre p₀ q₀
  have hDW : (W \ W').card ≤ W.card := Finset.card_le_card Finset.sdiff_subset
  have hvol : W.card ≤ 20 * (K * K * h * h) * t := hgrid.outerVolume
  have hstep : N * (h * h) ≤ (20 * (K * K) * t + 1) * (h * h) := by
    calc N * (h * h) ≤ (W \ W').card + h * h := hcell
      _ ≤ 20 * (K * K * h * h) * t + h * h := Nat.add_le_add_right (le_trans hDW hvol) _
      _ = (20 * (K * K) * t + 1) * (h * h) := by ring
  have hN : N ≤ 20 * (K * K) * t + 1 := Nat.le_of_mul_le_mul_right hstep hhh
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKt : 1 ≤ K * K * t := Nat.mul_pos (Nat.mul_pos hK hK) htpos
  calc 64 * N ≤ 64 * (20 * (K * K) * t + 1) := Nat.mul_le_mul_left _ hN
    _ = 1280 * (K * K * t) + 64 := by ring
    _ ≤ 1280 * (K * K * t) + 64 * (K * K * t) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right 64 hKt) _
    _ = 1344 * (K * K) * t := by ring
    _ ≤ 6400 * (K * K) * t := Nat.mul_le_mul_right _ (by omega)
    _ ≤ h * t := Nat.mul_le_mul_right _ hwide

/-- **The total number of links a vertex belongs to**, in the design's own units.  This is the
quantity the sweep has to spread over the `h` cells of a row of the grid; once it is spread to
within a factor two of the average, `BKLO.sharp_spread_budget` applies. -/
theorem sharp_link_multiplicity_le
    (hgrid : IsGridSharpReservoir ε K W W' W'' F R C x y)
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
  -- the pool is not much larger than `10h²t`
  have hteq : t = W'.card / (10 * h * h) := by rw [htdef, hhdef]; rfl
  have hpool : W'.card < 10 * h * h * (t + 1) := by
    have hd := Nat.div_add_mod W'.card (10 * h * h)
    have hm := Nat.mod_lt W'.card hhh
    rw [hteq]
    nlinarith only [hd, hm]
  have hpoolr : (W'.card : ℝ) ≤ 10 * (h : ℝ) * h * ((t : ℝ) + 1) := by
    have hc : ((W'.card : ℕ) : ℝ) ≤ ((10 * h * h * (t + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_lt hpool
    push_cast at hc
    linarith
  have hperturb := eight_cleanEta_mul_card_le hgrid hK
  rw [← htdef] at hperturb
  have hW'0 : (0 : ℝ) ≤ (W'.card : ℝ) := Nat.cast_nonneg _
  have h2 : (160 : ℝ) * (ε / 16 * (W'.card : ℝ)) ≤ (h : ℝ) * h * ((t : ℝ) + 1) := by
    have hA : (10 : ℝ) * ε * (W'.card : ℝ) ≤ (W'.card : ℝ) / 10 := by nlinarith
    have hB : (W'.card : ℝ) / 10 ≤ (h : ℝ) * h * ((t : ℝ) + 1) := by linarith
    linarith
  have hfinal : (160 : ℝ) * ((((W \ W').filter (fun u => a ∈ X u)).card : ℕ) : ℝ)
      ≤ (h : ℝ) * h * ((t : ℝ) + 1) + 40 * (t : ℝ) := by linarith
  have hcast : ((160 * ((((W \ W').filter (fun u => a ∈ X u)).card : ℕ)) : ℕ) : ℝ)
      ≤ ((h * h * (t + 1) + 40 * t : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

end BKLO
