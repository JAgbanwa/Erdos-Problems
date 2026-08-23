/-
# The class ledger of a sweep at the two-sided design.

`BKLO.twoSided_step_of_spread` (`BKLO/TwoSidedLedger.lean`) pairs up one more link of a two-sided
grid design as soon as two counts are small: the **cross-cell spread** (how often the partners
already chosen for a vertex `a` land in the link being processed) and the number of **saturated**
vertices of the link (those already at their protected-level budget).  This file discharges the
second count outright and reduces the first one to a ledger carried along the sweep.

* `BKLO.regionLoad` — the ledger: for a vertex `a` and a cell `(P, Q)` of the grid, the number of
  outer vertices `w` already processed, *of another cell*, which paired `a` into the region of
  `(P, Q)`.
* `BKLO.card_resLink_usedPairs_region_split` — the used degree at `a` inside the link of `u` is at
  most the competition of `u`'s own cell (free, by `BKLO.twoSided_cell_fibre_budget`), plus the
  ledger entry of `a` at `u`'s cell, plus the perturbation.  So the cross-cell spread *is* the
  ledger.
* `BKLO.twoSided_card_saturated_le` — **the protected level is free**: whatever the pairings
  already chosen, at most `h t / 64` vertices of a link are at their protected-level budget.  Only
  the perturbation of the links can pair a vertex into the protected level (the classes of the
  design avoid it), the multiplicity bound `hXmult` caps how often each protected vertex is used,
  and the budget `ε |W''| / 8` is far above the resulting average.  This is a theorem, not a
  demand: it needs no invariant of the sweep at all.
* `BKLO.LedgerSpread` — the invariant of the sweep: every ledger entry is at most `h t / 32`.
* `BKLO.TwoSidedClassDirectedRule` — **the remaining residual**: the class-directed pairing rule.
  Word for word the conclusion of `BKLO.exists_pairing_of_twoSided_link_avoiding` (a theorem, from
  Dirac's threshold), with one extra demand: the pairing chosen keeps the ledger spread.
* `BKLO.twoSided_step_of_rule` — one step of the sweep, from the rule alone: Dirac's threshold, the
  cell competition, the perturbation, the protected level and its load are all discharged here.
* `BKLO.gridPairingResidualTwoSided_of_rule`,
  `BKLO.triangle_decomposition_of_inputs_and_twoSidedClassDirectedRule` — the AX2 half of
  Erdős #81 from the three classical inputs and the class-directed rule.

Everything here is `sorry`-free.
-/
import BKLO.TwoSidedLedger

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### The ledger of a sweep -/

/-- **The ledger of a sweep.**  `regionLoad h C X g S x y a P Q` is the number of outer vertices
`w` already processed, *of a cell other than* `(P, Q)`, whose link contains `a` and which paired
`a` into the region of the cell `(P, Q)`. -/
def regionLoad (h : ℕ) (C : ℕ → Finset V) (X : V → Finset V) (g : V → V → V) (S : Finset V)
    (x y : V → ℕ) (a : V) (P Q : ℕ) : ℕ :=
  (S.filter (fun w =>
    ¬ (x w = P ∧ y w = Q) ∧ a ∈ X w ∧ g w a ∈ gridRegion h C P Q)).card

theorem regionLoad_empty (h : ℕ) (C : ℕ → Finset V) (X : V → Finset V) (g : V → V → V)
    (x y : V → ℕ) (a : V) (P Q : ℕ) : regionLoad h C X g (∅ : Finset V) x y a P Q = 0 := by
  simp [regionLoad]

/-- **The used degree splits into the cell competition, the ledger and the perturbation.**  The
edges already used at a vertex `a` of the link of `u` reach at most `Ncell + regionLoad + n`
vertices of the link: those paired by an outer vertex of `u`'s own cell, those paired into the
region of `u`'s cell by an outer vertex of another cell — the ledger entry — and those outside the
region, which lie in the perturbation of the link. -/
theorem card_resLink_usedPairs_region_split {X : V → Finset V} {g₀ : V → V → V} {S D : Finset V}
    {R : Finset (Sym2 V)} {W' : Finset V} {C : ℕ → Finset V} {x y : V → ℕ} {h : ℕ}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) (hSD : S ⊆ D) {u a : V}
    (hlink : resLink R W' u ⊆ gridRegion h C (x u) (y u)) :
    (resLink (usedPairs X g₀ S) (X u) a).card
      ≤ (D.filter (fun w => x w = x u ∧ y w = y u)).card
        + regionLoad h C X g₀ S x y a (x u) (y u)
        + (X u \ resLink R W' u).card := by
  classical
  set A : Finset V := resLink (usedPairs X g₀ S) (X u) a with hAdef
  set Reg : Finset V := gridRegion h C (x u) (y u) with hRegdef
  have hAX : A ⊆ X u := fun z hz => (mem_resLink.1 hz).1
  -- the partners outside the region lie in the perturbation
  have hout : A \ Reg ⊆ X u \ resLink R W' u := by
    intro z hz
    obtain ⟨hzA, hzR⟩ := Finset.mem_sdiff.1 hz
    exact Finset.mem_sdiff.2 ⟨hAX hzA, fun hcon => hzR (hlink hcon)⟩
  -- the partners inside the region are indexed by the outer vertices of the ledger
  have hin : A ∩ Reg
      ⊆ (S.filter (fun w => (a ∈ X w ∧ g₀ w a ∈ X u) ∧ g₀ w a ∈ Reg)).image (fun w => g₀ w a) := by
    intro z hz
    obtain ⟨hzA, hzReg⟩ := Finset.mem_inter.1 hz
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.1 (resLink_usedPairs_subset hmaps hinv (X u) a hzA)
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hwS, hwa, heq ▸ hzReg⟩, heq⟩
  set T : Finset V := S.filter (fun w => (a ∈ X w ∧ g₀ w a ∈ X u) ∧ g₀ w a ∈ Reg) with hTdef
  have h1 : (A ∩ Reg).card ≤ T.card := le_trans (Finset.card_le_card hin) Finset.card_image_le
  have hsplit : (T.filter (fun w => x w = x u ∧ y w = y u)).card
      + (T.filter (fun w => ¬ (x w = x u ∧ y w = y u))).card = T.card :=
    Finset.card_filter_add_card_filter_not _
  have h2 : (T.filter (fun w => x w = x u ∧ y w = y u)).card
      ≤ (D.filter (fun w => x w = x u ∧ y w = y u)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    obtain ⟨hwT, hwc⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hSD (Finset.mem_of_mem_filter w hwT), hwc⟩
  have h3 : (T.filter (fun w => ¬ (x w = x u ∧ y w = y u))).card
      ≤ regionLoad h C X g₀ S x y a (x u) (y u) := by
    refine Finset.card_le_card ?_
    intro w hw
    obtain ⟨hwT, hwc⟩ := Finset.mem_filter.1 hw
    obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hwT
    exact Finset.mem_filter.2 ⟨hwS, hwc, hwa.1.1, hwa.2⟩
  have h4 : (A \ Reg).card ≤ (X u \ resLink R W' u).card := Finset.card_le_card hout
  have h5 : A.card = (A ∩ Reg).card + (A \ Reg).card := (Finset.card_inter_add_card_sdiff _ _).symm
  omega

/-! ### Why the rule must arrange the past -/

/-- **A vertex whose link-edges are all used cannot be paired.**  If the pairings already chosen
have used every edge of the link of `u` at one of its vertices `a₀`, then no fixed-point-free
pairing of the link avoids the used edges.

This is the obstruction to any demand in which the earlier pairings `g₀` are *arbitrary* — such as
`BKLO.GridPairingStepClauseTwoSidedInv`, whose `g₀` ranges over all involutions of the earlier
links.  A vertex `a` of `W'` lies in up to `(ε/16)|W'|` reserved links, far more than the
`(2h-1)c ≈ 3 h t / 2` vertices of a single link, so nothing in the design prevents the earlier
pairings from exhausting the link at `a₀`.  The sweep must therefore be allowed to *arrange* the
past — `BKLO.exists_pairedLinkCore_of_step_invariant` — which is exactly what the spread discipline
of `BKLO.TwoSidedClassDirectedRule` does. -/
theorem no_pairing_of_blocked_vertex {X : V → Finset V} {g₀ : V → V → V} {S : Finset V} {u a₀ : V}
    (ha₀ : a₀ ∈ X u) (hblocked : ∀ z ∈ X u, z ≠ a₀ → s(a₀, z) ∈ usedPairs X g₀ S) :
    ¬ ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p a ≠ a) ∧
      (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) := by
  rintro ⟨p, h1, h2, h3⟩
  exact h3 a₀ ha₀ (hblocked (p a₀) (h1 a₀ ha₀) (h2 a₀ ha₀))

/-! ### The protected level is free -/

/-- One outer vertex pairs at most `|X w ∩ W''|` vertices into the protected level: its pairing is
an involution of its own link. -/
theorem card_filter_paired_into_le {X : V → Finset V} {g₀ : V → V → V} {W'' : Finset V} {w : V}
    (hmaps : ∀ b ∈ X w, g₀ w b ∈ X w) (hinv : ∀ b ∈ X w, g₀ w (g₀ w b) = b) (Y : Finset V) :
    (Y.filter (fun v => v ∈ X w ∧ g₀ w v ∈ W'')).card ≤ (X w ∩ W'').card := by
  classical
  refine Finset.card_le_card_of_injOn (fun v => g₀ w v) ?_ ?_
  · intro v hv
    obtain ⟨-, hvX, hvW''⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_inter.2 ⟨hmaps v hvX, hvW''⟩
  · intro v hv z hz heq
    obtain ⟨-, hvX, -⟩ := Finset.mem_filter.1 hv
    obtain ⟨-, hzX, -⟩ := Finset.mem_filter.1 hz
    have h1 : g₀ w (g₀ w v) = g₀ w (g₀ w z) := congrArg (g₀ w) heq
    rw [hinv v hvX, hinv z hzX] at h1
    exact h1

/-- The total protected-level load of the pairings already chosen is at most
`|W''| · 2 η |W|`: only the perturbation of a link can meet the protected level, and each protected
vertex is used by at most `2 η |W|` links. -/
theorem sum_protected_load_le {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {X : V → Finset V} {g₀ : V → V → V} {S : Finset V}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hSD : S ⊆ W \ W')
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
    (hXmult : ∀ a ∈ W', (((W \ W').filter (fun v => a ∈ X v \ resLink R W' v)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hW''W' : W'' ⊆ W') (Y : Finset V) :
    ((∑ v ∈ Y, (S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℕ) : ℝ)
      ≤ (W''.card : ℝ) * (2 * cleanEta ε K * (W.card : ℝ)) := by
  classical
  -- double counting: sum over the processed vertices
  have hswap : ∑ v ∈ Y, (S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card
      = ∑ w ∈ S, (Y.filter (fun v => v ∈ X w ∧ g₀ w v ∈ W'')).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hstep1 : ∑ w ∈ S, (Y.filter (fun v => v ∈ X w ∧ g₀ w v ∈ W'')).card
      ≤ ∑ w ∈ S, (X w ∩ W'').card :=
    Finset.sum_le_sum fun w hw =>
      card_filter_paired_into_le (hmaps w hw) (hinv w hw) Y
  -- and now over the protected vertices
  have hstep2 : ∑ w ∈ S, (X w ∩ W'').card
      = ∑ a ∈ W'', (S.filter (fun w => a ∈ X w)).card := by
    have hrw : ∀ w : V, (X w ∩ W'').card = (W''.filter (fun a => a ∈ X w)).card := by
      intro w
      congr 1
      ext a
      simp only [Finset.mem_inter, Finset.mem_filter]
      tauto
    simp only [hrw, Finset.card_filter]
    rw [Finset.sum_comm]
  have hstep3 : ∀ a ∈ W'', ((S.filter (fun w => a ∈ X w)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ) := by
    intro a ha
    refine le_trans ?_ (hXmult a (hW''W' ha))
    have : S.filter (fun w => a ∈ X w) ⊆ (W \ W').filter (fun v => a ∈ X v \ resLink R W' v) := by
      intro w hw
      obtain ⟨hwS, hwa⟩ := Finset.mem_filter.1 hw
      refine Finset.mem_filter.2 ⟨hSD hwS, Finset.mem_sdiff.2 ⟨hwa, ?_⟩⟩
      exact fun hcon => resLink_notMem_protected hgrid (hSD hwS) hcon ha
    exact_mod_cast Finset.card_le_card this
  have hsum : ((∑ a ∈ W'', (S.filter (fun w => a ∈ X w)).card : ℕ) : ℝ)
      ≤ (W''.card : ℝ) * (2 * cleanEta ε K * (W.card : ℝ)) := by
    push_cast
    calc ∑ a ∈ W'', ((S.filter (fun w => a ∈ X w)).card : ℝ)
        ≤ ∑ _a ∈ W'', 2 * cleanEta ε K * (W.card : ℝ) := Finset.sum_le_sum hstep3
      _ = (W''.card : ℝ) * (2 * cleanEta ε K * (W.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ((∑ v ∈ Y, (S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℕ) : ℝ)
      = ((∑ w ∈ S, (Y.filter (fun v => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hswap
    _ ≤ ((∑ w ∈ S, (X w ∩ W'').card : ℕ) : ℝ) := by exact_mod_cast hstep1
    _ = ((∑ a ∈ W'', (S.filter (fun w => a ∈ X w)).card : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hstep2
    _ ≤ (W''.card : ℝ) * (2 * cleanEta ε K * (W.card : ℝ)) := hsum

/-- **The protected level is free at a two-sided design.**  Whatever the pairings already chosen —
no invariant of the sweep is used — at most `h t / 64` vertices of the link being processed are
already at their protected-level budget `ε |W''| / 8`. -/
theorem twoSided_card_saturated_le {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {X : V → Finset V} {g₀ : V → V → V} {S : Finset V}
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hε : 0 < ε) (hK : 2 ≤ K)
    (hSD : S ⊆ W \ W')
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
    (hXmult : ∀ a ∈ W', (((W \ W').filter (fun v => a ∈ X v \ resLink R W' v)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hW''W' : W'' ⊆ W') (hM : (16 : ℝ) / ε ≤ (W''.card : ℝ)) (Y : Finset V) :
    64 * (Y.filter (fun v =>
        ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
          ≤ ε / 8 * (W''.card : ℝ)))).card
      ≤ gridSize ε K * gridClassSize ε K W'.card := by
  classical
  have hK0 : 0 < K := by omega
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  set Sat : Finset V := Y.filter (fun v =>
    ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
      ≤ ε / 8 * (W''.card : ℝ))) with hSatdef
  set M : ℝ := (W''.card : ℝ) with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hone : (1 : ℝ) ≤ ε / 16 * M := by
    have h1 : ε / 16 * ((16 : ℝ) / ε) ≤ ε / 16 * M :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have h2 : ε / 16 * ((16 : ℝ) / ε) = 1 := by field_simp
    linarith
  -- every saturated vertex carries at least `ε M / 16` of the protected-level load
  have hlow : ∀ v ∈ Sat, ε / 16 * M
      ≤ ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) := by
    intro v hv
    have hvsat := (Finset.mem_filter.1 hv).2
    push_neg at hvsat
    have h8 : ε / 8 * M = 2 * (ε / 16 * M) := by ring
    linarith only [hvsat, hone]
  have hsumlow : (Sat.card : ℝ) * (ε / 16 * M)
      ≤ ∑ v ∈ Sat, ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) := by
    have := Finset.card_nsmul_le_sum Sat
      (fun v => ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ)) (ε / 16 * M) hlow
    simpa [nsmul_eq_mul, mul_comm] using this
  have hsumhigh := sum_protected_load_le hgrid hSD hmaps hinv hXmult hW''W' Sat
  have hcast : ((∑ v ∈ Sat, (S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℕ) : ℝ)
      = ∑ v ∈ Sat, ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) := by push_cast; rfl
  rw [hcast] at hsumhigh
  -- the perturbation of the links is at most a quarter of a class
  have hquarter : 8 * cleanEta ε K * (W.card : ℝ) ≤ (t : ℝ) :=
    eight_cleanEta_mul_card_le_twoSided hgrid hK0
  have hkey : (Sat.card : ℝ) * (ε / 16 * M) ≤ M * (2 * cleanEta ε K * (W.card : ℝ)) :=
    le_trans hsumlow hsumhigh
  have h1 : (Sat.card : ℝ) * (ε / 16) ≤ 2 * cleanEta ε K * (W.card : ℝ) := by
    have hrw : (Sat.card : ℝ) * (ε / 16 * M) = M * ((Sat.card : ℝ) * (ε / 16)) := by ring
    rw [hrw] at hkey
    exact le_of_mul_le_mul_left hkey hMpos
  have h2 : (Sat.card : ℝ) * ε ≤ 4 * (t : ℝ) := by nlinarith only [h1, hquarter]
  -- the grid is wide enough
  have h5 : (256 : ℝ) ≤ ε * (h : ℝ) := by
    have h3 : (64 : ℝ) * (K : ℝ) ^ 2 / ε ≤ (h : ℝ) := by rw [hhdef]; exact le_gridSize ε K
    have hKr : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have h6 : 64 * (K : ℝ) ^ 2 / ε * ε ≤ (h : ℝ) * ε := mul_le_mul_of_nonneg_right h3 hε.le
    rw [div_mul_cancel₀ _ (ne_of_gt hε)] at h6
    nlinarith
  have htnn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  have hfinal : (64 : ℝ) * (Sat.card : ℝ) ≤ (h : ℝ) * (t : ℝ) := by
    nlinarith only [h2, htnn, hε.le, h5]
  have : ((64 * Sat.card : ℕ) : ℝ) ≤ ((h * t : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-! ### The margin of the sweep, with a ledger -/

/-- **The budget of the sweep closes with a ledger.**  The cell competition (`Ncell ≤ h t / 64`),
the ledger (`SP ≤ h t / 16`), the saturated vertices (`ns ≤ h t / 64`) and the perturbation
(`n ≤ t / 4`) together fit in the margin `(2h - 1)c` of a two-sided design. -/
theorem twoSided_margin_ledger {h t q c n Ncell SP ns nb m : ℕ} (hh : 21 ≤ h)
    (hn : 4 * n ≤ t) (hcell : 64 * Ncell ≤ h * t) (hSP : 16 * SP ≤ h * t)
    (hns : 64 * ns ≤ h * t) (hnb : nb ≤ n) (hm : m ≤ Ncell + SP + n + (ns + nb))
    (hq3 : 3 * t ≤ 4 * q) (hqc : 3 * q ≤ 4 * c) :
    12 * n + 8 * m ≤ (2 * h - 1) * c := by
  have h16 : 9 * t ≤ 16 * c := by omega
  set h2 : ℕ := 2 * h - 1 with hh2def
  have hh2 : 2 * h = h2 + 1 := by omega
  have hh2big : 41 ≤ h2 := by omega
  have hA : 2 * (h * t) = h2 * t + t := by
    have hrw : 2 * (h * t) = (2 * h) * t := by ring
    rw [hrw, hh2]; ring
  have hB : 9 * (h2 * t) ≤ 16 * (h2 * c) := by
    calc 9 * (h2 * t) = h2 * (9 * t) := by ring
      _ ≤ h2 * (16 * c) := Nat.mul_le_mul_left _ h16
      _ = 16 * (h2 * c) := by ring
  have hC : 118 * t ≤ 3 * (h2 * t) := by
    calc 118 * t ≤ (3 * h2) * t := Nat.mul_le_mul_right t (by omega)
      _ = 3 * (h2 * t) := by ring
  set A : ℕ := h2 * t with hAdef
  set B : ℕ := h2 * c with hBdef
  set HT : ℕ := h * t with hHTdef
  omega

/-! ### The invariant of the sweep and the class-directed rule -/

/-- **The ledger invariant of the sweep**: every entry of the ledger is at most `h t / 16`. -/
def LedgerSpread (ε : ℝ) (K : ℕ) (W' : Finset V) (C : ℕ → Finset V) (X : V → Finset V)
    (x y : V → ℕ) (S : Finset V) (g : V → V → V) : Prop :=
  ∀ a ∈ W', ∀ P < gridSize ε K, ∀ Q < gridSize ε K,
    regionLoad (gridSize ε K) C X g S x y a P Q
      ≤ gridSize ε K * gridClassSize ε K W'.card / 16

/-- **One step of a spread discipline.**  The pairing chosen for the link of `u` must avoid a
forbidden edge set `U` of degree at most `m` inside the link — word for word the hypothesis of the
theorem `BKLO.exists_pairing_of_twoSided_link_avoiding`, which produces such a pairing from Dirac's
threshold — and must, in addition, maintain the invariant `J`. -/
def IsSpreadStep {V : Type} [DecidableEq V] (ε : ℝ) (K : ℕ) (W W' : Finset V)
    (F R : Finset (Sym2 V)) (X : V → Finset V) (c : ℕ)
    (J : Finset V → (V → V → V) → Prop) : Prop :=
  ∀ (S : Finset V) (g₀ : V → V → V) (u : V) (n m : ℕ) (U : Finset (Sym2 V)),
    u ∈ W \ W' → X u ⊆ W' → Even (X u).card →
    (X u \ resLink R W' u).card ≤ n → (resLink R W' u \ X u).card ≤ n →
    (∀ a ∈ X u, (resLink U (X u) a).card ≤ m) →
    12 * n + 8 * m ≤ (2 * gridSize ε K - 1) * c →
    S ⊆ W \ W' → u ∉ S →
    (∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w) → (∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b) →
    J S g₀ →
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧ (∀ a ∈ X u, p a ≠ a) ∧
      (∀ a ∈ X u, s(a, p a) ∈ F ∧ s(a, p a) ∉ U) ∧
      J (insert u S) (Function.update g₀ u p)

/-- **The class-directed pairing rule: the remaining residual of AX2 §10 at the two-sided grid
design.**

At a two-sided grid design there is a *spread discipline*: an invariant `J` of the pairings already
chosen which holds at the start of the sweep, which keeps every entry of the ledger below `h t / 16`
— no vertex is paired into the region of one cell of the grid too often — and which one more
pairing can always maintain, that pairing being subject to nothing else than the hypothesis of the
theorem `BKLO.exists_pairing_of_twoSided_link_avoiding` (a forbidden edge set of small degree
inside the link).

This is the whole of what is left: `BKLO.gridPairingResidualTwoSided_of_rule` derives §10 from it,
Dirac's threshold, the cell competition, the perturbation of the links and the protected level
being theorems.  The intended discipline is the least-loaded one — pair the row part of a link to
its column part (the two sides have exactly the same size, by
`IsGridTwoSidedReservoir.rowColBalanced`) and choose, for each vertex, a target class of least load
so far. -/
def TwoSidedClassDirectedRule : Prop :=
  ∀ {V : Type} [DecidableEq V] {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)}
    {C : ℕ → Finset V} {x y : V → ℕ} {q c : ℕ} (X : V → Finset V),
    IsGridTwoSidedReservoir ε K W W' W'' F R C x y →
    (∀ e ∈ F, ¬ e.IsDiag) → W' ⊆ W →
    (∀ i < gridSize ε K * gridSize ε K, (C i).card = q) →
    (∀ v ∈ W \ W', ∀ i ∈ gridIdx (gridSize ε K) (x v) (y v),
      (resLink R W' v ∩ C i).card = c) →
    3 * q ≤ 4 * c →
    ∃ J : Finset V → (V → V → V) → Prop,
      J (∅ : Finset V) (fun _ a => a) ∧
      (∀ S g, J S g → LedgerSpread ε K W' C X x y S g) ∧
      IsSpreadStep ε K W W' F R X c J

/-! ### One step of the sweep, from the rule -/

section Step

variable {V : Type} [DecidableEq V] {X : V → Finset V}

/-- **One more link is paired up, from the class-directed rule.**  Dirac's threshold, the
competition of `u`'s own cell, the perturbation of the links, the protected level and its load are
all discharged here: the rule is asked only for a pairing that keeps the ledger spread. -/
theorem twoSided_step_of_rule
    {ε : ℝ} {K : ℕ} {W W' W'' : Finset V} {F R : Finset (Sym2 V)} {C : ℕ → Finset V}
    {x y : V → ℕ} {q c : ℕ} {J : Finset V → (V → V → V) → Prop}
    (hJled : ∀ S g, J S g → LedgerSpread ε K W' C X x y S g)
    (hJstep : IsSpreadStep ε K W W' F R X c J)
    (hgrid : IsGridTwoSidedReservoir ε K W W' W'' F R C x y)
    (hq : ∀ i < gridSize ε K * gridSize ε K, (C i).card = q)
    (hqc : 3 * q ≤ 4 * c) (hW''W' : W'' ⊆ W')
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hK : 2 ≤ K)
    (hM : W''.Nonempty → (16 : ℝ) / ε ≤ (W''.card : ℝ))
    {u : V} (hu : u ∈ W \ W') (hXW' : X u ⊆ W') (hXeven : Even (X u).card)
    (hadd : ((X u \ resLink R W' u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hdel : ((resLink R W' u \ X u).card : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ))
    (hXmult : ∀ a ∈ W', (((W \ W').filter (fun v => a ∈ X v \ resLink R W' v)).card : ℝ)
      ≤ 2 * cleanEta ε K * (W.card : ℝ))
    {S : Finset V} (hSD : S ⊆ W \ W') (huS : u ∉ S) {g₀ : V → V → V}
    (hmaps : ∀ w ∈ S, ∀ b ∈ X w, g₀ w b ∈ X w)
    (hinv : ∀ w ∈ S, ∀ b ∈ X w, g₀ w (g₀ w b) = b)
    (hJ : J S g₀) :
    ∃ p : V → V, (∀ a ∈ X u, p a ∈ X u) ∧ (∀ a ∈ X u, p (p a) = a) ∧
      (∀ a ∈ X u, p a ≠ a) ∧ (∀ a ∈ X u, s(a, p a) ∈ F) ∧
      (∀ a ∈ X u, a ∉ W'' ∨ p a ∉ W'') ∧
      (∀ a ∈ X u, s(a, p a) ∉ usedPairs X g₀ S) ∧
      (∀ v ∈ W', v ∈ X u → p v ∈ W'' →
        ((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
          ≤ ε / 8 * (W''.card : ℝ)) ∧
      J (insert u S) (Function.update g₀ u p) := by
  classical
  set h : ℕ := gridSize ε K with hhdef
  set t : ℕ := gridClassSize ε K W'.card with htdef
  have hK0 : 0 < K := by omega
  have hhpos : 0 < h := gridSize_pos ε K
  have hwide : 6400 * (K * K) ≤ h := gridSize_ge_of_eps_small hε hε' K
  have hKK : 1 ≤ K * K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hK0.ne' hK0.ne')
  have hh21 : 21 ≤ h := by nlinarith only [hwide, hKK]
  have hhh : 0 < h * h := Nat.mul_pos hhpos hhpos
  have hq3 : 3 * t ≤ 4 * q := by
    have h1 := hgrid.classCardGe 0 hhh
    have h2 := hq 0 hhh
    rw [← htdef] at h1
    omega
  -- the perturbation
  set n : ℕ := max ((X u \ resLink R W' u).card) ((resLink R W' u \ X u).card) with hndef
  have hnr : (n : ℝ) ≤ 2 * cleanEta ε K * (W.card : ℝ) := by
    rcases max_cases ((X u \ resLink R W' u).card) ((resLink R W' u \ X u).card) with
      ⟨he, -⟩ | ⟨he, -⟩ <;> rw [hndef, he]
    · exact hadd
    · exact hdel
  have hn : 4 * n ≤ t := twoSided_perturbation_quarter hgrid hK0 hnr
  -- the competition of `u`'s own cell
  set Ncell : ℕ := ((W \ W').filter (fun w => x w = x u ∧ y w = y u)).card with hNdef
  have hcell : 64 * Ncell ≤ h * t := twoSided_cell_fibre_budget hgrid hε hε' hK0 (x u) (y u)
  -- the ledger and the saturated vertices
  set SP : ℕ := h * t / 16 with hSPdef
  have hSP : 16 * SP ≤ h * t := by
    have := Nat.div_mul_le_self (h * t) 16
    omega
  set ns : ℕ := h * t / 64 with hnsdef
  have hns : 64 * ns ≤ h * t := by
    have := Nat.div_mul_le_self (h * t) 64
    omega
  -- the forbidden edges of the protected level
  set Bad : Finset V := X u ∩ W'' with hBaddef
  set Sat : Finset V := (X u).filter (fun v =>
    ¬ (((S.filter (fun w => v ∈ X w ∧ g₀ w v ∈ W'')).card : ℝ) + 1
      ≤ ε / 8 * (W''.card : ℝ))) with hSatdef
  set Forb : Finset (Sym2 V) := crossStars Bad (fun _ => Sat ∪ Bad) with hForbdef
  set U : Finset (Sym2 V) := usedPairs X g₀ S ∪ Forb with hUdef
  have hbad : Bad.card ≤ n := card_inter_protected_le hgrid hu (le_max_left _ _)
  have hforb : ∀ a ∈ X u, (resLink Forb (X u) a).card ≤ ns + n := by
    intro a _
    by_cases hW''ne : W''.Nonempty
    · have hsat : Sat.card ≤ ns := by
        have hkey := twoSided_card_saturated_le hgrid hε hK hSD hmaps hinv hXmult hW''W'
          (hM hW''ne) (X u)
        rw [← hhdef, ← htdef, ← hSatdef] at hkey
        omega
      have h1 : (resLink Forb (X u) a).card ≤ ((Sat ∪ Bad) ∪ Bad).card :=
        card_resLink_crossStars_le Bad (Sat ∪ Bad) (X u) a
      have h2 : (Sat ∪ Bad) ∪ Bad = Sat ∪ Bad := by
        ext z; simp only [Finset.mem_union]; tauto
      rw [h2] at h1
      have h3 : (Sat ∪ Bad).card ≤ Sat.card + Bad.card := Finset.card_union_le _ _
      omega
    · have hempty : W'' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hW''ne
      have hBad0 : Bad = ∅ := by rw [hBaddef, hempty, Finset.inter_empty]
      have hForb0 : Forb = ∅ := by
        rw [hForbdef, hBad0]
        simp [crossStars]
      simp [hForb0, resLink]
  -- the used degree, from the ledger
  have hlink : resLink R W' u ⊆ gridRegion h C (x u) (y u) := fun z hz =>
    (Finset.mem_inter.1 (hgrid.linkSubset u hu hz)).2
  have hused : ∀ a ∈ X u, (resLink (usedPairs X g₀ S) (X u) a).card ≤ Ncell + SP + n := by
    intro a ha
    have h1 := card_resLink_usedPairs_region_split (D := W \ W') hmaps hinv hSD hlink (a := a)
    have h2 : regionLoad h C X g₀ S x y a (x u) (y u) ≤ SP := by
      have := hJled S g₀ hJ a (hXW' ha) (x u) (hgrid.rowLt u hu) (y u) (hgrid.colLt u hu)
      rw [← hhdef, ← htdef] at this
      exact this
    have h3 : (X u \ resLink R W' u).card ≤ n := le_max_left _ _
    omega
  have hUdeg : ∀ a ∈ X u, (resLink U (X u) a).card ≤ (Ncell + SP + n) + (ns + n) := by
    intro a ha
    have hsplit : resLink U (X u) a
        ⊆ resLink (usedPairs X g₀ S) (X u) a ∪ resLink Forb (X u) a := by
      intro z hz
      obtain ⟨hzX, hzU⟩ := mem_resLink.1 hz
      rcases Finset.mem_union.1 hzU with h1 | h1
      · exact Finset.mem_union_left _ (mem_resLink.2 ⟨hzX, h1⟩)
      · exact Finset.mem_union_right _ (mem_resLink.2 ⟨hzX, h1⟩)
    have h1 := hused a ha
    have h2 := hforb a ha
    have h3 := Finset.card_le_card hsplit
    have h4 := Finset.card_union_le (resLink (usedPairs X g₀ S) (X u) a) (resLink Forb (X u) a)
    omega
  have hmargin : 12 * n + 8 * ((Ncell + SP + n) + (ns + n)) ≤ (2 * h - 1) * c :=
    twoSided_margin_ledger hh21 hn hcell hSP hns (le_refl n) (le_refl _) hq3 hqc
  -- the rule
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5⟩ :=
    hJstep S g₀ u n ((Ncell + SP + n) + (ns + n)) U hu hXW' hXeven (le_max_left _ _)
      (le_max_right _ _) hUdeg hmargin hSD huS hmaps hinv hJ
  refine ⟨p, hp1, hp2, hp3, fun a ha => (hp4 a ha).1, ?_, ?_, ?_, hp5⟩
  · -- no pair inside the protected level
    intro a ha
    by_contra hcon
    push_neg at hcon
    obtain ⟨haW'', hpaW''⟩ := hcon
    refine (hp4 a ha).2 (Finset.mem_union_right _ ?_)
    exact crossStars_mem (Finset.mem_inter.2 ⟨ha, haW''⟩)
      (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hp1 a ha, hpaW''⟩))
  · -- the pairs avoid the edges already used
    intro a ha hcon
    exact (hp4 a ha).2 (Finset.mem_union_left _ hcon)
  · -- the protected-level load stays under budget
    intro v _ hvX hpv
    by_contra hcon
    have hvSat : v ∈ Sat := Finset.mem_filter.2 ⟨hvX, hcon⟩
    have hpvBad : p v ∈ Bad := Finset.mem_inter.2 ⟨hp1 v hvX, hpv⟩
    refine (hp4 v hvX).2 (Finset.mem_union_right _ ?_)
    have hmem : s(p v, v) ∈ Forb := crossStars_mem hpvBad (Finset.mem_union_left _ hvSat)
    rwa [Sym2.eq_swap] at hmem

end Step

/-! ### The sweep, the residual and the main theorem -/

/-- **The pairing clause at the two-sided design, from the class-directed rule.** -/
theorem gridPairingClauseTwoSided_of_rule (hrule : TwoSidedClassDirectedRule)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 100) {K : ℕ} (hK : 2 ≤ K) {f : ℕ → ℝ} {n₂ : ℕ}
    (hn₂ : (16 : ℝ) / ε ≤ (n₂ : ℝ)) : GridPairingClauseTwoSided ε f n₂ K := by
  intro V _ W W' W'' F R C x y X hn₂W hW'W hW''W' hKW' hW'K hKW'' hbig hFW hdiv hdegW hdegW'
    hres hRF hcross hsparse hsparse' hgrid hXW' hXF hXeven hXadd hXdel hXmult
  classical
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := fun e he => (mem_cliqueEdgesV.1 (hFW he)).2
  have hM : W''.Nonempty → (16 : ℝ) / ε ≤ (W''.card : ℝ) := by
    intro hne
    have h1 : (n₂ : ℝ) ≤ (W''.card : ℝ) := by exact_mod_cast hbig hne
    linarith
  obtain ⟨q, c, hq, hc, hqc, -⟩ := hgrid.exists_sizes
  obtain ⟨J, hJ0, hJled, hJstep⟩ := hrule X hgrid hnd hW'W hq hc hqc
  refine exists_pairedLinkCore_of_step_invariant (by positivity) J hJ0 ?_
  intro S hSD g₀ hmaps hinv hJ u huD huS
  obtain ⟨p, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    twoSided_step_of_rule hJled hJstep hgrid hq hqc hW''W' hε hε' hK hM huD
      (hXW' u huD) (hXeven u huD) (hXadd u huD) (hXdel u huD) hXmult hSD huS hmaps hinv hJ
  exact ⟨p, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **The remaining residual of AX2 §10 at the two-sided design, from the class-directed rule.** -/
theorem gridPairingResidualTwoSided_of_rule (hrule : TwoSidedClassDirectedRule) :
    GridPairingResidualTwoSided := by
  intro ε hε hε' K hK hKε
  refine ⟨⌈(16 : ℝ) / ε⌉₊, fun f n₂ hn₂ _hwin =>
    gridPairingClauseTwoSided_of_rule hrule hε hε' (by omega) ?_⟩
  have h1 : (16 : ℝ) / ε ≤ ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(16 : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn₂
  linarith

/-- **The §10 interface, from the class-directed rule.** -/
theorem vortexReservoirEngineR4_of_twoSidedClassDirectedRule (h : TwoSidedClassDirectedRule) :
    VortexReservoirEngineR4 :=
  vortexReservoirEngineR4_of_gridPairingResidualTwoSided (gridPairingResidualTwoSided_of_rule h)

/-- **Main theorem (AX2 half of Erdős #81), from the three classical inputs and the class-directed
pairing rule at the two-sided grid design.** -/
theorem triangle_decomposition_of_inputs_and_twoSidedClassDirectedRule
    (hDross : FracTriangleThreshold) (hNib : FracToApproxMaxDeg) (hDirac : PerfectMatchingDirac)
    (hRule : TwoSidedClassDirectedRule) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V →
        (3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)) →
        (9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        TriangleDecomposable G :=
  triangle_decomposition_of_inputs_and_gridPairingTwoSided hDross hNib hDirac
    (gridPairingResidualTwoSided_of_rule hRule)

end BKLO
