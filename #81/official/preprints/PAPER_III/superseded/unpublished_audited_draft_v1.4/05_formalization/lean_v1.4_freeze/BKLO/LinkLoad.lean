/-
# The load of a perturbed link system, from the sparsity of the reservoir.

`BKLO.IsPairedLinkSystem` — the pairing form of the link-covering clause (c) of
`BKLO.ReservoirClauseR` — carries two bookkeeping fields besides the pairings themselves.  One of
them, `load`, says that each `v ∈ W'` lies in at most `γ|W'|` of the links `X u`.  It does not
mention the pairings at all: it is a property of the link system, and this file proves it.

A vertex `v ∈ W'` lies in the *reservoir* link of `u` exactly when `s(u, v) ∈ R`, and `u ↦ s(u, v)`
is injective on the outer vertices, so the number of outer vertices whose reservoir link contains
`v` is at most `edeg R v`.  The remaining outer vertices whose perturbed link contains `v` are
counted by the *global multiplicity bound* of the clause.  So

  `#{u : v ∈ X u} ≤ edeg R v + 2η|W|`,

and the reservoir built in `BKLO/ReservoirDesign.lean` has `edeg R v ≤ (ε/16)|W'|` for `v ∈ W'`,
while `2η|W| ≤ (ε/16)|W'|` at the scale `η = BKLO.reservoirEta ε K`.  Together they give exactly
the `γ = ε/8` budget the clause allows.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirDesign

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The outer vertices whose *reservoir* link contains `v` are counted by the reservoir degree at
`v`: the crossing edge `s(u, v)` determines `u`. -/
theorem card_filter_mem_resLink_le_edeg {D W' : Finset V} {R : Finset (Sym2 V)} {v : V}
    (hDW' : ∀ u ∈ D, u ∉ W') (hv : v ∈ W') :
    (D.filter (fun u => v ∈ resLink R W' u)).card ≤ edeg R v := by
  classical
  refine Finset.card_le_card_of_injOn (fun u => s(u, v)) ?_ ?_
  · intro u hu
    obtain ⟨huD, hvu⟩ := Finset.mem_filter.1 hu
    have hR : s(u, v) ∈ R := (mem_resLink.1 hvu).2
    exact Finset.mem_filter.2 ⟨hR, by simp⟩
  · intro u hu u' hu' heq
    have huD : u ∈ D := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).1
    have hu'D : u' ∈ D := (Finset.mem_filter.1 (Finset.mem_coe.1 hu')).1
    have hune : u ≠ v := fun h => hDW' u huD (h ▸ hv)
    rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 hune

/-- **The load bound of a paired link system, proved.**  If the reservoir is sparse at the scale of
`W'` and the link system obeys the global multiplicity bound of `BKLO.ReservoirClauseR`, then every
vertex of `W'` lies in at most `b + c` of the links. -/
theorem card_filter_mem_link_le {D W' : Finset V} {R : Finset (Sym2 V)} {X : V → Finset V}
    {b c : ℝ} (hDW' : ∀ u ∈ D, u ∉ W') {v : V} (hv : v ∈ W')
    (hsparse : (edeg R v : ℝ) ≤ b)
    (hmult : ((D.filter (fun u => v ∈ X u \ resLink R W' u)).card : ℝ) ≤ c) :
    ((D.filter (fun u => v ∈ X u)).card : ℝ) ≤ b + c := by
  classical
  have hsub : D.filter (fun u => v ∈ X u) ⊆
      D.filter (fun u => v ∈ resLink R W' u) ∪ D.filter (fun u => v ∈ X u \ resLink R W' u) := by
    intro u hu
    obtain ⟨huD, hvX⟩ := Finset.mem_filter.1 hu
    by_cases hvr : v ∈ resLink R W' u
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨huD, hvr⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨huD, Finset.mem_sdiff.2 ⟨hvX, hvr⟩⟩)
  have h1 : (D.filter (fun u => v ∈ X u)).card ≤
      (D.filter (fun u => v ∈ resLink R W' u)).card
        + (D.filter (fun u => v ∈ X u \ resLink R W' u)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have h2 := card_filter_mem_resLink_le_edeg (D := D) (W' := W') (R := R) hDW' hv
  have h3 : ((D.filter (fun u => v ∈ X u)).card : ℝ) ≤
      ((D.filter (fun u => v ∈ resLink R W' u)).card : ℝ)
        + ((D.filter (fun u => v ∈ X u \ resLink R W' u)).card : ℝ) := by exact_mod_cast h1
  have h4 : ((D.filter (fun u => v ∈ resLink R W' u)).card : ℝ) ≤ (edeg R v : ℝ) := by
    exact_mod_cast h2
  linarith only [hsparse, hmult, h3, h4]

/-- At the scale delivered by the grid design, the perturbation itself costs at most `(ε/16)|W'|`
per vertex: `2η|W| ≤ (ε/16)|W'|`. -/
theorem two_reservoirEta_mul_le {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 0 < K) {N m : ℕ}
    (hNm : N ≤ K * K * m) :
    2 * reservoirEta ε K * (N : ℝ) ≤ ε / 16 * (m : ℝ) := by
  set h : ℕ := gridSize ε K with hhdef
  have hhpos : 0 < h := gridSize_pos ε K
  have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK1r : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hεh : (64 : ℝ) * (K : ℝ) ^ 2 ≤ ε * (h : ℝ) := by
    have h1 := le_gridSize ε K
    have h2 : (64 : ℝ) * (K : ℝ) ^ 2 / ε * ε ≤ (h : ℝ) * ε :=
      mul_le_mul_of_nonneg_right h1 hε.le
    rw [div_mul_cancel₀] at h2
    · linarith only [h2]
    · exact ne_of_gt hε
  have hNr : (N : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) := by
    have : (N : ℝ) ≤ ((K * K * m : ℕ) : ℝ) := by exact_mod_cast hNm
    push_cast at this
    linarith only [this]
  have hden : (0 : ℝ) < 80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2 := by positivity
  have hηdef : reservoirEta ε K = 1 / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
    simp only [reservoirEta, hhdef]
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhpos
  have h64 : (64 : ℝ) ≤ ε * (h : ℝ) := by nlinarith only [hεh, hK1r]
  have hA : (0 : ℝ) ≤ (K : ℝ) ^ 2 * (m : ℝ) := by positivity
  have h1 : (64 : ℝ) * ((K : ℝ) ^ 2 * (m : ℝ)) ≤ (ε * (h : ℝ)) * ((K : ℝ) ^ 2 * (m : ℝ)) :=
    mul_le_mul_of_nonneg_right h64 hA
  have hεhA : (0 : ℝ) ≤ (ε * (h : ℝ)) * ((K : ℝ) ^ 2 * (m : ℝ)) := by positivity
  have h2 : (ε * (h : ℝ)) * ((K : ℝ) ^ 2 * (m : ℝ)) * 1
      ≤ (ε * (h : ℝ)) * ((K : ℝ) ^ 2 * (m : ℝ)) * (h : ℝ) :=
    mul_le_mul_of_nonneg_left hh1 hεhA
  have key : 2 * (N : ℝ) ≤ (ε / 16 * (m : ℝ)) * (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by
    linarith only [h1, h2, hNr, hA]
  rw [hηdef]
  calc 2 * (1 / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2)) * (N : ℝ)
      = (2 * (N : ℝ)) / (80 * (K : ℝ) ^ 2 * (h : ℝ) ^ 2) := by field_simp
    _ ≤ ε / 16 * (m : ℝ) := by rw [div_le_iff₀ hden]; exact key

/-- **The load field of `BKLO.IsPairedLinkSystem`, for the reservoir of the grid design.**  For
every link system `X` obeying the global multiplicity bound of `BKLO.ReservoirClauseR` at the scale
`η = BKLO.reservoirEta ε K`, every vertex of `W'` lies in at most `(ε/8)|W'|` of the links.  So the
only thing the residual `BKLO.ReservoirPairingResidual` still asks for, at the reservoir built in
`BKLO/ReservoirDesign.lean`, is the pairings themselves together with their edge-disjointness and
the bound `loadInner` at the scale of `W''`. -/
theorem link_load_of_reservoir_design {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 0 < K)
    {W W' : Finset V} {R : Finset (Sym2 V)} {X : V → Finset V}
    (hNm : W.card ≤ K * K * W'.card)
    (hsparse : ∀ a ∈ W', (edeg R a : ℝ) ≤ ε / 16 * (W'.card : ℝ))
    (hmult : ∀ a ∈ W', ((((W \ W').filter (fun u => a ∈ X u \ resLink R W' u)).card : ℝ)
      ≤ 2 * reservoirEta ε K * (W.card : ℝ))) :
    ∀ v ∈ W', (((W \ W').filter (fun u => v ∈ X u)).card : ℝ) ≤ ε / 8 * (W'.card : ℝ) := by
  intro v hv
  have hDW' : ∀ u ∈ W \ W', u ∉ W' := fun u hu => (Finset.mem_sdiff.1 hu).2
  have hbound := card_filter_mem_link_le (D := W \ W') (W' := W') (R := R) (X := X)
    hDW' hv (hsparse v hv) (hmult v hv)
  have hη := two_reservoirEta_mul_le (ε := ε) hε (K := K) hK (N := W.card) (m := W'.card) hNm
  linarith only [hbound, hη]

end BKLO
