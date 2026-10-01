import A4S1.DefectOneReduction
import PaperIV.FarRegimeAllGraphs

/-!
# Narrowing the residual case at rooted defect one: far regime and low-degree descent

`A4S1.DefectOneReduction` reduced the literal target `A4Sharp₁` to the rooted-defect-one
graphs that are neither apex-chordal nor chordal after `padBudget 1 n` deletions.  This module
removes two further classes, both unconditionally:

* **the far regime.**  If the fixed-`L = 4` fractional functional satisfies
  `F4'(G) < n²/6 - η n²` for a fixed `η > 0`, the universal mixed `K₃/K₄` far-regime rounding
  `PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` (no chordality) gives a
  partition with at most `M(n) ≤ Q₁(n)` pieces;
* **low-degree vertices.**  Rooted defect one is inherited by induced subgraphs
  (`rootedDefectAt_comap`), and `Q₁(n) = Q₁(n-1) + ⌊(n+2)/3⌋` (`defectTarget_one_succ`).  So a
  vertex of degree at most `⌊(n+2)/3⌋` can be deleted and its edges paid as `K₂` pieces
  (`target_of_lowDegree`).

What remains is `CriticalResidualAt η n`: the target for rooted-defect-one graphs that are
near-extremal for the fixed-`L = 4` functional, have minimum degree above `⌊(n+2)/3⌋`, are not
apex-chordal, and are not chordal after `padBudget 1 n` deletions.

The descent needs a base order.  `a4Sharp_one_of_critical` proves: for every `η > 0` there is
an explicit-in-terms-of-the-package threshold `N₀` such that, for every `N ≥ N₀`,
`TargetAt₁ N` together with `CriticalResidualAt η n` for all `n > N` implies `A4Sharp₁`.
Conversely `A4Sharp₁` gives both hypotheses from some order on (`critical_of_a4Sharp_one`).
Neither hypothesis is asserted anywhere.
-/

namespace A4S1.CriticalReduction

open Finset
open PaperIV.FarRounding
open PaperIV.DefectTargetArithmetic
open PaperIV.RootedSimplicialDefect
open PaperIV.DefectDeletionRoute
open PaperIV.DefectApexStability
open A4S1.DefectOneReduction

/-! ### Rooted defect is inherited along induced embeddings -/

section Heredity

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype V] [Fintype W] in
/-- **Heredity.**  If `H` is the graph induced by `G` along an embedding `e : W ↪ V`, then
rooted defect at most `s` passes from `G` to `H`. -/
theorem rootedDefectAt_comap (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ↪ V)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b))
    {s : ℕ} (hG : RootedDefectAt G s) : RootedDefectAt H s := by
  intro U' R' hRU hR hne
  have hRU' : R'.map e ⊆ U'.map e := Finset.map_subset_map.mpr hRU
  have hRcl : G.IsClique ((R'.map e : Finset V) : Set V) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact (hH a b).1 (hR ha hb (fun h => hxy (h ▸ rfl)))
  have hne' : (U'.map e \ R'.map e).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    rw [Finset.mem_sdiff] at ha
    exact ⟨e a, Finset.mem_sdiff.2 ⟨Finset.mem_map_of_mem e ha.1,
      fun h => ha.2 ((Finset.mem_map' e).1 h)⟩⟩
  obtain ⟨v, hv, C, hCsub, hCcl, hcard⟩ := hG (U'.map e) (R'.map e) hRU' hRcl hne'
  rw [Finset.mem_sdiff, Finset.mem_map] at hv
  obtain ⟨⟨v', hv'U, rfl⟩, hvR⟩ := hv
  have hv'R : v' ∉ R' := fun h => hvR (Finset.mem_map_of_mem e h)
  -- the neighbourhood maps onto the neighbourhood
  have hnbr : (neighborsIn H U' v').map e = neighborsIn G (U'.map e) (e v') := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [neighborsIn, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_map_of_mem e ha.1, (hH v' a).1 ha.2⟩
    · intro hy
      rw [neighborsIn, Finset.mem_filter, Finset.mem_map] at hy
      obtain ⟨⟨a, haU, rfl⟩, hadj⟩ := hy
      rw [Finset.mem_map]
      exact ⟨a, by rw [neighborsIn, Finset.mem_filter]; exact ⟨haU, (hH v' a).2 hadj⟩, rfl⟩
  set C' : Finset W := (neighborsIn H U' v').filter fun a => e a ∈ C with hC'
  have hC'map : C'.map e = C := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact (Finset.mem_filter.1 ha).2
    · intro hy
      have hy' := hCsub hy
      rw [← hnbr, Finset.mem_map] at hy'
      obtain ⟨a, ha, rfl⟩ := hy'
      exact Finset.mem_map_of_mem e (Finset.mem_filter.2 ⟨ha, hy⟩)
  refine ⟨v', Finset.mem_sdiff.2 ⟨hv'U, hv'R⟩, C', Finset.filter_subset _ _, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : e a ∈ C := (Finset.mem_filter.1 ha).2
    have hb' : e b ∈ C := (Finset.mem_filter.1 hb).2
    exact (hH a b).2 (hCcl ha' hb' (fun h => hab (e.injective h)))
  · have h1 : (neighborsIn H U' v').card = (neighborsIn G (U'.map e) (e v')).card := by
      rw [← hnbr, Finset.card_map]
    have h2 : C'.card = C.card := by rw [← hC'map, Finset.card_map]
    omega

end Heredity

/-! ### The one-step increment of `Q₁` -/

/-- **Exact increment.**  `Q₁(n+1) = Q₁(n) + ⌊(n+3)/3⌋`, i.e. at order `m` the increment
over order `m-1` is `⌊(m+2)/3⌋`. -/
theorem defectTarget_one_succ (n : ℕ) (hn : 1 ≤ n) :
    defectTarget 1 (n + 1) = defectTarget 1 n + (n + 1 + 2) / 3 := by
  rw [A4S1.ApexSharp.defectTarget_one_eq, A4S1.ApexSharp.defectTarget_one_eq]
  have h1 := A4S1.ApexSharp.six_mul_div_six n
  have h2 := A4S1.ApexSharp.six_mul_div_six (n + 1)
  have hring : (n + 1 + 1) * (n + 1 + 2) = (n + 1) * (n + 2) + 2 * (n + 2) := by ring
  have hX6 : 6 ≤ (n + 1) * (n + 2) := by nlinarith
  rw [hring] at h2 ⊢
  have hmod : (n + 1) % 3 = 0 ↔ n % 3 = 2 := by omega
  generalize (n + 1) * (n + 2) = X at h1 h2 hX6 ⊢
  by_cases h0 : n % 3 = 0
  · have h0' : ¬ (n + 1) % 3 = 0 := by omega
    rw [if_pos h0] at h1
    rw [if_neg h0'] at h2
    omega
  · rw [if_neg h0] at h1
    by_cases h0' : (n + 1) % 3 = 0
    · rw [if_pos h0'] at h2
      omega
    · rw [if_neg h0'] at h2
      omega

/-! ### Low-degree descent -/

/-- The literal target at one order. -/
def TargetAt₁ (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G 1 →
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n

/-- **Low-degree descent.**  If the target holds at order `n`, then every rooted-defect-one
graph of order `n+1` with a vertex of degree at most `⌊(n+3)/3⌋` satisfies the target. -/
theorem target_of_lowDegree {n : ℕ} (hn : 1 ≤ n) (ht : TargetAt₁ n)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hdef : RootedDefectAt G 1)
    (v : Fin (n + 1)) (hv : G.degree v ≤ (n + 1 + 2) / 3) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 (n + 1) := by
  classical
  set D : Finset (Fin (n + 1)) := {v} with hDdef
  have hDs : D.card = 1 := Finset.card_singleton v
  set n' := (Dᶜ).card with hn'
  have hn'eq : n' = n := by rw [hn', Finset.card_compl, Fintype.card_fin, hDs]; omega
  let e : Fin n' ↪ Fin (n + 1) := ((Dᶜ).orderEmbOfFin hn'.symm).toEmbedding
  have he : ∀ y, y ∉ D ↔ ∃ a, e a = y := by
    intro y
    have hr := Finset.range_orderEmbOfFin (Dᶜ) hn'.symm
    constructor
    · intro hy
      have hy' : y ∈ Set.range ((Dᶜ).orderEmbOfFin hn'.symm) := by
        rw [hr]; simpa using hy
      obtain ⟨a, ha⟩ := hy'
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (Dᶜ) hn'.symm a)
  let H : SimpleGraph (Fin n') := G.comap e
  haveI : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G.Adj (e a) (e b)))
  have hH : ∀ a b, H.Adj a b ↔ G.Adj (e a) (e b) := fun a b => Iff.rfl
  have hHdef : RootedDefectAt H 1 := rootedDefectAt_comap G e H hH hdef
  have ht' : TargetAt₁ n' := hn'eq ▸ ht
  obtain ⟨QH, hQH4, hQHsize⟩ := ht' H hHdef
  obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH QH hQH4
  obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
  rw [sdiff_avoidPart] at hPs
  have hT : (G.edgeFinset.filter (Touches D)).card = G.degree v := by
    rw [A4S1.DefectOneAbsorbed.card_touch_singleton, SimpleGraph.card_neighborFinset_eq_degree]
  refine ⟨P, hP4, ?_⟩
  rw [defectTarget_one_succ n hn]
  have hQHn : QH.size ≤ defectTarget 1 n := by rw [← hn'eq]; exact hQHsize
  omega

/-! ### The critical residual and the reduction -/

/-- **The critical residual case (open).**  The literal target at order `n` for rooted
defect-one graphs that are near-extremal for the fixed-`L = 4` functional
(`F4'(G) ≥ n²/6 - η n²`), have minimum degree above `⌊(n+2)/3⌋`, are not apex-chordal, and
are not chordal after deleting at most `padBudget 1 n` edges. -/
def CriticalResidualAt (η : ℚ) (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G 1 →
    (n : ℝ) ^ 2 / 6 - (η : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    (∀ v : Fin n, (n + 2) / 3 < G.degree v) →
    (∀ x : Fin n, ¬ (G.induce (({x}ᶜ : Finset (Fin n)) : Set (Fin n))).IsChordal) →
    (∀ H : SimpleGraph (Fin n), H ≤ G → H.IsChordal →
        padBudget 1 n < (G.edgeSet \ H.edgeSet).ncard) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n

/-- The four closed classes at a single large order: far regime, apex-chordal, chordal
after `padBudget` deletions; everything else is critical once low degrees are excluded. -/
theorem target_step (η : ℚ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → TargetAt₁ n → CriticalResidualAt η (n + 1) →
      TargetAt₁ (n + 1) := by
  classical
  obtain ⟨Nf, hNf⟩ := PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs η hη
  obtain ⟨Na, hNa⟩ := A4S1.ApexSharp.apex_chordal_sharp
  obtain ⟨Nc, hNc⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨Nf + Na + Nc + 2, ?_⟩
  intro n hn ht hcrit G _ hdef
  have hnf : Nf ≤ n + 1 := by omega
  have hna : Na ≤ n + 1 := by omega
  have hnc : Nc ≤ n + 1 := by omega
  have hn2 : 2 ≤ n + 1 := by omega
  -- far regime
  by_cases hfar : PaperIV.VertexCopyGate.F4' G <
      ((n + 1 : ℕ) : ℝ) ^ 2 / 6 - (η : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
  · obtain ⟨Q, hQ4, hQs⟩ := hNf (n + 1) hnf G hfar
    refine ⟨Q, hQ4, le_trans hQs ?_⟩
    exact targetSize_le_defectTarget 1 (n + 1) hn2
  push_neg at hfar
  -- apex-chordal
  by_cases hapex : ∃ x : Fin (n + 1),
      (G.induce (({x}ᶜ : Finset (Fin (n + 1))) : Set (Fin (n + 1)))).IsChordal
  · obtain ⟨x, hx⟩ := hapex
    exact hNa (n + 1) hna G x hx
  push_neg at hapex
  -- chordal after few deletions
  by_cases hdel : ∃ H : SimpleGraph (Fin (n + 1)), H ≤ G ∧ H.IsChordal ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ padBudget 1 (n + 1)
  · obtain ⟨H, hHG, hHch, hHcard⟩ := hdel
    letI : DecidableRel H.Adj := Classical.decRel _
    obtain ⟨QH, hQH4, hQHsize⟩ := hNc (n + 1) hnc H hHch
    obtain ⟨Q, hQ4, hQsize⟩ :=
      PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph G H hHG QH hQH4
    refine ⟨Q, hQ4, ?_⟩
    have hcard : (G.edgeSet \ H.edgeSet).ncard = (G.edgeFinset \ H.edgeFinset).card := by
      have hset : G.edgeSet \ H.edgeSet =
          ((G.edgeFinset \ H.edgeFinset : Finset (Sym2 (Fin (n + 1)))) :
            Set (Sym2 (Fin (n + 1)))) := by
        ext e
        simp
      rw [hset, Set.ncard_coe_finset]
    have hbudget : (G.edgeFinset \ H.edgeFinset).card ≤ padBudget 1 (n + 1) := by
      rw [← hcard]; exact hHcard
    calc Q.size ≤ QH.size + (G.edgeFinset \ H.edgeFinset).card := hQsize
      _ ≤ PaperIV.targetSize (n + 1) + padBudget 1 (n + 1) := Nat.add_le_add hQHsize hbudget
      _ = defectTarget 1 (n + 1) := targetSize_add_padBudget 1 (n + 1) hn2
  push_neg at hdel
  -- a low-degree vertex
  by_cases hlow : ∃ v : Fin (n + 1), G.degree v ≤ (n + 1 + 2) / 3
  · obtain ⟨v, hv⟩ := hlow
    exact target_of_lowDegree (by omega) ht G hdef v hv
  push_neg at hlow
  exact hcrit G hdef (by exact_mod_cast hfar) hlow hapex hdel

/-- **Reduction to the critical residual.**  For every `η > 0` there is `N₀` such that for
every base order `N ≥ N₀`: the target at order `N` and the critical residual case at every
larger order imply the full literal target `A4Sharp₁`. -/
theorem a4Sharp_one_of_critical (η : ℚ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → TargetAt₁ N → (∀ n : ℕ, N < n → CriticalResidualAt η n) →
      A4Sharp₁ := by
  obtain ⟨N₀, hstep⟩ := target_step η hη
  refine ⟨N₀, ?_⟩
  intro N hN hbase hcrit
  have hall : ∀ n : ℕ, N ≤ n → TargetAt₁ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih => exact hstep m (le_trans hN hm) ih (hcrit (m + 1) (by omega))
  exact ⟨N, fun n hn G _ hdef => hall n hn G hdef⟩

/-- Conversely, the full target supplies both hypotheses from some order on. -/
theorem critical_of_a4Sharp_one (η : ℚ) (h : A4Sharp₁) :
    ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      TargetAt₁ N' ∧ ∀ n : ℕ, N' < n → CriticalResidualAt η n := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun N' hN' => ⟨fun G _ hdef => hN N' hN' G hdef,
    fun n hn G _ hdef _ _ _ _ => hN n (by omega) G hdef⟩⟩

end A4S1.CriticalReduction
