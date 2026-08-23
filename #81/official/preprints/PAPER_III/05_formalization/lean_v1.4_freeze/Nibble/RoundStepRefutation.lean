/-
# Nibble — REFUTATION of the single nibble round `NibbleRoundStep`

`Nibble.RoundOracleKernel.NibbleRoundStep` — the statement that was left as the sole remaining
obligation of the nibble (`nibbleRoundStep_holds`) — is **false**, and this file proves it:
`Nibble.not_nibbleRoundStep`.

The obstruction is again purely combinatorial (no probability), and it is again carried by the
complete bipartite witness `K_{m,8m}` of `Nibble.RoundProbRefutation` — but by a *counting*
argument which, unlike the one refuting `NibbleRoundProb`, survives an arbitrary pruning
`K' ⊆ residual K R'`.

Setting: `r = 2`, `V = hubs ⊎ leaves` with `m` hubs of degree `8m` and `8m` leaves of degree `m`, so
`L = m`, `U = 8m = 8L`, codegree `≤ 1 ≤ ecod·L`, `|V| = 9m`, `S = Exc = ∅`.  Write `M` for the round
matching, `k = |M|`, `C = support M`; every edge has exactly one hub and one leaf, so `M` covers
exactly `k` hubs and `k` leaves and `|C| = 2k`.  Counting the edges of `K'` from the two sides:

* **hub side (capacity).**  A covered hub has residual degree `0`, and every other hub obeys the new
  ceiling, so `|K'| ≤ (m - k)·(1/2+ε)·8m`.
* **leaf side (demand).**  Every uncovered leaf outside `Exc'` obeys the new floor, and there are at
  least `8m - k - |Exc'| ≥ 8m - k - 9δm` of them, so `(8m - k - 9δm)·(1/2-ε)·m ≤ |K'|`.

Combining and simplifying gives the **cover ceiling** `7·|C| ≤ (64ε + 18δ)·m`
(`Nibble.BipRef.bip_cover_le_of_step`): on this witness a round which halves the degree scale to
within a relative slack `ε` and spends at most `δ|V|` new exceptional vertices can cover only an
`O(ε + δ)` fraction of the vertices.  The reason is the `8 : 1` imbalance of the two sides: matching
one edge destroys `4m` units of hub capacity but only `m/2` units of leaf demand.

`NibbleRoundStep`, on the other hand, demands the *fixed* cover fraction `1/(256r) = 1/512` of the
`9m` good uncovered vertices for *every* `δ, ε > 0`.  With `δ = ε = 1/10000` the two are
incompatible (`7·9/512 = 0.123 > 0.0082 = 64ε + 18δ`), which refutes the statement.

What this means for the architecture: the per-round covering fraction of the ceiling oracle cannot
be a constant `1/(256r)` independent of the relative slack `ε` and of the exceptional-growth budget
`δ` while the degree band `[L, 8L]` allowed by `Nibble.CeilRoundInv` is that wide.  A repaired atom
has to let the covering fraction degrade with `ε` and `δ` (see `Nibble.NibbleRoundStepVar`), and the
outer loop of `Nibble.RoundOracleKernel` has to be re-parameterised accordingly.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.RoundProbRefutation

open Finset Hypergraph

namespace Nibble

namespace BipRef

/-! ## A one-sided handshake -/

/-- **Handshake along one side of a bipartition.**  If every edge of `K'` meets `W` in exactly one
vertex, then the degrees of `K'` on `W` add up to `|K'|`. -/
theorem sum_degree_eq_card_of_inter_one {V : Type*} [DecidableEq V] (K' : Finset (Finset V))
    (W : Finset V) (h : ∀ e ∈ K', (e ∩ W).card = 1) :
    ∑ v ∈ W, degree K' v = K'.card := by
  classical
  calc ∑ v ∈ W, degree K' v
      = ∑ v ∈ W, ∑ e ∈ K', (if v ∈ e then 1 else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [degree, Finset.card_filter]
    _ = ∑ e ∈ K', ∑ v ∈ W, (if v ∈ e then 1 else 0) := Finset.sum_comm
    _ = ∑ e ∈ K', (e ∩ W).card := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    _ = ∑ _e ∈ K', 1 := Finset.sum_congr rfl h
    _ = K'.card := by simp

/-! ## The cover ceiling forced by the bipartite witness -/

/-- **The cover ceiling on `K_{m,8m}`.**  Suppose a retained set `R' ⊆ K_{m,8m}` admits a
sub-hypergraph `K'` of its residual whose degrees are all `≤ (1/2+ε)·8m` and which has degree
`≥ (1/2-ε)·m` at every uncovered vertex outside an exceptional set of size `≤ δ·9m`.  Then the round
matching of `R'` covers at most `(64ε + 18δ)·m/7` vertices.

This is the two-sided edge count of the file header; it holds for *every* choice of `K'`, so no
pruning can evade it. -/
theorem bip_cover_le_of_step {m : ℕ} (hm : 1 ≤ m) {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε8 : ε ≤ 1 / 8)
    (hδ0 : 0 ≤ δ) {R' K' : Finset (Finset (BV m))} {Exc' : Finset (BV m)}
    (hR'K : R' ⊆ bipK m)
    (hK'res : K' ⊆ Hypergraph.residual (bipK m) R')
    (hceil : ∀ v : BV m, (degree K' v : ℝ) ≤ (1 / 2 + ε) * (8 * (m : ℝ)))
    (hExc' : (Exc'.card : ℝ) ≤ δ * (9 * (m : ℝ)))
    (hfloor : ∀ v : BV m, v ∉ support (roundMatching R') → v ∉ Exc' →
      (1 / 2 - ε) * (m : ℝ) ≤ (degree K' v : ℝ)) :
    7 * ((support (roundMatching R')).card : ℝ) ≤ (64 * ε + 18 * δ) * (m : ℝ) := by
  classical
  set M : Finset (Finset (BV m)) := roundMatching R' with hMdef
  set C : Finset (BV m) := support M with hCdef
  have hMdisj : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f :=
    (roundMatching_isMatching hR'K).disjoint
  have hMsub : M ⊆ bipK m := (roundMatching_subset R').trans hR'K
  -- the matching meets each side in exactly `|M|` vertices
  have hcA : (C ∩ hubs m).card = M.card := by
    refine card_support_inter M hMdisj (hubs m) (fun e he => ?_)
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hMsub he)
    rw [bipEdge_inter_hubs]; simp
  have hcB : (C ∩ leaves m).card = M.card := by
    refine card_support_inter M hMdisj (leaves m) (fun e he => ?_)
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hMsub he)
    rw [bipEdge_inter_leaves]; simp
  -- `C` is the disjoint union of its hub part and its leaf part
  have hCsplit : C.card = 2 * M.card := by
    have hdisj : Disjoint (C ∩ hubs m) (C ∩ leaves m) := by
      rw [Finset.disjoint_left]
      rintro v hv hv'
      have h1 : v ∈ hubs m := (Finset.mem_inter.1 hv).2
      have h2 : v ∈ leaves m := (Finset.mem_inter.1 hv').2
      cases v with
      | inl i => exact (inl_not_mem_leaves i) h2
      | inr j => exact (inr_not_mem_hubs j) h1
    have hunion : (C ∩ hubs m) ∪ (C ∩ leaves m) = C := by
      ext v
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro h
        cases v with
        | inl i => exact Or.inl ⟨h, by simp⟩
        | inr j => exact Or.inr ⟨h, by simp⟩
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, hcA, hcB] at this
    omega
  -- uncovered cardinalities on the two sides
  have hunA : (hubs m \ C).card + M.card = m := by
    rw [← hcA, Finset.inter_comm, Finset.card_sdiff_add_card_inter, card_hubs]
  have hunB : (leaves m \ C).card + M.card = 8 * m := by
    rw [← hcB, Finset.inter_comm, Finset.card_sdiff_add_card_inter, card_leaves]
  -- edge counts from the two sides
  have hK'K : K' ⊆ bipK m := hK'res.trans (Hypergraph.residual_subset _ _)
  have hhub1 : ∀ e ∈ K', (e ∩ hubs m).card = 1 := by
    intro e he
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hK'K he)
    rw [bipEdge_inter_hubs]; simp
  have hleaf1 : ∀ e ∈ K', (e ∩ leaves m).card = 1 := by
    intro e he
    obtain ⟨i, j, rfl⟩ := mem_bipK.1 (hK'K he)
    rw [bipEdge_inter_leaves]; simp
  have hsumhub : ∑ v ∈ hubs m, degree K' v = K'.card :=
    sum_degree_eq_card_of_inter_one K' (hubs m) hhub1
  have hsumleaf : ∑ v ∈ leaves m, degree K' v = K'.card :=
    sum_degree_eq_card_of_inter_one K' (leaves m) hleaf1
  -- a covered vertex has no edge of `K'`
  have hzero : ∀ v ∈ C, degree K' v = 0 := by
    intro v hv
    rw [degree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hve
    have hres : e ∈ Hypergraph.residual (bipK m) R' := hK'res he
    have hd : Disjoint e C := by
      simpa [Hypergraph.residual, covered, hMdef, hCdef] using (Finset.mem_filter.1 hres).2
    exact (Finset.disjoint_left.1 hd hve) hv
  -- HUB SIDE: the capacity bound
  have hupper : (K'.card : ℝ) ≤ (((hubs m \ C).card : ℝ)) * ((1 / 2 + ε) * (8 * (m : ℝ))) := by
    have hres : ∑ v ∈ hubs m \ C, degree K' v = ∑ v ∈ hubs m, degree K' v := by
      refine Finset.sum_subset Finset.sdiff_subset ?_
      intro v hv hv'
      have hvC : v ∈ C := by
        by_contra h
        exact hv' (Finset.mem_sdiff.2 ⟨hv, h⟩)
      exact hzero v hvC
    have hcast : (K'.card : ℝ) = ∑ v ∈ hubs m \ C, (degree K' v : ℝ) := by
      rw [← Nat.cast_sum, hres, hsumhub]
    rw [hcast]
    calc ∑ v ∈ hubs m \ C, (degree K' v : ℝ)
        ≤ ∑ _v ∈ hubs m \ C, ((1 / 2 + ε) * (8 * (m : ℝ))) :=
          Finset.sum_le_sum (fun v _ => hceil v)
      _ = (((hubs m \ C).card : ℝ)) * ((1 / 2 + ε) * (8 * (m : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- LEAF SIDE: the demand bound
  have hlower : ((((leaves m \ C).card : ℝ)) - (Exc'.card : ℝ)) * ((1 / 2 - ε) * (m : ℝ))
      ≤ (K'.card : ℝ) := by
    have hsub : (leaves m \ C) \ Exc' ⊆ leaves m := (Finset.sdiff_subset).trans Finset.sdiff_subset
    have hcast : (K'.card : ℝ) = ∑ v ∈ leaves m, (degree K' v : ℝ) := by
      rw [← Nat.cast_sum, hsumleaf]
    have hpart : ∑ v ∈ (leaves m \ C) \ Exc', (degree K' v : ℝ)
        ≤ ∑ v ∈ leaves m, (degree K' v : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => by positivity)
    have hfl : ∀ v ∈ (leaves m \ C) \ Exc', (1 / 2 - ε) * (m : ℝ) ≤ (degree K' v : ℝ) := by
      intro v hv
      rw [Finset.mem_sdiff, Finset.mem_sdiff] at hv
      exact hfloor v hv.1.2 hv.2
    have hbig : ((((leaves m \ C) \ Exc').card : ℝ)) * ((1 / 2 - ε) * (m : ℝ))
        ≤ ∑ v ∈ (leaves m \ C) \ Exc', (degree K' v : ℝ) := by
      calc ((((leaves m \ C) \ Exc').card : ℝ)) * ((1 / 2 - ε) * (m : ℝ))
          = ∑ _v ∈ (leaves m \ C) \ Exc', ((1 / 2 - ε) * (m : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ v ∈ (leaves m \ C) \ Exc', (degree K' v : ℝ) := Finset.sum_le_sum hfl
    have hcard : ((leaves m \ C).card : ℝ) - (Exc'.card : ℝ)
        ≤ ((((leaves m \ C) \ Exc').card : ℝ)) := by
      have h2 : (leaves m \ C).card ≤ ((leaves m \ C) \ Exc').card + Exc'.card :=
        Finset.card_le_card_sdiff_add_card
      have : ((leaves m \ C).card : ℝ) ≤ ((((leaves m \ C) \ Exc').card : ℝ)) + (Exc'.card : ℝ) := by
        exact_mod_cast h2
      linarith only [this]
    have hnn : (0 : ℝ) ≤ (1 / 2 - ε) * (m : ℝ) := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      nlinarith only [hε8]
    calc ((((leaves m \ C).card : ℝ)) - (Exc'.card : ℝ)) * ((1 / 2 - ε) * (m : ℝ))
        ≤ ((((leaves m \ C) \ Exc').card : ℝ)) * ((1 / 2 - ε) * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ ≤ ∑ v ∈ (leaves m \ C) \ Exc', (degree K' v : ℝ) := hbig
      _ ≤ ∑ v ∈ leaves m, (degree K' v : ℝ) := hpart
      _ = (K'.card : ℝ) := hcast.symm
  -- arithmetic
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) ≤ (M.card : ℝ) := Nat.cast_nonneg _
  have hA : (((hubs m \ C).card : ℝ)) = (m : ℝ) - (M.card : ℝ) := by
    have : (((hubs m \ C).card : ℝ)) + (M.card : ℝ) = (m : ℝ) := by exact_mod_cast hunA
    linarith only [this]
  have hB : (((leaves m \ C).card : ℝ)) = 8 * (m : ℝ) - (M.card : ℝ) := by
    have : (((leaves m \ C).card : ℝ)) + (M.card : ℝ) = 8 * (m : ℝ) := by exact_mod_cast hunB
    linarith only [this]
  have hC2 : ((C.card : ℝ)) = 2 * (M.card : ℝ) := by exact_mod_cast hCsplit
  rw [hC2]
  rw [hA] at hupper
  rw [hB] at hlower
  nlinarith [hupper, hlower, hExc', hkR, hmR, hε0, hδ0,
    mul_nonneg hε0 hkR, mul_nonneg hδ0 hε0, mul_nonneg (mul_nonneg hδ0 hε0) (le_trans zero_le_one hmR)]

end BipRef

/-! ## The refutation -/

open BipRef in
/-- **`NibbleRoundStep` is false.**  On the complete bipartite witness `K_{m,8m}` (which satisfies
every hypothesis: `2`-uniform, codegree `≤ 1 ≤ ecod·L`, all degrees `≤ U = 8m = 8L` and `≥ L = m`,
`S = Exc = ∅`) the two degree clauses force, by the two-sided edge count
`Nibble.BipRef.bip_cover_le_of_step`, the cover ceiling `7·|support M| ≤ (64ε + 18δ)·m`.  At
`δ = ε = 1/10000` this contradicts the demanded cover `(1/512)·9m ≤ |support M|`.

Hence the previously-intended remaining obligation `nibbleRoundStep_holds` cannot be proved; the
covering fraction of a round must be allowed to degrade with `ε` and `δ`. -/
theorem not_nibbleRoundStep : ¬ NibbleRoundStep := by
  intro hstep
  obtain ⟨ecod, hecod, L₀, hL₀, hmain⟩ :=
    hstep 2 le_rfl (1 / 10000) (1 / 10000) (by norm_num) (by norm_num) (by norm_num)
  -- a degree scale beyond both thresholds
  set m : ℕ := max 1 (max ⌈L₀⌉₊ ⌈1 / ecod⌉₊) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmL₀ : L₀ ≤ (m : ℝ) := by
    refine le_trans (Nat.le_ceil L₀) ?_
    exact_mod_cast le_trans (le_max_left _ _) (le_max_right 1 _)
  have hmecod : 1 ≤ ecod * (m : ℝ) := by
    have h1 : 1 / ecod ≤ (m : ℝ) := by
      refine le_trans (Nat.le_ceil (1 / ecod)) ?_
      exact_mod_cast le_trans (le_max_right _ _) (le_max_right 1 _)
    rw [div_le_iff₀ hecod] at h1
    linarith
  have hcodeg : CodegreeBounded (bipK m) (ecod * (m : ℝ)) := by
    intro x y hxy
    have h1 := codegree_bipK_le_one x y hxy
    have h2 : (codegree (bipK m) x y : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  have hdegU : ∀ v : BV m, (degree (bipK m) v : ℝ) ≤ 8 * (m : ℝ) := by
    rintro (i | j)
    · rw [degree_bipK_inl]; push_cast; linarith
    · rw [degree_bipK_inr]; linarith
  have hdegL : ∀ v : BV m, v ∉ (∅ : Finset (BV m)) → v ∉ (∅ : Finset (BV m)) →
      (m : ℝ) ≤ (degree (bipK m) v : ℝ) := by
    rintro (i | j) _ _
    · rw [degree_bipK_inl]; push_cast; linarith
    · rw [degree_bipK_inr]
  obtain ⟨R', hR'K, hcov, K', hK'res, hceil, Exc', hExc', hfloor⟩ :=
    hmain (bipK m) ∅ ∅ (m : ℝ) (8 * (m : ℝ)) hmL₀ (by linarith) (by linarith)
      (bipK_uniform m) hcodeg (by simp) hdegU hdegL
  -- the cover ceiling forced by the witness
  have hExc'R : ((Exc'.card : ℝ)) ≤ 1 / 10000 * (9 * (m : ℝ)) := by
    have hN : (Fintype.card (BV m) : ℝ) = 9 * (m : ℝ) := by
      rw [card_univ_BV]; push_cast; ring
    rw [hN] at hExc'
    simpa using hExc'
  have hceiling := bip_cover_le_of_step (m := m) hm1 (ε := 1 / 10000) (δ := 1 / 10000)
    (by norm_num) (by norm_num) (by norm_num) hR'K hK'res hceil hExc'R
    (fun v hv hv' => hfloor v (by simpa using hv) hv')
  -- but the cover clause demands a fixed fraction
  have hcovR : (1 / (256 * (2 : ℝ))) * (9 * (m : ℝ))
      ≤ ((support (roundMatching R')).card : ℝ) := by
    have hN : (Fintype.card (BV m) : ℝ) = 9 * (m : ℝ) := by
      rw [card_univ_BV]; push_cast; ring
    rw [hN] at hcov
    simpa using hcov
  norm_num at hceiling hcovR
  linarith

end Nibble
