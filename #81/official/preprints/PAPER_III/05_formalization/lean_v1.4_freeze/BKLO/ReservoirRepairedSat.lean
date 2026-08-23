/-
# Non-vacuity of the **repaired** fused §10 interface.

The repair of `BKLO/ReservoirRepaired.lean` *adds* hypotheses to the reservoir clause and
*strengthens* its conclusion, so both directions have to be checked, exactly as
`BKLO/ReservoirSat.lean` checks them for the (false) original.

1. **The strengthened hypotheses are still satisfiable** — `reservoirClauseR_hypotheses_realizable`
   produces arbitrarily large configurations `W'' ⊆ W' ⊆ W`, `F` meeting *every* hypothesis of the
   repaired clause, including the new between-levels density, and with `W \ W'`, `W''` and
   `F ∩ cliqueEdges W''` nonempty.  So the repaired clause is still a genuine demand: the repair did
   not make it vacuously true.

2. **The strengthened conclusion is still attainable** — `isLinkCoverR_of_pairing` and
   `isLinkCoverR_empty` show that the two proved constructions of link covers already satisfy the
   added `W''`-scale damage bound, with room to spare: a cover built from a pairing avoiding `W''`
   uses *no* edge running into `W''` at all.  Together with `BKLO.isLinkCover_single_of_dirac`
   (Dirac's theorem supplies the pairing) this is the same evidence as for the original clause.

Everything here is `sorry`-free.
-/
import BKLO.ReservoirRepaired
import BKLO.ReservoirSat

open Finset

namespace BKLO

/-! ### The repaired link-cover conclusion is attainable -/

section Pairing

variable {V : Type*} [DecidableEq V]

/-- **A repaired link cover from a pairing.**  The cover of `BKLO.isLinkCover_of_pairing`, run with
the protected level removed from the ambient level, uses no edge running into `W''` at all, so it
meets the added damage bound at the scale of `W''` with room to spare. -/
theorem isLinkCoverR_of_pairing {F : Finset (Sym2 V)} {W' W'' X : Finset V} {u : V} {γ : ℝ}
    (g : V → V) (hg : ∀ a ∈ X, g a ∈ X) (hginv : ∀ a ∈ X, g (g a) = a)
    (hgne : ∀ a ∈ X, g a ≠ a)
    (hXW' : X ⊆ W') (huW' : u ∉ W') (hW''W' : W'' ⊆ W') (hXW'' : ∀ a ∈ X, a ∉ W'')
    (hXF : ∀ a ∈ X, s(u, a) ∈ F) (hgF : ∀ a ∈ X, s(a, g a) ∈ F)
    (hγ : (1 : ℝ) ≤ γ * ((W' \ W'').card : ℝ)) (hγ0 : 0 ≤ γ) :
    ∃ Q : Finset (Finset V), IsLinkCoverR F W' W'' {u} (fun _ => X) γ Q := by
  classical
  obtain ⟨Q, hQtri, hQcov, hQuse, hQdisj, hQdam⟩ :=
    isLinkCover_of_pairing (F := F) (W' := W' \ W'') (W'' := W'') (X := X) (u := u) (γ := γ)
      g hg hginv hgne (fun a ha => Finset.mem_sdiff.2 ⟨hXW' ha, hXW'' a ha⟩)
      (fun h => huW' (Finset.mem_sdiff.1 h).1) hXW'' hXF hgF hγ
  -- every edge of the cover that lies inside `W'` already lies inside `W' \ W''`
  have hinside : famEdges Q ∩ cliqueEdges W' ⊆ cliqueEdges (W' \ W'') := by
    intro e he
    obtain ⟨heQ, heW'⟩ := Finset.mem_inter.1 he
    rcases Finset.mem_union.1 (hQuse heQ) with hcross | hcl
    · obtain ⟨w, hw, a, -, rfl⟩ := mem_crossStars.1 hcross
      rw [Finset.mem_singleton] at hw
      subst hw
      exact absurd ((mem_cliqueEdgesV.1 heW').1 w (by simp)) huW'
    · exact hcl
  have hcardle : ((W' \ W'').card : ℝ) ≤ (W'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
  refine ⟨Q, ⟨hQtri, hQcov, ?_, hQdisj, ?_⟩, ?_⟩
  · exact hQuse.trans (Finset.union_subset_union_right (cliqueEdges_mono Finset.sdiff_subset))
  · -- the damage inside `W'`
    intro v hv
    have hmono : (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ)
        ≤ (edeg (famEdges Q ∩ cliqueEdges (W' \ W'')) v : ℝ) := by
      exact_mod_cast edeg_mono (Finset.subset_inter Finset.inter_subset_left hinside) v
    by_cases hvW'' : v ∈ W''
    · have hzero : edeg (famEdges Q ∩ cliqueEdges (W' \ W'')) v = 0 := by
        refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun e he => ?_)
        obtain ⟨heQ, hve⟩ := Finset.mem_filter.1 he
        have := (mem_cliqueEdgesV.1 (Finset.mem_inter.1 heQ).2).1 v hve
        exact (Finset.mem_sdiff.1 this).2 hvW''
      have hge : (0 : ℝ) ≤ γ * (W'.card : ℝ) := mul_nonneg hγ0 (Nat.cast_nonneg _)
      rw [hzero] at hmono
      have h0 : (edeg (famEdges Q ∩ cliqueEdges W') v : ℝ) ≤ 0 := by simpa using hmono
      linarith only [hge, h0]
    · have := hQdam v (Finset.mem_sdiff.2 ⟨hv, hvW''⟩)
      have hγW' : γ * ((W' \ W'').card : ℝ) ≤ γ * (W'.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcardle hγ0
      linarith only [hmono, this, hγW']
  · -- no edge of the cover runs into `W''`
    intro v hv
    have hempty : resLink (famEdges Q) W'' v = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun b hb => ?_
      obtain ⟨hbW'', hbe⟩ := mem_resLink.1 hb
      rcases Finset.mem_union.1 (hQuse hbe) with hcross | hcl
      · obtain ⟨w, hw, a, -, heq⟩ := mem_crossStars.1 hcross
        rw [Finset.mem_singleton] at hw
        subst hw
        have : w ∈ s(v, b) := by rw [heq]; simp
        rcases Sym2.mem_iff.1 this with rfl | rfl
        · exact huW' hv
        · exact huW' (hW''W' hbW'')
      · exact (Finset.mem_sdiff.1 ((mem_cliqueEdgesV.1 hcl).1 b (by simp))).2 hbW''
    rw [hempty]
    simpa using mul_nonneg hγ0 (Nat.cast_nonneg (W''.card))

/-- **The empty link system is covered by the empty family**, in the repaired sense too. -/
theorem isLinkCoverR_empty (F : Finset (Sym2 V)) (W' W'' D : Finset V) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsLinkCoverR F W' W'' D (fun _ => (∅ : Finset V)) γ ∅ := by
  classical
  refine ⟨isLinkCover_empty F W' W'' D hγ, fun v _ => ?_⟩
  have : resLink (famEdges (∅ : Finset (Finset V))) W'' v = ∅ := by
    simp [famEdges, resLink]
  rw [this]
  simpa using mul_nonneg hγ (Nat.cast_nonneg (W''.card))

end Pairing

/-! ### The repaired hypotheses are satisfiable -/

/-- In a complete graph, every vertex sees all of a set but possibly itself. -/
theorem card_resLink_cliqueEdges_univ {N : ℕ} (W' : Finset (Fin N)) (v : Fin N) :
    W'.card - 1 ≤ (resLink (cliqueEdges (Finset.univ : Finset (Fin N))) W' v).card := by
  classical
  have hsub : W'.erase v ⊆ resLink (cliqueEdges (Finset.univ : Finset (Fin N))) W' v := by
    intro a ha
    obtain ⟨hav, haW'⟩ := Finset.mem_erase.1 ha
    exact mem_resLink.2 ⟨haW', mem_cliqueEdgesV.2 ⟨fun x _ => Finset.mem_univ x, by
      simpa [Sym2.isDiag_iff_proj_eq] using (Ne.symm hav)⟩⟩
  exact le_trans Finset.pred_card_le_card_erase (Finset.card_le_card hsub)

set_option maxHeartbeats 1000000 in
/-- **The hypotheses of `ReservoirClauseR` are satisfiable.**  Same statement as
`BKLO.reservoirClause_hypotheses_realizable`, with the added between-levels density: the repaired
clause is still a genuine demand at each of its parts. -/
theorem reservoirClauseR_hypotheses_realizable {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10)
    {f : ℕ → ℝ} {n₂ K : ℕ} (hK : 2 ≤ K) (hf : ∀ s : ℕ, n₂ ≤ s → f s ≤ 9 / 10 + ε) (n₀ : ℕ) :
    ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
      n₀ ≤ W.card ∧ n₂ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
      K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
      F ⊆ cliqueEdges W ∧ TriDivisible F ∧
      (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
      (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) ∧
      (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) ∧
      (W \ W').Nonempty ∧ W''.Nonempty ∧ (F ∩ cliqueEdges W'').Nonempty := by
  classical
  have hKpos : 0 < K := by omega
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 / 10 - ε))
  set t : ℕ := max (max (n₀ + n₂ + k + 3) (4 * K * K)) ((n₂ + k) * K) with ht
  set N : ℕ := 6 * t + 3 with hN
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have htbig : n₀ + n₂ + k + 3 ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have htKK : 4 * K * K ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  have htmul : (n₂ + k) * K ≤ t := le_max_right _ _
  have hKKN : K * K * 1 < N := by simp only [hN]; linarith only [htKK]
  obtain ⟨-, -, -, hKm, hmm⟩ := vortex_next_level_sizes hK (le_refl 1) hKKN
  obtain ⟨W', hW'sub, hW'card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N))) (n := N / K)
      (by rw [hcard]; exact Nat.div_le_self _ _)
  obtain ⟨W'', hW''sub, hW''card⟩ :=
    Finset.exists_subset_card_eq (s := W') (n := (N / K) / K)
      (by rw [hW'card]; exact Nat.div_le_self _ _)
  have hW''le : K * ((N / K) / K) ≤ N / K := Nat.le.intro (Nat.div_add_mod (N / K) K)
  have hW''pos : 2 ≤ (N / K) / K := by
    rw [Nat.le_div_iff_mul_le hKpos, Nat.le_div_iff_mul_le hKpos]
    simp only [hN]; linarith only [htKK]
  have hNK1 : 1 ≤ N / K := by
    rcases Nat.eq_zero_or_pos (N / K) with h | h
    · rw [h] at hW''pos; simp at hW''pos
    · exact h
  have hlow : n₂ + k ≤ N / K := by
    rw [Nat.le_div_iff_mul_le hKpos]
    simp only [hN]; omega
  have hpos : (0 : ℝ) < 1 / 10 - ε := by linarith only [hε']
  have hkinv : (1 : ℝ) ≤ (1 / 10 - ε) * (k : ℝ) := by
    have h := hk.le
    rw [div_le_iff₀ hpos] at h
    linarith only [h]
  have hmain : ∀ x : ℝ, (k : ℝ) ≤ x → (9 / 10 + ε) * x ≤ x - 1 := by
    intro x hx
    nlinarith [hkinv, hpos]
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : 1 ≤ N := by omega
    push_cast [Nat.cast_sub h1]; ring
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    have : k ≤ N := by simp only [hN]; omega
    exact_mod_cast this
  have hk' : (k : ℝ) ≤ ((N / K : ℕ) : ℝ) := by
    have : k ≤ N / K := le_trans (Nat.le_add_left _ _) hlow
    exact_mod_cast this
  have hcast : (((N / K) - 1 : ℕ) : ℝ) = ((N / K : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub hNK1]; ring
  refine ⟨N, Finset.univ, W', W'', cliqueEdges (Finset.univ : Finset (Fin N)), ?_, ?_, hW'sub,
    hW''sub, ?_, ?_, ?_, Finset.Subset.refl _, triDivisible_cliqueEdges_univ (t := t) rfl, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hcard]; simp only [hN]; omega
  · rw [hcard]; simp only [hN]; omega
  · rw [hcard, hW'card]; exact hKm
  · rw [hcard, hW'card]; exact hmm
  · rw [hW'card, hW''card]; exact hW''le
  · -- minimum degree on `W`
    intro v _
    rw [edeg_cliqueEdges_of_mem (Finset.mem_univ v), hcard, hN1]
    have h1 := hmain (N : ℝ) hkN
    have h2 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith only [h1, h2, hε]
  · -- density inside `W'`
    intro v hv
    have hinter : cliqueEdges (Finset.univ : Finset (Fin N)) ∩ cliqueEdges W' = cliqueEdges W' :=
      Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
    rw [hinter, edeg_cliqueEdges_of_mem hv, hW'card, hcast]
    have hn₂ : n₂ ≤ N / K := le_trans (Nat.le_add_right _ _) hlow
    have hfle : f (N / K) ≤ 9 / 10 + ε := hf _ hn₂
    have h1 := hmain _ hk'
    have h2 : (0 : ℝ) ≤ ((N / K : ℕ) : ℝ) := by positivity
    nlinarith only [h1, h2, hfle]
  · -- the between-levels density: the complete graph joins every vertex to all of `W'`
    intro v _
    have h0 : (W'.card - 1 : ℕ)
        ≤ (resLink (cliqueEdges (Finset.univ : Finset (Fin N))) W' v).card :=
      card_resLink_cliqueEdges_univ W' v
    have h1 : ((W'.card - 1 : ℕ) : ℝ)
        ≤ ((resLink (cliqueEdges (Finset.univ : Finset (Fin N))) W' v).card : ℝ) := by
      exact_mod_cast h0
    rw [hW'card] at h1 ⊢
    rw [hcast] at h1
    have h2 := hmain _ hk'
    have h3 : (0 : ℝ) ≤ ((N / K : ℕ) : ℝ) := by positivity
    nlinarith only [h1, h2, h3, hε]
  · -- `W \ W'` is nonempty
    rw [Finset.sdiff_nonempty]
    intro hsub
    have hcle : (Finset.univ : Finset (Fin N)).card ≤ W'.card := Finset.card_le_card hsub
    rw [hcard, hW'card] at hcle
    have : N / K ≤ N / 2 := Nat.div_le_div_left hK (by omega)
    omega
  · rw [← Finset.card_pos, hW''card]; omega
  · have hinter : cliqueEdges (Finset.univ : Finset (Fin N)) ∩ cliqueEdges W'' = cliqueEdges W'' :=
      Finset.inter_eq_right.2 (cliqueEdges_mono (Finset.subset_univ _))
    rw [hinter]
    exact cliqueEdges_nonempty (by omega)

/-- **The reservoir clause supplied by the repaired interface is not vacuous.**  Whatever schedule,
thresholds, ratio and nibble parameter `VortexReservoirEngineR` produces, configurations satisfying
every hypothesis of its reservoir clause exist, arbitrarily large. -/
theorem vortexReservoirEngineR_reservoir_not_vacuous (hEng : VortexReservoirEngineR)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 10) (n₀ : ℕ) (Nthr : ℝ → ℕ) :
    ∃ (f : ℕ → ℝ) (n₂ C K : ℕ) (η : ℝ), 2 ≤ K ∧ 0 < η ∧ n₀ ≤ n₂ ∧ n₂ ≤ C ∧
      ReservoirClauseR ε η f n₂ K ∧
      ∃ (N : ℕ) (W W' W'' : Finset (Fin N)) (F : Finset (Sym2 (Fin N))),
        n₀ ≤ W.card ∧ n₂ ≤ W.card ∧ W' ⊆ W ∧ W'' ⊆ W' ∧
        K * W'.card ≤ W.card ∧ W.card ≤ K * K * W'.card ∧ K * W''.card ≤ W'.card ∧
        F ⊆ cliqueEdges W ∧ TriDivisible F ∧
        (∀ v ∈ W, (9 / 10 + ε / 4) * (W.card : ℝ) ≤ (edeg F v : ℝ)) ∧
        (∀ v ∈ W', f W'.card * (W'.card : ℝ) ≤ (edeg (F ∩ cliqueEdges W') v : ℝ)) ∧
        (∀ v ∈ W, (9 / 10 + ε / 4) * (W'.card : ℝ) ≤ ((resLink F W' v).card : ℝ)) ∧
        (W \ W').Nonempty ∧ W''.Nonempty ∧ (F ∩ cliqueEdges W'').Nonempty := by
  obtain ⟨f, n₂, C, K, η, hK, -, hη, hn₀, -, hn₂C, -, hfbd, -, -, hRes⟩ := hEng ε hε n₀ Nthr
  exact ⟨f, n₂, C, K, η, hK, hη, hn₀, hn₂C, hRes,
    reservoirClauseR_hypotheses_realizable hε hε' hK (fun s hs => (hfbd s hs).2) n₀⟩

end BKLO
