import E33.Assembly

/-!
# E33 — the existential input reduced to an `s`-free removal statement

* `NK t k δ` — the explicit threshold of Erdős's theorem for `k`-partite `k`-graphs, read off
  from the recursion in the proof of `PaperIV.ErdosKPartite.erdos_kpartite`:
  `NK t 0 δ = 0`, `NK t (k+1) δ = max (NK t k (δ/2·(δ/4)^t)) (⌈4t/δ⌉ + t + 1)`.
* `erdos_kpartite_explicit`, `lemmaK_explicit` — the same proofs, with the witness kept.
  Hence Lemma K (few induced `C_k` under rooted defect `s`) is **explicit**.
* **`CycleRemovalExplicit Nrem Krem drem`** — the induced removal lemma for the family
  `{C_k : k ≥ 4}` with explicit parameter functions of `ε` alone (no `s`).  This is the
  exact content of the formal Alon–Shapira input that remains existential;
  `exists_cycleRemovalExplicit` shows it is satisfiable (non-explicitly).
* `editApproxExplicit_of_removal` — `CycleRemovalExplicit` gives `EditApproxExplicit` with
  the explicit `NeditOfRem Nrem Krem drem s δ = max (Nrem δ) (max_{k ≤ Krem δ} NK (s+1) k (drem δ))`.
* **`theoremC_of_removal`** — Theorem C above the threshold
  `Fexp (NeditOfRem Nrem Krem drem) s`, explicit in `s` given the three `s`-free functions.
-/

namespace E33

open Finset PaperIV.ErdosKPartite PaperIV.EditRoute PaperIV.RootedSimplicialDefect
  PaperIV.FarRounding PaperIV.DefectTargetArithmetic

/-- The explicit threshold of Erdős's `k`-partite theorem (parts of size `t`, density `δ`). -/
noncomputable def NK (t : ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | k + 1, δ => max (NK t k (δ / 2 * (δ / 4) ^ t)) (⌈4 * (t : ℝ) / δ⌉₊ + t + 1)

/-- **Erdős's theorem for `k`-partite `k`-graphs with the explicit threshold `NK`**
(the proof of `PaperIV.ErdosKPartite.erdos_kpartite`, keeping the witness). -/
theorem erdos_kpartite_explicit (t : ℕ) : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∀ n ≥ NK t k δ,
    ∀ E : Finset (Fin k → Fin n), δ * (n : ℝ) ^ k ≤ E.card →
      ∃ W : Fin k → Finset (Fin n), (∀ i, (W i).card = t) ∧ Covers E W := by
  intro k
  induction k with
  | zero =>
    intro δ hδ n _ E hE
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro f _
    have hpos : 0 < E.card := by
      have : (0 : ℝ) < E.card := by simp at hE; linarith
      exact_mod_cast this
    obtain ⟨g, hg⟩ := card_pos.mp hpos
    have : f = g := funext (fun i => i.elim0)
    rw [this]; exact hg
  | succ k ih =>
    intro δ hδ
    set δ' : ℝ := δ / 2 * (δ / 4) ^ t with hδ'
    have hδ'pos : 0 < δ' := by positivity
    have hN' := ih δ' hδ'pos
    intro n hn E hE
    have hn : max (NK t k δ') (⌈4 * (t : ℝ) / δ⌉₊ + t + 1) ≤ n := hn
    set N' := NK t k δ' with hN'def
    have hnN' : N' ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : ⌈4 * (t : ℝ) / δ⌉₊ + t + 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : 1 ≤ n := by omega
    have htn : t ≤ n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnt : 4 * (t : ℝ) ≤ δ * n := by
      have h1 : 4 * (t : ℝ) / δ ≤ ⌈4 * (t : ℝ) / δ⌉₊ := Nat.le_ceil _
      have hc : ⌈4 * (t : ℝ) / δ⌉₊ ≤ n := by omega
      have h2 : ((⌈4 * (t : ℝ) / δ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
      have h3 : 4 * (t : ℝ) / δ ≤ n := le_trans h1 h2
      rw [div_le_iff₀ hδ] at h3
      linarith
    -- the prefixes of large degree
    set a : ℕ := ⌈δ * n / 2⌉₊ with ha
    set X := (univ : Finset (Fin k → Fin n)).filter (fun x => a ≤ (nbhd E x).card) with hX
    have hcardX : δ / 2 * (n : ℝ) ^ k ≤ X.card := by
      have hsplit := (sum_filter_add_sum_filter_not (univ : Finset (Fin k → Fin n))
        (fun x => a ≤ (nbhd E x).card) (fun x => ((nbhd E x).card : ℝ)))
      have hin : ∑ x ∈ X, ((nbhd E x).card : ℝ) ≤ X.card * n := by
        have := sum_le_card_nsmul X (fun x => ((nbhd E x).card : ℝ)) n (fun x _ => by
          show ((nbhd E x).card : ℝ) ≤ n
          have : (nbhd E x).card ≤ n := by
            calc (nbhd E x).card ≤ (univ : Finset (Fin n)).card := card_le_univ _
              _ = n := by simp
          exact_mod_cast this)
        simpa using this
      have hout : ∑ x ∈ (univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card),
          ((nbhd E x).card : ℝ) ≤ (n : ℝ) ^ k * (δ * n / 2) := by
        have hb := sum_le_card_nsmul ((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card))
          (fun x => ((nbhd E x).card : ℝ)) (δ * n / 2) (fun x hx => by
            show ((nbhd E x).card : ℝ) ≤ δ * n / 2
            have hlt : (nbhd E x).card < a := by simpa using (mem_filter.mp hx).2
            exact (Nat.lt_ceil.mp hlt).le)
        have hc : (((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card)).card : ℝ) ≤
            (n : ℝ) ^ k := by
          have : ((univ : Finset (Fin k → Fin n)).filter (fun x => ¬ a ≤ (nbhd E x).card)).card ≤ n ^ k := by
            calc _ ≤ (univ : Finset (Fin k → Fin n)).card := card_filter_le _ _
              _ = n ^ k := by simp
          exact_mod_cast this
        simp only [nsmul_eq_mul] at hb
        have hdn : 0 ≤ δ * n / 2 := by positivity
        nlinarith
      have hE' : (E.card : ℝ) ≤ ∑ x : Fin k → Fin n, ((nbhd E x).card : ℝ) := by
        exact_mod_cast card_le_sum_nbhd E
      have hEk : δ * (n : ℝ) ^ (k + 1) ≤ X.card * n + (n : ℝ) ^ k * (δ * n / 2) := by
        rw [← hX] at hsplit; linarith
      have hpk : (n : ℝ) ^ (k + 1) = (n : ℝ) ^ k * n := pow_succ _ _
      rw [hpk] at hEk
      nlinarith
    -- double counting and pigeonhole over the `t`-subsets of the last class
    have hsumX : (X.card : ℝ) * (a.choose t : ℝ) ≤
        ∑ T ∈ (univ : Finset (Fin n)).powersetCard t, ((link E T).card : ℝ) := by
      have hlink := sum_card_link E t
      have hge : (X.card : ℝ) * (a.choose t : ℝ) ≤ ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) := by
        calc (X.card : ℝ) * (a.choose t : ℝ) = ∑ x ∈ X, (a.choose t : ℝ) := by simp
          _ ≤ ∑ x ∈ X, (((nbhd E x).card).choose t : ℝ) := sum_le_sum (fun x hx => by
              exact_mod_cast Nat.choose_le_choose t (mem_filter.mp hx).2)
          _ ≤ ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      have : (∑ T ∈ (univ : Finset (Fin n)).powersetCard t, ((link E T).card : ℝ)) =
          ∑ x : Fin k → Fin n, (((nbhd E x).card).choose t : ℝ) := by exact_mod_cast hlink
      linarith
    have hratio := choose_ratio (n := n) hδ (a := a) (t := t) (Nat.le_ceil _) hnt
    obtain ⟨T, hT, hTcard⟩ : ∃ T ∈ (univ : Finset (Fin n)).powersetCard t,
        δ' * (n : ℝ) ^ k ≤ (link E T).card := by
      by_contra hno
      push_neg at hno
      have hne : ((univ : Finset (Fin n)).powersetCard t).Nonempty :=
        powersetCard_nonempty.mpr (by simpa using htn)
      have hlt := sum_lt_sum_of_nonempty hne hno
      rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      have hA : 0 ≤ (a.choose t : ℝ) := by positivity
      have hkey : δ' * (n : ℝ) ^ k * (n.choose t : ℝ) ≤ (X.card : ℝ) * (a.choose t : ℝ) := by
        rw [hδ']
        have hnk : 0 ≤ (n : ℝ) ^ k := by positivity
        calc δ / 2 * (δ / 4) ^ t * (n : ℝ) ^ k * (n.choose t : ℝ)
            = δ / 2 * (n : ℝ) ^ k * ((δ / 4) ^ t * (n.choose t : ℝ)) := by ring
          _ ≤ δ / 2 * (n : ℝ) ^ k * (a.choose t : ℝ) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
          _ ≤ (X.card : ℝ) * (a.choose t : ℝ) := mul_le_mul_of_nonneg_right hcardX hA
      linarith
    obtain ⟨hTsub, hTt⟩ := mem_powersetCard.mp hT
    obtain ⟨W', hW'card, hW'cov⟩ := hN' n hnN' (link E T) hTcard
    refine ⟨Fin.snoc (α := fun _ => Finset (Fin n)) W' T, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]; exact hTt
      · simp only [Fin.snoc_castSucc]; exact hW'card j
    · intro f hf
      have hx : Fin.init f ∈ link E T := hW'cov (Fin.init f) (fun j => by
        have := hf j.castSucc
        simpa [Fin.init, Fin.snoc_castSucc] using this)
      have hlast : f (Fin.last k) ∈ T := by
        have := hf (Fin.last k)
        simpa [Fin.snoc_last] using this
      have hmem := (mem_filter.mp hx).2 hlast
      simp only [nbhd, mem_filter, mem_univ, true_and, Fin.snoc_init_self] at hmem
      exact hmem

/-- **Lemma K with the explicit threshold `NK (s+1) k δ`.** -/
theorem lemmaK_explicit (s k : ℕ) (hk : 4 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n ≥ NK (s + 1) k δ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
      ((cycTuples G k).card : ℝ) < δ * (n : ℝ) ^ k := by
  classical
  have hN := erdos_kpartite_explicit (s + 1) k δ hδ
  intro n hn G _ hG
  by_contra hlt
  push_neg at hlt
  obtain ⟨W, hWcard, hWcov⟩ := hN n hn (cycTuples G k) hlt
  have hne : ∀ l, (W l).Nonempty := fun l => card_pos.mp (by rw [hWcard l]; omega)
  have hmem : ∀ f : Fin k → Fin n, (∀ l, f l ∈ W l) →
      Function.Injective f ∧ ∀ i j, G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph k).Adj i j := fun f hf =>
    (mem_filter.mp (hWcov f hf)).2
  have hk2 : 2 ≤ k := by omega
  -- the parts, indexed by naturals as Lemma B expects
  let P : ℕ → Finset (Fin n) := fun i => if h : i < k then W ⟨i, h⟩ else ∅
  have hP : ∀ i (h : i < k), P i = W ⟨i, h⟩ := fun i h => by simp [P, h]
  apply noBlowup_of_rootedDefect hk P _ _ _ _ hG
  · intro i hi; rw [hP i hi, hWcard]
  · intro i hi j hj hij
    rw [hP i hi, hP j hj, Finset.disjoint_left]
    intro w hwi hwj
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hwi hwj (Or.inr rfl)
    have := (hmem f hf).1 (hfi.trans hfj.symm)
    exact hij (by simpa using congrArg Fin.val this)
  · intro i hi x hx y hy
    have hi' : (i + 1) % k < k := Nat.mod_lt _ (by omega)
    rw [hP i hi] at hx
    rw [hP _ hi'] at hy
    have hne' : (⟨i, hi⟩ : Fin k) ≠ ⟨(i + 1) % k, hi'⟩ := by
      intro h
      have h' := congrArg Fin.val h
      simp only at h'
      rcases Nat.lt_or_ge (i + 1) k with hlt' | hge
      · rw [Nat.mod_eq_of_lt hlt'] at h'; omega
      · have : i + 1 = k := by omega
        rw [this, Nat.mod_self] at h'; omega
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hx hy (Or.inl hne')
    have hadj := ((hmem f hf).2 ⟨i, hi⟩ ⟨(i + 1) % k, hi'⟩).mpr
      ((cycleGraph_adj_iff_mod hk2 _ _).mpr (Or.inl rfl))
    rwa [hfi, hfj] at hadj
  · intro i hi j hj hij hcons1 hcons2 x hx y hy
    rw [hP i hi] at hx
    rw [hP j hj] at hy
    have hne' : (⟨i, hi⟩ : Fin k) ≠ ⟨j, hj⟩ := fun h => hij (by simpa using congrArg Fin.val h)
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hx hy (Or.inl hne')
    intro hadj
    rw [← hfi, ← hfj] at hadj
    have := (cycleGraph_adj_iff_mod hk2 _ _).mp (((hmem f hf).2 _ _).mp hadj)
    rcases this with h | h
    · exact hcons1 h
    · exact hcons2 h

/-- **The refined named Prop**: the induced removal lemma for `{C_k : k ≥ 4}` with explicit
parameter functions `Nrem`, `Krem`, `drem` of the precision `ε` only. -/
def CycleRemovalExplicit (Nrem Krem : ℚ → ℕ) (drem : ℚ → ℝ) : Prop :=
  ∀ ε : ℚ, 0 < ε → 0 < drem ε ∧ ∀ n : ℕ, Nrem ε ≤ n → ∀ G : SimpleGraph (Fin n),
    (∀ k, 4 ≤ k → k ≤ Krem ε →
      (AlonShapira.indCopies (SimpleGraph.cycleGraph k) G : ℝ) < drem ε * (n : ℝ) ^ k) →
      ∃ G' : SimpleGraph (Fin n), AlonShapira.IsChordal G' ∧
        (AlonShapira.editDist G G' : ℝ) < (ε : ℝ) * (n : ℝ) ^ 2

/-- Satisfiable (non-explicitly), from the formal Alon–Shapira Lemma 4.2. -/
theorem exists_cycleRemovalExplicit :
    ∃ (Nrem Krem : ℚ → ℕ) (drem : ℚ → ℝ), CycleRemovalExplicit Nrem Krem drem := by
  obtain ⟨N, K, δ, h⟩ := AlonShapira.near_chordal_of_few_induced_cycles'
  refine ⟨fun ε => N ε, fun ε => K ε, fun ε => δ ε, fun ε hε => ?_⟩
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  exact ⟨(h ε hεR).1, fun n hn G hG => (h ε hεR).2 n hn G hG⟩

/-- The explicit edit threshold obtained from the removal functions and Lemma K. -/
noncomputable def NeditOfRem (Nrem Krem : ℚ → ℕ) (drem : ℚ → ℝ) (s : ℕ) (δ : ℚ) : ℕ :=
  max (Nrem δ) ((range (Krem δ + 1)).sup (fun k => NK (s + 1) k (drem δ)))

/-- **Reduction**: the explicit removal lemma gives `EditApproxExplicit` with `NeditOfRem`. -/
theorem editApproxExplicit_of_removal {Nrem Krem : ℚ → ℕ} {drem : ℚ → ℝ}
    (h : CycleRemovalExplicit Nrem Krem drem) :
    EditApproxExplicit (NeditOfRem Nrem Krem drem) := by
  classical
  intro s δ hδ n hn G inst hG
  obtain ⟨hd, hmain⟩ := h δ hδ
  have hn1 : Nrem δ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨G', hch, hed⟩ := hmain n hn1 G (fun k h4 hk => by
    rw [@indCopies_eq_card_cycTuples n k G inst]
    have hNK : NK (s + 1) k (drem δ) ≤ n := by
      refine le_trans ?_ (le_trans (le_max_right _ _) hn)
      exact Finset.le_sup (f := fun k => NK (s + 1) k (drem δ))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    exact @lemmaK_explicit s k h4 (drem δ) hd n hNK G inst hG)
  refine ⟨G', isChordal_of_noInducedCycle G' (fun k hk => hch k (SimpleGraph.cycleGraph k)
    ⟨hk, rfl⟩), ?_⟩
  have hset : symmDiff G.edgeSet G'.edgeSet =
      ((symmDiff G.edgeFinset G'.edgeFinset : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
    rw [Finset.coe_symmDiff, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  have hcard : (symmDiff G.edgeSet G'.edgeSet).ncard = AlonShapira.editDist G G' := by
    rw [hset, Set.ncard_coe_finset]
    unfold AlonShapira.editDist
    congr 1
    ext e
    simp only [Finset.mem_symmDiff, SimpleGraph.mem_edgeFinset]
  rw [hcard]
  have h' : ((AlonShapira.editDist G G' : ℚ) : ℝ) ≤ ((δ * (n : ℚ) ^ 2 : ℚ) : ℝ) := by
    push_cast; exact hed.le
  exact_mod_cast h'

/-- **Theorem C with a threshold explicit in `s`**, given the three `s`-free removal
functions. -/
theorem theoremC_of_removal {Nrem Krem : ℚ → ℕ} {drem : ℚ → ℝ}
    (h : CycleRemovalExplicit Nrem Krem drem) (s n : ℕ)
    (hn : Fexp (NeditOfRem Nrem Krem drem) s ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_explicit _ (editApproxExplicit_of_removal h) s n hn G hdef

/-- Uniform version, given the removal functions. -/
theorem theoremC_uniform_of_removal {Nrem Krem : ℚ → ℕ} {drem : ℚ → ℝ}
    (h : CycleRemovalExplicit Nrem Krem drem) (n : ℕ)
    (h0 : Fmono (NeditOfRem Nrem Krem drem) 0 ≤ n) :
    ∀ s : ℕ, s ≤ Finv (NeditOfRem Nrem Krem drem) n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_uniform _ (editApproxExplicit_of_removal h) n h0

end E33
