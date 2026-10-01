module

public import RequestProject.AS.Lemma35
public import RequestProject.AS.ColoredHom
public import RequestProject.AS.Modify

/-!
# Proof of Lemma 4.2 of Alon–Shapira

We follow Section 5 of the paper. Fix `𝓕` and `0 < ε ≤ 1`, and put `η = ε/6`.
1. Apply Lemma 3.8 (`AFKS.corollary_4_2`) with `m = ⌈100/ε⌉` and
   `E(r) = min(α(r) γ*(r), η)` (`E(0) = η`), where `γ*(r)` is small enough to apply the counting
   lemma (Lemma 3.2) to every graph with at most `Ψ_𝓕(r)` vertices, and `α(r)` is given by
   Lemma 3.5 for `l = Ψ_𝓕(r)` and `γ*(r)`.
2. Apply Lemma 3.5 inside every `Uᵢ` to get sets `W_{i,1}, …, W_{i,Ψ(k)}`.
3. Build the modified graph `G̃` (`modGraph`); it is `< εn²` edits away from `G`, so it contains an
   induced copy of some `F' ∈ 𝓕`, which gives a colored homomorphism from `F'` into the colored
   regularity graph `R`.
4. By definition of `Ψ_𝓕` some `F ∈ 𝓕` with `f ≤ Ψ_𝓕(k)` vertices has a colored homomorphism `φ`
   into `R`; the sets `W_{φ(a), a}` satisfy the hypotheses of the counting lemma in `G`, which
   produces `≥ δ n^f` induced copies of `F` in `G`.
-/

@[expose] public section

open Finset AFKS

open scoped Classical

namespace AlonShapira

theorem dens_comm' {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    dens G A B = dens G B A := by
  unfold AFKS.dens; rw [SimpleGraph.edgeDensity_comm]

/-- Ordered pairs vs. unordered pairs of a symmetric relation. -/
theorem card_ordered_le {k : ℕ} (bad : Fin k → Fin k → Prop) (hb : ∀ i j, bad i j → bad j i) :
    #{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} ≤
      2 * #{p : Fin k × Fin k | p.1 < p.2 ∧ bad p.1 p.2} := by
  set A := ({p : Fin k × Fin k | p.1 < p.2 ∧ bad p.1 p.2} : Finset (Fin k × Fin k))
  have hsub : ({p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : Finset (Fin k × Fin k)) ⊆
      A ∪ A.image Prod.swap := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases lt_or_gt_of_ne hp.1 with h | h
    · exact Finset.mem_union_left _ (by simp [A, h, hp.2])
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨p.swap, ?_, by simp⟩)
      simp [A, h, hb _ _ hp.2]
  calc _ ≤ #(A ∪ A.image Prod.swap) := Finset.card_le_card hsub
    _ ≤ #A + #(A.image Prod.swap) := Finset.card_union_le _ _
    _ ≤ #A + #A := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * #A := by ring

/-- In an equipartition of `Fin n` into `k ≤ n` parts, every part has at most `2n/k` elements. -/
theorem card_part_le_two_mul_div {n k : ℕ} (cl : Fin n → Fin k) (Vp : Fin k → Finset (Fin n))
    (hVp : ∀ i u, u ∈ Vp i ↔ cl u = i) (hequi : ∀ i j, #(Vp i) ≤ #(Vp j) + 1) (hk : 1 ≤ k)
    (hkn : k ≤ n) (i : Fin k) : (#(Vp i) : ℝ) ≤ 2 * n / k := by
  have hsum : ∑ j, #(Vp j) = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ)
      (f := cl) (fun _ _ => by simp)
    rw [card_univ, Fintype.card_fin] at this
    refine Eq.trans ?_ this.symm
    refine Finset.sum_congr rfl fun j _ => congrArg _ ?_
    ext u; simp [hVp]
  have h1 : k * #(Vp i) ≤ n + k := by
    calc k * #(Vp i) = ∑ _j : Fin k, #(Vp i) := by simp
      _ ≤ ∑ j : Fin k, (#(Vp j) + 1) := Finset.sum_le_sum fun j _ => hequi i j
      _ = n + k := by rw [Finset.sum_add_distrib, hsum]; simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1' : (k : ℝ) * #(Vp i) ≤ n + k := by exact_mod_cast h1
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rw [le_div_iff₀ hkR]
  nlinarith

/-- An injective tuple spanning an induced copy of `F` gives an induced embedding. -/
noncomputable def embOfTuple {V : Type*} {G : SimpleGraph V} {f : ℕ} {F : SimpleGraph (Fin f)}
    (u : Fin f → V) (hinj : Function.Injective u) (hadj : ∀ i j, F.Adj i j ↔ G.Adj (u i) (u j)) :
    F ↪g G :=
  ⟨⟨u, hinj⟩, fun {a b} => (hadj a b).symm⟩

/-- If the sets `Uᵢ` are pairwise disjoint, the induced tuples are at most the number of induced
copies. -/
theorem card_inducedTuples_le {n f : ℕ} (G : SimpleGraph (Fin n)) (F : SimpleGraph (Fin f))
    (U : Fin f → Finset (Fin n)) (hU : ∀ a b, a ≠ b → Disjoint (U a) (U b)) :
    #(inducedTuples G F U) ≤ indCopies F G := by
  have hmem := fun u (hu : u ∈ inducedTuples G F U) => (mem_inducedTuples G F U u).1 hu
  have hinj : ∀ u (hu : u ∈ inducedTuples G F U), Function.Injective u := by
    intro u hu a b hab
    by_contra hne
    exact Finset.disjoint_left.1 (hU a b hne) ((hmem u hu).1 a) (hab ▸ (hmem u hu).1 b)
  let g : inducedTuples G F U → (F ↪g G) := fun u =>
    embOfTuple u.1 (hinj u.1 u.2) (hmem u.1 u.2).2
  have : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    have := congrArg (fun e : F ↪g G => (e : Fin f → Fin n)) huv
    exact this
  have := Fintype.card_le_of_injective g this
  rwa [Fintype.card_coe] at this

set_option maxHeartbeats 4000000 in
/-- **Lemma 4.2 of Alon–Shapira, for a fixed `0 < ε ≤ 1`.** -/
theorem lemma42_fixed (𝓕 : GraphFamily) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N K : ℕ, ∃ δ > (0 : ℝ), ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), FarFromIndFree 𝓕 ε G →
      ∃ f ≤ K, ∃ F ∈ 𝓕 f, δ * (n : ℝ) ^ f ≤ indCopies F G := by
  set η : ℝ := ε / 6 with hηdef
  have hη : 0 < η := by positivity
  have hη6 : η ≤ 1 / 6 := by rw [hηdef]; linarith
  -- constants of the counting lemma
  choose γc hγc δc hδc hC using fun f => counting_lemma.{0} f η hη (by linarith)
  set Ψ : ℕ → ℕ := Psi 𝓕 with hΨ
  set γs : ℕ → ℝ := fun k => min 1 ((range (Ψ k + 1)).inf' nonempty_range_add_one γc) with hγsdef
  have hγs : ∀ k, 0 < γs k := fun k =>
    lt_min one_pos ((Finset.lt_inf'_iff _).2 fun f _ => hγc f)
  have hγs1 : ∀ k, γs k ≤ 1 := fun k => min_le_left _ _
  have hγs_le : ∀ k f, f ≤ Ψ k → γs k ≤ γc f := fun k f hf =>
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hf)))
  set δs : ℕ → ℝ := fun k => (range (Ψ k + 1)).inf' nonempty_range_add_one δc with hδsdef
  have hδs : ∀ k, 0 < δs k := fun k => (Finset.lt_inf'_iff _).2 fun f _ => hδc f
  have hδs_le : ∀ k f, f ≤ Ψ k → δs k ≤ δc f := fun k f hf =>
    Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hf))
  -- constants of Lemma 3.5
  choose α hα hα2 M hM using fun k => lemma_3_5.{0} (Ψ k) (hγs k)
  set β : ℕ → ℝ := fun k => α k * γs k with hβdef
  set E : ℕ → ℝ := fun r => if r = 0 then η else min (β r) η with hEdef
  have hE0 : E 0 = η := by simp [hEdef]
  have hEk : ∀ k, k ≠ 0 → E k ≤ β k ∧ E k ≤ η := fun k hk => by
    simp only [hEdef, if_neg hk]; exact ⟨min_le_left _ _, min_le_right _ _⟩
  have hEpos : ∀ r, 0 < E r := fun r => by
    simp only [hEdef]; split_ifs
    · exact hη
    · exact lt_min (mul_pos (hα r) (hγs r)) hη
  have hE1 : ∀ r, E r < 1 := fun r => by
    simp only [hEdef]; split_ifs
    · linarith
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set m : ℕ := ⌈100 / ε⌉₊ with hmdef
  have hm : 100 / ε ≤ m := Nat.le_ceil _
  have hm1 : 1 ≤ m := by
    rw [hmdef, Nat.one_le_ceil_iff]; positivity
  obtain ⟨S, hS⟩ := corollary_4_2.{0} m E hEpos hE1
  set N : ℕ := S * (range (S + 1)).sup M + S + 1 with hNdef
  set K : ℕ := (range (S + 1)).sup Ψ with hKdef
  set δF : ℝ := (range (S + 1)).inf' nonempty_range_add_one
    (fun k => δs k * (α k / ((S : ℝ) + 1)) ^ Ψ k) with hδFdef
  have hδF : 0 < δF := (Finset.lt_inf'_iff _).2 fun k _ => by
    have := hδs k; have := hα k; positivity
  refine ⟨N, K, δF, hδF, fun n hn G hfar => ?_⟩
  have hnN : N ≤ n := hn
  have hnS : S ≤ n := by rw [hNdef] at hnN; nlinarith [Nat.zero_le (S * (range (S + 1)).sup M)]
  obtain ⟨k, Vp, Up, hdisj, hcover, hequi, hmk, hkS, hUV, hUsize, -, hreg, hbad⟩ :=
    hS G (by rw [Fintype.card_fin]; exact hnS)
  have hk1 : 1 ≤ k := hm1.trans hmk
  have hk0 : k ≠ 0 := by omega
  have hS1 : 1 ≤ S := hk1.trans hkS
  have hkn : k ≤ n := hkS.trans hnS
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  -- the sets `Uᵢ` are large enough for Lemma 3.5
  have hMk : ∀ i, M k ≤ #(Up i) := by
    intro i
    have h1 : M k ≤ (range (S + 1)).sup M :=
      Finset.le_sup (f := M) (Finset.mem_range.2 (Nat.lt_succ_of_le hkS))
    have h2 : S * M k ≤ n := by
      rw [hNdef] at hnN
      have := Nat.mul_le_mul_left S h1
      omega
    have h3 := hUsize i
    rw [Fintype.card_fin] at h3
    have h4 : ((S * M k : ℕ) : ℝ) ≤ S * #(Up i) := le_trans (by exact_mod_cast h2) h3
    push_cast at h4
    have : (M k : ℝ) ≤ #(Up i) := le_of_mul_le_mul_left h4 (by positivity)
    exact_mod_cast this
  choose W hWsub hWsize hWdisj hWreg c hc using fun i => hM k G (Up i) (hMk i)
  -- the cluster of a vertex
  choose cl hcl using hcover
  have hVp : ∀ i u, u ∈ Vp i ↔ cl u = i := by
    intro i u
    refine ⟨fun hu => ?_, fun h => h ▸ hcl u⟩
    by_contra hne
    exact Finset.disjoint_left.1 (hdisj _ _ hne) (hcl u) hu
  -- the colored regularity graph
  set dU : Fin k → Fin k → ℝ := fun i j => dens G (Up i) (Up j) with hdU
  set bad : Fin k → Fin k → Prop :=
    fun i j => E 0 ≤ |dens G (Vp i) (Vp j) - dens G (Up i) (Up j)| with hbaddef
  have hbadsymm : ∀ i j, bad i j → bad j i := by
    intro i j h
    simp only [hbaddef] at h ⊢
    rwa [dens_comm' G (Vp j), dens_comm' G (Up j)]
  set col : Fin k → Fin k → Fin 3 := fun i j =>
    if bad i j then (if 1 / 2 ≤ dU i j then 1 else 0)
    else if dU i j < 2 * η then 0 else if 1 - 2 * η < dU i j then 1 else 2 with hcoldef
  have hcs : ∀ i j, col i j = col j i := by
    intro i j
    have hb : bad i j ↔ bad j i := ⟨hbadsymm i j, hbadsymm j i⟩
    have hd : dU i j = dU j i := dens_comm' G _ _
    simp only [hcoldef, hb, hd]
  set Gt := modGraph G cl c col hcs with hGt
  -- Claim 5.4: `G̃` is close to `G`
  have hedit : (editDist G Gt : ℝ) < ε * (n : ℝ) ^ 2 := by
    have hcol : ∀ i j, i ≠ j → ¬ bad i j →
        (col i j = 0 → dens G (Vp i) (Vp j) ≤ 3 * η) ∧
        (col i j = 1 → 1 - 3 * η ≤ dens G (Vp i) (Vp j)) := by
      intro i j _ hnb
      have hclose : |dens G (Vp i) (Vp j) - dU i j| < η := by
        simp only [hbaddef, hE0, not_le] at hnb; exact hnb
      rw [abs_lt] at hclose
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · simp only [hcoldef, if_neg hnb] at h0
        split_ifs at h0 with ha hb
        · linarith
        · exact absurd h0 (by decide)
        · exact absurd h0 (by decide)
      · simp only [hcoldef, if_neg hnb] at h1
        split_ifs at h1 with ha hb
        · exact absurd h1 (by decide)
        · linarith
        · exact absurd h1 (by decide)
    have key := two_mul_editDist_modGraph_le G cl Vp hVp c col hcs bad (L := 2 * n / k)
      (θ := 3 * η) (card_part_le_two_mul_div cl Vp hVp hequi hk1 hkn) (by positivity) hcol
    have hord := card_ordered_le bad hbadsymm
    have hb2 : #{p : Fin k × Fin k | p.1 < p.2 ∧ bad p.1 p.2} =
        #{p : Fin k × Fin k | p.1 < p.2 ∧
          E 0 ≤ |dens G (Vp p.1) (Vp p.2) - dens G (Up p.1) (Up p.2)|} := by
      congr 1
    rw [hb2] at hord
    have hB : (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) ≤ η * (k : ℝ) ^ 2 := by
      have h1 : (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) ≤
          2 * (#{p : Fin k × Fin k | p.1 < p.2 ∧
            E 0 ≤ |dens G (Vp p.1) (Vp p.2) - dens G (Up p.1) (Up p.2)|} : ℝ) := by
        exact_mod_cast hord
      have h2 := hbad
      rw [Nat.cast_choose_two] at h2
      have h3 : E 0 * ((k : ℝ) * ((k : ℝ) - 1) / 2) ≤ E 0 * ((k : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (hEpos 0).le
      have hB0 : (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) ≤ E 0 * (k : ℝ) ^ 2 := by
        linarith
      rw [← hE0]; exact hB0
    have hkpos : (0 : ℝ) < k := by linarith
    have hkL : (k : ℝ) * (2 * n / k) = 2 * n := by field_simp
    have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
    have hkε : 100 ≤ k * ε := by
      rw [div_le_iff₀ hε] at hm; nlinarith
    have hL1 : 2 * (n : ℝ) / k * n ≤ ε * n ^ 2 / 50 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hkpos (by norm_num)]
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
      nlinarith
    have hL2 : (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) * (2 * n / k) ^ 2 ≤
        4 * η * (n : ℝ) ^ 2 := by
      calc (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) * (2 * n / k) ^ 2
          ≤ η * (k : ℝ) ^ 2 * (2 * n / k) ^ 2 := by gcongr
        _ = η * ((k : ℝ) * (2 * n / k)) ^ 2 := by ring
        _ = 4 * η * (n : ℝ) ^ 2 := by rw [hkL]; ring
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have : 2 * (editDist G Gt : ℝ) ≤ ε * n ^ 2 / 50 + 4 * η * n ^ 2 + 3 * η * n ^ 2 := by
      linarith
    rw [hηdef] at this
    nlinarith
  -- Claim 5.5: `G̃` contains an induced copy of a member of `𝓕`
  have hnot : ¬ IndFree 𝓕 Gt := fun h => absurd (hfar Gt h) (not_le.2 hedit)
  simp only [IndFree, not_forall, not_isEmpty_iff] at hnot
  obtain ⟨f', F', hF', ⟨e⟩⟩ := hnot
  set R : CGraph k := (c, col) with hR
  have hchom' : IsCHom F' R (cl ∘ e) := by
    intro a b hab
    have hne : e a ≠ e b := e.injective.ne hab
    have hadj : F'.Adj a b ↔ Gt.Adj (e a) (e b) := e.map_adj_iff.symm
    have hGt : Gt.Adj (e a) (e b) ↔ e a ≠ e b ∧ (if cl (e a) = cl (e b) then c (cl (e a)) = true
        else (col (cl (e a)) (cl (e b)) = 1 ∨
          (col (cl (e a)) (cl (e b)) = 2 ∧ G.Adj (e a) (e b)))) := Iff.rfl
    rw [hadj, hGt]
    simp only [Function.comp_apply, hR]
    refine ⟨fun h => by rw [if_pos h]; exact ⟨fun h' => h'.2, fun h' => ⟨hne, h'⟩⟩,
      fun h => ?_⟩
    rw [if_neg h]
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rcases h'.2 with h2 | ⟨h2, _⟩ <;> rw [h2] <;> decide
    · intro h2; exact h' ⟨hne, Or.inl h2⟩
  -- Claim 5.6
  obtain ⟨f, hf, F, hF, φ, hφ⟩ := exists_small_chom 𝓕 R ⟨f', F', hF', cl ∘ e, hchom'⟩
  -- the sets `W_{φ(a), a}`
  set X : Fin f → Finset (Fin n) := fun a => W (φ a) (Fin.castLE hf a) with hX
  have hXU : ∀ a, X a ⊆ Up (φ a) := fun a => hWsub _ _
  have hXsize : ∀ a, α k * #(Up (φ a)) ≤ #(X a) := fun a => hWsize _ _
  have hXdisj : ∀ a b, a ≠ b → Disjoint (X a) (X b) := by
    intro a b hab
    by_cases h : φ a = φ b
    · simp only [hX]
      rw [h]
      exact hWdisj _ _ _ fun h' => hab (Fin.castLE_injective hf h')
    · exact ((hdisj _ _ h).mono (hUV _) (hUV _)).mono (hXU a) (hXU b)
  -- Claim 5.2
  have hEk' := hEk k hk0
  have hEα : E k ≤ α k :=
    hEk'.1.trans (by simp only [hβdef]; exact mul_le_of_le_one_right (hα k).le (hγs1 k))
  have hcross : ∀ a b, φ a ≠ φ b → IsRegularPair G (γs k) (X a) (X b) ∧
      |dens G (X a) (X b) - dU (φ a) (φ b)| ≤ η := by
    intro a b hab
    have hr := hreg _ _ hab
    constructor
    · have := IsRegularPair.sub G (hEpos k) hEα hr (hXU a) (hXU b) (hXsize a) (hXsize b)
      refine IsRegularPair.mono G (max_le ?_ ?_) this
      · have h1 : E k ≤ α k * γs k := hEk'.1
        have h2 : α k * γs k ≤ 1 / 2 * γs k :=
          mul_le_mul_of_nonneg_right (hα2 k) (hγs k).le
        linarith
      · rw [div_le_iff₀ (hα k)]
        have h1 : E k ≤ α k * γs k := hEk'.1
        linarith
    · have h1 : E k * #(Up (φ a)) ≤ #(X a) :=
        le_trans (mul_le_mul_of_nonneg_right hEα (Nat.cast_nonneg _)) (hXsize a)
      have h2 : E k * #(Up (φ b)) ≤ #(X b) :=
        le_trans (mul_le_mul_of_nonneg_right hEα (Nat.cast_nonneg _)) (hXsize b)
      exact (hr _ (hXU a) _ (hXU b) h1 h2).trans hEk'.2
  have hsame : ∀ a b, a ≠ b → φ a = φ b → IsRegularPair G (γs k) (X a) (X b) ∧
      (1 / 2 ≤ dens G (X a) (X b) ↔ c (φ a) = true) := by
    intro a b hab h
    have hne : Fin.castLE hf a ≠ Fin.castLE hf b := fun h' => hab (Fin.castLE_injective hf h')
    simp only [hX]
    rw [h]
    exact ⟨hWreg _ _ _ hne, hc _ _ _ hne⟩
  -- Proposition 5.7
  have hadjX : ∀ a b, F.Adj a b → η ≤ dens G (X a) (X b) := by
    intro a b hab
    have hne := F.ne_of_adj hab
    obtain ⟨h1, h2⟩ := hφ a b hne
    by_cases h : φ a = φ b
    · have hc' : c (φ a) = true := (h1 h).1 hab
      have := (hsame a b hne h).2.2 hc'
      linarith
    · obtain ⟨-, hd⟩ := hcross a b h
      have hcol0 : col (φ a) (φ b) ≠ 0 := (h2 h).1 hab
      rw [abs_le] at hd
      by_cases hb : bad (φ a) (φ b)
      · by_cases hu : 1 / 2 ≤ dU (φ a) (φ b)
        · linarith
        · exact absurd (by simp only [hcoldef, if_pos hb, if_neg hu]) hcol0
      · by_cases hl : dU (φ a) (φ b) < 2 * η
        · exact absurd (by simp only [hcoldef, if_neg hb, if_pos hl]) hcol0
        · push_neg at hl; linarith
  have hnadjX : ∀ a b, a ≠ b → ¬ F.Adj a b → dens G (X a) (X b) ≤ 1 - η := by
    intro a b hne hab
    obtain ⟨h1, h2⟩ := hφ a b hne
    by_cases h : φ a = φ b
    · have hc' : ¬ c (φ a) = true := fun hh => hab ((h1 h).2 hh)
      have := mt (hsame a b hne h).2.1 hc'
      push_neg at this
      linarith
    · obtain ⟨-, hd⟩ := hcross a b h
      have hcol1 : col (φ a) (φ b) ≠ 1 := (h2 h).2 hab
      rw [abs_le] at hd
      by_cases hb : bad (φ a) (φ b)
      · by_cases hu : 1 / 2 ≤ dU (φ a) (φ b)
        · exact absurd (by simp only [hcoldef, if_pos hb, if_pos hu]) hcol1
        · push_neg at hu; linarith
      · by_cases hl : dU (φ a) (φ b) < 2 * η
        · linarith
        · by_cases hh : 1 - 2 * η < dU (φ a) (φ b)
          · exact absurd (by simp only [hcoldef, if_neg hb, if_neg hl, if_pos hh]) hcol1
          · push_neg at hh; linarith
  -- the counting lemma
  have hcnt := hC f G F X (fun a b hab => by
      by_cases h : φ a = φ b
      · exact IsRegularPair.mono G (hγs_le k f hf) (hsame a b hab h).1
      · exact IsRegularPair.mono G (hγs_le k f hf) (hcross a b h).1) hadjX hnadjX
  have hcopies := card_inducedTuples_le G F X hXdisj
  refine ⟨f, hf.trans (Finset.le_sup (f := Ψ) (Finset.mem_range.2 (Nat.lt_succ_of_le hkS))),
    F, hF, ?_⟩
  have hSpos : (0 : ℝ) < (S : ℝ) + 1 := by positivity
  have hbase : 0 ≤ α k / ((S : ℝ) + 1) := by have := hα k; positivity
  have hbase1 : α k / ((S : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hSpos]; linarith [hα2 k]
  have hXbig : ∀ a, α k * n / ((S : ℝ) + 1) ≤ #(X a) := by
    intro a
    have h3 := hUsize (φ a)
    rw [Fintype.card_fin] at h3
    have h4 : (n : ℝ) / ((S : ℝ) + 1) ≤ #(Up (φ a)) := by
      rw [div_le_iff₀ hSpos]
      have : (0 : ℝ) ≤ #(Up (φ a)) := Nat.cast_nonneg _
      nlinarith
    calc α k * n / ((S : ℝ) + 1) = α k * ((n : ℝ) / ((S : ℝ) + 1)) := by ring
      _ ≤ α k * #(Up (φ a)) := mul_le_mul_of_nonneg_left h4 (hα k).le
      _ ≤ _ := hXsize a
  calc δF * (n : ℝ) ^ f
      ≤ δs k * (α k / ((S : ℝ) + 1)) ^ Ψ k * (n : ℝ) ^ f := by
        gcongr
        exact Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hkS))
    _ ≤ δc f * (α k / ((S : ℝ) + 1)) ^ f * (n : ℝ) ^ f := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (hδs_le k f hf)
          (pow_le_pow_of_le_one hbase hbase1 hf) (by positivity) (hδc f).le) (by positivity)
    _ = δc f * ∏ _a : Fin f, (α k * n / ((S : ℝ) + 1)) := by
        rw [Finset.prod_const, card_univ, Fintype.card_fin, mul_assoc, ← mul_pow]
        congr 2; ring
    _ ≤ δc f * ∏ a, (#(X a) : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun a _ => ?_)
          (fun a _ => hXbig a)) (hδc f).le
        exact div_nonneg (mul_nonneg (hα k).le (Nat.cast_nonneg _)) hSpos.le
    _ ≤ #(inducedTuples G F X) := hcnt
    _ ≤ indCopies F G := by exact_mod_cast hcopies

/-- **Lemma 4.2 of Alon–Shapira** (proof). -/
theorem lemma42_holds (𝓕 : GraphFamily) : Lemma42 𝓕 := by
  have h : ∀ ε : ℝ, ∃ N K : ℕ, ∃ δ : ℝ, 0 < ε → 0 < δ ∧
      ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), FarFromIndFree 𝓕 ε G →
        ∃ f ≤ K, ∃ F ∈ 𝓕 f, δ * (n : ℝ) ^ f ≤ indCopies F G := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨N, K, δ, hδ, h⟩ :=
        lemma42_fixed 𝓕 (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
      refine ⟨N, K, δ, fun _ => ⟨hδ, fun n hn G hG => h n hn G fun G' hG' => ?_⟩⟩
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (hG G' hG')
    · exact ⟨0, 0, 0, fun h => absurd h hε⟩
  choose N K δ hNKδ using h
  exact ⟨N, K, δ, fun ε hε => hNKδ ε hε⟩

end AlonShapira
