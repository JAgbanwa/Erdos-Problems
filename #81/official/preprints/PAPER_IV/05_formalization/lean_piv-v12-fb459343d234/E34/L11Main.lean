import E34.Main
import E34.L11Claim6
import E34.L11Params

/-!
# E34 — Lemma 11 of arXiv:1902.06135, assembled (`lemma11_V`)

Fix `ε > 0`, a rooted tree `Γ` on `Fin K`, pins `x` and a graph `G` which is `ε`-far from
chordal.  With `m = m11V ε K`, `y = y11 ε K`, `δ = δ11 ε K`, `η = ε / (2K)`:

* trivial cases: `G` far from chordal forces `ε < 1/2` and `n ≥ 1` (`far_basic`), hence `K ≥ 1`;
* **Case A** (`l11_caseA`): every admissible colouring has `≥ δ n²` conflicts: Theorem 2 and
  Claim 2 (`properOn_of_pinned`);
* **Case B1** (`l11_caseB1`): a colouring `ψ` with `< δ n²` conflicts and a section `c` that is
  `η`-far from chain graphs: Claim 5 on the length-`y` prefix of the sample;
* **Case B2** (`l11_caseB2`): otherwise every section has a rank with `≤ η n²` mismatches; after
  normalising the ranks (`normRk`) the glued graph is chordal and `ε n²`-close to `G`, which is
  impossible.
-/

namespace E34

open Finset

open scoped Classical

variable {n K : ℕ}

/-! ## Rank normalisation -/

/-- Normalised rank: the number of vertices of strictly smaller rank. -/
noncomputable def normRk (rk : Fin n → ℕ) : Fin n → ℕ :=
  fun u => (univ.filter (fun v => rk v < rk u)).card

theorem normRk_le (rk : Fin n → ℕ) (u : Fin n) : normRk rk u ≤ n := by
  unfold normRk
  exact (card_le_univ _).trans (by simp)

theorem normRk_lt_iff (rk : Fin n → ℕ) (a b : Fin n) :
    normRk rk a < normRk rk b ↔ rk a < rk b := by
  unfold normRk
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    refine absurd h (not_lt.2 (card_le_card ?_))
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    omega
  · intro h
    refine card_lt_card ((ssubset_iff_of_subset ?_).2 ⟨a, ?_, ?_⟩)
    · intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      omega
    · simp [h]
    · simp

theorem chainMisOn_normRk (G : SimpleGraph (Fin n)) (L R A : Finset (Fin n))
    (rk : Fin n → ℕ) : chainMisOn G L R A (normRk rk) = chainMisOn G L R A rk := by
  unfold chainMisOn
  simp_rw [normRk_lt_iff]

/-! ## Trivial cases -/

theorem isChordal_bot_fin : AlonShapira.IsChordal (⊥ : SimpleGraph (Fin n)) :=
  isChordal_of_rank ⊥ (fun v => v.val) Fin.val_injective (fun _ _ _ h => h.elim)

theorem two_mul_card_edges_le (G : SimpleGraph (Fin n)) :
    2 * G.edgeFinset.card ≤ n * n := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  calc ∑ v, G.degree v ≤ ∑ _v : Fin n, n :=
        sum_le_sum (fun v _ => (G.degree_lt_card_verts v).le.trans (by simp))
    _ = n * n := by simp

/-- A graph that is `ε`-far from chordal has `n ≥ 1` and forces `ε < 1/2`. -/
theorem far_basic {ε : ℝ} {G : SimpleGraph (Fin n)}
    (hfar : ∀ F : SimpleGraph (Fin n), AlonShapira.IsChordal F →
      ε * (n : ℝ) ^ 2 < (AlonShapira.editDist G F : ℝ)) :
    ε < 1 / 2 ∧ 1 ≤ n := by
  have h := hfar ⊥ isChordal_bot_fin
  rw [editDist_eq_card] at h
  have e : symmDiff G.edgeFinset (⊥ : SimpleGraph (Fin n)).edgeFinset = G.edgeFinset := by
    simp
  rw [e] at h
  have h2 : ((2 * G.edgeFinset.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
    exact_mod_cast two_mul_card_edges_le G
  push_cast at h2
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h
    · exact h0
  refine ⟨?_, hn⟩
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  by_contra hc
  push_neg at hc
  nlinarith

/-! ## Prefix counting -/

theorem card_prefix_le (y k : ℕ) (Q : Finset (Fin n) → Prop)
    (hQ : ∀ A A', A' ⊆ A → Q A → Q A') :
    (univ.filter (fun w : Fin (y + k) → Fin n => Q (img w))).card ≤
      (univ.filter (fun u : Fin y → Fin n => Q (img u))).card * n ^ k := by
  have hsub : univ.filter (fun w : Fin (y + k) → Fin n => Q (img w)) ⊆
      univ.filter (fun w : Fin (y + k) → Fin n =>
        (fun (u : Fin y → Fin n) (_ : Fin k → Fin n) => Q (img u))
          (fun i => w (Fin.castAdd k i)) (fun i => w (Fin.natAdd y i))) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    refine hQ _ _ ?_ hw
    intro v hv
    obtain ⟨i, rfl⟩ := (mem_img _ v).1 hv
    exact (mem_img w _).2 ⟨_, rfl⟩
  refine (card_le_card hsub).trans (le_of_eq ?_)
  refine (card_append y k (fun (u : Fin y → Fin n) (_ : Fin k → Fin n) => Q (img u))).trans ?_
  have e : univ.filter (fun p : (Fin y → Fin n) × (Fin k → Fin n) => Q (img p.1)) =
      (univ.filter (fun u : Fin y → Fin n => Q (img u))) ×ˢ univ := by
    ext p; simp
  rw [e, card_product, card_univ]
  simp

/-! ## The three cases -/

section Cases

variable {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hK : 1 ≤ K)
include hε0 hε1 hK

/-- **Case A**: all admissible colourings have many conflicts. -/
theorem l11_caseA (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (hA : ∀ ψ : Fin n → Finset (Fin K), (∀ v, ψ v ∈ (pinProblem Γ x G).L v) →
      δ11 ε K * (n : ℝ) ^ 2 ≤ (pinProblem Γ x G).conf ψ) :
    2 * (univ.filter (fun w : Fin (m11V ε K) → Fin n => PinnedOn Γ x G (img w))).card ≤
      n ^ (m11V ε K) := by
  have hB : 8 * (K : ℝ) / δ11 ε K < B11 ε K + 1 := by
    unfold B11; exact Nat.lt_floor_add_one _
  have h := (pinProblem Γ x G).thm2 (pinProblem_L_nonempty Γ x G) (δ11 ε K)
    (δ11_pos hε0 hε1 hK) (δ11_le_one hε0 hε1 hK) hA (m11V ε K) (B11 ε K) hB
    (thm2_ineq hε0 hε1 hK)
  refine le_trans (Nat.mul_le_mul_left 2 (card_le_card ?_)) h
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact properOn_of_pinned hw

/-- **Case B1**: few conflicts and a section far from chain graphs. -/
theorem l11_caseB1 (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (ψ : Fin n → Finset (Fin K))
    (hconf : ((pinProblem Γ x G).conf ψ : ℝ) < δ11 ε K * (n : ℝ) ^ 2) (c : Fin K)
    (hc : ∀ rk : Fin n → ℕ, ε / (2 * K) * (n : ℝ) ^ 2 <
      chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ rk) :
    2 * (univ.filter (fun w : Fin (m11V ε K) → Fin n => PinnedOn Γ x G (img w))).card ≤
      n ^ (m11V ε K) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (y11_le_m11V hε0 hε1 hK)
  suffices H : ∀ m, m = y11 ε K + k →
      2 * (univ.filter (fun w : Fin m → Fin n => PinnedOn Γ x G (img w))).card ≤ n ^ m from
    H _ hk
  intro m hm
  subst hm
  set y := y11 ε K with hy
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hη0 : 0 ≤ ε / (2 * K) := by positivity
  have hη1 : ε / (2 * K) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hy2 : 2 ≤ y := two_le_y11 hε0 hε1 hK
  have hy2' : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  -- pinned ⊆ chordal
  have h1 := card_prefix_le (n := n) y k (fun A => AlonShapira.IsChordal (G.induce (A : Set (Fin n))))
    (fun A A' h hA => isChordal_induce_mono G h hA)
  have hsub : univ.filter (fun w : Fin (y + k) → Fin n => PinnedOn Γ x G (img w)) ⊆
      univ.filter (fun w : Fin (y + k) → Fin n =>
        AlonShapira.IsChordal (G.induce ((img w : Finset (Fin n)) : Set (Fin n)))) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact chordal_of_pinned hw
  have h5 := claim5_count Γ x G ψ c (ε / (2 * K)) hη0 hη1 hc y
  set C := (univ.filter (fun u : Fin y → Fin n =>
    AlonShapira.IsChordal (G.induce ((img u : Finset (Fin n)) : Set (Fin n))))).card with hC
  -- numerics
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ y := by positivity
  have hblock := block_ineq hε0 hε1 hK
  rw [← hy] at hblock
  have hpow : (n : ℝ) ^ (y - 2) * (n : ℝ) ^ 2 = (n : ℝ) ^ y := pow_sub_mul_pow _ hy2
  have hδ : δ11 ε K * (y : ℝ) ^ 2 = 1 / 4 := by
    unfold δ11; rw [← hy]; field_simp
  have hA1 : ((y : ℝ) + 1) * (1 - ε / (2 * K)) ^ (y - 1) * (n : ℝ) ^ y ≤ 1 / 4 * (n : ℝ) ^ y :=
    mul_le_mul_of_nonneg_right hblock hn0
  have hA2 : (y : ℝ) ^ 2 * (pinProblem Γ x G).conf ψ * (n : ℝ) ^ (y - 2) ≤
      1 / 4 * (n : ℝ) ^ y := by
    have hp : (0 : ℝ) ≤ (y : ℝ) ^ 2 * (n : ℝ) ^ (y - 2) := by positivity
    calc (y : ℝ) ^ 2 * (pinProblem Γ x G).conf ψ * (n : ℝ) ^ (y - 2)
        = ((pinProblem Γ x G).conf ψ : ℝ) * ((y : ℝ) ^ 2 * (n : ℝ) ^ (y - 2)) := by ring
      _ ≤ δ11 ε K * (n : ℝ) ^ 2 * ((y : ℝ) ^ 2 * (n : ℝ) ^ (y - 2)) :=
          mul_le_mul_of_nonneg_right hconf.le hp
      _ = δ11 ε K * (y : ℝ) ^ 2 * ((n : ℝ) ^ (y - 2) * (n : ℝ) ^ 2) := by ring
      _ = 1 / 4 * (n : ℝ) ^ y := by rw [hδ, hpow]
  have hCle : (C : ℝ) ≤ 1 / 2 * (n : ℝ) ^ y := by linarith
  have htot : ((2 * (univ.filter (fun w : Fin (y + k) → Fin n =>
      PinnedOn Γ x G (img w))).card : ℕ) : ℝ) ≤ ((2 * (C * n ^ k) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 ((card_le_card hsub).trans h1)
  have hfin : ((2 * (C * n ^ k) : ℕ) : ℝ) ≤ ((n ^ (y + k) : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    have hk0 : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
    nlinarith
  exact_mod_cast htot.trans hfin

/-- **Case B2**: every section is close to a chain graph; the glued graph is then a chordal
graph at distance `< ε n²` from `G`. -/
theorem l11_caseB2 (Γ : RTree K) (x : Fin n → Fin K) (G : SimpleGraph (Fin n))
    (ψ : Fin n → Finset (Fin K)) (hψL : ∀ v, ψ v ∈ (pinProblem Γ x G).L v)
    (hconf : ((pinProblem Γ x G).conf ψ : ℝ) < δ11 ε K * (n : ℝ) ^ 2)
    (hrk : ∀ c : Fin K, ∃ rk : Fin n → ℕ,
      (chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ rk : ℝ) ≤ ε / (2 * K) * (n : ℝ) ^ 2) :
    ∃ F : SimpleGraph (Fin n), AlonShapira.IsChordal F ∧
      (AlonShapira.editDist G F : ℝ) < ε * (n : ℝ) ^ 2 := by
  choose rk hrk using hrk
  set rk' : Fin K → Fin n → ℕ := fun c => normRk (rk c)
  have hB : ∀ c u, rk' c u ≤ n := fun c u => normRk_le _ _
  have hsub : ∀ u, Γ.IsSub (ψ u) := fun u => by
    have := hψL u
    simp only [pinProblem, mem_filter, mem_univ, true_and] at this
    exact this.1
  refine ⟨glueGraph Γ ψ rk' n, glueGraph_chordal Γ ψ rk' n hB hsub, ?_⟩
  have hd := editDist_glue_le Γ x G ψ rk' n hB hψL
  simp only [rk', chainMisOn_normRk] at hd
  have hd' : (AlonShapira.editDist G (glueGraph Γ ψ rk' n) : ℝ) ≤
      (pinProblem Γ x G).conf ψ + ∑ c, (chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ (rk c) : ℝ) := by
    exact_mod_cast hd
  have hsum : ∑ c, (chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ (rk c) : ℝ) ≤
      ε / 2 * (n : ℝ) ^ 2 := by
    calc ∑ c, (chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ (rk c) : ℝ)
        ≤ ∑ _c : Fin K, ε / (2 * K) * (n : ℝ) ^ 2 := sum_le_sum (fun c _ => hrk c)
      _ = ε / 2 * (n : ℝ) ^ 2 := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hK0 : (K : ℝ) ≠ 0 := by positivity
          field_simp
  have hhalf := δ11_le_half hε0 hε1 hK
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have : δ11 ε K * (n : ℝ) ^ 2 ≤ ε / 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hhalf hn2
  linarith

end Cases

/-! ## Lemma 11 -/

/-- **Lemma 11 of arXiv:1902.06135** with the explicit sample size
`m11V ε K = ⌈2^58 (K+1)^15 / ε^12⌉₊`. -/
theorem lemma11_V : Lemma11Explicit := by
  intro ε hε0 K Γ n G x hfar
  obtain ⟨hε2, hn⟩ := far_basic hfar
  have hε1 : ε < 1 := by linarith
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; exact (x ⟨0, hn⟩).elim0
    · exact h
  by_cases hA : ∀ ψ : Fin n → Finset (Fin K), (∀ v, ψ v ∈ (pinProblem Γ x G).L v) →
      δ11 ε K * (n : ℝ) ^ 2 ≤ (pinProblem Γ x G).conf ψ
  · exact l11_caseA hε0 hε1 hK Γ x G hA
  push_neg at hA
  obtain ⟨ψ, hψL, hconf⟩ := hA
  by_cases hB : ∃ c : Fin K, ∀ rk : Fin n → ℕ, ε / (2 * K) * (n : ℝ) ^ 2 <
      chainMisOn G (Lc Γ ψ c) (Rc Γ ψ c) univ rk
  · obtain ⟨c, hc⟩ := hB
    exact l11_caseB1 hε0 hε1 hK Γ x G ψ hconf c hc
  · push_neg at hB
    exfalso
    obtain ⟨F, hF, hd⟩ := l11_caseB2 hε0 hε1 hK Γ x G ψ hψL hconf hB
    linarith [hfar F hF]

/-! ## Unconditional corollaries -/

open PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.FixedL4 PaperIV.DefectTargetArithmetic

/-- **Theorem 1 of arXiv:1902.06135** (subset form, explicit sample size `mVq ε`,
threshold `mVq ε`), unconditionally. -/
theorem chordalEasyRemoval_final : ChordalEasyRemovalWith mVq mVq :=
  chordalEasyRemoval_V lemma11_V

/-- **`E33.EditApproxExplicit` with the explicit closed-form threshold `NeditE`**,
unconditionally. -/
theorem editApproxExplicit_final : E33.EditApproxExplicit NeditE :=
  editApproxExplicit_V lemma11_V

/-- **Theorem C, fully explicit and unconditional**: above `E33.Fexp NeditE s`. -/
theorem theoremC_fully_explicit_final (s n : ℕ)
    (hn : E33.Fexp NeditE s ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdef : RootedDefectAt G s) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_fully_explicit lemma11_V s n hn G hdef

/-- **Uniform Theorem C, fully explicit and unconditional.** -/
theorem theoremC_fully_explicit_uniform_final (n : ℕ)
    (h0 : E33.Fmono NeditE 0 ≤ n) :
    ∀ s : ℕ, s ≤ E33.Finv NeditE n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n :=
  theoremC_fully_explicit_uniform lemma11_V n h0

end E34
