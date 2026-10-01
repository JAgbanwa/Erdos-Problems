import E32.PieceIdentity
import E32.DeletionInduction

/-!
# E32 — from linear edit stability (a) to partition stability (b) and classification (c)

* `EditStable s γ Cs N` — statement (a) of Theorem C′ with constant `Cs`.
* `TheoremCPrimeAB s γ Cs N` — (a) and (b) together, with the **same** root, chosen before
  the partition `Q`: at most `τ + (1 + 7·Cs)·δ` noncanonical pieces in every clique partition `Q`
  (no order restriction) with `|Q| ≤ Q_s(n) + τ`.
* `TheoremCPrimeC s N` — statement (c): for `n ≥ N` and `RootedDefectAt G s`,
  `c₄(G) = Q_s(n)` iff `G` is `E_s(n,k)` with `k` a nearest integer to `(2(n+s)+1)/6`.
* `theoremCPrime_of_editStable` — (a) + Theorem C imply (a)+(b) and (c).

The arithmetic: `rootBaseline + C(s+1,2) = baseline(n+s, k)` with `k = |C| + s`
(`rootBaseline_add_choose`), so `rootBaseline ≤ Q_s(n)`, with equality iff `k` is an optimal
core of `n + s` (`SplitCompleteRigidity.baseline_eq_targetSize_iff`), i.e. a nearest integer.
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic PaperIV.ExtremalClassification
open scoped symmDiff

/-! ## Arithmetic -/

theorem rootBaseline_add_choose (c s h : ℕ) (hch : c ≤ h) :
    ((c + s) * h - c.choose 2) + (s + 1).choose 2 =
      (c + s) * (h + s) - (c + s).choose 2 := by
  have h1 : c.choose 2 ≤ (c + s) * h :=
    le_trans (choose_two_le_mul hch) (Nat.mul_le_mul_right _ (by omega))
  have h2 : (c + s).choose 2 ≤ (c + s) * (h + s) := choose_two_le_mul (by omega)
  have e1 := two_mul_choose_two_int c
  have e2 := two_mul_choose_two_int (c + s)
  have e3 := two_mul_choose_two_int (s + 1)
  have hZ : ((((c + s) * h - c.choose 2) + (s + 1).choose 2 : ℕ) : ℤ) =
      (((c + s) * (h + s) - (c + s).choose 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at e1 e2 e3 ⊢
    nlinarith
  exact_mod_cast hZ

theorem targetSize_ge_choose (n s : ℕ) (hn : s + 1 ≤ n) :
    (s + 1).choose 2 ≤ targetSize (n + s) := by
  -- the optimal core `k = (n+s+1)/3` exhibits `targetSize (n+s) = rootBaseline-type + C(s+1,2)`
  have h := targetSize_le_defectTarget s n hn
  have hM : targetSize n ≤ targetSize (n + s) := by
    rw [PaperIV.DefectApexStability.farRounding_targetSize_eq,
      PaperIV.DefectApexStability.farRounding_targetSize_eq]
    exact PaperIV.DefectApexStability.targetSize_mono (by omega)
  unfold defectTarget at h
  -- `targetSize n ≤ targetSize (n+s) - C(s+1,2)` forces the subtraction to be honest unless
  -- `targetSize n = 0`
  by_contra hlt
  push_neg at hlt
  have h0 : targetSize (n + s) - (s + 1).choose 2 = 0 := Nat.sub_eq_zero_of_le hlt.le
  rw [h0] at h
  have hn0 : targetSize n = 0 := by omega
  have hs : (s + 1).choose 2 ≤ targetSize (n + s) := by
    -- `targetSize (n+s) ≥ (n+s)(n+s+1)/6 - 1` and `n ≥ s + 1`
    have hdiv := Nat.div_add_mod ((n + s) * (n + s + 1)) 6
    have hmod := Nat.mod_lt ((n + s) * (n + s + 1)) (show 0 < 6 by norm_num)
    have hch : 2 * (s + 1).choose 2 = (s + 1) * s := by
      rw [Nat.choose_two_right, Nat.mul_comm 2]
      exact Nat.div_mul_cancel (Nat.even_mul_pred_self (s + 1)).two_dvd
    have hts : targetSize (n + s) = (n + s) * (n + s + 1) / 6 := rfl
    have hn1 : (s + 1) * s * 3 + 6 ≤ (n + s) * (n + s + 1) := by nlinarith
    omega
  omega

/-- `rootBaseline ≤ Q_s(n)`, with equality iff the core size is a nearest integer. -/
theorem rootBaseline_le_and_eq_iff {n s c h : ℕ} (hsum : c + s + h = n) (hch : c ≤ h)
    (hn : s + 2 ≤ n) :
    (c + s) * h - c.choose 2 ≤ defectTarget s n ∧
      ((c + s) * h - c.choose 2 = defectTarget s n ↔ NearestCore (n + s) (c + s)) := by
  have hid := rootBaseline_add_choose c s h hch
  have hk : c + s ≤ n + s := by omega
  have hhs : h + s = n + s - (c + s) := by omega
  have hbase : PaperIV.SplitCompleteRigidity.baseline (n + s) (c + s) =
      (c + s) * (h + s) - (c + s).choose 2 := by
    unfold PaperIV.SplitCompleteRigidity.baseline; rw [hhs]
  have hle := PaperIV.SplitCompleteRigidity.baseline_le_targetSize (n + s) (c + s) hk
  have hge := targetSize_ge_choose n s (by omega)
  have hiff := PaperIV.SplitCompleteRigidity.baseline_eq_targetSize_iff (n + s) (c + s)
    (by omega) hk
  have hT : PaperIV.targetSize (n + s) = targetSize (n + s) := rfl
  unfold defectTarget
  rw [hbase] at hle hiff
  rw [hT] at hle hiff
  refine ⟨by omega, ?_⟩
  rw [nearestCore_iff_optimalCore]
  constructor
  · intro heq
    have : (c + s) * (h + s) - (c + s).choose 2 = targetSize (n + s) := by omega
    rcases hiff.1 this with h1 | h1
    · exact Or.inl h1
    · right; constructor <;> omega
  · intro hopt
    have : (c + s) * (h + s) - (c + s).choose 2 = targetSize (n + s) := by
      apply hiff.2
      rcases hopt with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · right; omega
    omega

/-- A nearest core leaves room for the exterior: `|C| ≤ |H|`. -/
theorem core_le_hosts_of_nearest {n s c h : ℕ} (hsum : c + s + h = n) (hn : 4 ≤ n)
    (hnear : NearestCore (n + s) (c + s)) : c ≤ h := by
  unfold NearestCore at hnear
  rw [abs_le] at hnear
  omega

/-! ## Stability statements -/

/-- Statement (a) of Theorem C′. -/
def EditStable (s : ℕ) (γ Cs : ℚ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ * (n : ℚ) ^ 2 →
    (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ) - δ ≤ Q.size) →
      ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧ (rootEdit G C D H : ℚ) ≤ Cs * δ

open Classical in
/-- Statements (a) and (b) of Theorem C′, with one root serving every partition. -/
def TheoremCPrimeAB (s : ℕ) (γ Cs : ℚ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ * (n : ℚ) ^ 2 →
    (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℚ) - δ ≤ Q.size) →
      ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧
        (rootEdit G C D H : ℚ) ≤ Cs * δ ∧
        ∀ τ : ℚ, 0 ≤ τ → ∀ Q : CliquePartition G, (Q.size : ℚ) ≤ defectTarget s n + τ →
          ((Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K).card : ℚ) ≤
            τ + (1 + 7 * Cs) * δ

/-- Statement (c) of Theorem C′: the eventual extremal graphs for `c₄`. -/
def TheoremCPrimeC (s N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], RootedDefectAt G s →
    (CliqueCover4Eq G (defectTarget s n) ↔ IsAdmissibleExtremal G s)

/-- The edit distance splits into deleted and added edges. -/
theorem rootEdit_eq_add {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (C D H : Finset V) :
    rootEdit G C D H = (G.edgeFinset \ (defSplitGraph C D H).edgeFinset).card +
      ((defSplitGraph C D H).edgeFinset \ G.edgeFinset).card := by
  unfold rootEdit PaperIV.EditMetric.editDist
  exact card_union_of_disjoint disjoint_sdiff_sdiff

/-- An order-`≤ 4` partition of `G` with at most `rootBaseline + 4·rootEdit` pieces. -/
theorem exists_partition_near_root {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s : ℕ} {C D H : Finset V} (hR : IsDefectRoot G s C D H) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size ≤ rootBaseline C D H + 4 * rootEdit G C D H := by
  obtain ⟨QE, hQE4, hQE⟩ := exists_extremal_partition (D := D) hR.disjCH hR.two_le
    hR.core_le_hosts
  obtain ⟨Q, hQ4, hQ⟩ := exists_partition_of_edit G (defSplitGraph C D H) QE hQE4
  refine ⟨Q, hQ4, ?_⟩
  have := rootEdit_eq_add G C D H
  omega

/-- The root-size identity `rootBaseline = (|C| + s)·|H| − C(|C|,2)`, `|C| + s + |H| = n`. -/
theorem IsDefectRoot.card_sum {n : ℕ} {G : SimpleGraph (Fin n)} {s : ℕ} {C D H : Finset (Fin n)}
    (hR : IsDefectRoot G s C D H) : C.card + s + H.card = n := by
  have h1 : (C ∪ D ∪ H) = univ := by
    ext x; simp only [mem_union, mem_univ, iff_true]
    rcases hR.cover x with h | h | h <;> tauto
  have h2 := congrArg card h1
  rw [card_union_of_disjoint (disjoint_union_left.2 ⟨hR.disjCH, hR.disjDH⟩),
    card_union_of_disjoint hR.disjCD, card_univ,
    Fintype.card_fin, hR.card_def] at h2
  exact h2

/-- **(a) ⟹ (a) + (b).** -/
theorem theoremCPrimeAB_of_editStable {s : ℕ} {γ Cs : ℚ} {N : ℕ}
    (hA : EditStable s γ Cs N) : TheoremCPrimeAB s γ Cs N := by
  classical
  intro n hn G _ hdef δ hδ0 hδ hlow
  obtain ⟨C, D, H, hR, hE⟩ := hA n hn G hdef δ hδ0 hδ hlow
  refine ⟨C, D, H, hR, hE, ?_⟩
  intro τ hτ Q hQ
  have hnc := noncanonical_card_le hR Q
  obtain ⟨Q0, hQ04, hQ0⟩ := exists_partition_near_root G hR
  have hl := hlow Q0 hQ04
  have hQ0Q : (Q0.size : ℚ) ≤ rootBaseline C D H + 4 * rootEdit G C D H := by exact_mod_cast hQ0
  have hncQ : ((Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K).card : ℚ) ≤
      (Q.size : ℚ) - (rootBaseline C D H : ℚ) + 3 * (rootEdit G C D H : ℚ) := by
    exact_mod_cast hnc
  convert (show ((Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K).card : ℚ) ≤
      τ + (1 + 7 * Cs) * δ by nlinarith) using 3

/-- **(a) + Theorem C ⟹ (c).** -/
theorem theoremCPrimeC_of_editStable {s : ℕ} {γ Cs : ℚ} {N NC : ℕ} (hγ : 0 ≤ γ)
    (hA : EditStable s γ Cs N) (hC : TheoremCAt s NC) :
    TheoremCPrimeC s (N + NC + s + 4) := by
  classical
  intro n hn G _ hdef
  constructor
  · rintro ⟨hlow4, -⟩
    obtain ⟨C, D, H, hR, hE⟩ := hA n (by omega) G hdef 0 le_rfl (by positivity)
      (fun Q hQ => by
        have h1 := hlow4 Q hQ
        have h2 : (defectTarget s n : ℚ) ≤ Q.size := by exact_mod_cast h1
        linarith)
    have hE0 : rootEdit G C D H = 0 := by
      have : (rootEdit G C D H : ℚ) ≤ 0 := by simpa using hE
      exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
    have hGE : G = defSplitGraph C D H := by
      have := PaperIV.EditMetric.editDist_eq_zero_iff.1 hE0
      exact SimpleGraph.edgeFinset_inj.1 this
    obtain ⟨Q0, hQ04, hQ0⟩ := exists_partition_near_root G hR
    rw [hE0, mul_zero, add_zero] at hQ0
    have hl := hlow4 Q0 hQ04
    have hsum := hR.card_sum
    have hB := rootBaseline_le_and_eq_iff (c := C.card) (s := s) (h := H.card) hsum
      hR.core_le_hosts (by omega)
    have hrb : rootBaseline C D H = (C.card + s) * H.card - C.card.choose 2 := by
      unfold rootBaseline; rw [hR.card_def]
    refine ⟨C, D, H, hR.disjCD, hR.disjCH, hR.disjDH, hR.cover, hR.card_def, hGE, ?_⟩
    rw [Fintype.card_fin]
    apply hB.2.1
    rw [← hrb]
    omega
  · rintro ⟨C, D, H, hCD, hCH, hDH, hcov, hDs, hGE, hnear⟩
    rw [Fintype.card_fin] at hnear
    have hsum : C.card + s + H.card = n := by
      have h1 : (C ∪ D ∪ H) = univ := by
        ext x; simp only [mem_union, mem_univ, iff_true]
        rcases hcov x with h | h | h <;> tauto
      have h2 := congrArg card h1
      rw [card_union_of_disjoint (disjoint_union_left.2 ⟨hCH, hDH⟩),
        card_union_of_disjoint hCD, card_univ, Fintype.card_fin, hDs] at h2
      exact h2
    have hch := core_le_hosts_of_nearest hsum (by omega) hnear
    have hB := rootBaseline_le_and_eq_iff (c := C.card) (s := s) (h := H.card) hsum hch
      (by omega)
    have heq := hB.2.2 hnear
    refine ⟨fun Q _ => ?_, ?_⟩
    · have hl := PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline hCD hDH
        (disjoint_union_left.2 ⟨hCH, hDH⟩)
        (PaperIV.CliquePartitionTransport.transport (fun x y => by rw [hGE]) Q)
      rw [PaperIV.CliquePartitionTransport.transport_size, hDs] at hl
      omega
    · obtain ⟨Q, hQ4, hQ⟩ := hC n (by omega) G hdef
      refine ⟨Q, hQ4, le_antisymm hQ ?_⟩
      have hl := PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline hCD hDH
        (disjoint_union_left.2 ⟨hCH, hDH⟩)
        (PaperIV.CliquePartitionTransport.transport (fun x y => by rw [hGE]) Q)
      rw [PaperIV.CliquePartitionTransport.transport_size, hDs] at hl
      omega

end E32
