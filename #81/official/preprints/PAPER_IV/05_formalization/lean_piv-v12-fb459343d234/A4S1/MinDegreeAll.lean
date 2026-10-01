import A4S1.MinDegreeTerminal
import PaperIV.A4AllDefects

/-!
# A4 at every rooted defect `s` from the minimum-degree terminal

The generalization of `A4S1.MinDegreeTerminal` (the §9 assembly of theorem T1) to every rooted defect `s`, with
`Q_s(n) = defectTarget s n = M(n+s) − C(s+1,2)` and `Q_s(n+1) = Q_s(n) + ⌊(n+s+2)/3⌋` (`defectTarget_succ`).

`MinDegTerminal s ε`: the localized terminal ledger at defect `s`, restricted to graphs of minimum degree at least
`(1/3 − ε) n`.

`a4Sharp_of_minDegTerminal`: `MinDegTerminal s ε` for one `ε > 0` gives `PaperIV.A4AllDefects.A4Sharp s`, with no
base order. First `c₄ ≤ Q_s(n) + N₀²` holds at every order. Then the constant is removed by deleting a vertex of degree
`≤ ⌊(n+s+2)/3⌋ − N₀²`; if there is none, `δ ≥ (1/3 − ε) n`.

So for every `s` the open input of A4 is the terminal **with a minimum-degree hypothesis**. This is the form in which
T1 (`TERMINAL_S1_PRUEBA_20260924.md`, after Okechukwu §§4–5) is proved.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/

namespace A4S1.MinDegreeAll

open Finset PaperIV.FarRounding PaperIV.DefectTargetArithmetic PaperIV.RootedSimplicialDefect
  PaperIV.DefectApexStability PaperIV.FixedL4 A4S1.CriticalReduction PaperIV.A4AllDefects

/-- `M(m+1) = M(m) + ⌊(m+2)/3⌋`. -/
theorem targetSize_succ (m : ℕ) :
    PaperIV.FarRounding.targetSize (m + 1) = PaperIV.FarRounding.targetSize m + (m + 2) / 3 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> decide
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have h := defectTarget_one_succ n (by omega)
    have h1 : 1 ≤ PaperIV.FarRounding.targetSize (n + 1) := by
      rw [farRounding_targetSize_eq]
      exact le_trans (by decide : 1 ≤ PaperIV.targetSize 2) (targetSize_mono (by omega))
    unfold defectTarget at h
    simp only [Nat.choose_self] at h
    omega

/-- `Q_s(n+1) = Q_s(n) + ⌊(n+s+2)/3⌋`. -/
theorem defectTarget_succ (s n : ℕ) (hn : s + 2 ≤ n) :
    defectTarget s (n + 1) = defectTarget s n + (n + s + 2) / 3 := by
  have hle := targetSize_le_defectTarget s n (by omega)
  have h2 : 1 ≤ PaperIV.FarRounding.targetSize n := by
    rw [farRounding_targetSize_eq]
    exact le_trans (by decide : 1 ≤ PaperIV.targetSize 2) (targetSize_mono (by omega))
  have hsucc := targetSize_succ (n + s)
  unfold defectTarget at hle ⊢
  rw [show n + 1 + s = n + s + 1 by ring, hsucc]
  omega

/-- The localized terminal ledger at defect `s`, restricted to minimum degree `≥ (1/3 − ε) n`. -/
def MinDegTerminal (s : ℕ) (eps : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G s →
    (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
    (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (LocalizedClique G eps) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n

/-- The target at defect `s` up to an additive constant `K`. -/
def TargetK (s K n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n + K

/-- **Deleting one vertex** at defect `s`. -/
theorem delete_vertex {s n K : ℕ} (ht : TargetK s K n)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hdef : RootedDefectAt G s)
    (v : Fin (n + 1)) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n + K + G.degree v := by
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
  have hHdef : RootedDefectAt H s := rootedDefectAt_comap G e H hH hdef
  have ht' : TargetK s K n' := hn'eq ▸ ht
  obtain ⟨QH, hQH4, hQHsize⟩ := ht' H hHdef
  obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH QH hQH4
  obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
  rw [sdiff_avoidPart] at hPs
  have hT : (G.edgeFinset.filter (Touches D)).card = G.degree v := by
    rw [A4S1.DefectOneAbsorbed.card_touch_singleton, SimpleGraph.card_neighborFinset_eq_degree]
  refine ⟨P, hP4, ?_⟩
  have hQHn : QH.size ≤ defectTarget s n + K := by rw [← hn'eq]; exact hQHsize
  omega

/-- **The near/far step** at defect `s`. -/
theorem near_or_far {s : ℕ} {eps : ℚ} (heps : 0 < eps) (hterm : MinDegTerminal s eps) :
    ∃ N₀ : ℕ, s + 3 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s → (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  classical
  obtain ⟨eta, heta, NL, hNL⟩ := PaperIV.EditRoute.fixedL4Localization_unconditional s eps heps
  set eta' : ℚ := min eta eps with heta'
  have heta'pos : 0 < eta' := lt_min heta heps
  have h1 : eta' ≤ eta := min_le_left _ _
  have h2 : eta' ≤ eps := min_le_right _ _
  obtain ⟨Nf, hNf⟩ := PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs eta' heta'pos
  obtain ⟨NT, hNT⟩ := hterm
  refine ⟨NL + Nf + NT + s + 3, by omega, ?_⟩
  intro n hn G _ hdef hdeg
  by_cases hfar : PaperIV.VertexCopyGate.F4' G <
      (n : ℝ) ^ 2 / 6 - (eta' : ℝ) * (n : ℝ) ^ 2
  · obtain ⟨Q, hQ4, hQs⟩ := hNf n (by omega) G hfar
    exact ⟨Q, hQ4, le_trans hQs (targetSize_le_defectTarget s n (by omega))⟩
  push_neg at hfar
  have hsqR : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1R : (eta' : ℝ) ≤ (eta : ℝ) := by exact_mod_cast h1
  have h2R : (eta' : ℝ) ≤ (eps : ℝ) := by exact_mod_cast h2
  have hfarEps : (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G := by
    nlinarith
  obtain ⟨w, hw⟩ := PaperIV.CertifiedOptimumExistence.exists_certifiedFractionalOptimum G
  have hF := PaperIV.CertifiedF4Bridge.F4'_eq_edge_sub_certified hw
  have hnear : (n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 ≤ (G.edgeFinset.card : ℚ) - w := by
    have hR : (n : ℝ) ^ 2 / 6 - (eta : ℝ) * (n : ℝ) ^ 2 ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      rw [← hF]; nlinarith
    have h : ((((n : ℚ) ^ 2 / 6 - eta * (n : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((G.edgeFinset.card : ℚ) - w : ℚ) : ℝ) := by
      push_cast at hR ⊢; linarith
    exact_mod_cast h
  exact hNT n (by omega) G hdef hdeg hfarEps (hNL n (by omega) G hdef w hw hnear)

/-- **Step 1: a global additive constant** at defect `s`. -/
theorem targetK_all {s : ℕ} {eps : ℚ} (heps : 0 < eps) (N₀ : ℕ) (hN₀ : s + 3 ≤ N₀)
    (hnear : ∀ n : ℕ, N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s → (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n) :
    ∀ n : ℕ, TargetK s (N₀ * N₀) n := by
  intro n
  induction n with
  | zero =>
      intro G _ _
      obtain ⟨Q, hQ4, hQ⟩ := A4S1.MinDegreeTerminal.trivial_partition G
      exact ⟨Q, hQ4, by simp at hQ; omega⟩
  | succ n ih =>
      intro G _ hdef
      by_cases hsmall : n + 1 < N₀
      · obtain ⟨Q, hQ4, hQ⟩ := A4S1.MinDegreeTerminal.trivial_partition G
        refine ⟨Q, hQ4, le_trans hQ ?_⟩
        have : (n + 1) * (n + 1) ≤ N₀ * N₀ := Nat.mul_le_mul (by omega) (by omega)
        omega
      push_neg at hsmall
      by_cases hlow : ∃ v : Fin (n + 1), G.degree v ≤ (n + s + 2) / 3
      · obtain ⟨v, hv⟩ := hlow
        obtain ⟨Q, hQ4, hQ⟩ := delete_vertex ih G hdef v
        refine ⟨Q, hQ4, ?_⟩
        rw [defectTarget_succ s n (by omega)]
        omega
      push_neg at hlow
      obtain ⟨Q, hQ4, hQ⟩ := hnear (n + 1) hsmall G hdef (fun v => by
        have h := hlow v
        have h3 : n + 1 < 3 * G.degree v := by omega
        have h3Q : ((n + 1 : ℕ) : ℚ) < 3 * (G.degree v : ℚ) := by exact_mod_cast h3
        have hnn : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by positivity
        push_cast at h3Q ⊢
        nlinarith)
      exact ⟨Q, hQ4, le_trans hQ (Nat.le_add_right _ _)⟩

/-- **A4 at rooted defect `s` from the minimum-degree terminal.** -/
theorem a4Sharp_of_minDegTerminal (s : ℕ) {eps : ℚ} (heps : 0 < eps) (hterm : MinDegTerminal s eps) :
    A4Sharp s := by
  classical
  obtain ⟨N₀, hN₀, hnear⟩ := near_or_far heps hterm
  set K := N₀ * N₀ with hK
  have hall := targetK_all heps N₀ hN₀ hnear
  set M : ℕ := ⌈((K : ℚ) + 1) / eps⌉₊ with hM
  refine ⟨N₀ + M + 1, ?_⟩
  intro m hm G _ hdef
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases hlow : ∃ v : Fin (n + 1), G.degree v + K ≤ (n + s + 2) / 3
  · obtain ⟨v, hv⟩ := hlow
    obtain ⟨Q, hQ4, hQ⟩ := delete_vertex (hall n) G hdef v
    refine ⟨Q, hQ4, ?_⟩
    rw [defectTarget_succ s n (by omega)]
    omega
  push_neg at hlow
  refine hnear (n + 1) (by omega) G hdef (fun v => ?_)
  have h := hlow v
  have h3 : n + 3 ≤ 3 * (G.degree v + K) := by omega
  have h3Q : ((n : ℚ) + 3) ≤ 3 * ((G.degree v : ℚ) + K) := by exact_mod_cast h3
  have hMle : ((K : ℚ) + 1) / eps ≤ (M : ℚ) := Nat.le_ceil _
  have hnM : (M : ℚ) ≤ (n : ℚ) + 1 := by
    have : M ≤ n + 1 := by omega
    exact_mod_cast this
  have hKe : (K : ℚ) + 1 ≤ eps * ((n : ℚ) + 1) := by
    have := (div_le_iff₀ heps).1 (hMle.trans hnM)
    linarith
  push_cast
  nlinarith

end A4S1.MinDegreeAll
