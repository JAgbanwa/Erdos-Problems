import A4S1.CriticalReduction
import A4S1.TerminalPacking
import PaperIV.EditRouteUnconditional
import PaperIV.CertifiedF4Bridge
import PaperIV.CertifiedOptimumExistence

/-!
# A4 at rooted defect one from the terminal with a minimum-degree hypothesis

This is the §9 assembly of the handoff note `TERMINAL_S1_PRUEBA_20260924.md` (theorem T1). The terminal ledger only has
to be proved for graphs of **minimum degree at least `(1/3 − ε) n`**:

`MinDegTerminal₁ ε`: for large `n`, every rooted-defect-one graph with `δ(G) ≥ (1/3 − ε) n`, near-extremal for the
fixed-`L = 4` functional and carrying a localized real clique at precision `ε`, has an order-four clique partition with
at most `Q₁(n)` pieces.

`a4Sharp_one_of_minDegTerminal`: `MinDegTerminal₁ ε` for one `ε > 0` gives `A4Sharp₁`. There is **no base order**,
unlike `A4S1.CriticalReduction.a4Sharp_one_of_critical`. The argument has two steps.

1. **A global constant.** Let `N₀` be the threshold of the far regime, the localization and the terminal, and
   `K = N₀²`. Then `c₄(G) ≤ Q₁(n) + K` at **every** order, by induction on `n` (`targetK_all`).
   * Below `N₀` the trivial partition into edges has at most `n² ≤ K` pieces.
   * Above `N₀`, a vertex of degree at most `⌊(n+2)/3⌋ = Q₁(n) − Q₁(n−1)` is deleted and its edges paid as `K₂`.
   * Otherwise `δ(G) > n/3`, and the far regime or the localized terminal give `Q₁(n)`.
2. **Removing the constant.** At large `n`, a vertex with `deg v + K ≤ ⌊(n+2)/3⌋` is deleted with the bound of
   step 1. Otherwise `δ(G) ≥ n/3 − K ≥ (1/3 − ε) n` once `ε n ≥ K + 1`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/

namespace A4S1.MinDegreeTerminal

open Finset PaperIV.FarRounding PaperIV.DefectTargetArithmetic PaperIV.RootedSimplicialDefect
  PaperIV.DefectApexStability PaperIV.FixedL4 A4S1.DefectOneReduction A4S1.CriticalReduction

/-- The localized terminal ledger at rooted defect one, restricted to minimum degree `≥ (1/3 − ε) n`. -/
def MinDegTerminal₁ (eps : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    RootedDefectAt G 1 →
    (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
    (n : ℝ) ^ 2 / 6 - (eps : ℝ) * (n : ℝ) ^ 2 ≤ PaperIV.VertexCopyGate.F4' G →
    Nonempty (LocalizedClique G eps) →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n

/-- The target up to an additive constant `K`. -/
def TargetK (K n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G 1 →
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n + K

/-- **Deleting one vertex.** From the target with constant `K` at order `n`, every graph of order `n + 1` gets a
partition with at most `Q₁(n) + K + deg v` pieces. -/
theorem delete_vertex {n K : ℕ} (ht : TargetK K n)
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hdef : RootedDefectAt G 1)
    (v : Fin (n + 1)) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n + K + G.degree v := by
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
  have ht' : TargetK K n' := hn'eq ▸ ht
  obtain ⟨QH, hQH4, hQHsize⟩ := ht' H hHdef
  obtain ⟨Q0, hQ04, hQ0s⟩ := exists_push_partition G D e he H hH QH hQH4
  obtain ⟨P, hP4, hPs⟩ := PaperIV.SubgraphPadding.exists_cliquePartition_of_subgraph
    G (avoidPart G D) (avoidPart_le G D) Q0 hQ04
  rw [sdiff_avoidPart] at hPs
  have hT : (G.edgeFinset.filter (Touches D)).card = G.degree v := by
    rw [A4S1.DefectOneAbsorbed.card_touch_singleton, SimpleGraph.card_neighborFinset_eq_degree]
  refine ⟨P, hP4, ?_⟩
  have hQHn : QH.size ≤ defectTarget 1 n + K := by rw [← hn'eq]; exact hQHsize
  omega

/-- The trivial partition into edges has at most `n²` pieces. -/
theorem trivial_partition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ n * n := by
  classical
  obtain ⟨Q, hQ4, hQ⟩ := A4S1.TerminalPacking.exists_partition_of_triangles (G := G) ∅
    (by simp) (by simp) (by simp)
  refine ⟨Q, hQ4, ?_⟩
  have h1 : G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 :=
    G.card_edgeFinset_le_card_choose_two
  rw [Fintype.card_fin, Nat.choose_two_right] at h1
  have h2 : n * (n - 1) / 2 ≤ n * n :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  simp only [card_empty, mul_zero, add_zero] at hQ
  omega

/-- **The near/far step.** Beyond the thresholds, a graph of minimum degree `≥ (1/3 − ε) n` meets the target. -/
theorem near_or_far {eps : ℚ} (heps : 0 < eps) (hterm : MinDegTerminal₁ eps) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G 1 → (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n := by
  classical
  obtain ⟨eta, heta, NL, hNL⟩ := PaperIV.EditRoute.fixedL4Localization_unconditional 1 eps heps
  set eta' : ℚ := min eta eps with heta'
  have heta'pos : 0 < eta' := lt_min heta heps
  have h1 : eta' ≤ eta := min_le_left _ _
  have h2 : eta' ≤ eps := min_le_right _ _
  obtain ⟨Nf, hNf⟩ := PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs eta' heta'pos
  obtain ⟨NT, hNT⟩ := hterm
  refine ⟨NL + Nf + NT + 3, by omega, ?_⟩
  intro n hn G _ hdef hdeg
  by_cases hfar : PaperIV.VertexCopyGate.F4' G <
      (n : ℝ) ^ 2 / 6 - (eta' : ℝ) * (n : ℝ) ^ 2
  · obtain ⟨Q, hQ4, hQs⟩ := hNf n (by omega) G hfar
    exact ⟨Q, hQ4, le_trans hQs (targetSize_le_defectTarget 1 n (by omega))⟩
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

/-- **Step 1: a global additive constant.** -/
theorem targetK_all {eps : ℚ} (heps : 0 < eps) (N₀ : ℕ) (hN₀ : 2 ≤ N₀)
    (hnear : ∀ n : ℕ, N₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G 1 → (∀ v : Fin n, ((1 : ℚ) / 3 - eps) * n ≤ (G.degree v : ℚ)) →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget 1 n) :
    ∀ n : ℕ, TargetK (N₀ * N₀) n := by
  intro n
  induction n with
  | zero =>
      intro G _ _
      obtain ⟨Q, hQ4, hQ⟩ := trivial_partition G
      exact ⟨Q, hQ4, by simp at hQ; omega⟩
  | succ n ih =>
      intro G _ hdef
      by_cases hsmall : n + 1 < N₀
      · obtain ⟨Q, hQ4, hQ⟩ := trivial_partition G
        refine ⟨Q, hQ4, le_trans hQ ?_⟩
        have : (n + 1) * (n + 1) ≤ N₀ * N₀ := Nat.mul_le_mul (by omega) (by omega)
        omega
      push_neg at hsmall
      by_cases hlow : ∃ v : Fin (n + 1), G.degree v ≤ (n + 1 + 2) / 3
      · obtain ⟨v, hv⟩ := hlow
        obtain ⟨Q, hQ4, hQ⟩ := delete_vertex ih G hdef v
        refine ⟨Q, hQ4, ?_⟩
        rw [defectTarget_one_succ n (by omega)]
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

/-- **A4 at rooted defect one from the minimum-degree terminal.** -/
theorem a4Sharp_one_of_minDegTerminal {eps : ℚ} (heps : 0 < eps) (hterm : MinDegTerminal₁ eps) :
    A4Sharp₁ := by
  classical
  obtain ⟨N₀, hN₀, hnear⟩ := near_or_far heps hterm
  set K := N₀ * N₀ with hK
  have hall := targetK_all heps N₀ hN₀ hnear
  set M : ℕ := ⌈((K : ℚ) + 1) / eps⌉₊ with hM
  refine ⟨N₀ + M + 1, ?_⟩
  intro m hm G _ hdef
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases hlow : ∃ v : Fin (n + 1), G.degree v + K ≤ (n + 1 + 2) / 3
  · obtain ⟨v, hv⟩ := hlow
    obtain ⟨Q, hQ4, hQ⟩ := delete_vertex (hall n) G hdef v
    refine ⟨Q, hQ4, ?_⟩
    rw [defectTarget_one_succ n (by omega)]
    omega
  push_neg at hlow
  refine hnear (n + 1) (by omega) G hdef (fun v => ?_)
  have h := hlow v
  have h3 : n + 4 ≤ 3 * (G.degree v + K) := by omega
  have h3Q : ((n : ℚ) + 4) ≤ 3 * ((G.degree v : ℚ) + K) := by exact_mod_cast h3
  have hMle : ((K : ℚ) + 1) / eps ≤ (M : ℚ) := Nat.le_ceil _
  have hnM : (M : ℚ) ≤ (n : ℚ) + 1 := by
    have : M ≤ n + 1 := by omega
    exact_mod_cast this
  have hKe : (K : ℚ) + 1 ≤ eps * ((n : ℚ) + 1) := by
    have := (div_le_iff₀ heps).1 (hMle.trans hnM)
    linarith
  push_cast
  nlinarith

end A4S1.MinDegreeTerminal
