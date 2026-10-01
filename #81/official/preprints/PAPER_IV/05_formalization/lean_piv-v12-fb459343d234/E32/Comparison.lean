import E32.Main

/-!
# E32 — comparison corollary

`Ref15Theorem11Statement s` is the published statement of [15, Theorem 1.1]
(arXiv:2609.20871v1), quoted for comparison, written literally about **our** definitions:

> For each integer `s ≥ 0` there are constants `K_s ≥ 0` and `N_s` … every graph `G` of order `n`
> with `rsd(G) ≤ s` satisfies `cp(G) ≤ Q_s(n) + K_s`. For `n ≥ N_s`, the maximum is exactly
> `Q_s(n)`. Equality at these orders holds precisely for the graphs `(K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k}`,
> `k` a nearest integer to `(2(n+s)+1)/6`.

Here `rsd` is `E32.rsd` (`rsd G ≤ s ↔ RootedDefectAt G s`, `E32.rsd_le_iff`), `cp(G) = t` is
`PaperIV.ExtremalClassification.CliqueCoverEq G t` (lower bound for **all** clique partitions and
attainment), `cp(G) ≤ t` is the existence of a clique partition with at most `t` pieces, `Q_s(n)`
is `defectTarget s n`, and the equality graphs are `IsAdmissibleExtremal G s`.

* `rsd_bound_all_orders`, `rsd_eventual_maximum` — the first two clauses, unconditionally (from
  Theorem C, which even uses pieces of order at most four, and the unrestricted lower witness).
* `cp_classification_of_theoremCPrimeC` — from (c) and Theorem C: for `n ≥ N`,
  `cp(G) = Q_s(n) ↔ c₄(G) = Q_s(n) ↔ G` is an admissible `E_s(n,k)`.
* `ref15Theorem11_of_theoremCPrimeC`, `ref15Theorem11_of_retained`,
  `ref15Theorem11_zero` (unconditional at `s = 0`).
-/

namespace E32

open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect PaperIV.DefectComparatorGraph
  PaperIV.DefectTargetArithmetic PaperIV.ExtremalClassification

/-- Literal restatement of [15, Theorem 1.1] (arXiv:2609.20871v1) in our definitions; the proofs below are ours. -/
def Ref15Theorem11Statement (s : ℕ) : Prop :=
  ∃ K N : ℕ,
    (∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], rsd G ≤ s →
      ∃ Q : CliquePartition G, Q.size ≤ defectTarget s n + K) ∧
    (∀ n, N ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], rsd G ≤ s →
        ∃ Q : CliquePartition G, Q.size ≤ defectTarget s n) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), rsd G ≤ s ∧
        CliqueCoverEq G (defectTarget s n))) ∧
    (∀ n, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], rsd G ≤ s →
      (CliqueCoverEq G (defectTarget s n) ↔ IsAdmissibleExtremal G s))

/-- All-orders bound, with pieces of order at most four: `c₄(G) ≤ Q_s(n) + N_C²`. -/
theorem rsd_bound_all_orders (s : ℕ) :
    ∃ K : ℕ, ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n + K := by
  obtain ⟨NC, hC⟩ := theoremC_at s
  refine ⟨NC * NC, fun n G _ hG => ?_⟩
  by_cases hn : NC ≤ n
  · obtain ⟨Q, hQ4, hQ⟩ := hC n hn G hG
    exact ⟨Q, hQ4, by omega⟩
  · obtain ⟨Q, hQ4, hQ⟩ := A4S1.MinDegreeTerminal.trivial_partition G
    refine ⟨Q, hQ4, ?_⟩
    have : n * n ≤ NC * NC := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- The eventual maximum, against unrestricted clique partitions. -/
theorem rsd_eventual_maximum (s : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), RootedDefectAt G s ∧
        CliqueCoverEq G (defectTarget s n)) := by
  obtain ⟨N, hN⟩ := PaperIV.DefectSharpPublication.rooted_defect_maximum s
  refine ⟨N, fun n hn => ⟨(hN n hn).1, ?_⟩⟩
  obtain ⟨G, inst, hG, Q, -, hQ, hmin⟩ := (hN n hn).2
  exact ⟨G, inst, hG, fun R => hQ ▸ hmin R, ⟨Q, hQ⟩⟩

/-- An admissible extremal graph needs `Q_s(n)` pieces in every clique partition. -/
theorem admissibleExtremal_lower {n s : ℕ} (hn : s + 4 ≤ n) {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h : IsAdmissibleExtremal G s) (Q : CliquePartition G) :
    defectTarget s n ≤ Q.size := by
  obtain ⟨C, D, H, hCD, hCH, hDH, hcov, hDs, hGE, hnear⟩ := h
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
  have hB := rootBaseline_le_and_eq_iff (c := C.card) (s := s) (h := H.card) hsum hch (by omega)
  have heq := hB.2.2 hnear
  have hl := PaperIV.DefectComparatorLower.cliquePartition_size_ge_defect_baseline hCD hDH
    (disjoint_union_left.2 ⟨hCH, hDH⟩)
    (PaperIV.CliquePartitionTransport.transport (fun x y => by rw [hGE]) Q)
  rw [PaperIV.CliquePartitionTransport.transport_size, hDs] at hl
  omega

/-- **Corollary (comparison).** From (c) and Theorem C: for `n ≥ N'`,
`cp(G) = Q_s(n) ↔ c₄(G) = Q_s(n) ↔ G` is an admissible `E_s(n,k)`. -/
theorem cp_classification_of_theoremCPrimeC {s N : ℕ} (hc : TheoremCPrimeC s N) :
    ∃ N' : ℕ, ∀ n, N' ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        (CliqueCoverEq G (defectTarget s n) ↔ CliqueCover4Eq G (defectTarget s n)) ∧
        (CliqueCover4Eq G (defectTarget s n) ↔ IsAdmissibleExtremal G s) := by
  obtain ⟨NC, hC⟩ := theoremC_at s
  refine ⟨N + NC + s + 4, fun n hn G _ hG => ?_⟩
  have hc' := hc n (by omega) G hG
  have hcp : CliqueCoverEq G (defectTarget s n) ↔ CliqueCover4Eq G (defectTarget s n) := by
    constructor
    · rintro ⟨hlow, -⟩
      obtain ⟨Q, hQ4, hQ⟩ := hC n (by omega) G hG
      exact ⟨fun R _ => hlow R, ⟨Q, hQ4, le_antisymm hQ (hlow Q)⟩⟩
    · intro h4
      have hadm := hc'.1 h4
      obtain ⟨-, Q, -, hQ⟩ := h4
      exact ⟨admissibleExtremal_lower (by omega) hadm, ⟨Q, hQ⟩⟩
  exact ⟨hcp, hc'⟩

/-- (c) implies the quoted Theorem 1.1. -/
theorem ref15Theorem11_of_theoremCPrimeC {s N : ℕ} (hc : TheoremCPrimeC s N) :
    Ref15Theorem11Statement s := by
  obtain ⟨K, hK⟩ := rsd_bound_all_orders s
  obtain ⟨N₁, hN₁⟩ := rsd_eventual_maximum s
  obtain ⟨N₂, hN₂⟩ := cp_classification_of_theoremCPrimeC hc
  refine ⟨K, N₁ + N₂, ?_, ?_, ?_⟩
  · intro n G _ hG
    obtain ⟨Q, -, hQ⟩ := hK n G ((rsd_le_iff G s).1 hG)
    exact ⟨Q, hQ⟩
  · intro n hn
    refine ⟨fun G _ hG => ?_, ?_⟩
    · obtain ⟨Q, -, hQ⟩ := (hN₁ n (by omega)).1 G ((rsd_le_iff G s).1 hG)
      exact ⟨Q, hQ⟩
    · obtain ⟨G, inst, hG, hcp⟩ := (hN₁ n (by omega)).2
      exact ⟨G, inst, (rsd_le_iff G s).2 hG, hcp⟩
  · intro n hn G _ hG
    obtain ⟨h1, h2⟩ := hN₂ n (by omega) G ((rsd_le_iff G s).1 hG)
    exact h1.trans h2

/-- The quoted Theorem 1.1 follows from the remaining step. -/
theorem ref15Theorem11_of_retained {s : ℕ} (h : RetainedTerminalStability s) :
    Ref15Theorem11Statement s := by
  obtain ⟨_, _, _, _, N, -, hC⟩ := theoremCPrime_of_retainedStability h
  exact ref15Theorem11_of_theoremCPrimeC hC

/-- The quoted Theorem 1.1 at `s = 0`, unconditionally. -/
theorem ref15Theorem11_zero : Ref15Theorem11Statement 0 := by
  obtain ⟨_, _, N, -, hC⟩ := theoremCPrime_zero
  exact ref15Theorem11_of_theoremCPrimeC hC

end E32
