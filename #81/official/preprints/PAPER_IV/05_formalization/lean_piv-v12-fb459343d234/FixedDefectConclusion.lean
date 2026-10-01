import E32Bridge

namespace FixedDefectStability
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
  PaperIV.DefectTargetArithmetic A4S1.IndepAll

/-- The requested edit and size-deficit bounds hold for the same literal root.
The global constant includes the charge from E32's low-degree induction. -/
theorem fixed_defect_edit_and_size (s : ℕ) :
    ∃ γ K B : ℚ, 0 < γ ∧ 0 ≤ K ∧ B=1+4*K ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
        RootedDefectAt G s → ∀ δ : ℚ, 0 ≤ δ → δ ≤ γ*(n:ℚ)^2 →
        (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
          (defectTarget s n:ℚ)-δ ≤ Q.size) →
        ∃ C D H : Finset (Fin n), E32.IsDefectRoot G s C D H ∧
          (E32.rootEdit G C D H:ℚ) ≤ K*δ ∧
          0 ≤ (defectTarget s n:ℚ)-E32.rootBaseline C D H ∧
          (defectTarget s n:ℚ)-E32.rootBaseline C D H ≤ B*δ := by
  obtain ⟨γ,hγ,N,hAB,_⟩ := fixed_defect_stability_all s
  let K : ℚ := max (40000*((s:ℚ)+1)^3) (2/epsS s)
  have hK : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  refine ⟨γ,K,1+4*K,hγ,hK,rfl,N,?_⟩
  intro n hn G _ hdef δ hδ hδmax hlower
  obtain ⟨C,D,H,hR,hedit,_⟩ := hAB n hn G hdef δ hδ hδmax hlower
  have hsum := hR.card_sum
  have h2 := hR.two_le
  have hbase := (E32.rootBaseline_le_and_eq_iff hsum hR.core_le_hosts
    (show s+2 ≤ n by omega)).1
  have hB : E32.rootBaseline C D H ≤ defectTarget s n := by
    simpa only [E32.rootBaseline,hR.card_def] using hbase
  obtain ⟨Q,hQ4,hQ⟩ := E32.exists_partition_near_root G hR
  have hl := hlower Q hQ4
  have hQq : (Q.size:ℚ) ≤ E32.rootBaseline C D H+4*(E32.rootEdit G C D H:ℚ) := by
    exact_mod_cast hQ
  have hBq : (E32.rootBaseline C D H:ℚ) ≤ defectTarget s n := by exact_mod_cast hB
  refine ⟨C,D,H,hR,hedit,sub_nonneg.mpr hBq,?_⟩
  change (E32.rootEdit G C D H:ℚ) ≤ K*δ at hedit
  nlinarith only [hl,hQq,hedit]

end FixedDefectStability
#print axioms FixedDefectStability.fixed_defect_edit_and_size
