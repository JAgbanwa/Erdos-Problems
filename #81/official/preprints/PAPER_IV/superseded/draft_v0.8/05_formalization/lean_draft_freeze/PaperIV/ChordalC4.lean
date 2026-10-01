import PaperIV.RootVocabulary

/-!
# Cordalidad: no hay cuadrados inducidos

Un grafo cordal no contiene ciclos inducidos de longitud cuatro. Esta es la única consecuencia
de `PaperIV.IsChordal` que usa la regularización de la raíz.
-/

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- En un grafo cordal no hay ningún cuadrado inducido `a - b - c - d - a`. -/
theorem no_induced_fourCycle (h : IsChordal G) {a b c d : V}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hnac : ¬ G.Adj a c) (hnbd : ¬ G.Adj b d) : False := by
  classical
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c := hbc.ne
  have hcd' : c ≠ d := hcd.ne
  have hda' : d ≠ a := hda.ne
  have hba' : b ≠ a := hab.ne'
  have hcb' : c ≠ b := hbc.ne'
  have hdc' : d ≠ c := hcd.ne'
  have had' : a ≠ d := hda.ne'
  have hca' : c ≠ a := hac.symm
  have hdb' : d ≠ b := hbd.symm
  set w : G.Walk a a :=
    SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda
        SimpleGraph.Walk.nil))) with hw
  have hcyc : w.IsCycle := by
    rw [hw, SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, by simp, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true, or_false]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
      simp_all [List.nodup_cons]
  have hlen : 4 ≤ w.length := by simp [hw]
  obtain ⟨x, y, hx, hy, hxy, hxyedge⟩ := h w hcyc hlen
  have hsupp : w.support = [a, b, c, d, a] := by simp [hw]
  have hedges : w.edges = [s(a,b), s(b,c), s(c,d), s(d,a)] := by simp [hw]
  rw [hsupp] at hx hy
  rw [hedges] at hxyedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hxyedge
  push_neg at hxyedge
  obtain ⟨e1, e2, e3, e4⟩ := hxyedge
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hxy.ne rfl
      | exact hnac hxy
      | exact hnac hxy.symm
      | exact hnbd hxy
      | exact hnbd hxy.symm
      | simp_all

end PaperIV.RootVocab
