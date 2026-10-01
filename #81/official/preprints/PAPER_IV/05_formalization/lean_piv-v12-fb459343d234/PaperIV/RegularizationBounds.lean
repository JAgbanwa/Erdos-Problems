import PaperIV.Regularization

/-!
# Cotas para la raíz regularizada

Aquí se acotan, una a una, todas las magnitudes que aparecen en las trece condiciones de
`RegularizedRoot` cuando la raíz es `regularizedRootSet G P`: columnas faltantes, grados
exteriores, aristas exteriores, incidencias faltantes, número de clique del exterior y grado
máximo del exterior.

Todas las cotas se dejan en forma entera, con `|P|` y `|P|²` como únicos denominadores
implícitos, para que la aritmética final sea lineal.
-/

open scoped BigOperators

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {P : Finset V}

theorem card_add_card_outsideVertices (P : Finset V) :
    P.card + (outsideVertices P).card = Fintype.card V := by
  classical
  have := Finset.card_sdiff_add_card_eq_card (s := P) (t := (Finset.univ : Finset V))
    (Finset.subset_univ P)
  rw [Finset.card_univ] at this
  rw [outsideVertices]
  omega

/-! ## Columnas faltantes de la raíz regularizada -/

/-- Fuera de la raíz regularizada sólo hay vértices exteriores o strays. -/
theorem missingColumn_reg_subset (v : V) :
    missingColumn G (regularizedRootSet G P) v ⊆ missingColumn G P v ∪ strays G P := by
  classical
  intro z hz
  simp only [missingColumn, Finset.mem_filter, mem_outsideVertices] at hz
  obtain ⟨hzout, hnadj⟩ := hz
  have : z ∈ (outsideVertices P \ hubs G P) ∪ strays G P := by
    rw [← outsideVertices_regularizedRootSet]
    simpa using hzout
  rcases Finset.mem_union.1 this with h | h
  · refine Finset.mem_union_left _ ?_
    simp only [missingColumn, Finset.mem_filter, mem_outsideVertices]
    exact ⟨by simpa using (Finset.mem_sdiff.1 h).1, hnadj⟩
  · exact Finset.mem_union_right _ h

/-- Para un vértice de la raíz que no es stray, la columna faltante no crece. -/
theorem missingColumn_reg_subset_of_mem (hP : G.IsClique (P : Set V)) {x : V} (hx : x ∈ P)
    (hxs : x ∉ strays G P) :
    missingColumn G (regularizedRootSet G P) x ⊆ missingColumn G P x := by
  classical
  intro z hz
  rcases Finset.mem_union.1 (missingColumn_reg_subset x hz) with h | h
  · exact h
  · exfalso
    have hzP : z ∈ P := strays_subset h
    have hne : x ≠ z := fun hxz => hxs (hxz ▸ h)
    have hadj : G.Adj x z := hP (by exact_mod_cast hx) (by exact_mod_cast hzP) hne
    simp only [missingColumn, Finset.mem_filter] at hz
    exact hz.2 hadj

/-! ## Grados exteriores -/

/-- Los vecinos exteriores de la raíz regularizada son vecinos exteriores de `P` o strays. -/
theorem neighborFinset_outsideGraph_subset (v : V) :
    (outsideGraph G (regularizedRootSet G P)).neighborFinset v
      ⊆ outNbrs G P v ∪ strays G P := by
  classical
  intro z hz
  rw [SimpleGraph.mem_neighborFinset] at hz
  obtain ⟨hadj, -, hzR⟩ := hz
  have : z ∈ (outsideVertices P \ hubs G P) ∪ strays G P := by
    rw [← outsideVertices_regularizedRootSet]
    simpa using hzR
  rcases Finset.mem_union.1 this with h | h
  · exact Finset.mem_union_left _ (mem_outNbrs.2 ⟨by simpa using (Finset.mem_sdiff.1 h).1, hadj⟩)
  · exact Finset.mem_union_right _ h

/-- Todo vértice fuera de la raíz regularizada tiene grado exterior moderado en `G`. -/
theorem card_outNbrs_le_of_not_mem_reg
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    {v : V} (hv : v ∉ regularizedRootSet G P) :
    64 * (outNbrs G P v).card ≤ 113 * P.card := by
  classical
  have hv' : v ∈ (outsideVertices P \ hubs G P) ∪ strays G P := by
    rw [← outsideVertices_regularizedRootSet]
    simpa using hv
  rcases Finset.mem_union.1 hv' with h | h
  · have hnhub : v ∉ hubs G P := (Finset.mem_sdiff.1 h).2
    have hvout : v ∉ P := by simpa using (Finset.mem_sdiff.1 h).1
    have : ¬ (7 * P.card ≤ 4 * (outNbrs G P v).card) := fun hc => hnhub (mem_hubs.2 ⟨hvout, hc⟩)
    omega
  · have hmiss := (mem_strays.1 h).2
    have hsum := card_outNbrs_add_card_missingColumn G P v
    omega


/-- Cota entera para el grado máximo del exterior de la raíz regularizada. -/
theorem maxDegree_outsideGraph_reg_le
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card) :
    64 * (outsideGraph G (regularizedRootSet G P)).maxDegree
      ≤ 113 * P.card + 64 * (strays G P).card := by
  classical
  set D : ℕ := (113 * P.card) / 64 + (strays G P).card with hD
  have hdeg : ∀ v, (outsideGraph G (regularizedRootSet G P)).degree v ≤ D := by
    intro v
    have hsub := neighborFinset_outsideGraph_subset (G := G) (P := P) v
    have h1 : (outsideGraph G (regularizedRootSet G P)).degree v
        ≤ (outNbrs G P v).card + (strays G P).card := by
      calc (outsideGraph G (regularizedRootSet G P)).degree v
          ≤ (outNbrs G P v ∪ strays G P).card := Finset.card_le_card hsub
        _ ≤ (outNbrs G P v).card + (strays G P).card := Finset.card_union_le _ _
    by_cases hv : v ∈ regularizedRootSet G P
    · have hempty : (outsideGraph G (regularizedRootSet G P)).neighborFinset v = ∅ := by
        ext z
        constructor
        · intro hz
          rw [SimpleGraph.mem_neighborFinset] at hz
          exact absurd hv hz.2.1
        · intro hz
          exact absurd hz (Finset.notMem_empty z)
      have : (outsideGraph G (regularizedRootSet G P)).degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hempty, Finset.card_empty]
      omega
    · have h2 := card_outNbrs_le_of_not_mem_reg hbalanceUpper hv
      omega
  have hmax := SimpleGraph.maxDegree_le_of_forall_degree_le _ D hdeg
  omega

/-- Cota entera para el número de clique del exterior de la raíz regularizada. -/
theorem cliqueNum_outsideGraph_reg_le
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    128 * (outsideGraph G (regularizedRootSet G P)).cliqueNum
      ≤ P.card + 128 + 128 * (strays G P).card := by
  classical
  obtain ⟨s, hs⟩ := (outsideGraph G (regularizedRootSet G P)).exists_isNClique_cliqueNum
  have hcard : s.card = (outsideGraph G (regularizedRootSet G P)).cliqueNum := hs.card_eq
  rcases Nat.lt_or_ge s.card 2 with h1 | h1
  · omega
  · have hout : ∀ a ∈ s, a ∉ regularizedRootSet G P := by
      intro a ha
      obtain ⟨b, hb, hab⟩ : ∃ b ∈ s, b ≠ a := by
        by_contra hcon
        push_neg at hcon
        have : s ⊆ {a} := fun b hb => Finset.mem_singleton.2 (hcon b hb)
        have := Finset.card_le_card this
        simp at this
        omega
      exact (hs.isClique (Finset.mem_coe.2 hb) (Finset.mem_coe.2 ha) hab).2.2
    set K : Finset V := s \ strays G P with hK
    have hKsub : K ⊆ outsideVertices P := by
      intro a ha
      have ha1 : a ∈ s := (Finset.mem_sdiff.1 ha).1
      have ha2 : a ∉ strays G P := (Finset.mem_sdiff.1 ha).2
      have : a ∈ (outsideVertices P \ hubs G P) ∪ strays G P := by
        rw [← outsideVertices_regularizedRootSet]
        simpa using hout a ha1
      rcases Finset.mem_union.1 this with h | h
      · exact (Finset.mem_sdiff.1 h).1
      · exact absurd h ha2
    have hKclique : G.IsClique (K : Set V) := by
      intro a ha b hb hab
      have ha1 : a ∈ s := (Finset.mem_sdiff.1 (Finset.mem_coe.1 ha)).1
      have hb1 : b ∈ s := (Finset.mem_sdiff.1 (Finset.mem_coe.1 hb)).1
      exact (hs.isClique (Finset.mem_coe.2 ha1) (Finset.mem_coe.2 hb1) hab).1
    have hKcard := clique_outside_card_le (G := G) (P := P) hdefect hKsub hKclique
    have hsplit : s.card ≤ K.card + (strays G P).card := by
      have hsd := Finset.card_sdiff_add_card s (strays G P)
      rw [← hK] at hsd
      have h2 : (s ∪ strays G P).card ≤ s.card + (strays G P).card := Finset.card_union_le _ _
      have h3 : s.card ≤ (s ∪ strays G P).card :=
        Finset.card_le_card Finset.subset_union_left
      omega
    omega

/-! ## Aristas e incidencias -/

/-- Las aristas exteriores nuevas o bien ya lo eran, o bien tocan un stray. -/
theorem card_outsideEdges_reg_le :
    (outsideEdges G (regularizedRootSet G P)).card
      ≤ (outsideEdges G P).card + (strays G P).card * Fintype.card V := by
  classical
  have hsub : outsideEdges G (regularizedRootSet G P) ⊆
      outsideEdges G P ∪ (strays G P).biUnion
        (fun x => Finset.univ.image (fun z : V => s(x, z))) := by
    intro ε hε
    simp only [outsideEdges, Finset.mem_filter] at hε
    obtain ⟨hmem, hsubset⟩ := hε
    induction ε with
    | h a b =>
      have ha : a ∈ outsideVertices (regularizedRootSet G P) := by
        refine hsubset ?_
        rw [Sym2.mem_toFinset]
        simp
      have hb : b ∈ outsideVertices (regularizedRootSet G P) := by
        refine hsubset ?_
        rw [Sym2.mem_toFinset]
        simp
      rw [outsideVertices_regularizedRootSet] at ha hb
      rcases Finset.mem_union.1 ha with ha' | ha'
      · rcases Finset.mem_union.1 hb with hb' | hb'
        · refine Finset.mem_union_left _ ?_
          simp only [outsideEdges, Finset.mem_filter]
          refine ⟨hmem, ?_⟩
          intro z hz
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact (Finset.mem_sdiff.1 ha').1
          · exact (Finset.mem_sdiff.1 hb').1
        · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb', ?_⟩)
          exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, Sym2.eq_swap⟩
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha', ?_⟩)
        exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩
  calc (outsideEdges G (regularizedRootSet G P)).card
      ≤ (outsideEdges G P ∪ (strays G P).biUnion
          (fun x => Finset.univ.image (fun z : V => s(x, z)))).card := Finset.card_le_card hsub
    _ ≤ (outsideEdges G P).card + ((strays G P).biUnion
          (fun x => Finset.univ.image (fun z : V => s(x, z)))).card := Finset.card_union_le _ _
    _ ≤ (outsideEdges G P).card + (strays G P).card * Fintype.card V := by
        have hbu : ((strays G P).biUnion
            (fun x => Finset.univ.image (fun z : V => s(x, z)))).card
            ≤ ∑ _x ∈ strays G P, Fintype.card V := by
          refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum ?_)
          intro x _
          calc (Finset.univ.image (fun z : V => s(x, z))).card
              ≤ (Finset.univ : Finset V).card := Finset.card_image_le
            _ = Fintype.card V := Finset.card_univ
        rw [Finset.sum_const, smul_eq_mul] at hbu
        omega

/-- Las incidencias faltantes de la raíz regularizada. -/
theorem missingIncidences_reg_le (hP : G.IsClique (P : Set V)) :
    missingIncidences G (regularizedRootSet G P)
      ≤ missingIncidences G P + (hubs G P).card * Fintype.card V := by
  classical
  have hdisj : Disjoint (P \ strays G P) (hubs G P) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    exact (mem_hubs.1 hb).1 (Finset.mem_sdiff.1 ha).1
  have hsplit : missingIncidences G (regularizedRootSet G P)
      = (∑ v ∈ P \ strays G P, (missingColumn G (regularizedRootSet G P) v).card)
        + ∑ v ∈ hubs G P, (missingColumn G (regularizedRootSet G P) v).card := by
    rw [missingIncidences, regularizedRootSet, Finset.sum_union hdisj]
  have h1 : (∑ v ∈ P \ strays G P, (missingColumn G (regularizedRootSet G P) v).card)
      ≤ missingIncidences G P := by
    calc (∑ v ∈ P \ strays G P, (missingColumn G (regularizedRootSet G P) v).card)
        ≤ ∑ v ∈ P \ strays G P, (missingColumn G P v).card := by
          refine Finset.sum_le_sum fun v hv => Finset.card_le_card ?_
          exact missingColumn_reg_subset_of_mem hP (Finset.mem_sdiff.1 hv).1
            (Finset.mem_sdiff.1 hv).2
      _ ≤ missingIncidences G P :=
          Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
  have h2 : (∑ v ∈ hubs G P, (missingColumn G (regularizedRootSet G P) v).card)
      ≤ (hubs G P).card * Fintype.card V := by
    have : ∀ v ∈ hubs G P, (missingColumn G (regularizedRootSet G P) v).card
        ≤ Fintype.card V := by
      intro v _
      calc (missingColumn G (regularizedRootSet G P) v).card
          ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card V := Finset.card_univ
    calc (∑ v ∈ hubs G P, (missingColumn G (regularizedRootSet G P) v).card)
        ≤ ∑ _v ∈ hubs G P, Fintype.card V := Finset.sum_le_sum this
      _ = (hubs G P).card * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- La columna faltante máxima de la raíz regularizada es pequeña. -/
theorem maxMissingColumn_reg_le (hP : G.IsClique (P : Set V)) (hp : 1024 ≤ P.card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    3 * maxMissingColumn G (regularizedRootSet G P) ≤ P.card := by
  classical
  have hX := card_strays_le (P := P) (G := G) (by omega) hdefect
  have hbound : ∀ v ∈ regularizedRootSet G P,
      (missingColumn G (regularizedRootSet G P) v).card ≤ P.card / 3 := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv' | hv'
    · have hsub := missingColumn_reg_subset_of_mem hP (Finset.mem_sdiff.1 hv').1
        (Finset.mem_sdiff.1 hv').2
      have hle := Finset.card_le_card hsub
      have hns : ¬ (P.card ≤ 4 * (missingColumn G P v).card) := fun hc =>
        (Finset.mem_sdiff.1 hv').2 (mem_strays.2 ⟨(Finset.mem_sdiff.1 hv').1, hc⟩)
      omega
    · have hle := Finset.card_le_card (missingColumn_reg_subset (G := G) (P := P) v)
      have hle2 : (missingColumn G (regularizedRootSet G P) v).card
          ≤ (missingColumn G P v).card + (strays G P).card :=
        le_trans hle (Finset.card_union_le _ _)
      have hhub := (mem_hubs.1 hv').2
      have hsum := card_outNbrs_add_card_missingColumn G P v
      omega
  have hsup : maxMissingColumn G (regularizedRootSet G P) ≤ P.card / 3 :=
    Finset.sup_le hbound
  omega


/-! ## Aritmética final

Los cuatro pasos aritméticos que convierten las cotas anteriores en las constantes del
enunciado. Se aíslan con `Q = |P|²` como variable para que todo sea lineal. -/

theorem arith_outsideEdges_bound {E' E XN Q : ℕ} (h1 : E' ≤ E + XN)
    (h2 : 65536 * E ≤ Q) (h3 : 1048576 * XN ≤ 193 * Q) : 1048576 * E' ≤ 209 * Q := by
  omega

theorem arith_missingIncidences_bound {MI' MI HN Q : ℕ} (h1 : MI' ≤ MI + HN)
    (h2 : 65536 * MI ≤ Q) (h3 : 3670016 * HN ≤ 193 * Q) : 3670016 * MI' ≤ 249 * Q := by
  omega

theorem arith_outside_edges_small {E' Q : ℕ} (h : 1048576 * E' ≤ 209 * Q) (hQ : 0 < Q) :
    400 * E' < Q := by
  omega

theorem arith_mass_envelope {MI' E' Q : ℕ} (h1 : 3670016 * MI' ≤ 249 * Q)
    (h2 : 1048576 * E' ≤ 209 * Q) : 2000 * (MI' + 2 * E') ≤ 11 * Q := by
  omega

end PaperIV.RootVocab
