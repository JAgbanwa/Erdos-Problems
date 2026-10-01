import PaperIV.ChordalC4
import PaperIV.OutsideCounting

/-!
# La raíz regularizada

Dada una clique de referencia `P`, se construye la raíz regularizada

```text
regularizedRootSet G P = (P \ strays G P) ∪ hubs G P
```

donde

* `strays G P` son los vértices de `P` cuya columna faltante es grande (al menos `|P|/4`), y
* `hubs G P` son los vértices exteriores de grado exterior grande (al menos `7·|P|/4`).

Los *hubs* deben entrar en la raíz porque su grado exterior excede lo que la condición de paleta
tolera; los *strays* deben salir porque son exactamente los vértices de `P` que pueden no ser
adyacentes a algún hub, y su grado exterior es pequeño, así que sacarlos es inocuo.

La cordalidad interviene una sola vez, a través de `PaperIV.no_induced_fourCycle`: garantiza que
los hubs son adyacentes entre sí y que todo vértice de `P` no adyacente a un hub es un stray.
-/

open scoped BigOperators

namespace PaperIV.RootVocab

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vértices exteriores de grado exterior grande. -/
noncomputable def hubs (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) : Finset V := by
  classical
  exact (outsideVertices P).filter fun y => 7 * P.card ≤ 4 * (outNbrs G P y).card

/-- Vértices de la raíz con columna faltante grande. -/
noncomputable def strays (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) : Finset V := by
  classical
  exact P.filter fun x => P.card ≤ 4 * (missingColumn G P x).card

/-- La raíz regularizada: se quitan los strays y se meten los hubs. -/
noncomputable def regularizedRootSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset V :=
  (P \ strays G P) ∪ hubs G P

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P : Finset V}

@[simp] theorem mem_hubs {y : V} :
    y ∈ hubs G P ↔ y ∉ P ∧ 7 * P.card ≤ 4 * (outNbrs G P y).card := by
  simp [hubs]

@[simp] theorem mem_strays {x : V} :
    x ∈ strays G P ↔ x ∈ P ∧ P.card ≤ 4 * (missingColumn G P x).card := by
  simp [strays]

theorem hubs_subset : hubs G P ⊆ outsideVertices P := Finset.filter_subset _ _

theorem strays_subset : strays G P ⊆ P := Finset.filter_subset _ _

/-! ## Cotas de tamaño por Markov -/

/-- Markov sobre las columnas faltantes: hay muy pocos strays. -/
theorem card_strays_le (hp : 1 ≤ P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    16384 * (strays G P).card ≤ P.card := by
  classical
  have hsub : ∑ x ∈ strays G P, (missingColumn G P x).card ≤ missingIncidences G P :=
    Finset.sum_le_sum_of_subset strays_subset
  have hlow : ∑ _x ∈ strays G P, P.card
      ≤ ∑ x ∈ strays G P, 4 * (missingColumn G P x).card :=
    Finset.sum_le_sum fun x hx => (mem_strays.1 hx).2
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hlow
  have key : (16384 * (strays G P).card) * P.card ≤ P.card * P.card := by nlinarith
  exact Nat.le_of_mul_le_mul_right key hp

/-- Markov sobre los grados exteriores: hay muy pocos hubs. -/
theorem card_hubs_le (hp : 1 ≤ P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    57344 * (hubs G P).card ≤ P.card := by
  classical
  have hsub : ∑ y ∈ hubs G P, (outNbrs G P y).card ≤ 2 * (outsideEdges G P).card :=
    sum_card_outNbrs_le G P _ hubs_subset
  have hlow : ∑ _y ∈ hubs G P, 7 * P.card ≤ ∑ y ∈ hubs G P, 4 * (outNbrs G P y).card :=
    Finset.sum_le_sum fun y hy => (mem_hubs.1 hy).2
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hlow
  have key : (57344 * (hubs G P).card) * P.card ≤ P.card * P.card := by nlinarith
  exact Nat.le_of_mul_le_mul_right key hp

/-- Un clique exterior es corto: el presupuesto cuadrático de `hdefect` sólo permite cliques
exteriores de tamaño `≤ |P|/128` (más el caso trivial de un vértice). -/
theorem clique_outside_card_le
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card)
    {K : Finset V} (hK : K ⊆ outsideVertices P) (hclq : G.IsClique (K : Set V)) :
    128 * K.card ≤ P.card + 128 := by
  classical
  rcases Nat.lt_or_ge K.card 2 with h1 | h1
  · omega
  · have hpairs : K.card * (K.card - 1) ≤ 2 * (outsideEdges G P).card :=
      clique_outside_card_mul_le G P K hK hclq
    have hbudget : 32768 * (K.card * (K.card - 1)) ≤ P.card * P.card := by omega
    have hhalf : K.card ≤ 2 * (K.card - 1) := by omega
    have hsq : (128 * K.card) * (128 * K.card) ≤ P.card * P.card := by
      have : 16384 * (K.card * K.card) ≤ 32768 * (K.card * (K.card - 1)) := by
        have := Nat.mul_le_mul_left K.card hhalf
        nlinarith
      nlinarith
    have : 128 * K.card ≤ P.card := by nlinarith
    omega

/-! ## Consecuencias de la cordalidad -/

/-- Dos hubs distintos son adyacentes: si no, sus vecindarios exteriores comunes —que son
enormes— tendrían que formar un clique exterior, cosa imposible por el presupuesto. -/
theorem hubs_isClique (hchordal : IsChordal G) (hp : 1024 ≤ P.card)
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    G.IsClique ((hubs G P : Finset V) : Set V) := by
  classical
  intro y hy z hz hyz
  simp only [Finset.mem_coe] at hy hz
  by_contra hnadj
  set S : Finset V := outNbrs G P y ∩ outNbrs G P z with hS
  have hSsub : S ⊆ outsideVertices P := by
    intro s hs
    have := Finset.mem_of_mem_inter_left hs
    simpa using (mem_outNbrs.1 this).1
  have hcards : (outNbrs G P y).card + (outNbrs G P z).card
      ≤ (outsideVertices P).card + S.card := by
    have hunion : (outNbrs G P y ∪ outNbrs G P z).card ≤ (outsideVertices P).card := by
      refine Finset.card_le_card ?_
      intro s hs
      rcases Finset.mem_union.1 hs with h | h
      · simpa using (mem_outNbrs.1 h).1
      · simpa using (mem_outNbrs.1 h).1
    have hui := Finset.card_union_add_card_inter (outNbrs G P y) (outNbrs G P z)
    rw [← hS] at hui
    omega
  have hy' := (mem_hubs.1 hy).2
  have hz' := (mem_hubs.1 hz).2
  have hSbig : 256 * S.card ≥ 380 * P.card := by omega
  have hSnotclique : ¬ G.IsClique ((S : Finset V) : Set V) := by
    intro hc
    have := clique_outside_card_le hdefect hSsub hc
    omega
  obtain ⟨s1, hs1, s2, hs2, hne, hnadj12⟩ :
      ∃ s1 ∈ S, ∃ s2 ∈ S, s1 ≠ s2 ∧ ¬ G.Adj s1 s2 := by
    by_contra hcon
    push_neg at hcon
    exact hSnotclique fun a ha b hb hab =>
      hcon a (by simpa using ha) b (by simpa using hb) hab
  have h1y : G.Adj y s1 := (mem_outNbrs.1 (Finset.mem_of_mem_inter_left hs1)).2
  have h1z : G.Adj z s1 := (mem_outNbrs.1 (Finset.mem_of_mem_inter_right hs1)).2
  have h2y : G.Adj y s2 := (mem_outNbrs.1 (Finset.mem_of_mem_inter_left hs2)).2
  have h2z : G.Adj z s2 := (mem_outNbrs.1 (Finset.mem_of_mem_inter_right hs2)).2
  exact no_induced_fourCycle hchordal hyz hne h1y h1z.symm h2z h2y.symm hnadj hnadj12

/-- Todo vértice de la raíz que no sea adyacente a un hub es un stray. -/
theorem mem_strays_of_not_adj_hub (hchordal : IsChordal G) (hp : 1024 ≤ P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card)
    {x y : V} (hx : x ∈ P) (hy : y ∈ hubs G P) (hnadj : ¬ G.Adj x y) :
    x ∈ strays G P := by
  classical
  set S : Finset V := (outNbrs G P y).filter fun s => G.Adj x s with hS
  have hxy : x ≠ y := by
    intro h; exact (mem_hubs.1 hy).1 (h ▸ hx)
  have hSsub : S ⊆ outsideVertices P := by
    intro s hs
    have := Finset.mem_of_mem_filter s hs
    simpa using (mem_outNbrs.1 this).1
  have hSclique : G.IsClique ((S : Finset V) : Set V) := by
    intro s1 hs1 s2 hs2 hne
    simp only [Finset.mem_coe, hS, Finset.mem_filter] at hs1 hs2
    by_contra hn12
    exact no_induced_fourCycle hchordal hxy hne hs1.2
      (mem_outNbrs.1 hs1.1).2.symm (mem_outNbrs.1 hs2.1).2 hs2.2.symm hnadj hn12
  have hScard : 128 * S.card ≤ P.card + 128 := clique_outside_card_le hdefect hSsub hSclique
  have hsplit : (outNbrs G P y).card ≤ S.card + (missingColumn G P x).card := by
    have hsub : (outNbrs G P y) \ S ⊆ missingColumn G P x := by
      intro s hs
      have hs1 : s ∈ outNbrs G P y := Finset.mem_sdiff.1 hs |>.1
      have hs2 : s ∉ S := Finset.mem_sdiff.1 hs |>.2
      have hnot : ¬ G.Adj x s := by
        intro hadj
        exact hs2 (Finset.mem_filter.2 ⟨hs1, hadj⟩)
      simp only [missingColumn, Finset.mem_filter, mem_outsideVertices]
      exact ⟨by simpa using (mem_outNbrs.1 hs1).1, hnot⟩
    have := Finset.card_le_card hsub
    have hcard := Finset.card_sdiff_add_card_eq_card
      (show S ⊆ outNbrs G P y from Finset.filter_subset _ _)
    omega
  have hy' := (mem_hubs.1 hy).2
  exact mem_strays.2 ⟨hx, by omega⟩

/-- La raíz regularizada es una clique. -/
theorem regularizedRootSet_isClique (hchordal : IsChordal G) (hp : 1024 ≤ P.card)
    (hP : G.IsClique (P : Set V))
    (hbalanceUpper : 64 * (outsideVertices P).card ≤ 129 * P.card)
    (hdefect : 65536 * ((outsideEdges G P).card + missingIncidences G P) ≤ P.card * P.card) :
    G.IsClique ((regularizedRootSet G P : Finset V) : Set V) := by
  classical
  have hhub := hubs_isClique hchordal hp hbalanceUpper hdefect
  have hmix : ∀ x ∈ P \ strays G P, ∀ y ∈ hubs G P, G.Adj x y := by
    intro x hx y hy
    have hxP : x ∈ P := (Finset.mem_sdiff.1 hx).1
    have hxS : x ∉ strays G P := (Finset.mem_sdiff.1 hx).2
    by_contra hn
    exact hxS (mem_strays_of_not_adj_hub hchordal hp hdefect hxP hy hn)
  intro a ha b hb hab
  simp only [Finset.mem_coe, regularizedRootSet, Finset.mem_union] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hP (by exact_mod_cast (Finset.mem_sdiff.1 ha).1)
      (by exact_mod_cast (Finset.mem_sdiff.1 hb).1) hab
  · exact hmix a ha b hb
  · exact (hmix b hb a ha).symm
  · exact hhub (by simpa using ha) (by simpa using hb) hab

/-! ## Descripción del exterior de la raíz regularizada -/

theorem outsideVertices_regularizedRootSet :
    outsideVertices (regularizedRootSet G P)
      = (outsideVertices P \ hubs G P) ∪ strays G P := by
  classical
  ext v
  simp only [mem_outsideVertices, regularizedRootSet, Finset.mem_union, Finset.mem_sdiff,
    not_or]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hvP : v ∈ P
    · right
      by_contra hv
      exact h1 ⟨hvP, hv⟩
    · left; exact ⟨hvP, h2⟩
  · rintro (⟨h1, h2⟩ | h)
    · exact ⟨fun hc => h1 hc.1, h2⟩
    · refine ⟨fun hc => hc.2 h, fun hc => (mem_hubs.1 hc).1 (strays_subset h)⟩

theorem card_regularizedRootSet :
    (regularizedRootSet G P).card + (strays G P).card = P.card + (hubs G P).card := by
  classical
  have hdisj : Disjoint (P \ strays G P) (hubs G P) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    exact (mem_hubs.1 hb).1 (Finset.mem_sdiff.1 ha).1
  rw [regularizedRootSet, Finset.card_union_of_disjoint hdisj]
  have := Finset.card_sdiff_add_card_eq_card (s := strays G P) (t := P) strays_subset
  omega

theorem card_outsideVertices_regularizedRootSet :
    (outsideVertices (regularizedRootSet G P)).card + (hubs G P).card
      = (outsideVertices P).card + (strays G P).card := by
  classical
  have hdisj : Disjoint (outsideVertices P \ hubs G P) (strays G P) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    have : a ∉ P := by simpa using (Finset.mem_sdiff.1 ha).1
    exact this (strays_subset hb)
  rw [outsideVertices_regularizedRootSet, Finset.card_union_of_disjoint hdisj]
  have := Finset.card_sdiff_add_card_eq_card (s := hubs G P) (t := outsideVertices P) hubs_subset
  omega

end PaperIV.RootVocab
