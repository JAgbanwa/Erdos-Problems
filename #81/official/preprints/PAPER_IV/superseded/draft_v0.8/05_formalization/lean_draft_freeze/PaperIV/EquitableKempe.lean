import PaperIV.EquitableEdgeColouring

/-!
# Localisation of an unbalanced pair to one Kempe component

This module is the graph-theoretic front end of equitable edge recolouring.
It is intentionally built on the native `PaperIV` literal edge model.  The
global descent and the ceiling arithmetic live in `EquitableEdgeColouring`;
here we only construct the two-colour graph and localise a global imbalance
to one of its connected components.
-/

namespace PaperIV.EquitableKempe

open PaperIV.ColourClasses PaperIV.EquitableEdgeColouring

variable {V Color : Type*} [Fintype V] [DecidableEq V]
  [Fintype Color] [DecidableEq Color]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A literal colour class is a matching, hence its distinct endpoints occupy
twice as many vertices as it has edges. -/
theorem two_mul_card_colourClass_le_vertices
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (colour : Sym2 V → Color)
    (hproper : ProperOn (PaperIV.Model.graphEdges H) colour) (a : Color) :
    2 * (colourClass (PaperIV.Model.graphEdges H) colour a).card ≤
      Fintype.card V := by
  classical
  let endpoints : Finset V :=
    (colourClass (PaperIV.Model.graphEdges H) colour a).biUnion Sym2.toFinset
  have hedgeCard (e : Sym2 V)
      (he : e ∈ colourClass (PaperIV.Model.graphEdges H) colour a) :
      e.toFinset.card = 2 := by
    apply Sym2.card_toFinset_of_not_isDiag
    exact PaperIV.Model.not_isDiag_of_mem_graphEdges (G := H)
      ((colourClass_subset _ _ _ he))
  have hendpoints :
      endpoints.card = 2 *
        (colourClass (PaperIV.Model.graphEdges H) colour a).card := by
    rw [show endpoints =
      (colourClass (PaperIV.Model.graphEdges H) colour a).biUnion
        Sym2.toFinset from rfl,
      Finset.card_biUnion
        (colourClass_pairwiseDisjoint_toFinset hproper a)]
    calc
      (∑ e ∈ colourClass (PaperIV.Model.graphEdges H) colour a,
          e.toFinset.card) =
          ∑ _e ∈ colourClass (PaperIV.Model.graphEdges H) colour a, 2 := by
            apply Finset.sum_congr rfl
            intro e he
            exact hedgeCard e he
      _ = 2 * (colourClass (PaperIV.Model.graphEdges H) colour a).card := by
        simp [Nat.mul_comm]
  calc
    2 * (colourClass (PaperIV.Model.graphEdges H) colour a).card =
        endpoints.card := hendpoints.symm
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ endpoints)
    _ = Fintype.card V := Finset.card_univ

/-- In a connected graph properly edge-coloured with two colours, either
colour has at most one edge more than the other. -/
theorem finTwo_class_zero_le_one_add_one
    {H : SimpleGraph V} [DecidableRel H.Adj] (hconnected : H.Connected)
    (colour : Sym2 V → Fin 2)
    (hproper : ProperOn (PaperIV.Model.graphEdges H) colour) :
    (colourClass (PaperIV.Model.graphEdges H) colour 0).card ≤
      (colourClass (PaperIV.Model.graphEdges H) colour 1).card + 1 := by
  have hmatching :=
    two_mul_card_colourClass_le_vertices colour hproper (0 : Fin 2)
  have hconnectedEdges := hconnected.card_vert_le_card_edgeSet_add_one
  have hsum := sum_card_colourClass_univ
    (PaperIV.Model.graphEdges H) colour
  have hsum' :
      (colourClass (PaperIV.Model.graphEdges H) colour 0).card +
          (colourClass (PaperIV.Model.graphEdges H) colour 1).card =
        (PaperIV.Model.graphEdges H).card := by
    simpa [Fin.sum_univ_two] using hsum
  have hconnectedEdges' :
      Fintype.card V ≤ (PaperIV.Model.graphEdges H).card + 1 := by
    simpa [PaperIV.Model.graphEdges, Nat.card_eq_fintype_card,
      SimpleGraph.edgeFinset_card] using hconnectedEdges
  omega

/-- The spanning subgraph whose edges have one of the selected colours. -/
def twoColourGraph (colour : Sym2 V → Color) (a b : Color) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (colour s(u, v) = a ∨ colour s(u, v) = b)
  symm := by
    rintro u v ⟨huv, hcolour⟩
    refine ⟨huv.symm, ?_⟩
    simpa only [Sym2.eq_swap] using hcolour
  loopless.irrefl := by
    rintro u ⟨huu, _⟩
    exact G.loopless.irrefl u huu

noncomputable instance twoColourGraphDecidableAdj
    (colour : Sym2 V → Color) (a b : Color) :
    DecidableRel (twoColourGraph (G := G) colour a b).Adj :=
  Classical.decRel _

/-- A deterministic endpoint used only to name the component containing an
edge.  No orientation is introduced into the resource model. -/
noncomputable def edgeAnchor (e : Sym2 V) : V := e.out.1

theorem edgeAnchor_mem (e : Sym2 V) : edgeAnchor e ∈ e :=
  Sym2.out_fst_mem e

/-- Edges of colour `x` assigned to one connected component of the selected
two-colour graph. -/
noncomputable def componentClass (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (x : Color) : Finset (Sym2 V) := by
  classical
  exact (colourClass (PaperIV.Model.graphEdges G) colour x).filter fun e =>
    (twoColourGraph (G := G) colour a b).connectedComponentMk (edgeAnchor e) = c

@[simp] theorem mem_componentClass
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (x : Color) (e : Sym2 V) :
    e ∈ componentClass (G := G) colour a b c x ↔
      e ∈ PaperIV.Model.graphEdges G ∧ colour e = x ∧
        (twoColourGraph (G := G) colour a b).connectedComponentMk
          (edgeAnchor e) = c := by
  classical
  simp [componentClass, colourClass, and_assoc]

/-- The component classes partition a global colour class exactly. -/
theorem sum_card_componentClass
    (colour : Sym2 V → Color) (a b x : Color) :
    ∑ c : (twoColourGraph (G := G) colour a b).ConnectedComponent,
        (componentClass (G := G) colour a b c x).card =
      (colourClass (PaperIV.Model.graphEdges G) colour x).card := by
  classical
  simpa [componentClass] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (colourClass (PaperIV.Model.graphEdges G) colour x)
      (Finset.univ : Finset
        (twoColourGraph (G := G) colour a b).ConnectedComponent)
      (fun e => (twoColourGraph (G := G) colour a b).connectedComponentMk
        (edgeAnchor e)))

/-- A global strict imbalance between two colours occurs in at least one
literal two-colour connected component. -/
theorem exists_component_strict_imbalance
    (colour : Sym2 V → Color) {a b : Color}
    (hlarge :
      (colourClass (PaperIV.Model.graphEdges G) colour b).card <
        (colourClass (PaperIV.Model.graphEdges G) colour a).card) :
    ∃ c : (twoColourGraph (G := G) colour a b).ConnectedComponent,
      (componentClass (G := G) colour a b c b).card <
        (componentClass (G := G) colour a b c a).card := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsum :
      (∑ c : (twoColourGraph (G := G) colour a b).ConnectedComponent,
        (componentClass (G := G) colour a b c a).card) ≤
      ∑ c : (twoColourGraph (G := G) colour a b).ConnectedComponent,
        (componentClass (G := G) colour a b c b).card := by
    exact Finset.sum_le_sum fun c _ => hnone c
  rw [sum_card_componentClass, sum_card_componentClass] at hsum
  omega

/-- Negating equitability produces the ordered pair needed by the Kempe
descent step. -/
theorem exists_pair_gap_two_of_not_equitable
    (colour : Sym2 V → Color)
    (hnot : ¬ IsEquitable (PaperIV.Model.graphEdges G) colour) :
    ∃ a b : Color,
      (colourClass (PaperIV.Model.graphEdges G) colour b).card + 1 <
        (colourClass (PaperIV.Model.graphEdges G) colour a).card := by
  unfold IsEquitable at hnot
  push_neg at hnot
  exact hnot

/-! ## Restriction to one connected component -/

/-- Forget the component subtype on an unordered pair. -/
noncomputable def liftComponentEdge
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    Sym2 c → Sym2 V := Sym2.map Subtype.val

theorem liftComponentEdge_injective
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    Function.Injective (liftComponentEdge (G := G) colour a b c) := by
  exact (Function.Embedding.subtype
    (fun v : V => v ∈ c.supp)).sym2Map.injective

theorem liftComponentEdge_mem_graphEdges
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj]
    {e : Sym2 c} (he : e ∈ PaperIV.Model.graphEdges c.toSimpleGraph) :
    liftComponentEdge (G := G) colour a b c e ∈
      PaperIV.Model.graphEdges G := by
  rw [PaperIV.Model.mem_graphEdges] at he ⊢
  revert he
  refine Sym2.inductionOn e ?_
  intro u v huv
  change G.Adj u.1 v.1
  exact huv.1

theorem liftComponentEdge_has_selected_colour
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj]
    {e : Sym2 c} (he : e ∈ PaperIV.Model.graphEdges c.toSimpleGraph) :
    colour (liftComponentEdge (G := G) colour a b c e) = a ∨
      colour (liftComponentEdge (G := G) colour a b c e) = b := by
  rw [PaperIV.Model.mem_graphEdges] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v huv
  exact huv.2

/-- Encode the selected pair of colours as `Fin 2`. -/
def twoColourCode (a : Color) (x : Color) : Fin 2 :=
  if x = a then 0 else 1

theorem twoColourCode_injective_on_pair {a b x y : Color}
    (hab : a ≠ b) (hx : x = a ∨ x = b) (hy : y = a ∨ y = b)
    (hcode : twoColourCode a x = twoColourCode a y) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · simp [twoColourCode, hab, hab.symm] at hcode
  · simp [twoColourCode, hab, hab.symm] at hcode
  · rfl

/-- The original colouring restricted to one connected component and recoded
with exactly two colours. -/
noncomputable def componentColour
    (colour : Sym2 V → Color) {a b : Color} (_hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    Sym2 c → Fin 2 := fun e =>
  twoColourCode a (colour (liftComponentEdge (G := G) colour a b c e))

theorem componentColour_proper
    (colour : Sym2 V → Color) (hproper :
      ProperOn (PaperIV.Model.graphEdges G) colour)
    {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj] :
    ProperOn (PaperIV.Model.graphEdges c.toSimpleGraph)
      (componentColour (G := G) colour hab c) := by
  intro e he f hf hef hsame
  have heG := liftComponentEdge_mem_graphEdges colour a b c he
  have hfG := liftComponentEdge_mem_graphEdges colour a b c hf
  have hlift_ne :
      liftComponentEdge (G := G) colour a b c e ≠
        liftComponentEdge (G := G) colour a b c f :=
    fun h => hef (liftComponentEdge_injective colour a b c h)
  have hcolour :
      colour (liftComponentEdge (G := G) colour a b c e) =
        colour (liftComponentEdge (G := G) colour a b c f) := by
    apply twoColourCode_injective_on_pair hab
      (liftComponentEdge_has_selected_colour colour a b c he)
      (liftComponentEdge_has_selected_colour colour a b c hf)
    exact hsame
  have hdisj := hproper _ heG _ hfG hlift_ne hcolour
  rw [Finset.disjoint_left]
  intro v hve hvf
  rw [Finset.disjoint_left] at hdisj
  apply hdisj
  · exact Sym2.mem_toFinset.mpr
      (Sym2.mem_map.mpr ⟨v, Sym2.mem_toFinset.mp hve, rfl⟩)
  · exact Sym2.mem_toFinset.mpr
      (Sym2.mem_map.mpr ⟨v, Sym2.mem_toFinset.mp hvf, rfl⟩)

/-- Every endpoint of a selected-colour edge lies in the connected component
named by its anchor. -/
theorem endpoint_mem_component_of_anchor
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (e : Sym2 V) (heG : e ∈ PaperIV.Model.graphEdges G)
    (hcolour : colour e = a ∨ colour e = b)
    (hcomponent : (twoColourGraph (G := G) colour a b).connectedComponentMk
      (edgeAnchor e) = c) :
    ∀ v ∈ e, v ∈ c.supp := by
  intro v hv
  have hadjG : G.Adj e.out.1 e.out.2 := by
    rw [PaperIV.Model.mem_graphEdges] at heG
    apply G.mem_edgeSet.mp
    simpa only [e.out_eq] using heG
  have hadj : (twoColourGraph (G := G) colour a b).Adj e.out.1 e.out.2 := by
    refine ⟨hadjG, ?_⟩
    simpa [e.out_eq] using hcolour
  rw [← e.out_eq, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl
  · exact hcomponent
  · exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj.symm).trans hcomponent

/-- Put a selected original edge into the subtype of its named component. -/
noncomputable def restrictComponentEdge
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (e : Sym2 V) (heG : e ∈ PaperIV.Model.graphEdges G)
    (hcolour : colour e = a ∨ colour e = b)
    (hcomponent : (twoColourGraph (G := G) colour a b).connectedComponentMk
      (edgeAnchor e) = c) : Sym2 c := by
  let hu : e.out.1 ∈ c.supp :=
    endpoint_mem_component_of_anchor colour a b c e heG hcolour hcomponent
      e.out.1 (Sym2.out_fst_mem e)
  let hv : e.out.2 ∈ c.supp :=
    endpoint_mem_component_of_anchor colour a b c e heG hcolour hcomponent
      e.out.2 (Sym2.out_snd_mem e)
  exact s((⟨e.out.1, hu⟩ : c), (⟨e.out.2, hv⟩ : c))

@[simp] theorem lift_restrictComponentEdge
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (e : Sym2 V) (heG : e ∈ PaperIV.Model.graphEdges G)
    (hcolour : colour e = a ∨ colour e = b)
    (hcomponent : (twoColourGraph (G := G) colour a b).connectedComponentMk
      (edgeAnchor e) = c) :
    liftComponentEdge (G := G) colour a b c
      (restrictComponentEdge colour a b c e heG hcolour hcomponent) = e := by
  exact e.out_eq

theorem restrictComponentEdge_mem_graphEdges
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj]
    (e : Sym2 V) (heG : e ∈ PaperIV.Model.graphEdges G)
    (hcolour : colour e = a ∨ colour e = b)
    (hcomponent : (twoColourGraph (G := G) colour a b).connectedComponentMk
      (edgeAnchor e) = c) :
    restrictComponentEdge colour a b c e heG hcolour hcomponent ∈
      PaperIV.Model.graphEdges c.toSimpleGraph := by
  rw [PaperIV.Model.mem_graphEdges]
  change (twoColourGraph (G := G) colour a b).Adj e.out.1 e.out.2
  have hadjG : G.Adj e.out.1 e.out.2 := by
    rw [PaperIV.Model.mem_graphEdges] at heG
    apply G.mem_edgeSet.mp
    simpa only [e.out_eq] using heG
  refine ⟨hadjG, ?_⟩
  simpa only [e.out_eq] using hcolour

theorem anchor_liftComponentEdge_mem_support
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (e : Sym2 c) :
    edgeAnchor (liftComponentEdge (G := G) colour a b c e) ∈ c.supp := by
  have hmem : edgeAnchor (liftComponentEdge (G := G) colour a b c e) ∈
      Sym2.map Subtype.val e := edgeAnchor_mem _
  obtain ⟨v, _hv, hval⟩ := Sym2.mem_map.mp hmem
  exact hval ▸ v.2

/-- The local zero-class and the original `a`-class in the component have
the same cardinality. -/
theorem card_componentClass_left
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj] :
    (componentClass (G := G) colour a b c a).card =
      (colourClass (PaperIV.Model.graphEdges c.toSimpleGraph)
        (componentColour (G := G) colour hab c) 0).card := by
  classical
  apply Finset.card_bij
    (fun e he =>
      let h := (mem_componentClass colour a b c a e).mp he
      restrictComponentEdge colour a b c e h.1 (Or.inl h.2.1) h.2.2)
  · intro e he
    have h := (mem_componentClass colour a b c a e).mp he
    apply mem_colourClass.mpr
    refine ⟨restrictComponentEdge_mem_graphEdges colour a b c e h.1
      (Or.inl h.2.1) h.2.2, ?_⟩
    simp [componentColour, twoColourCode, h.2.1]
  · intro e he f hf hef
    simpa using congrArg (liftComponentEdge (G := G) colour a b c) hef
  · intro f hf
    have hfmem := (mem_colourClass.mp hf)
    have hpair := liftComponentEdge_has_selected_colour colour a b c hfmem.1
    have hfa : colour (liftComponentEdge (G := G) colour a b c f) = a := by
      rcases hpair with ha | hb
      · exact ha
      · have hcode := hfmem.2
        simp [componentColour, twoColourCode, hb, hab, hab.symm] at hcode
    let e := liftComponentEdge (G := G) colour a b c f
    have heG := liftComponentEdge_mem_graphEdges colour a b c hfmem.1
    have heComp : (twoColourGraph (G := G) colour a b).connectedComponentMk
        (edgeAnchor e) = c := anchor_liftComponentEdge_mem_support colour a b c f
    refine ⟨e, (mem_componentClass colour a b c a e).mpr
      ⟨heG, hfa, heComp⟩, ?_⟩
    apply liftComponentEdge_injective colour a b c
    simp [e]

/-- The local one-class and the original `b`-class in the component have
the same cardinality. -/
theorem card_componentClass_right
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj] :
    (componentClass (G := G) colour a b c b).card =
      (colourClass (PaperIV.Model.graphEdges c.toSimpleGraph)
        (componentColour (G := G) colour hab c) 1).card := by
  classical
  apply Finset.card_bij
    (fun e he =>
      let h := (mem_componentClass colour a b c b e).mp he
      restrictComponentEdge colour a b c e h.1 (Or.inr h.2.1) h.2.2)
  · intro e he
    have h := (mem_componentClass colour a b c b e).mp he
    apply mem_colourClass.mpr
    refine ⟨restrictComponentEdge_mem_graphEdges colour a b c e h.1
      (Or.inr h.2.1) h.2.2, ?_⟩
    simp [componentColour, twoColourCode, h.2.1, hab, hab.symm]
  · intro e he f hf hef
    simpa using congrArg (liftComponentEdge (G := G) colour a b c) hef
  · intro f hf
    have hfmem := (mem_colourClass.mp hf)
    have hpair := liftComponentEdge_has_selected_colour colour a b c hfmem.1
    have hfb : colour (liftComponentEdge (G := G) colour a b c f) = b := by
      rcases hpair with ha | hb
      · have hcode := hfmem.2
        simp [componentColour, twoColourCode, ha] at hcode
      · exact hb
    let e := liftComponentEdge (G := G) colour a b c f
    have heG := liftComponentEdge_mem_graphEdges colour a b c hfmem.1
    have heComp : (twoColourGraph (G := G) colour a b).connectedComponentMk
        (edgeAnchor e) = c := anchor_liftComponentEdge_mem_support colour a b c f
    refine ⟨e, (mem_componentClass colour a b c b e).mpr
      ⟨heG, hfb, heComp⟩, ?_⟩
    apply liftComponentEdge_injective colour a b c
    simp [e]

theorem componentClass_left_le_right_add_one
    (colour : Sym2 V → Color)
    (hproper : ProperOn (PaperIV.Model.graphEdges G) colour)
    {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    [Fintype c] [DecidableRel c.toSimpleGraph.Adj] :
    (componentClass (G := G) colour a b c a).card ≤
      (componentClass (G := G) colour a b c b).card + 1 := by
  rw [card_componentClass_left colour hab c,
    card_componentClass_right colour hab c]
  exact finTwo_class_zero_le_one_add_one c.connected_toSimpleGraph
    (componentColour (G := G) colour hab c)
    (componentColour_proper colour hproper hab c)

/-! ## Swapping one component -/

theorem anchor_components_eq_of_common_endpoint
    (colour : Sym2 V → Color) (a b : Color)
    {e f : Sym2 V} (heG : e ∈ PaperIV.Model.graphEdges G)
    (hfG : f ∈ PaperIV.Model.graphEdges G)
    (he : colour e = a ∨ colour e = b)
    (hf : colour f = a ∨ colour f = b)
    {v : V} (hve : v ∈ e) (hvf : v ∈ f) :
    (twoColourGraph (G := G) colour a b).connectedComponentMk (edgeAnchor e) =
      (twoColourGraph (G := G) colour a b).connectedComponentMk (edgeAnchor f) := by
  let ce := (twoColourGraph (G := G) colour a b).connectedComponentMk (edgeAnchor e)
  let cf := (twoColourGraph (G := G) colour a b).connectedComponentMk (edgeAnchor f)
  have hve' : v ∈ ce.supp :=
    endpoint_mem_component_of_anchor colour a b ce e heG he rfl v hve
  have hvf' : v ∈ cf.supp :=
    endpoint_mem_component_of_anchor colour a b cf f hfG hf rfl v hvf
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hve' hvf'

def InSwappedComponent
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (e : Sym2 V) : Prop :=
  (colour e = a ∨ colour e = b) ∧
    (twoColourGraph (G := G) colour a b).connectedComponentMk
      (edgeAnchor e) = c

/-- Swap the two chosen colours exactly on one connected component. -/
noncomputable def swapComponentColour
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    Sym2 V → Color := by
  classical
  exact fun e =>
    if InSwappedComponent (G := G) colour a b c e then
      Equiv.swap a b (colour e) else colour e

theorem swapComponentColour_proper
    (colour : Sym2 V → Color)
    (hproper : ProperOn (PaperIV.Model.graphEdges G) colour)
    (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    ProperOn (PaperIV.Model.graphEdges G)
      (swapComponentColour (G := G) colour a b c) := by
  classical
  intro e heG f hfG hef
  rw [Finset.disjoint_left]
  intro hsame v hve hvf
  by_cases he : InSwappedComponent (G := G) colour a b c e <;>
    by_cases hf : InSwappedComponent (G := G) colour a b c f
  · have hold : colour e ≠ colour f := by
      intro h
      have hd := hproper e heG f hfG hef h
      exact (Finset.disjoint_left.mp hd) hve hvf
    exact hold ((Equiv.swap a b).injective (by
      simpa [swapComponentColour, he, hf] using hsame))
  · have heSwap : Equiv.swap a b (colour e) = a ∨
        Equiv.swap a b (colour e) = b := by
      rcases he.1 with hea | heb
      · rw [hea, Equiv.swap_apply_left]
        exact Or.inr rfl
      · rw [heb, Equiv.swap_apply_right]
        exact Or.inl rfl
    have hfcolour : colour f = a ∨ colour f = b := by
      have hs : Equiv.swap a b (colour e) = colour f := by
        simpa [swapComponentColour, he, hf] using hsame
      rwa [hs] at heSwap
    apply hf
    refine ⟨hfcolour, ?_⟩
    have hcomp := anchor_components_eq_of_common_endpoint colour a b
      heG hfG he.1 hfcolour (Sym2.mem_toFinset.mp hve)
        (Sym2.mem_toFinset.mp hvf)
    exact hcomp.symm.trans he.2
  · have hfSwap : Equiv.swap a b (colour f) = a ∨
        Equiv.swap a b (colour f) = b := by
      rcases hf.1 with hfa | hfb
      · rw [hfa, Equiv.swap_apply_left]
        exact Or.inr rfl
      · rw [hfb, Equiv.swap_apply_right]
        exact Or.inl rfl
    have hecolour : colour e = a ∨ colour e = b := by
      have hs : colour e = Equiv.swap a b (colour f) := by
        simpa [swapComponentColour, he, hf] using hsame
      rw [hs]
      exact hfSwap
    apply he
    refine ⟨hecolour, ?_⟩
    have hcomp := anchor_components_eq_of_common_endpoint colour a b
      heG hfG hecolour hf.1 (Sym2.mem_toFinset.mp hve)
        (Sym2.mem_toFinset.mp hvf)
    exact hcomp.trans hf.2
  · have hold : colour e ≠ colour f := by
      intro h
      have hd := hproper e heG f hfG hef h
      exact (Finset.disjoint_left.mp hd) hve hvf
    exact hold (by simpa [swapComponentColour, he, hf] using hsame)

theorem colourClass_swapComponent_left
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    colourClass (PaperIV.Model.graphEdges G)
        (swapComponentColour (G := G) colour a b c) a =
      (colourClass (PaperIV.Model.graphEdges G) colour a \
        componentClass (G := G) colour a b c a) ∪
      componentClass (G := G) colour a b c b := by
  classical
  ext e
  by_cases heG : e ∈ PaperIV.Model.graphEdges G
  · by_cases ha : colour e = a
    · have hnb : colour e ≠ b := fun hb => hab (ha.symm.trans hb)
      by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hnb, hc, Equiv.swap_apply_def,
          hab, hab.symm]
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hnb, hc, Equiv.swap_apply_def,
          hab, hab.symm]
    · by_cases hb : colour e = b
      · by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
            (edgeAnchor e) = c
        · simp [colourClass, componentClass, swapComponentColour,
            InSwappedComponent, heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm]
        · simp [colourClass, componentClass, swapComponentColour,
            InSwappedComponent, heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm]
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hb, Equiv.swap_apply_def]
  · simp [colourClass, componentClass, heG]

theorem colourClass_swapComponent_right
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    colourClass (PaperIV.Model.graphEdges G)
        (swapComponentColour (G := G) colour a b c) b =
      (colourClass (PaperIV.Model.graphEdges G) colour b \
        componentClass (G := G) colour a b c b) ∪
      componentClass (G := G) colour a b c a := by
  classical
  ext e
  by_cases heG : e ∈ PaperIV.Model.graphEdges G
  · by_cases ha : colour e = a
    · have hnb : colour e ≠ b := fun hb => hab (ha.symm.trans hb)
      by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hnb, hc, Equiv.swap_apply_def,
          hab, hab.symm]
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hnb, hc, Equiv.swap_apply_def,
          hab, hab.symm]
    · by_cases hb : colour e = b
      · by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
            (edgeAnchor e) = c
        · simp [colourClass, componentClass, swapComponentColour,
            InSwappedComponent, heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm]
        · simp [colourClass, componentClass, swapComponentColour,
            InSwappedComponent, heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm]
      · simp [colourClass, componentClass, swapComponentColour,
          InSwappedComponent, heG, ha, hb, Equiv.swap_apply_def]
  · simp [colourClass, componentClass, heG]

theorem componentClass_subset_colourClass
    (colour : Sym2 V → Color) (a b : Color)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent)
    (x : Color) :
    componentClass (G := G) colour a b c x ⊆
      colourClass (PaperIV.Model.graphEdges G) colour x := by
  classical
  intro e he
  exact (Finset.mem_filter.mp he).1

theorem card_swapComponent_left_add
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    (colourClass (PaperIV.Model.graphEdges G)
        (swapComponentColour (G := G) colour a b c) a).card +
        (componentClass (G := G) colour a b c a).card =
      (colourClass (PaperIV.Model.graphEdges G) colour a).card +
        (componentClass (G := G) colour a b c b).card := by
  classical
  rw [colourClass_swapComponent_left colour hab c]
  have hdisjoint : Disjoint
      (colourClass (PaperIV.Model.graphEdges G) colour a \
        componentClass (G := G) colour a b c a)
      (componentClass (G := G) colour a b c b) := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have hea := (mem_colourClass.mp (Finset.mem_sdiff.mp heA).1).2
    have heb := (mem_componentClass colour a b c b e).mp heB |>.2.1
    exact hab (hea.symm.trans heb)
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_sdiff_of_subset
      (componentClass_subset_colourClass colour a b c a)]
  have hcard := Finset.card_le_card
    (componentClass_subset_colourClass colour a b c a)
  omega

theorem card_swapComponent_right_add
    (colour : Sym2 V → Color) {a b : Color} (hab : a ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    (colourClass (PaperIV.Model.graphEdges G)
        (swapComponentColour (G := G) colour a b c) b).card +
        (componentClass (G := G) colour a b c b).card =
      (colourClass (PaperIV.Model.graphEdges G) colour b).card +
        (componentClass (G := G) colour a b c a).card := by
  classical
  rw [colourClass_swapComponent_right colour hab c]
  have hdisjoint : Disjoint
      (colourClass (PaperIV.Model.graphEdges G) colour b \
        componentClass (G := G) colour a b c b)
      (componentClass (G := G) colour a b c a) := by
    rw [Finset.disjoint_left]
    intro e heB heA
    have heb := (mem_colourClass.mp (Finset.mem_sdiff.mp heB).1).2
    have hea := (mem_componentClass colour a b c a e).mp heA |>.2.1
    exact hab (hea.symm.trans heb)
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_sdiff_of_subset
      (componentClass_subset_colourClass colour a b c b)]
  have hcard := Finset.card_le_card
    (componentClass_subset_colourClass colour a b c b)
  omega

theorem colourClass_swapComponent_of_ne
    (colour : Sym2 V → Color) {a b x : Color}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (c : (twoColourGraph (G := G) colour a b).ConnectedComponent) :
    colourClass (PaperIV.Model.graphEdges G)
        (swapComponentColour (G := G) colour a b c) x =
      colourClass (PaperIV.Model.graphEdges G) colour x := by
  classical
  ext e
  by_cases heG : e ∈ PaperIV.Model.graphEdges G
  · by_cases ha : colour e = a
    · by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
          (edgeAnchor e) = c
      · simp [colourClass, swapComponentColour, InSwappedComponent,
          heG, ha, hc, Equiv.swap_apply_def, hxa, hxb, hxa.symm, hxb.symm]
      · simp [colourClass, swapComponentColour, InSwappedComponent,
          heG, ha, hc, Equiv.swap_apply_def, hxa, hxa.symm]
    · by_cases hb : colour e = b
      · by_cases hc : (twoColourGraph (G := G) colour a b).connectedComponentMk
            (edgeAnchor e) = c
        · simp [colourClass, swapComponentColour, InSwappedComponent,
            heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm, hxa, hxb, hxa.symm, hxb.symm]
        · simp [colourClass, swapComponentColour, InSwappedComponent,
            heG, ha, hb, hc, Equiv.swap_apply_def,
            hab, hab.symm, hxb, hxb.symm]
      · simp [colourClass, swapComponentColour, InSwappedComponent,
          heG, ha, hb, Equiv.swap_apply_def]
  · simp [colourClass, heG]

theorem sum_eq_two_add_rest (f : Color → ℕ) {a b : Color} (hab : a ≠ b) :
    ∑ x : Color, f x = f a + f b +
      ∑ x ∈ (Finset.univ.erase a).erase b, f x := by
  classical
  have ha : a ∈ (Finset.univ : Finset Color) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset Color).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb]
  omega

/-- One unbalanced pair admits a proper component swap of strictly smaller
square-energy. -/
theorem exists_energy_decreasing_swap
    (colour : Sym2 V → Color)
    (hproper : ProperOn (PaperIV.Model.graphEdges G) colour)
    {a b : Color}
    (hgap : (colourClass (PaperIV.Model.graphEdges G) colour b).card + 1 <
      (colourClass (PaperIV.Model.graphEdges G) colour a).card) :
    ∃ colour' : Sym2 V → Color,
      ProperOn (PaperIV.Model.graphEdges G) colour' ∧
      energy (PaperIV.Model.graphEdges G) colour' <
        energy (PaperIV.Model.graphEdges G) colour := by
  classical
  have hab : a ≠ b := by
    intro h
    subst b
    omega
  obtain ⟨c, hcLarge⟩ := exists_component_strict_imbalance
    (G := G) (a := a) (b := b) colour (by omega)
  letI := Fintype.ofFinite c
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  have hcSmall := componentClass_left_le_right_add_one
    colour hproper hab c
  have hcEq : (componentClass (G := G) colour a b c a).card =
      (componentClass (G := G) colour a b c b).card + 1 := by omega
  let colour' := swapComponentColour (G := G) colour a b c
  have hleft := card_swapComponent_left_add colour hab c
  have hright := card_swapComponent_right_add colour hab c
  have hleft' :
      (colourClass (PaperIV.Model.graphEdges G) colour' a).card + 1 =
        (colourClass (PaperIV.Model.graphEdges G) colour a).card := by
    change (colourClass (PaperIV.Model.graphEdges G)
      (swapComponentColour (G := G) colour a b c) a).card + 1 = _
    omega
  have hright' :
      (colourClass (PaperIV.Model.graphEdges G) colour' b).card =
        (colourClass (PaperIV.Model.graphEdges G) colour b).card + 1 := by
    change (colourClass (PaperIV.Model.graphEdges G)
      (swapComponentColour (G := G) colour a b c) b).card = _
    omega
  have hrest :
      (∑ x ∈ (Finset.univ.erase a).erase b,
        (colourClass (PaperIV.Model.graphEdges G) colour' x).card ^ 2) =
      ∑ x ∈ (Finset.univ.erase a).erase b,
        (colourClass (PaperIV.Model.graphEdges G) colour x).card ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := fun h =>
      (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1 h
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    rw [colourClass_swapComponent_of_ne colour hab hxa hxb c]
  refine ⟨colour', swapComponentColour_proper colour hproper a b c, ?_⟩
  change (∑ x : Color,
      (colourClass (PaperIV.Model.graphEdges G) colour' x).card ^ 2) <
    ∑ x : Color,
      (colourClass (PaperIV.Model.graphEdges G) colour x).card ^ 2
  rw [sum_eq_two_add_rest _ hab, sum_eq_two_add_rest _ hab, hrest]
  nlinarith

/-- Every finite proper literal edge colouring has an equitable proper
recolouring on the same palette. -/
theorem exists_equitable_colouring
    (colour : Sym2 V → Color)
    (hproper : ProperOn (PaperIV.Model.graphEdges G) colour) :
    ∃ colour' : Sym2 V → Color,
      ProperOn (PaperIV.Model.graphEdges G) colour' ∧
      IsEquitable (PaperIV.Model.graphEdges G) colour' := by
  apply exists_equitable_of_energy_descent
    (PaperIV.Model.graphEdges G) (colour := colour) (hproper := hproper)
  intro current hcurrent hnot
  obtain ⟨a, b, hgap⟩ :=
    exists_pair_gap_two_of_not_equitable (G := G) current hnot
  exact exists_energy_decreasing_swap current hcurrent hgap

/-- The fully internal Vizing-plus-Kempe endpoint required by RD09 phase I. -/
noncomputable def equitableVizingBoundedColouring (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    BoundedColouring (PaperIV.Model.graphEdges G)
      (Fin (G.maxDegree + 1))
      (classCeiling (PaperIV.Model.graphEdges G).card (G.maxDegree + 1)) := by
  let initial := PaperIV.LineGraphColouring.vizingEdgeColour G
  have hproper := PaperIV.LineGraphColouring.properOn_vizingEdgeColour G
  let balanced := Classical.choose (exists_equitable_colouring initial hproper)
  have hbalanced := Classical.choose_spec
    (exists_equitable_colouring initial hproper)
  simpa using
    (boundedColouringOfEquitable _ balanced hbalanced.1 hbalanced.2)

end PaperIV.EquitableKempe
