import PaperIV.ColourClasses

/-!
# Transporting literal matching classes along a labelled clique

The terminal construction uses labels for vertices of a clique.  This module
contains the finite, resource-preserving part of that operation: a proper
edge-colouring on labelled source edges transports to an exact partition into
matching classes on the physical vertices.  Nothing is assumed about a
terminal partition; every target class is an `image` of a literal source
colour class.
-/

namespace PaperIV.TransportedMatchings

open PaperIV.ColourClasses

variable {A V Color : Type*} [DecidableEq A] [DecidableEq V] [DecidableEq Color]

/-- Transport a finite family of labelled edges through an injective vertex
labelling. -/
def mapEdges (f : A ↪ V) (E : Finset (Sym2 A)) : Finset (Sym2 V) :=
  E.image (Sym2.map f)

/-- The physical colour class obtained from a labelled colour class. -/
def mapColourClass (f : A ↪ V) (E : Finset (Sym2 A))
    (colour : Sym2 A → Color) (c : Color) : Finset (Sym2 V) :=
  (colourClass E colour c).image (Sym2.map f)

theorem mem_mapColourClass {f : A ↪ V} {E : Finset (Sym2 A)}
    {colour : Sym2 A → Color} {c : Color} {e : Sym2 V} :
    e ∈ mapColourClass f E colour c ↔
      ∃ d ∈ E, colour d = c ∧ Sym2.map f d = e := by
  constructor
  · rintro he
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    exact ⟨d, (mem_colourClass.mp hd).1, (mem_colourClass.mp hd).2, rfl⟩
  · rintro ⟨d, hd, hdc, rfl⟩
    exact Finset.mem_image.mpr ⟨d, mem_colourClass.mpr ⟨hd, hdc⟩, rfl⟩

/-- Transport preserves matchingness of each colour class. -/
theorem mapColourClass_pairwiseDisjoint_toFinset {f : A ↪ V}
    {E : Finset (Sym2 A)} {colour : Sym2 A → Color}
    (hproper : ProperOn E colour) (c : Color) :
    (↑(mapColourClass f E colour c) : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
  intro e he d hd hed
  rcases Finset.mem_image.mp (by simpa [mapColourClass] using he) with ⟨e₀, he₀, rfl⟩
  rcases Finset.mem_image.mp (by simpa [mapColourClass] using hd) with ⟨d₀, hd₀, rfl⟩
  have hne : e₀ ≠ d₀ := by
    intro h
    apply hed
    simpa [h]
  have hdisj := hproper e₀ (colourClass_subset E colour c he₀)
    d₀ (colourClass_subset E colour c hd₀) hne
    ((mem_colourClass.mp he₀).2.trans (mem_colourClass.mp hd₀).2.symm)
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hve hvd
  rcases Sym2.mem_map.mp (Sym2.mem_toFinset.mp hve) with ⟨a, hae, hav⟩
  rcases Sym2.mem_map.mp (Sym2.mem_toFinset.mp hvd) with ⟨b, hbd, hbv⟩
  have hab : a = b := f.injective (hav.trans hbv.symm)
  subst b
  exact Finset.disjoint_left.mp hdisj (Sym2.mem_toFinset.mpr hae) (Sym2.mem_toFinset.mpr hbd)

/-- The transported classes cover exactly the transported edge family. -/
theorem biUnion_mapColourClass (f : A ↪ V) (E : Finset (Sym2 A))
    (colour : Sym2 A → Color) :
    (usedColours E colour).biUnion (mapColourClass f E colour) = mapEdges f E := by
  ext e
  constructor
  · intro hmem
    obtain ⟨c, -, he⟩ := Finset.mem_biUnion.mp hmem
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    exact Finset.mem_image.mpr ⟨d, (mem_colourClass.mp hd).1, rfl⟩
  · rintro he
    rcases Finset.mem_image.mp he with ⟨d, hd, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨colour d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨d, mem_colourClass.mpr ⟨hd, rfl⟩, rfl⟩

/-- Different source colours remain edge-disjoint after transport. -/
theorem disjoint_mapColourClass {f : A ↪ V} {E : Finset (Sym2 A)}
    {colour : Sym2 A → Color} {c d : Color} (hcd : c ≠ d) :
    Disjoint (mapColourClass f E colour c) (mapColourClass f E colour d) := by
  rw [Finset.disjoint_left]
  intro e he hd
  rcases Finset.mem_image.mp he with ⟨a, ha, hae⟩
  rcases Finset.mem_image.mp hd with ⟨b, hb, hbe⟩
  have hab : a = b := Sym2.map.injective f.injective (hae.trans hbe.symm)
  subst b
  exact hcd (((mem_colourClass.mp ha).2).symm.trans (mem_colourClass.mp hb).2)

/-- Injective relabelling preserves the exact size of every matching class.
This is the cardinal part of the terminal ledger transport. -/
theorem card_mapColourClass {f : A ↪ V} (E : Finset (Sym2 A))
    (colour : Sym2 A → Color) (c : Color) :
    (mapColourClass f E colour c).card = (colourClass E colour c).card := by
  unfold mapColourClass
  exact Finset.card_image_of_injective _ (Sym2.map.injective f.injective)

end PaperIV.TransportedMatchings
