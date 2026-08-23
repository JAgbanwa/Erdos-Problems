/-
# The cross-patch gadget also walls: counting the webs it demands

`BKLO/CrossHexGadget.lean` shows that the cross-patch regime **closes**: there is a complete,
closed cross-patch routing for a leftover hexagon, using nineteen clusters, in which no cluster
ever pairs the two legs at a leftover vertex.  So the obstruction of `BKLO/HexWall.lean` — which
refutes exactly the *corner* mechanism — does not apply to it.

This file settles the remaining question: can a *sparse* reservoir supply that gadget for **every**
leftover hexagon?  It cannot, and for the same counting reason, applied now to the cross web.

The nineteen clusters of the gadget form a web in the cluster-intersection graph.  Reading the web
as a sequence of choices, only five of them are free:

* the closing cluster `P = {v 0, v 2, v 4}` (at most `|𝒞| ≤ |V| m / 7` choices);
* the three patch clusters `G 1, G 3, G 5` meeting `P` (at most `7m` each);
* the cluster `B 0` meeting `G 0` (at most `7m`).

Every one of the remaining fourteen clusters meets two already-chosen clusters in two *distinct*
vertices, so — two distinct vertices lying in at most one common cluster — it has at most `49`
choices.  Finally the six leftover vertices lie in the six clusters `A 0, …, A 5`, at most `7`
choices each.  Hence a family in which every vertex lies in at most `m` clusters serves at most
`7³⁸ |V| m⁵ / 7` hexagons (`BKLO.card_crossCovered_le`), against the `|V|(|V|-1)⋯(|V|-5)` hexagons
that a leftover may carry.

So the cross-patch regime walls too, and for the reason the corner regime did: the demand is a
*connected web* of clusters spanning the six leftover vertices, and a connected web with `k` free
choices is worth only `O(|V| m^{k})` — never the `|V|⁶` a universal absorber needs.

The results are `BKLO.card_crossCovered_le` (the counting), `BKLO.not_crossHexReservoir` (a sparse
cluster family cannot place the gadget at every hexagon) and `BKLO.not_clusterReservoirCrossHex`
(the packaged existence statement is false).  Everything in this file is `sorry`-free.
-/
import BKLO.HexWall
import BKLO.CrossHexGadget
import Mathlib.Data.List.GetD

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Chains of choices, recorded as lists -/

/-- One more choice appended to a set of partial choice sequences. -/
def cstep (L : Finset (List (Finset V))) (f : List (Finset V) → Finset (Finset V)) :
    Finset (List (Finset V)) :=
  L.biUnion (fun l => (f l).image (fun C => C :: l))

theorem mem_cstep {L : Finset (List (Finset V))} {f : List (Finset V) → Finset (Finset V)}
    {C : Finset V} {l : List (Finset V)} (hl : l ∈ L) (hC : C ∈ f l) : C :: l ∈ cstep L f :=
  Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image_of_mem _ hC⟩

theorem card_cstep {L : Finset (List (Finset V))} {f : List (Finset V) → Finset (Finset V)} {k : ℕ}
    (h : ∀ l ∈ L, (f l).card ≤ k) : (cstep L f).card ≤ L.card * k :=
  card_biUnion_le_mul (fun l hl => Finset.card_image_le.trans (h l hl))

/-- Every entry of a list in `cstep L f` is small, provided the same holds in `L` and `f` only
proposes clusters of the family. -/
theorem cstep_seven {𝒞 : Finset (Finset V)} {L : Finset (List (Finset V))}
    {f : List (Finset V) → Finset (Finset V)} (h7 : ∀ C ∈ 𝒞, C.card ≤ 7)
    (hL : ∀ l ∈ L, ∀ C ∈ l, C.card ≤ 7) (hf : ∀ l, f l ⊆ 𝒞) :
    ∀ l ∈ cstep L f, ∀ C ∈ l, C.card ≤ 7 := by
  intro l hl C hC
  obtain ⟨l', hl', hli⟩ := Finset.mem_biUnion.1 hl
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hli
  rcases List.mem_cons.1 hC with rfl | hC'
  · exact h7 C (hf l' hD)
  · exact hL l' hl' C hC'

omit [DecidableEq V] in
/-- Reading an entry of a small list off by index. -/
theorem getD_card_le {l : List (Finset V)} (hl : ∀ C ∈ l, C.card ≤ 7) (i : ℕ) :
    (l.getD i ∅).card ≤ 7 := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hl _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

/-! ### Ways of entering `meetsCl` and `dblMeets` -/

theorem mem_meetsCl_of {𝒞 : Finset (Finset V)} {A C : Finset V} {u : V} (hA : A ∈ 𝒞) (hu : u ∈ C)
    (hu' : u ∈ A) : A ∈ meetsCl 𝒞 C :=
  Finset.mem_biUnion.2 ⟨u, hu, mem_clustersAt.2 ⟨hA, hu'⟩⟩

theorem mem_dblMeets_of {𝒞 : Finset (Finset V)} {A C C' : Finset V} {u w : V} (hA : A ∈ 𝒞)
    (hu : u ∈ C) (hw : w ∈ C') (huA : u ∈ A) (hwA : w ∈ A) (huw : u ≠ w) :
    A ∈ dblMeets 𝒞 C C' := by
  refine Finset.mem_biUnion.2 ⟨(u, w), Finset.mem_product.2 ⟨hu, hw⟩, ?_⟩
  rw [if_neg huw]
  exact Finset.mem_filter.2 ⟨hA, huA, hwA⟩

/-! ### The demand of the cross-patch gadget -/

/-- **The cross web**: the part of the cross-patch gadget's demand that the counting refutes.  The
nineteen clusters of `BKLO/CrossHexGadget.lean`, related as they are there: `G 1, G 3, G 5` meet
the closing cluster `P`; `G 2, G 4, G 0` meet two of these in two distinct vertices; `B 0` meets
`G 0`; and the twelve clusters `A i, B i` walk around the hexagon, each meeting the previous one
and a patch cluster in two distinct vertices.  The six leftover vertices lie in `A 0, …, A 5`.

No distinctness of the clusters and no further incidence is asked for, so any placement of the
gadget yields it (`crossChain_of_placement`). -/
def CrossChain (𝒞 : Finset (Finset V)) (x : Fin 6 → V) : Prop :=
  ∃ P G0 G1 G2 G3 G4 G5 A0 A1 A2 A3 A4 A5 B0 B1 B2 B3 B4 B5 : Finset V,
    P ∈ 𝒞 ∧ G1 ∈ meetsCl 𝒞 P ∧ G3 ∈ meetsCl 𝒞 P ∧ G5 ∈ meetsCl 𝒞 P ∧
    G2 ∈ dblMeets 𝒞 G1 P ∧ G4 ∈ dblMeets 𝒞 G3 P ∧ G0 ∈ dblMeets 𝒞 G5 G1 ∧
    B0 ∈ meetsCl 𝒞 G0 ∧
    A1 ∈ dblMeets 𝒞 B0 G1 ∧ B1 ∈ dblMeets 𝒞 A1 G1 ∧
    A2 ∈ dblMeets 𝒞 B1 G2 ∧ B2 ∈ dblMeets 𝒞 A2 G2 ∧
    A3 ∈ dblMeets 𝒞 B2 G3 ∧ B3 ∈ dblMeets 𝒞 A3 G3 ∧
    A4 ∈ dblMeets 𝒞 B3 G4 ∧ B4 ∈ dblMeets 𝒞 A4 G4 ∧
    A5 ∈ dblMeets 𝒞 B4 G5 ∧ B5 ∈ dblMeets 𝒞 A5 G5 ∧
    A0 ∈ dblMeets 𝒞 B5 G0 ∧
    x 0 ∈ A0 ∧ x 1 ∈ A1 ∧ x 2 ∈ A2 ∧ x 3 ∈ A3 ∧ x 4 ∈ A4 ∧ x 5 ∈ A5

/-! ### The webs of clusters that can carry the gadget

The nineteen clusters are chosen in the order `P`, `G 1`, `G 3`, `G 5`, `G 2`, `G 4`, `G 0`,
`B 0`, `A 1`, `B 1`, …, `A 5`, `B 5`, `A 0`, and recorded as a list, most recent first.  Five of
the steps are free (`P` and the four clusters chosen by a single meeting point); the other
fourteen meet two already-chosen clusters in two distinct vertices, and so are almost determined.
-/

/-- Step 1: the closing cluster `P`. -/
def cw1 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) := 𝒞.image (fun P => [P])

/-- Step 2: `G 1`, meeting `P`. -/
def cw2 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw1 𝒞) (fun l => meetsCl 𝒞 (l.getD 0 ∅))

/-- Step 3: `G 3`, meeting `P`. -/
def cw3 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw2 𝒞) (fun l => meetsCl 𝒞 (l.getD 1 ∅))

/-- Step 4: `G 5`, meeting `P`. -/
def cw4 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw3 𝒞) (fun l => meetsCl 𝒞 (l.getD 2 ∅))

/-- Step 5: `G 2`, meeting `G 1` and `P`. -/
def cw5 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw4 𝒞) (fun l => dblMeets 𝒞 (l.getD 2 ∅) (l.getD 3 ∅))

/-- Step 6: `G 4`, meeting `G 3` and `P`. -/
def cw6 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw5 𝒞) (fun l => dblMeets 𝒞 (l.getD 2 ∅) (l.getD 4 ∅))

/-- Step 7: `G 0`, meeting `G 5` and `G 1`. -/
def cw7 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw6 𝒞) (fun l => dblMeets 𝒞 (l.getD 2 ∅) (l.getD 4 ∅))

/-- Step 8: `B 0`, meeting `G 0`. -/
def cw8 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw7 𝒞) (fun l => meetsCl 𝒞 (l.getD 0 ∅))

/-- Step 9: `A 1`, meeting `B 0` and `G 1`. -/
def cw9 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw8 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 6 ∅))

/-- Step 10: `B 1`, meeting `A 1` and `G 1`. -/
def cw10 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw9 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 7 ∅))

/-- Step 11: `A 2`, meeting `B 1` and `G 2`. -/
def cw11 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw10 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 5 ∅))

/-- Step 12: `B 2`, meeting `A 2` and `G 2`. -/
def cw12 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw11 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 6 ∅))

/-- Step 13: `A 3`, meeting `B 2` and `G 3`. -/
def cw13 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw12 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 9 ∅))

/-- Step 14: `B 3`, meeting `A 3` and `G 3`. -/
def cw14 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw13 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 10 ∅))

/-- Step 15: `A 4`, meeting `B 3` and `G 4`. -/
def cw15 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw14 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 8 ∅))

/-- Step 16: `B 4`, meeting `A 4` and `G 4`. -/
def cw16 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw15 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 9 ∅))

/-- Step 17: `A 5`, meeting `B 4` and `G 5`. -/
def cw17 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw16 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 12 ∅))

/-- Step 18: `B 5`, meeting `A 5` and `G 5`. -/
def cw18 (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw17 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 13 ∅))

/-- Step 19: `A 0`, meeting `B 5` and `G 0`.  The full web. -/
def crossWebs (𝒞 : Finset (Finset V)) : Finset (List (Finset V)) :=
  cstep (cw18 𝒞) (fun l => dblMeets 𝒞 (l.getD 0 ∅) (l.getD 11 ∅))

section Seven

variable {𝒞 : Finset (Finset V)} (h7 : ∀ C ∈ 𝒞, C.card ≤ 7)
include h7

theorem cw1_seven : ∀ l ∈ cw1 𝒞, ∀ C ∈ l, C.card ≤ 7 := by
  intro l hl C hC
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hl
  rcases List.mem_cons.1 hC with rfl | hC'
  · exact h7 C hP
  · simp at hC'

theorem cw2_seven : ∀ l ∈ cw2 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw1_seven h7) (fun _ => meetsCl_subset)

theorem cw3_seven : ∀ l ∈ cw3 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw2_seven h7) (fun _ => meetsCl_subset)

theorem cw4_seven : ∀ l ∈ cw4 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw3_seven h7) (fun _ => meetsCl_subset)

theorem cw5_seven : ∀ l ∈ cw5 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw4_seven h7) (fun _ => dblMeets_subset)

theorem cw6_seven : ∀ l ∈ cw6 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw5_seven h7) (fun _ => dblMeets_subset)

theorem cw7_seven : ∀ l ∈ cw7 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw6_seven h7) (fun _ => dblMeets_subset)

theorem cw8_seven : ∀ l ∈ cw8 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw7_seven h7) (fun _ => meetsCl_subset)

theorem cw9_seven : ∀ l ∈ cw9 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw8_seven h7) (fun _ => dblMeets_subset)

theorem cw10_seven : ∀ l ∈ cw10 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw9_seven h7) (fun _ => dblMeets_subset)

theorem cw11_seven : ∀ l ∈ cw11 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw10_seven h7) (fun _ => dblMeets_subset)

theorem cw12_seven : ∀ l ∈ cw12 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw11_seven h7) (fun _ => dblMeets_subset)

theorem cw13_seven : ∀ l ∈ cw13 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw12_seven h7) (fun _ => dblMeets_subset)

theorem cw14_seven : ∀ l ∈ cw14 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw13_seven h7) (fun _ => dblMeets_subset)

theorem cw15_seven : ∀ l ∈ cw15 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw14_seven h7) (fun _ => dblMeets_subset)

theorem cw16_seven : ∀ l ∈ cw16 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw15_seven h7) (fun _ => dblMeets_subset)

theorem cw17_seven : ∀ l ∈ cw17 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw16_seven h7) (fun _ => dblMeets_subset)

theorem cw18_seven : ∀ l ∈ cw18 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw17_seven h7) (fun _ => dblMeets_subset)

/-- Every cluster occurring in a web is a cluster of the family, hence has seven vertices. -/
theorem crossWebs_seven : ∀ l ∈ crossWebs 𝒞, ∀ C ∈ l, C.card ≤ 7 :=
  cstep_seven h7 (cw18_seven h7) (fun _ => dblMeets_subset)

end Seven

/-- **The web count.**  A cluster family in which every vertex lies in at most `m` clusters has at
most `|𝒞| (7m)⁴ 49¹⁴` webs. -/
theorem card_crossWebs_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    (crossWebs 𝒞).card ≤ 𝒞.card * (7 * m) ^ 4 * 49 ^ 14 := by
  have h7 : ∀ C ∈ 𝒞, C.card ≤ 7 := fun C hC => le_of_eq (h𝒞.1 C hC)
  have c1 : (cw1 𝒞).card ≤ 𝒞.card := Finset.card_image_le
  have c2 : (cw2 𝒞).card ≤ 𝒞.card * (7 * m) :=
    (card_cstep (fun l hl => card_meetsCl_le hm (getD_card_le (cw1_seven h7 l hl) 0))).trans
      (Nat.mul_le_mul_right _ c1)
  have c3 : (cw3 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) :=
    (card_cstep (fun l hl => card_meetsCl_le hm (getD_card_le (cw2_seven h7 l hl) 1))).trans
      (Nat.mul_le_mul_right _ c2)
  have c4 : (cw4 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) :=
    (card_cstep (fun l hl => card_meetsCl_le hm (getD_card_le (cw3_seven h7 l hl) 2))).trans
      (Nat.mul_le_mul_right _ c3)
  have c5 : (cw5 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw4_seven h7 l hl) 2)
      (getD_card_le (cw4_seven h7 l hl) 3))).trans (Nat.mul_le_mul_right _ c4)
  have c6 : (cw6 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw5_seven h7 l hl) 2)
      (getD_card_le (cw5_seven h7 l hl) 4))).trans (Nat.mul_le_mul_right _ c5)
  have c7 : (cw7 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw6_seven h7 l hl) 2)
      (getD_card_le (cw6_seven h7 l hl) 4))).trans (Nat.mul_le_mul_right _ c6)
  have c8 : (cw8 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) :=
    (card_cstep (fun l hl => card_meetsCl_le hm (getD_card_le (cw7_seven h7 l hl) 0))).trans
      (Nat.mul_le_mul_right _ c7)
  have c9 : (cw9 𝒞).card ≤ 𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw8_seven h7 l hl) 0)
      (getD_card_le (cw8_seven h7 l hl) 6))).trans (Nat.mul_le_mul_right _ c8)
  have c10 : (cw10 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw9_seven h7 l hl) 0)
      (getD_card_le (cw9_seven h7 l hl) 7))).trans (Nat.mul_le_mul_right _ c9)
  have c11 : (cw11 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw10_seven h7 l hl) 0)
      (getD_card_le (cw10_seven h7 l hl) 5))).trans (Nat.mul_le_mul_right _ c10)
  have c12 : (cw12 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw11_seven h7 l hl) 0)
      (getD_card_le (cw11_seven h7 l hl) 6))).trans (Nat.mul_le_mul_right _ c11)
  have c13 : (cw13 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw12_seven h7 l hl) 0)
      (getD_card_le (cw12_seven h7 l hl) 9))).trans (Nat.mul_le_mul_right _ c12)
  have c14 : (cw14 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw13_seven h7 l hl) 0)
      (getD_card_le (cw13_seven h7 l hl) 10))).trans (Nat.mul_le_mul_right _ c13)
  have c15 : (cw15 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw14_seven h7 l hl) 0)
      (getD_card_le (cw14_seven h7 l hl) 8))).trans (Nat.mul_le_mul_right _ c14)
  have c16 : (cw16 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw15_seven h7 l hl) 0)
      (getD_card_le (cw15_seven h7 l hl) 9))).trans (Nat.mul_le_mul_right _ c15)
  have c17 : (cw17 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw16_seven h7 l hl) 0)
      (getD_card_le (cw16_seven h7 l hl) 12))).trans (Nat.mul_le_mul_right _ c16)
  have c18 : (cw18 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 * 49 * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw17_seven h7 l hl) 0)
      (getD_card_le (cw17_seven h7 l hl) 13))).trans (Nat.mul_le_mul_right _ c17)
  have c19 : (crossWebs 𝒞).card ≤
      𝒞.card * (7 * m) * (7 * m) * (7 * m) * 49 * 49 * 49 * (7 * m) * 49 * 49 * 49 * 49 * 49 *
        49 * 49 * 49 * 49 * 49 * 49 :=
    (card_cstep (fun l hl => card_dblMeets_le h𝒞 (getD_card_le (cw18_seven h7 l hl) 0)
      (getD_card_le (cw18_seven h7 l hl) 11))).trans (Nat.mul_le_mul_right _ c18)
  exact c19.trans (le_of_eq (by ring))

variable [Fintype V]

/-- The hexagons the reservoir can serve: those carrying the cross web. -/
noncomputable def crossCovered (𝒞 : Finset (Finset V)) : Finset (V × V × V × V × V × V) :=
  open Classical in
  Finset.univ.filter (fun p => CrossChain 𝒞 (hexTup p))

/-- **Every served hexagon lies inside a web.**  Its six vertices lie in the six clusters
`A 0, …, A 5`, which sit at positions `0, 10, 8, 6, 4, 2` of the web. -/
theorem crossCovered_subset {𝒞 : Finset (Finset V)} :
    crossCovered 𝒞 ⊆ (crossWebs 𝒞).biUnion (fun l =>
      (l.getD 0 ∅) ×ˢ ((l.getD 10 ∅) ×ˢ ((l.getD 8 ∅) ×ˢ ((l.getD 6 ∅) ×ˢ
        ((l.getD 4 ∅) ×ˢ (l.getD 2 ∅)))))) := by
  classical
  intro q hq
  rw [crossCovered, Finset.mem_filter] at hq
  obtain ⟨P, G0, G1, G2, G3, G4, G5, A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5,
    hP, hG1, hG3, hG5, hG2, hG4, hG0, hB0, hA1, hB1, hA2, hB2, hA3, hB3, hA4, hB4, hA5, hB5, hA0,
    hx0, hx1, hx2, hx3, hx4, hx5⟩ := hq.2
  have m1 : [P] ∈ cw1 𝒞 := Finset.mem_image_of_mem _ hP
  have m2 : G1 :: [P] ∈ cw2 𝒞 := mem_cstep m1 (by simpa using hG1)
  have m3 : G3 :: G1 :: [P] ∈ cw3 𝒞 := mem_cstep m2 (by simpa using hG3)
  have m4 : G5 :: G3 :: G1 :: [P] ∈ cw4 𝒞 := mem_cstep m3 (by simpa using hG5)
  have m5 : G2 :: G5 :: G3 :: G1 :: [P] ∈ cw5 𝒞 := mem_cstep m4 (by simpa using hG2)
  have m6 : G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw6 𝒞 := mem_cstep m5 (by simpa using hG4)
  have m7 : G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw7 𝒞 := mem_cstep m6 (by simpa using hG0)
  have m8 : B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw8 𝒞 :=
    mem_cstep m7 (by simpa using hB0)
  have m9 : A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw9 𝒞 :=
    mem_cstep m8 (by simpa using hA1)
  have m10 : B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw10 𝒞 :=
    mem_cstep m9 (by simpa using hB1)
  have m11 : A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw11 𝒞 :=
    mem_cstep m10 (by simpa using hA2)
  have m12 : B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈ cw12 𝒞 :=
    mem_cstep m11 (by simpa using hB2)
  have m13 : A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈
      cw13 𝒞 := mem_cstep m12 (by simpa using hA3)
  have m14 : B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 :: [P] ∈
      cw14 𝒞 := mem_cstep m13 (by simpa using hB3)
  have m15 : A4 :: B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 :: G1 ::
      [P] ∈ cw15 𝒞 := mem_cstep m14 (by simpa using hA4)
  have m16 : B4 :: A4 :: B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 :: G3 ::
      G1 :: [P] ∈ cw16 𝒞 := mem_cstep m15 (by simpa using hB4)
  have m17 : A5 :: B4 :: A4 :: B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 :: G5 ::
      G3 :: G1 :: [P] ∈ cw17 𝒞 := mem_cstep m16 (by simpa using hA5)
  have m18 : B5 :: A5 :: B4 :: A4 :: B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 :: G2 ::
      G5 :: G3 :: G1 :: [P] ∈ cw18 𝒞 := mem_cstep m17 (by simpa using hB5)
  have m19 : A0 :: B5 :: A5 :: B4 :: A4 :: B3 :: A3 :: B2 :: A2 :: B1 :: A1 :: B0 :: G0 :: G4 ::
      G2 :: G5 :: G3 :: G1 :: [P] ∈ crossWebs 𝒞 := mem_cstep m18 (by simpa using hA0)
  refine Finset.mem_biUnion.2 ⟨_, m19, ?_⟩
  simp only [List.getD, Finset.mem_product]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hexTup] using hx0
  · simpa [hexTup] using hx1
  · simpa [hexTup] using hx2
  · simpa [hexTup] using hx3
  · simpa [hexTup] using hx4
  · simpa [hexTup] using hx5

/-- **The counting.**  A cluster family in which every vertex lies in at most `m` clusters serves
at most `7³⁸ |V| m⁵ / 7` hexagons. -/
theorem card_crossCovered_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    7 * (crossCovered 𝒞).card ≤ 7 ^ 38 * (Fintype.card V * m ^ 5) := by
  have h7 : ∀ C ∈ 𝒞, C.card ≤ 7 := fun C hC => le_of_eq (h𝒞.1 C hC)
  have hfib : (crossCovered 𝒞).card ≤ (crossWebs 𝒞).card * 7 ^ 6 := by
    refine (Finset.card_le_card crossCovered_subset).trans (card_biUnion_le_mul ?_)
    intro l hl
    have hcl := crossWebs_seven h7 l hl
    rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_product]
    calc (l.getD 0 ∅).card * ((l.getD 10 ∅).card * ((l.getD 8 ∅).card * ((l.getD 6 ∅).card *
          ((l.getD 4 ∅).card * (l.getD 2 ∅).card))))
        ≤ 7 * (7 * (7 * (7 * (7 * 7)))) :=
          Nat.mul_le_mul (getD_card_le hcl 0) (Nat.mul_le_mul (getD_card_le hcl 10)
            (Nat.mul_le_mul (getD_card_le hcl 8) (Nat.mul_le_mul (getD_card_le hcl 6)
              (Nat.mul_le_mul (getD_card_le hcl 4) (getD_card_le hcl 2)))))
      _ = 7 ^ 6 := by norm_num
  have hweb := card_crossWebs_le h𝒞 hm
  have hcl := seven_mul_card_le h𝒞 hm
  calc 7 * (crossCovered 𝒞).card
      ≤ 7 * ((crossWebs 𝒞).card * 7 ^ 6) := Nat.mul_le_mul_left _ hfib
    _ ≤ 7 * ((𝒞.card * (7 * m) ^ 4 * 49 ^ 14) * 7 ^ 6) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hweb)
    _ = (7 * 𝒞.card) * (7 ^ 38 * m ^ 4) := by ring
    _ ≤ (Fintype.card V * m) * (7 ^ 38 * m ^ 4) := Nat.mul_le_mul_right _ hcl
    _ = 7 ^ 38 * (Fintype.card V * m ^ 5) := by ring

/-! ### The arithmetic -/

/-- The numerical heart of the wall: with `1000 K d ≤ n` the hexagons a reservoir of maximum degree
`d` can serve, together with those meeting it, are fewer than the injective six-tuples. -/
theorem crosswall_arith {n d B K : ℕ} (hK : 1 ≤ K) (hB : 7 * B ≤ K * (n * d ^ 5))
    (hdn : 1000 * K * d ≤ n) (hn : 4000 ≤ n) : B + 6 * (n ^ 5 * d) < n.descFactorial 6 := by
  set N := n - 5 with hN
  have hnN : n ≤ 2 * N := by omega
  have hNpos : 0 < N := by omega
  have hdesc : N ^ 6 ≤ n.descFactorial 6 := by
    have hexp : n.descFactorial 6 = n * ((n - 1) * ((n - 2) * ((n - 3) * ((n - 4) * (n - 5))))) := by
      simp [Nat.descFactorial]; ring
    have h6 : N ^ 6 = N * (N * (N * (N * (N * N)))) := by ring
    rw [hexp, h6]
    exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega)))))
  have hn6 : n ^ 6 ≤ 64 * N ^ 6 := by
    calc n ^ 6 ≤ (2 * N) ^ 6 := Nat.pow_le_pow_left hnN 6
      _ = 64 * N ^ 6 := by ring
  have hpow : 10 ^ 15 * (K ^ 5 * d ^ 5) ≤ n ^ 5 := by
    calc 10 ^ 15 * (K ^ 5 * d ^ 5) = (1000 * K * d) ^ 5 := by ring
      _ ≤ n ^ 5 := Nat.pow_le_pow_left hdn 5
  have hKK : K ≤ K ^ 5 := Nat.le_self_pow (by norm_num) K
  have hA : 10 ^ 15 * (7 * B) ≤ n ^ 6 := by
    calc 10 ^ 15 * (7 * B) ≤ 10 ^ 15 * (K * (n * d ^ 5)) := Nat.mul_le_mul_left _ hB
      _ ≤ 10 ^ 15 * (K ^ 5 * (n * d ^ 5)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hKK)
      _ = n * (10 ^ 15 * (K ^ 5 * d ^ 5)) := by ring
      _ ≤ n * n ^ 5 := Nat.mul_le_mul_left _ hpow
      _ = n ^ 6 := by ring
  have hBst : 1000 * (n ^ 5 * d) ≤ n ^ 6 := by
    have h1 : 1000 * d ≤ n := le_trans (by nlinarith) hdn
    calc 1000 * (n ^ 5 * d) = n ^ 5 * (1000 * d) := by ring
      _ ≤ n ^ 5 * n := Nat.mul_le_mul_left _ h1
      _ = n ^ 6 := by ring
  have hA' : 7 * 10 ^ 15 * B ≤ 64 * N ^ 6 := by nlinarith only [hn6, hA]
  have hB' : 1000 * (n ^ 5 * d) ≤ 64 * N ^ 6 := le_trans hBst hn6
  have hXpos : 0 < N ^ 6 := by positivity
  have hkey : 7 * 10 ^ 15 * (B + 6 * (n ^ 5 * d)) < 7 * 10 ^ 15 * N ^ 6 := by nlinarith only [hA', hB', hXpos]
  exact lt_of_lt_of_le (Nat.lt_of_mul_lt_mul_left hkey) hdesc

/-! ### What the gadget asks of the reservoir -/

/-- **A placement of the cross-patch gadget at the hexagon `x`**: an injective placement `p` of its
twenty-four vertices extending `x`, and an assignment `Cl` of a cluster of the family to each of
the nineteen gadget clusters, distinct clusters for distinct gadget clusters. -/
def CrossHexPlacement (𝒞 : Finset (Finset V)) (x : Fin 6 → V) : Prop :=
  ∃ (p : ℕ → V) (Cl : Finset ℕ → Finset V),
    (∀ i : Fin 6, p (i : ℕ) = x i) ∧ (∀ u < 24, ∀ v < 24, p u = p v → u = v) ∧
      (∀ c ∈ cxClusters, Cl c ∈ 𝒞) ∧ (∀ c ∈ cxClusters, c.image p ⊆ Cl c) ∧
      (∀ c ∈ cxClusters, ∀ c' ∈ cxClusters, c ≠ c' → Cl c ≠ Cl c')

omit [Fintype V] in
/-- **A placement absorbs the hexagon.**  This is `BKLO.triDecomp_of_crossHexGadget` read off the
hexagon: the demand `BKLO.CrossHexPlacement` is exactly what the cross-patch gadget needs. -/
theorem triDecomp_of_crossHexPlacement {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) {x : Fin 6 → V} (hx : CrossHexPlacement 𝒞 x)
    (hdisj : Disjoint (famEdges 𝒞) (hexEdges x)) : TriDecomp (famEdges 𝒞 ∪ hexEdges x) := by
  obtain ⟨p, Cl, hpx, hp, hmem, hsub, hCl⟩ := hx
  refine triDecomp_of_crossHexGadget h𝒞 p hp Cl hmem hsub hCl ?_ hdisj
  have h0 : p 0 = x 0 := hpx 0
  have h1 : p 1 = x 1 := hpx 1
  have h2 : p 2 = x 2 := hpx 2
  have h3 : p 3 = x 3 := hpx 3
  have h4 : p 4 = x 4 := hpx 4
  have h5 : p 5 = x 5 := hpx 5
  have himg : cxH.image (Sym2.map p) =
      ({s(x 0, x 1), s(x 1, x 2), s(x 2, x 3), s(x 3, x 4), s(x 4, x 5), s(x 0, x 5)} :
        Finset (Sym2 V)) := by
    simp [cxH, h0, h1, h2, h3, h4, h5]
  rw [himg]
  ext e
  rw [mem_hexEdges]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [Sym2.eq_swap]; rfl)))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, by rw [Sym2.eq_swap]; rfl⟩]

omit [Fintype V] in
/-- **A placement of the gadget yields the web.**  Every incidence the counting uses is one of the
gadget's own incidences, the two meeting points being images of distinct gadget vertices. -/
theorem crossChain_of_placement {𝒞 : Finset (Finset V)} {x : Fin 6 → V}
    (hx : CrossHexPlacement 𝒞 x) : CrossChain 𝒞 x := by
  obtain ⟨p, Cl, hpx, hp, hmem, hsub, -⟩ := hx
  have hin : ∀ c ∈ cxClusters, ∀ k ∈ c, p k ∈ Cl c :=
    fun c hc k hk => hsub c hc (Finset.mem_image_of_mem p hk)
  have hne : ∀ u < 24, ∀ v < 24, u ≠ v → p u ≠ p v :=
    fun u hu v hv huv h => huv (hp u hu v hv h)
  refine ⟨Cl {18, 20, 22}, Cl {12, 18, 23}, Cl {13, 18, 19}, Cl {14, 19, 20}, Cl {15, 20, 21},
    Cl {16, 21, 22}, Cl {17, 22, 23}, Cl {0, 11, 12}, Cl {1, 6, 13}, Cl {2, 7, 14}, Cl {3, 8, 15},
    Cl {4, 9, 16}, Cl {5, 10, 17}, Cl {0, 6, 18}, Cl {1, 7, 19}, Cl {2, 8, 20}, Cl {3, 9, 21},
    Cl {4, 10, 22}, Cl {5, 11, 23}, hmem _ (by decide +kernel), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_meetsCl_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 18 (by decide +kernel))
      (hin _ (by decide +kernel) 18 (by decide +kernel))
  · exact mem_meetsCl_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 20 (by decide +kernel))
      (hin _ (by decide +kernel) 20 (by decide +kernel))
  · exact mem_meetsCl_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 22 (by decide +kernel))
      (hin _ (by decide +kernel) 22 (by decide +kernel))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 19 (by decide +kernel))
      (hin _ (by decide +kernel) 20 (by decide +kernel)) (hin _ (by decide +kernel) 19 (by decide +kernel))
      (hin _ (by decide +kernel) 20 (by decide +kernel)) (hne 19 (by norm_num) 20 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 21 (by decide +kernel))
      (hin _ (by decide +kernel) 22 (by decide +kernel)) (hin _ (by decide +kernel) 21 (by decide +kernel))
      (hin _ (by decide +kernel) 22 (by decide +kernel)) (hne 21 (by norm_num) 22 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 23 (by decide +kernel))
      (hin _ (by decide +kernel) 18 (by decide +kernel)) (hin _ (by decide +kernel) 23 (by decide +kernel))
      (hin _ (by decide +kernel) 18 (by decide +kernel)) (hne 23 (by norm_num) 18 (by norm_num) (by norm_num))
  · exact mem_meetsCl_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 18 (by decide +kernel))
      (hin _ (by decide +kernel) 18 (by decide +kernel))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 6 (by decide +kernel))
      (hin _ (by decide +kernel) 13 (by decide +kernel)) (hin _ (by decide +kernel) 6 (by decide +kernel))
      (hin _ (by decide +kernel) 13 (by decide +kernel)) (hne 6 (by norm_num) 13 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 1 (by decide +kernel))
      (hin _ (by decide +kernel) 19 (by decide +kernel)) (hin _ (by decide +kernel) 1 (by decide +kernel))
      (hin _ (by decide +kernel) 19 (by decide +kernel)) (hne 1 (by norm_num) 19 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 7 (by decide +kernel))
      (hin _ (by decide +kernel) 14 (by decide +kernel)) (hin _ (by decide +kernel) 7 (by decide +kernel))
      (hin _ (by decide +kernel) 14 (by decide +kernel)) (hne 7 (by norm_num) 14 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 2 (by decide +kernel))
      (hin _ (by decide +kernel) 20 (by decide +kernel)) (hin _ (by decide +kernel) 2 (by decide +kernel))
      (hin _ (by decide +kernel) 20 (by decide +kernel)) (hne 2 (by norm_num) 20 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 8 (by decide +kernel))
      (hin _ (by decide +kernel) 15 (by decide +kernel)) (hin _ (by decide +kernel) 8 (by decide +kernel))
      (hin _ (by decide +kernel) 15 (by decide +kernel)) (hne 8 (by norm_num) 15 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 3 (by decide +kernel))
      (hin _ (by decide +kernel) 21 (by decide +kernel)) (hin _ (by decide +kernel) 3 (by decide +kernel))
      (hin _ (by decide +kernel) 21 (by decide +kernel)) (hne 3 (by norm_num) 21 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 9 (by decide +kernel))
      (hin _ (by decide +kernel) 16 (by decide +kernel)) (hin _ (by decide +kernel) 9 (by decide +kernel))
      (hin _ (by decide +kernel) 16 (by decide +kernel)) (hne 9 (by norm_num) 16 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 4 (by decide +kernel))
      (hin _ (by decide +kernel) 22 (by decide +kernel)) (hin _ (by decide +kernel) 4 (by decide +kernel))
      (hin _ (by decide +kernel) 22 (by decide +kernel)) (hne 4 (by norm_num) 22 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 10 (by decide +kernel))
      (hin _ (by decide +kernel) 17 (by decide +kernel)) (hin _ (by decide +kernel) 10 (by decide +kernel))
      (hin _ (by decide +kernel) 17 (by decide +kernel)) (hne 10 (by norm_num) 17 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 5 (by decide +kernel))
      (hin _ (by decide +kernel) 23 (by decide +kernel)) (hin _ (by decide +kernel) 5 (by decide +kernel))
      (hin _ (by decide +kernel) 23 (by decide +kernel)) (hne 5 (by norm_num) 23 (by norm_num) (by norm_num))
  · exact mem_dblMeets_of (hmem _ (by decide +kernel)) (hin _ (by decide +kernel) 11 (by decide +kernel))
      (hin _ (by decide +kernel) 12 (by decide +kernel)) (hin _ (by decide +kernel) 11 (by decide +kernel))
      (hin _ (by decide +kernel) 12 (by decide +kernel)) (hne 11 (by norm_num) 12 (by norm_num) (by norm_num))
  · exact (hpx 0) ▸ hin _ (by decide +kernel) 0 (by decide +kernel)
  · exact (hpx 1) ▸ hin _ (by decide +kernel) 1 (by decide +kernel)
  · exact (hpx 2) ▸ hin _ (by decide +kernel) 2 (by decide +kernel)
  · exact (hpx 3) ▸ hin _ (by decide +kernel) 3 (by decide +kernel)
  · exact (hpx 4) ▸ hin _ (by decide +kernel) 4 (by decide +kernel)
  · exact (hpx 5) ▸ hin _ (by decide +kernel) 5 (by decide +kernel)

/-! ### The wall -/

/-- **What a reservoir would have to supply for the cross-patch gadget**: for every six-cycle on
`S` it does not already meet, a placement of the gadget of `BKLO/CrossHexGadget.lean`.  By
`BKLO.triDecomp_of_crossHexPlacement` this is enough to absorb the six-cycle. -/
def CrossHexReservoir (𝒞 : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ x : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → x i ≠ x j) → (∀ i, x i ∈ S) →
    Disjoint (famEdges 𝒞) (hexEdges x) → CrossHexPlacement 𝒞 x

/-- **The cross-patch reservoir does not exist.**  A cluster family whose reserved degree is at
most `d`, with `1000 · 7³⁸ · d ≤ |V|` and `|V| ≥ 4000`, fails `BKLO.CrossHexReservoir`: some
six-cycle of unreserved edges admits no placement of the gadget.

The nineteen clusters of the gadget form a connected web in the cluster-intersection graph with
only five free choices, and two distinct vertices lie in at most one common cluster, so all the
remaining clusters are almost determined.  The hexagons served are therefore `O(|V| d⁵)`, against
the `|V|⁶` six-cycles a leftover may carry. -/
theorem not_crossHexReservoir {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {d : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : ∀ v : V, edeg (famEdges 𝒞) v ≤ d)
    (hdn : 1000 * 7 ^ 38 * d ≤ Fintype.card V) (hn : 4000 ≤ Fintype.card V) :
    ¬ CrossHexReservoir 𝒞 (Finset.univ : Finset V) := by
  classical
  intro hres
  have hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ d := by
    intro v
    have h1 := six_mul_card_clustersAt_le h𝒞 v
    have h2 := hd v
    omega
  have hcov := card_crossCovered_le h𝒞 hm
  set Bad : Finset (V × V × V × V × V × V) :=
    crossCovered 𝒞 ∪ (Finset.univ : Finset (Fin 6)).biUnion (resEdgeSet (famEdges 𝒞)) with hBad
  have hBadcard : Bad.card ≤ (crossCovered 𝒞).card + 6 * (Fintype.card V ^ 5 * d) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    refine (card_biUnion_le_mul (fun i _ => card_resEdgeSet_le hd i)).trans ?_
    simp [Finset.card_univ]
  have hlt : Bad.card < (Fintype.card V).descFactorial 6 :=
    lt_of_le_of_lt hBadcard (crosswall_arith (by norm_num) hcov hdn hn)
  have hcardEmb : (Finset.univ : Finset (Fin 6 ↪ V)).card = (Fintype.card V).descFactorial 6 := by
    rw [Finset.card_univ, Fintype.card_embedding_eq]
    simp
  obtain ⟨f, hf⟩ : ∃ f : Fin 6 ↪ V, embTup f ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (Finset.univ : Finset (Fin 6 ↪ V)).card ≤ Bad.card :=
      Finset.card_le_card_of_injOn embTup (fun f _ => hcon f)
        (fun a _ b _ h => embTup_injective h)
    omega
  have hx : ∀ i j : Fin 6, i ≠ j → (f : Fin 6 → V) i ≠ f j := fun i j hij h => hij (f.injective h)
  have hdisj : Disjoint (famEdges 𝒞) (hexEdges (f : Fin 6 → V)) := by
    rw [Finset.disjoint_right]
    intro e he heR
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    refine hf (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩))
    rw [resEdgeSet, Finset.mem_filter, hexTup_embTup]
    exact ⟨Finset.mem_univ _, heR⟩
  have hplace := hres (f : Fin 6 → V) hx (fun i => Finset.mem_univ _) hdisj
  refine hf (Finset.mem_union_left _ ?_)
  rw [crossCovered, Finset.mem_filter, hexTup_embTup]
  exact ⟨Finset.mem_univ _, crossChain_of_placement hplace⟩

/-! ### The strengthening of the reservoir is impossible -/

/-- **The reservoir existence statement strengthened by the cross-patch demand.**  This is
`BKLO.ClusterReservoirExistence` with pair covering replaced by `BKLO.CrossHexReservoir`: what the
closed cross-patch gadget of `BKLO/CrossHexGadget.lean` would need in order to absorb every
six-cycle leftover. -/
def ClusterReservoirCrossHex : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧ CrossHexReservoir 𝒞 S

/-- **`BKLO.ClusterReservoirCrossHex` is false.**  Take the host to be a complete graph on `n`
vertices and `γ = 1/(1000 · 7³⁸)`; whatever cluster reservoir of maximum degree `γ n` is reserved,
`BKLO.not_crossHexReservoir` produces a six-cycle of unreserved edges at which the gadget cannot
be placed.

So the cross-patch mechanism, which *does* close (`BKLO.triDecomp_of_crossHexGadget`), still
cannot be supplied by a sparse reservoir: its demand is a connected web of nineteen clusters
through six prescribed vertices, and a reservoir of maximum degree `γ|S|` has only `O(γ⁵|S|⁶)` of
them — against the `|S|⁶` six-cycles that may carry the leftover. -/
theorem not_clusterReservoirCrossHex : ¬ ClusterReservoirCrossHex := by
  classical
  intro hCR
  set c : ℕ := 1000 * 7 ^ 38 with hc
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    have : 0 < c := by positivity
    exact_mod_cast this
  obtain ⟨n₀, hres⟩ := hCR (1 / (c : ℝ)) (by positivity)
  set n := max n₀ (4000 * c) with hndef
  have hn4000 : 4000 * c ≤ n := le_max_right _ _
  have hcge : 1 ≤ c := by rw [hc]; norm_num
  have hn4 : 4000 ≤ n := le_trans (Nat.le_mul_of_pos_right 4000 (by omega)) hn4000
  have hnn₀ : n₀ ≤ n := le_max_left _ _
  have hcardfin : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hdegE : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (9 / 10 + 1 / (c : ℝ)) * ((Finset.univ : Finset (Fin n)).card : ℝ) ≤
        (edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v : ℝ) := by
    intro v _
    have hv : edeg (cliqueEdges (Finset.univ : Finset (Fin n))) v = n - 1 := by
      rw [edeg_cliqueEdges_card v, if_pos (Finset.mem_univ v), hcardfin]
    rw [hv, hcardfin]
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h : (1 : ℕ) ≤ n := by omega
      push_cast [Nat.cast_sub h]
      ring
    rw [h1]
    have hn' : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hinv : 1 / (c : ℝ) ≤ 1 / 1000 := by
      have hcc : (1000 : ℝ) ≤ (c : ℝ) := by
        have : (1000 : ℕ) ≤ c := by rw [hc]; norm_num
        exact_mod_cast this
      exact one_div_le_one_div_of_le (by norm_num) hcc
    nlinarith
  obtain ⟨𝒞, hfam, hdeg, hcross⟩ :=
    hres (V := Fin n) (cliqueEdges (Finset.univ : Finset (Fin n))) Finset.univ
      (by rw [hcardfin]; exact hnn₀) (Finset.Subset.refl _) hdegE
  set d := n / c with hddef
  have hd : ∀ v : Fin n, edeg (famEdges 𝒞) v ≤ d := by
    intro v
    have h := hdeg v
    rw [hcardfin] at h
    have h' : (c : ℝ) * (edeg (famEdges 𝒞) v : ℝ) ≤ (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left h (le_of_lt hcpos)
      calc (c : ℝ) * (edeg (famEdges 𝒞) v : ℝ) ≤ (c : ℝ) * (1 / (c : ℝ) * (n : ℝ)) := this
        _ = (n : ℝ) := by field_simp
    have h'' : c * edeg (famEdges 𝒞) v ≤ n := by exact_mod_cast h'
    rw [hddef, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hcardV : Fintype.card (Fin n) = n := by simp
  refine not_crossHexReservoir hfam hd ?_ (by rw [hcardV]; exact hn4) hcross
  have hdiv : c * (n / c) ≤ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self n c
  rw [hcardV, hddef, ← hc]
  exact hdiv

end BKLO
