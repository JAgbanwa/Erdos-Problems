/-
# The hexagon gadget: a closed triangle web for a six-cycle leftover

`BKLO/ClusterWeb.lean` reduces the whole cluster route to `BKLO.TriangleWebExistence`: the *global*
existence of a closed triangle web.  The smallest leftover for which a web is genuinely needed is a
six-cycle (a triangle is decomposable on its own, and `3 ∣ |H|` forces the size), and the previous
analysis left open whether the web can close at all on it.

It can, and this file constructs the closure explicitly.  For a six-cycle `x 0 … x 5` with apexes
`a 0 … a 5` (the apex `a i` covering the leftover edge `x i x (i+1)`), the two legs at `x i` are
paired inside a cluster `C i ∋ x i, a (i-1), a i`, which therefore consumes the triangle
`{x i, a (i-1), a i}`; its third edge `a (i-1) a i` is a *patch edge*, and the six patch edges form
a hexagon on the apexes.  A hexagon has no triangle, so the patch edges cannot be grouped among
themselves — this is what refuted the corner mechanism.  The escape is the **octahedron trade**:
adding the three chords `a 0 a 2`, `a 2 a 4`, `a 4 a 0` — which lie in a *single* further cluster
`D ⊇ {a 0, a 2, a 4}` — turns the six patch edges into three triangles

  `{a 0, a 1, a 2}`,  `{a 2, a 3, a 4}`,  `{a 4, a 5, a 0}`,

while the three chords are exactly the triangle `D` gives back.  So the web closes with seven
active clusters and three cross triangles, and the count is exact:
`7 · 3 = 21 = 2 · 6 (legs) + 3 · 3 (cross edges)`.

The main results are `BKLO.HexWebData.isTriangleWeb_hex` — the closed web — and
`BKLO.triDecomp_hex_absorb`: a cluster reservoir carrying this overlap structure absorbs the
six-cycle outright.

What the gadget *demands of the reservoir* is recorded in `BKLO.HexWebData`: seven distinct
clusters with the stated memberships.  `BKLO.HexWebReservoir` packages that demand as a property
of the reservoir, and `BKLO.triDecomp_hexagon_of_reservoir` shows it is sufficient for six-cycle
leftovers.  Producing such a reservoir is the remaining content of `BKLO.TriangleWebExistence`;
it is not supplied by pair covering.

Everything in this file is `sorry`-free.
-/
import BKLO.ClusterWeb
import BKLO.CornerHexagon

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- Membership test for the edges of a clique. -/
theorem mem_cliqueEdges_of_mem_pair {u v : V} {S : Finset V} (hu : u ∈ S) (hv : v ∈ S)
    (huv : u ≠ v) : s(u, v) ∈ cliqueEdges S := by
  refine mem_cliqueEdgesV.2 ⟨?_, by simp [Sym2.isDiag_iff_proj_eq, huv]⟩
  intro w hw
  rcases Sym2.mem_iff.1 hw with rfl | rfl
  exacts [hu, hv]

/-! ### The data of the gadget -/

/-- The legs of the apex covering of the six-cycle: the two edges `a i x i` and `a i x (i+1)` of
the covering triangle of the leftover edge `x i x (i+1)`. -/
def hexLegs (x a : Fin 6 → V) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i : Fin 6 => ({s(a i, x i), s(a i, x (i + 1))} : Finset (Sym2 V))

/-- The three patching cross triangles of the octahedron trade. -/
def hexCross (a : Fin 6 → V) : Finset (Finset V) :=
  {({a 0, a 1, a 2} : Finset V), ({a 2, a 3, a 4} : Finset V), ({a 4, a 5, a 0} : Finset V)}

/-- The triangle designated inside each cluster: the cluster `C i` loses
`{x i, a (i-1), a i}`, the cluster `D` loses the chord triangle `{a 0, a 2, a 4}`, and every other
cluster loses nothing. -/
def hexPattern (x a : Fin 6 → V) (C : Fin 6 → Finset V) (D : Finset V) (S : Finset V) : Finset V :=
  if S = D then {a 0, a 2, a 4}
  else if S = C 0 then {x 0, a 5, a 0}
  else if S = C 1 then {x 1, a 0, a 1}
  else if S = C 2 then {x 2, a 1, a 2}
  else if S = C 3 then {x 3, a 2, a 3}
  else if S = C 4 then {x 4, a 3, a 4}
  else if S = C 5 then {x 5, a 4, a 5}
  else ∅

/-- **What the gadget demands of the reservoir.**  Six leftover vertices and six apexes, all
distinct; seven distinct clusters; the cluster `C i` contains `x i` and the two apexes `a (i-1)`,
`a i` of the two leftover edges at `x i`; and the cluster `D` contains the three even apexes. -/
structure HexWebData (𝒞 : Finset (Finset V)) (x a : Fin 6 → V) (C : Fin 6 → Finset V)
    (D : Finset V) : Prop where
  /-- the leftover vertices are distinct -/
  xx : ∀ i j : Fin 6, i ≠ j → x i ≠ x j
  /-- the apexes are distinct -/
  aa : ∀ i j : Fin 6, i ≠ j → a i ≠ a j
  /-- no apex is a leftover vertex -/
  xa : ∀ i j : Fin 6, x i ≠ a j
  /-- the clusters belong to the family -/
  Cmem : ∀ i, C i ∈ 𝒞
  /-- so does the chord cluster -/
  Dmem : D ∈ 𝒞
  /-- the seven clusters are distinct -/
  CC : ∀ i j : Fin 6, i ≠ j → C i ≠ C j
  /-- ... including from the chord cluster -/
  CD : ∀ i, C i ≠ D
  /-- `C i` holds the leftover vertex `x i` -/
  xC : ∀ i, x i ∈ C i
  /-- ... and the apex `a i` of the edge `x i x (i+1)` -/
  aC : ∀ i, a i ∈ C i
  /-- ... and, as `C (i+1)`, the apex `a i` again, seen from `x (i+1)` -/
  aC' : ∀ i, a i ∈ C (i + 1)
  /-- the chord cluster holds the three even apexes -/
  a0D : a 0 ∈ D
  a2D : a 2 ∈ D
  a4D : a 4 ∈ D

namespace HexWebData

variable {𝒞 : Finset (Finset V)} {x a : Fin 6 → V} {C : Fin 6 → Finset V} {D : Finset V}
  {f : Sym2 V → V}

/-! ### Distinctness, in the form simp wants it -/

omit [DecidableEq V] in
theorem eq_xa (hd : HexWebData 𝒞 x a C D) (i j : Fin 6) : (x i = a j) = False :=
  eq_false (hd.xa i j)

omit [DecidableEq V] in
theorem eq_ax (hd : HexWebData 𝒞 x a C D) (i j : Fin 6) : (a i = x j) = False :=
  eq_false fun h => hd.xa j i h.symm

omit [DecidableEq V] in
theorem eq_xx (hd : HexWebData 𝒞 x a C D) (i j : Fin 6) : (x i = x j) = (i = j) := by
  refine propext ⟨fun h => ?_, fun h => by rw [h]⟩
  by_contra hne
  exact hd.xx i j hne h

omit [DecidableEq V] in
theorem eq_aa (hd : HexWebData 𝒞 x a C D) (i j : Fin 6) : (a i = a j) = (i = j) := by
  refine propext ⟨fun h => ?_, fun h => by rw [h]⟩
  by_contra hne
  exact hd.aa i j hne h

/-! ### The designated triangles -/

theorem pattern_D (x a : Fin 6 → V) (C : Fin 6 → Finset V) (D : Finset V) :
    hexPattern x a C D D = ({a 0, a 2, a 4} : Finset V) := by
  simp [hexPattern]

theorem pattern_C0 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 0) = ({x 0, a 5, a 0} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 0), if_pos rfl]

theorem pattern_C1 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 1) = ({x 1, a 0, a 1} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 1), if_neg (hd.CC 1 0 (by decide)), if_pos rfl]

theorem pattern_C2 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 2) = ({x 2, a 1, a 2} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 2), if_neg (hd.CC 2 0 (by decide)),
    if_neg (hd.CC 2 1 (by decide)), if_pos rfl]

theorem pattern_C3 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 3) = ({x 3, a 2, a 3} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 3), if_neg (hd.CC 3 0 (by decide)),
    if_neg (hd.CC 3 1 (by decide)), if_neg (hd.CC 3 2 (by decide)), if_pos rfl]

theorem pattern_C4 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 4) = ({x 4, a 3, a 4} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 4), if_neg (hd.CC 4 0 (by decide)),
    if_neg (hd.CC 4 1 (by decide)), if_neg (hd.CC 4 2 (by decide)),
    if_neg (hd.CC 4 3 (by decide)), if_pos rfl]

theorem pattern_C5 (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D (C 5) = ({x 5, a 4, a 5} : Finset V) := by
  rw [hexPattern, if_neg (hd.CD 5), if_neg (hd.CC 5 0 (by decide)),
    if_neg (hd.CC 5 1 (by decide)), if_neg (hd.CC 5 2 (by decide)),
    if_neg (hd.CC 5 3 (by decide)), if_neg (hd.CC 5 4 (by decide)), if_pos rfl]

theorem pattern_other {S : Finset V} (hSD : S ≠ D)
    (hSC : ∀ i, S ≠ C i) : hexPattern x a C D S = ∅ := by
  rw [hexPattern, if_neg hSD, if_neg (hSC 0), if_neg (hSC 1), if_neg (hSC 2), if_neg (hSC 3),
    if_neg (hSC 4), if_neg (hSC 5)]

/-! ### The legs of the apex covering -/

theorem apexFam_hex (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    apexFam (hexEdges x) f
      = Finset.univ.image (fun i : Fin 6 => ({a i, x i, x (i + 1)} : Finset V)) := by
  rw [apexFam, hexEdges, Finset.image_image]
  refine Finset.image_congr ?_
  intro i _
  simp only [Function.comp_apply]
  rw [hf i, apexTri_eq]

theorem apexCover_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    apexCover (hexEdges x) f
      = Finset.univ.biUnion (fun i : Fin 6 =>
          ({s(a i, x i), s(x i, x (i + 1)), s(a i, x (i + 1))} : Finset (Sym2 V))) := by
  have hne : ∀ i : Fin 6, i ≠ i + 1 := by decide
  rw [apexCover, famEdges, apexFam_hex hf, Finset.image_biUnion]
  refine Finset.biUnion_congr rfl ?_
  intro i _
  have h : ({a i, x i, x (i + 1)} : Finset V) = apexTri s(x i, x (i + 1)) (a i) :=
    (apexTri_eq).symm
  rw [h, cliqueEdges_apexTri (hd.xx i (i + 1) (hne i)) (fun hc => hd.xa i i hc.symm)
    (fun hc => hd.xa (i + 1) i hc.symm)]

theorem apexEdges_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    apexEdges (hexEdges x) f = hexLegs x a := by
  ext g
  simp only [apexEdges, Finset.mem_sdiff, apexCover_hex hd hf, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hexLegs]
  constructor
  · rintro ⟨⟨i, hi⟩, hg⟩
    rcases hi with rfl | rfl | rfl
    · exact ⟨i, Or.inl rfl⟩
    · exact absurd (mem_hexEdges.2 ⟨i, rfl⟩) hg
    · exact ⟨i, Or.inr rfl⟩
  · rintro ⟨i, hi⟩
    have hnot : ∀ (u v : Fin 6), s(a u, x v) ∉ hexEdges x := by
      intro u v hmem
      obtain ⟨j, hj⟩ := mem_hexEdges.1 hmem
      rw [Sym2.eq_iff] at hj
      rcases hj with ⟨h1, _⟩ | ⟨h1, _⟩
      exacts [hd.xa j u h1.symm, hd.xa (j + 1) u h1.symm]
    rcases hi with rfl | rfl
    · exact ⟨⟨i, Or.inl rfl⟩, hnot i i⟩
    · exact ⟨⟨i, Or.inr (Or.inr rfl)⟩, hnot i (i + 1)⟩

/-! ### The edges of the three cross triangles -/

theorem famEdges_hexCross (hd : HexWebData 𝒞 x a C D) :
    famEdges (hexCross a)
      = ({s(a 0, a 1), s(a 1, a 2), s(a 0, a 2), s(a 2, a 3), s(a 3, a 4), s(a 2, a 4),
          s(a 4, a 5), s(a 5, a 0), s(a 4, a 0)} : Finset (Sym2 V)) := by
  have h01 : a 0 ≠ a 1 := hd.aa 0 1 (by decide)
  have h12 : a 1 ≠ a 2 := hd.aa 1 2 (by decide)
  have h02 : a 0 ≠ a 2 := hd.aa 0 2 (by decide)
  have h23 : a 2 ≠ a 3 := hd.aa 2 3 (by decide)
  have h34 : a 3 ≠ a 4 := hd.aa 3 4 (by decide)
  have h24 : a 2 ≠ a 4 := hd.aa 2 4 (by decide)
  have h45 : a 4 ≠ a 5 := hd.aa 4 5 (by decide)
  have h50 : a 5 ≠ a 0 := hd.aa 5 0 (by decide)
  have h40 : a 4 ≠ a 0 := hd.aa 4 0 (by decide)
  rw [hexCross, famEdges]
  rw [Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion,
    cliqueEdgesV_triple h01 h12 h02, cliqueEdgesV_triple h23 h34 h24,
    cliqueEdgesV_triple h45 h50 h40]
  ext e
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]

/-! ### Every consumed edge sits in its cluster's designated triangle -/

theorem pattern_C_succ (hd : HexWebData 𝒞 x a C D) (i : Fin 6) :
    hexPattern x a C D (C (i + 1)) = ({x (i + 1), a i, a (i + 1)} : Finset V) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hd.pattern_C1
  · exact hd.pattern_C2
  · exact hd.pattern_C3
  · exact hd.pattern_C4
  · exact hd.pattern_C5
  · exact hd.pattern_C0

theorem mem_pattern_self (hd : HexWebData 𝒞 x a C D) (i : Fin 6) :
    x i ∈ hexPattern x a C D (C i) ∧ a i ∈ hexPattern x a C D (C i) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hd.pattern_C0]; simp
  · rw [hd.pattern_C1]; simp
  · rw [hd.pattern_C2]; simp
  · rw [hd.pattern_C3]; simp
  · rw [hd.pattern_C4]; simp
  · rw [hd.pattern_C5]; simp

/-- **The home cluster of a consumed edge.**  Every edge the web consumes lies in one cluster of
the family, and there it belongs to that cluster's designated triangle. -/
theorem routed_home (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)
    {g : Sym2 V} (hg : g ∈ routedEdges (hexEdges x) f (hexCross a)) :
    ∃ C₀ ∈ 𝒞, g ∈ cliqueEdges C₀ ∧ g ∈ cliqueEdges (hexPattern x a C D C₀) := by
  rw [routedEdges, apexEdges_hex hd hf, famEdges_hexCross hd, Finset.mem_union] at hg
  rcases hg with hleg | hcross
  · -- a leg
    simp only [hexLegs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hleg
    obtain ⟨i, hi⟩ := hleg
    rcases hi with rfl | rfl
    · refine ⟨C i, hd.Cmem i, ?_, ?_⟩
      · exact mem_cliqueEdges_of_mem_pair (hd.aC i) (hd.xC i) (fun h => hd.xa i i h.symm)
      · exact mem_cliqueEdges_of_mem_pair (hd.mem_pattern_self i).2 (hd.mem_pattern_self i).1
          (fun h => hd.xa i i h.symm)
    · refine ⟨C (i + 1), hd.Cmem _, ?_, ?_⟩
      · exact mem_cliqueEdges_of_mem_pair (hd.aC' i) (hd.xC (i + 1))
          (fun h => hd.xa (i + 1) i h.symm)
      · rw [hd.pattern_C_succ i]
        exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (fun h => hd.xa (i + 1) i h.symm)
  · -- a cross edge
    have hC0 : a 5 ∈ C 0 := by simpa using hd.aC' 5
    have hC1 : a 0 ∈ C 1 := by simpa using hd.aC' 0
    have hC2 : a 1 ∈ C 2 := by simpa using hd.aC' 1
    have hC3 : a 2 ∈ C 3 := by simpa using hd.aC' 2
    have hC4 : a 3 ∈ C 4 := by simpa using hd.aC' 3
    have hC5 : a 4 ∈ C 5 := by simpa using hd.aC' 4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcross
    rcases hcross with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨C 1, hd.Cmem 1, mem_cliqueEdges_of_mem_pair hC1 (hd.aC 1) (hd.aa 0 1 (by decide)),
        by rw [hd.pattern_C1]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 0 1 (by decide))⟩
    · exact ⟨C 2, hd.Cmem 2, mem_cliqueEdges_of_mem_pair hC2 (hd.aC 2) (hd.aa 1 2 (by decide)),
        by rw [hd.pattern_C2]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 1 2 (by decide))⟩
    · exact ⟨D, hd.Dmem, mem_cliqueEdges_of_mem_pair hd.a0D hd.a2D (hd.aa 0 2 (by decide)),
        by rw [pattern_D]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 0 2 (by decide))⟩
    · exact ⟨C 3, hd.Cmem 3, mem_cliqueEdges_of_mem_pair hC3 (hd.aC 3) (hd.aa 2 3 (by decide)),
        by rw [hd.pattern_C3]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 2 3 (by decide))⟩
    · exact ⟨C 4, hd.Cmem 4, mem_cliqueEdges_of_mem_pair hC4 (hd.aC 4) (hd.aa 3 4 (by decide)),
        by rw [hd.pattern_C4]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 3 4 (by decide))⟩
    · exact ⟨D, hd.Dmem, mem_cliqueEdges_of_mem_pair hd.a2D hd.a4D (hd.aa 2 4 (by decide)),
        by rw [pattern_D]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 2 4 (by decide))⟩
    · exact ⟨C 5, hd.Cmem 5, mem_cliqueEdges_of_mem_pair hC5 (hd.aC 5) (hd.aa 4 5 (by decide)),
        by rw [hd.pattern_C5]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 4 5 (by decide))⟩
    · exact ⟨C 0, hd.Cmem 0, mem_cliqueEdges_of_mem_pair hC0 (hd.aC 0) (hd.aa 5 0 (by decide)),
        by rw [hd.pattern_C0]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 5 0 (by decide))⟩
    · exact ⟨D, hd.Dmem, mem_cliqueEdges_of_mem_pair hd.a4D hd.a0D (hd.aa 4 0 (by decide)),
        by rw [pattern_D]
           exact mem_cliqueEdges_of_mem_pair (by simp) (by simp) (hd.aa 4 0 (by decide))⟩

/-! ### The apex assignment -/

theorem isApexAssignment_hex (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) : IsApexAssignment (hexEdges x) f where
  nondiag := by
    intro e he
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    have hne : ∀ k : Fin 6, k ≠ k + 1 := by decide
    simpa [Sym2.isDiag_iff_proj_eq] using hd.xx i (i + 1) (hne i)
  apex_notMem := by
    intro e he
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    rw [hf i]
    simp only [Sym2.mem_iff, not_or]
    exact ⟨fun h => hd.xa i i h.symm, fun h => hd.xa (i + 1) i h.symm⟩
  edge_disjoint := by
    intro e he e' he' hne
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    obtain ⟨j, rfl⟩ := mem_hexEdges.1 he'
    have hij : i ≠ j := fun h => hne (by rw [h])
    clear he he' hne
    have hsucc : ∀ k : Fin 6, k ≠ k + 1 := by decide
    rw [hf i, hf j, cliqueEdges_apexTri (hd.xx i (i + 1) (hsucc i)) (fun hc => hd.xa i i hc.symm)
      (fun hc => hd.xa (i + 1) i hc.symm),
      cliqueEdges_apexTri (hd.xx j (j + 1) (hsucc j)) (fun hc => hd.xa j j hc.symm)
      (fun hc => hd.xa (j + 1) j hc.symm), Finset.disjoint_left]
    intro g hg hg'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg hg'
    rcases hg with rfl | rfl | rfl <;> rcases hg' with h | h | h <;>
      simp only [Sym2.eq_iff, hd.eq_xx, hd.eq_aa, hd.eq_xa, hd.eq_ax, and_false, false_and,
        or_false] at h <;>
      revert h <;> revert hij <;> clear hsucc <;> revert i j <;> decide

/-! ### The consumed edges, and what each cluster gives back -/

theorem routedEdges_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    routedEdges (hexEdges x) f (hexCross a)
      = hexLegs x a ∪ ({s(a 0, a 1), s(a 1, a 2), s(a 0, a 2), s(a 2, a 3), s(a 3, a 4),
          s(a 2, a 4), s(a 4, a 5), s(a 5, a 0), s(a 4, a 0)} : Finset (Sym2 V)) := by
  rw [routedEdges, apexEdges_hex hd hf, famEdges_hexCross hd]

theorem leg_mem₁ (x a : Fin 6 → V) (i : Fin 6) : s(a i, x i) ∈ hexLegs x a := by
  simp only [hexLegs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact ⟨i, Or.inl rfl⟩

theorem leg_mem₂ (x a : Fin 6 → V) (i : Fin 6) : s(a i, x (i + 1)) ∈ hexLegs x a := by
  simp only [hexLegs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact ⟨i, Or.inr rfl⟩

theorem mem_triple₁ (u v w : V) : u ∈ ({u, v, w} : Finset V) := Finset.mem_insert_self _ _

theorem mem_triple₂ (u v w : V) : v ∈ ({u, v, w} : Finset V) :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem mem_triple₃ (u v w : V) : w ∈ ({u, v, w} : Finset V) :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- An edge of one of the three cross triangles is a patch edge. -/
theorem mem_routed_of_cross {u v : V} {T : Finset V} (hT : T ∈ hexCross a) (hu : u ∈ T)
    (hv : v ∈ T) (huv : u ≠ v) :
    s(u, v) ∈ routedEdges (hexEdges x) f (hexCross a) := by
  refine Finset.mem_union_right _ ?_
  rw [famEdges]
  exact Finset.mem_biUnion.2 ⟨T, hT, mem_cliqueEdges_of_mem_pair hu hv huv⟩

/-- A leg is a consumed edge. -/
theorem mem_routed_of_leg (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) {g : Sym2 V} (hg : g ∈ hexLegs x a) :
    g ∈ routedEdges (hexEdges x) f (hexCross a) := by
  refine Finset.mem_union_left _ ?_
  rw [apexEdges_hex hd hf]
  exact hg

/-- A generic check that a designated triple is a triangle inside its cluster whose three edges
are consumed. -/
theorem spec_of_triple (S T : Finset V) (u v w : V) (U : Finset (Sym2 V))
    (hP : T = ({u, v, w} : Finset V)) (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (h1 : s(u, v) ∈ U) (h2 : s(v, w) ∈ U) (h3 : s(u, w) ∈ U) :
    T ⊆ S ∧ T.card = 3 ∧ cliqueEdges T ⊆ U := by
  subst hP
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    exacts [hu, hv, hw]
  · rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
      Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
  · rw [cliqueEdgesV_triple huv hvw huw]
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    exacts [h1, h2, h3]

/-! ### The seven active clusters, one at a time

Each of the seven active clusters is treated in its own lemma, and every argument of
`BKLO.HexWebData.spec_of_triple` is passed explicitly.  Leaving the ambient edge set implicit
makes the elaborator unfold `routedEdges` — a six-element image and a union of cliques over
opaque vertices — which is prohibitively expensive. -/

attribute [local irreducible] routedEdges

section Active

variable (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)

theorem mem_hexCross₀ : ({a 0, a 1, a 2} : Finset V) ∈ hexCross a := Finset.mem_insert_self _ _

theorem mem_hexCross₁ : ({a 2, a 3, a 4} : Finset V) ∈ hexCross a :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem mem_hexCross₂ : ({a 4, a 5, a 0} : Finset V) ∈ hexCross a :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

include hd in
theorem crossR_01 : s(a 0, a 1) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 0, a 1, a 2} : Finset V)) mem_hexCross₀
    (mem_triple₁ (a 0) (a 1) (a 2))
    (mem_triple₂ (a 0) (a 1) (a 2)) (hd.aa 0 1 (by decide))

include hd in
theorem crossR_12 : s(a 1, a 2) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 0, a 1, a 2} : Finset V)) mem_hexCross₀
    (mem_triple₂ (a 0) (a 1) (a 2))
    (mem_triple₃ (a 0) (a 1) (a 2)) (hd.aa 1 2 (by decide))

include hd in
theorem crossR_02 : s(a 0, a 2) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 0, a 1, a 2} : Finset V)) mem_hexCross₀
    (mem_triple₁ (a 0) (a 1) (a 2))
    (mem_triple₃ (a 0) (a 1) (a 2)) (hd.aa 0 2 (by decide))

include hd in
theorem crossR_23 : s(a 2, a 3) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 2, a 3, a 4} : Finset V)) mem_hexCross₁
    (mem_triple₁ (a 2) (a 3) (a 4))
    (mem_triple₂ (a 2) (a 3) (a 4)) (hd.aa 2 3 (by decide))

include hd in
theorem crossR_34 : s(a 3, a 4) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 2, a 3, a 4} : Finset V)) mem_hexCross₁
    (mem_triple₂ (a 2) (a 3) (a 4))
    (mem_triple₃ (a 2) (a 3) (a 4)) (hd.aa 3 4 (by decide))

include hd in
theorem crossR_24 : s(a 2, a 4) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 2, a 3, a 4} : Finset V)) mem_hexCross₁
    (mem_triple₁ (a 2) (a 3) (a 4))
    (mem_triple₃ (a 2) (a 3) (a 4)) (hd.aa 2 4 (by decide))

include hd in
theorem crossR_45 : s(a 4, a 5) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 4, a 5, a 0} : Finset V)) mem_hexCross₂
    (mem_triple₁ (a 4) (a 5) (a 0))
    (mem_triple₂ (a 4) (a 5) (a 0)) (hd.aa 4 5 (by decide))

include hd in
theorem crossR_50 : s(a 5, a 0) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 4, a 5, a 0} : Finset V)) mem_hexCross₂
    (mem_triple₂ (a 4) (a 5) (a 0))
    (mem_triple₃ (a 4) (a 5) (a 0)) (hd.aa 5 0 (by decide))

include hd in
theorem crossR_04 : s(a 0, a 4) ∈ routedEdges (hexEdges x) f (hexCross a) :=
  mem_routed_of_cross (T := ({a 4, a 5, a 0} : Finset V)) mem_hexCross₂
    (mem_triple₃ (a 4) (a 5) (a 0))
    (mem_triple₁ (a 4) (a 5) (a 0)) (hd.aa 0 4 (by decide))

include hd hf in
theorem legR₁ (i : Fin 6) : s(x i, a i) ∈ routedEdges (hexEdges x) f (hexCross a) := by
  rw [Sym2.eq_swap]; exact mem_routed_of_leg hd hf (leg_mem₁ x a i)

include hd hf in
theorem legR₂ (i j : Fin 6) (hij : i + 1 = j) :
    s(x j, a i) ∈ routedEdges (hexEdges x) f (hexCross a) := by
  subst hij
  rw [Sym2.eq_swap]; exact mem_routed_of_leg hd hf (leg_mem₂ x a i)

omit [DecidableEq V] in
theorem aC_prev (hd : HexWebData 𝒞 x a C D) (i j : Fin 6) (hij : i + 1 = j) : a i ∈ C j := by
  subst hij; exact hd.aC' i

set_option maxHeartbeats 1000000 in
theorem spec_D (hd : HexWebData 𝒞 x a C D) :
    hexPattern x a C D D ⊆ D ∧ (hexPattern x a C D D).card = 3 ∧
      cliqueEdges (hexPattern x a C D D) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple D (hexPattern x a C D D) (a 0) (a 2) (a 4)
    (routedEdges (hexEdges x) f (hexCross a))
    (pattern_D x a C D) hd.a0D hd.a2D hd.a4D
    (hd.aa 0 2 (by decide)) (hd.aa 2 4 (by decide)) (hd.aa 0 4 (by decide))
    (crossR_02 (f := f) hd) (crossR_24 (f := f) hd) (crossR_04 (f := f) hd)

set_option maxHeartbeats 1000000 in
theorem spec_C0 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 0) ⊆ C 0 ∧ (hexPattern x a C D (C 0)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 0)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 0) (hexPattern x a C D (C 0)) (x 0) (a 5) (a 0)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C0 (hd.xC 0) (aC_prev hd 5 0 (by decide)) (hd.aC 0)
    (hd.xa 0 5) (hd.aa 5 0 (by decide)) (hd.xa 0 0)
    (legR₂ hd hf 5 0 (by decide)) (crossR_50 (f := f) hd) (legR₁ hd hf 0)

set_option maxHeartbeats 1000000 in
theorem spec_C1 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 1) ⊆ C 1 ∧ (hexPattern x a C D (C 1)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 1)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 1) (hexPattern x a C D (C 1)) (x 1) (a 0) (a 1)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C1 (hd.xC 1) (aC_prev hd 0 1 (by decide)) (hd.aC 1)
    (hd.xa 1 0) (hd.aa 0 1 (by decide)) (hd.xa 1 1)
    (legR₂ hd hf 0 1 (by decide)) (crossR_01 (f := f) hd) (legR₁ hd hf 1)

set_option maxHeartbeats 1000000 in
theorem spec_C2 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 2) ⊆ C 2 ∧ (hexPattern x a C D (C 2)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 2)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 2) (hexPattern x a C D (C 2)) (x 2) (a 1) (a 2)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C2 (hd.xC 2) (aC_prev hd 1 2 (by decide)) (hd.aC 2)
    (hd.xa 2 1) (hd.aa 1 2 (by decide)) (hd.xa 2 2)
    (legR₂ hd hf 1 2 (by decide)) (crossR_12 (f := f) hd) (legR₁ hd hf 2)

set_option maxHeartbeats 1000000 in
theorem spec_C3 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 3) ⊆ C 3 ∧ (hexPattern x a C D (C 3)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 3)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 3) (hexPattern x a C D (C 3)) (x 3) (a 2) (a 3)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C3 (hd.xC 3) (aC_prev hd 2 3 (by decide)) (hd.aC 3)
    (hd.xa 3 2) (hd.aa 2 3 (by decide)) (hd.xa 3 3)
    (legR₂ hd hf 2 3 (by decide)) (crossR_23 (f := f) hd) (legR₁ hd hf 3)

set_option maxHeartbeats 1000000 in
theorem spec_C4 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 4) ⊆ C 4 ∧ (hexPattern x a C D (C 4)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 4)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 4) (hexPattern x a C D (C 4)) (x 4) (a 3) (a 4)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C4 (hd.xC 4) (aC_prev hd 3 4 (by decide)) (hd.aC 4)
    (hd.xa 4 3) (hd.aa 3 4 (by decide)) (hd.xa 4 4)
    (legR₂ hd hf 3 4 (by decide)) (crossR_34 (f := f) hd) (legR₁ hd hf 4)

set_option maxHeartbeats 1000000 in
theorem spec_C5 (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    hexPattern x a C D (C 5) ⊆ C 5 ∧ (hexPattern x a C D (C 5)).card = 3 ∧
      cliqueEdges (hexPattern x a C D (C 5)) ⊆ routedEdges (hexEdges x) f (hexCross a) :=
  spec_of_triple (C 5) (hexPattern x a C D (C 5)) (x 5) (a 4) (a 5)
    (routedEdges (hexEdges x) f (hexCross a))
    hd.pattern_C5 (hd.xC 5) (aC_prev hd 4 5 (by decide)) (hd.aC 5)
    (hd.xa 5 4) (hd.aa 4 5 (by decide)) (hd.xa 5 5)
    (legR₂ hd hf 4 5 (by decide)) (crossR_45 (f := f) hd) (legR₁ hd hf 5)

end Active

/-- **The designated triangle of every cluster is a triangle inside it which the web consumes.**
This packages `tri_sub`, `tri_card` and `le_consumed` of `BKLO.IsTriangleWeb`. -/
theorem pattern_spec (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)
    (S : Finset V) :
    hexPattern x a C D S = ∅ ∨
      (hexPattern x a C D S ⊆ S ∧ (hexPattern x a C D S).card = 3 ∧
        cliqueEdges (hexPattern x a C D S) ⊆ routedEdges (hexEdges x) f (hexCross a)) := by
  by_cases hSD : S = D
  · rw [hSD]; exact Or.inr (spec_D hd)
  by_cases hS0 : S = C 0
  · rw [hS0]; exact Or.inr (spec_C0 hd hf)
  by_cases hS1 : S = C 1
  · rw [hS1]; exact Or.inr (spec_C1 hd hf)
  by_cases hS2 : S = C 2
  · rw [hS2]; exact Or.inr (spec_C2 hd hf)
  by_cases hS3 : S = C 3
  · rw [hS3]; exact Or.inr (spec_C3 hd hf)
  by_cases hS4 : S = C 4
  · rw [hS4]; exact Or.inr (spec_C4 hd hf)
  by_cases hS5 : S = C 5
  · rw [hS5]; exact Or.inr (spec_C5 hd hf)
  refine Or.inl (pattern_other hSD ?_)
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hS0, hS1, hS2, hS3, hS4, hS5]

/-! ### The closed web -/

theorem card_triple {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) :
    ({u, v, w} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
    Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]

theorem routed_sub_famEdges (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    routedEdges (hexEdges x) f (hexCross a) ⊆ famEdges 𝒞 := by
  intro g hg
  obtain ⟨C₀, hC₀, hgc, -⟩ := routed_home hd hf hg
  rw [famEdges]
  exact Finset.mem_biUnion.2 ⟨C₀, hC₀, hgc⟩

theorem cross_sub_routed (t : Finset V) (ht : t ∈ hexCross a) :
    cliqueEdges t ⊆ routedEdges (hexEdges x) f (hexCross a) := by
  intro g hg
  rw [routedEdges]
  refine Finset.mem_union_right _ ?_
  rw [famEdges]
  exact Finset.mem_biUnion.2 ⟨t, ht, hg⟩

/-- Two cliques meeting in at most one vertex have no common edge. -/
theorem disjoint_cliqueEdges_of_inter {t t' : Finset V} {z : V} (h : t ∩ t' ⊆ {z}) :
    Disjoint (cliqueEdges t) (cliqueEdges t') := by
  rw [Finset.disjoint_left]
  intro g hg hg'
  obtain ⟨hgt, hdiag⟩ := mem_cliqueEdgesV.1 hg
  obtain ⟨hgt', -⟩ := mem_cliqueEdgesV.1 hg'
  induction g with
  | _ p q =>
    have hp : p ∈ t ∩ t' := Finset.mem_inter.2 ⟨hgt p (by simp), hgt' p (by simp)⟩
    have hq : q ∈ t ∩ t' := Finset.mem_inter.2 ⟨hgt q (by simp), hgt' q (by simp)⟩
    have hpz : p = z := Finset.mem_singleton.1 (h hp)
    have hqz : q = z := Finset.mem_singleton.1 (h hq)
    exact hdiag (by simp [Sym2.isDiag_iff_proj_eq, hpz, hqz])

/-- The three cross triangles of the trade meet pairwise in a single apex. -/
theorem cross_disj_hex (hd : HexWebData 𝒞 x a C D) :
    ∀ t ∈ hexCross a, ∀ t' ∈ hexCross a, t ≠ t' →
      Disjoint (cliqueEdges t) (cliqueEdges t') := by
  have key : ∀ p q r p' q' r' z : Fin 6,
      ({a p, a q, a r} : Finset V) ∩ ({a p', a q', a r'} : Finset V) ⊆ {a z} →
      Disjoint (cliqueEdges ({a p, a q, a r} : Finset V))
        (cliqueEdges ({a p', a q', a r'} : Finset V)) :=
    fun _ _ _ _ _ _ _ h => disjoint_cliqueEdges_of_inter h
  have sub : ∀ p q r p' q' r' z : Fin 6,
      (∀ i ∈ ({p, q, r} : Finset (Fin 6)), ∀ j ∈ ({p', q', r'} : Finset (Fin 6)),
        i = j → i = z) →
      ({a p, a q, a r} : Finset V) ∩ ({a p', a q', a r'} : Finset V) ⊆ {a z} := by
    intro p q r p' q' r' z hij y hy
    rw [Finset.mem_inter] at hy
    obtain ⟨hy1, hy2⟩ := hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy1 hy2 ⊢
    have step : ∀ i j : Fin 6, i ∈ ({p, q, r} : Finset (Fin 6)) →
        j ∈ ({p', q', r'} : Finset (Fin 6)) → y = a i → y = a j → y = a z := by
      intro i j hi hj h1 h2
      have : i = j := by
        by_contra hne
        exact hd.aa i j hne (h1 ▸ h2 ▸ rfl)
      rw [h1, hij i hi j hj this]
    rcases hy1 with rfl | rfl | rfl <;> rcases hy2 with h | h | h <;>
      exact step _ _ (by simp) (by simp) rfl h
  intro t ht t' ht' hne
  simp only [hexCross, Finset.mem_insert, Finset.mem_singleton] at ht ht'
  rcases ht with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact key 0 1 2 2 3 4 2 (sub 0 1 2 2 3 4 2 (by decide))
  · exact key 0 1 2 4 5 0 0 (sub 0 1 2 4 5 0 0 (by decide))
  · exact key 2 3 4 0 1 2 2 (sub 2 3 4 0 1 2 2 (by decide))
  · exact absurd rfl hne
  · exact key 2 3 4 4 5 0 4 (sub 2 3 4 4 5 0 4 (by decide))
  · exact key 4 5 0 0 1 2 0 (sub 4 5 0 0 1 2 0 (by decide))
  · exact key 4 5 0 2 3 4 4 (sub 4 5 0 2 3 4 4 (by decide))
  · exact absurd rfl hne

/-- The patch edges join two apexes; the legs join an apex to a leftover vertex. -/
theorem cross_legs_hex (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    Disjoint (famEdges (hexCross a)) (apexEdges (hexEdges x) f) := by
  rw [famEdges_hexCross hd, apexEdges_hex hd hf, Finset.disjoint_left]
  intro g hg hg'
  simp only [hexLegs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton] at hg hg'
  obtain ⟨i, hi⟩ := hg'
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hi with h | h <;>
    simp only [Sym2.eq_iff, hd.eq_ax, and_false, false_and, or_false] at h

theorem legs_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    apexEdges (hexEdges x) f ⊆ famEdges 𝒞 := by
  intro g hg
  refine routed_sub_famEdges hd hf ?_
  rw [routedEdges]
  exact Finset.mem_union_left _ hg

theorem cross_card_hex (hd : HexWebData 𝒞 x a C D) : ∀ t ∈ hexCross a, t.card = 3 := by
  intro t ht
  simp only [hexCross, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact card_triple (hd.aa 0 1 (by decide)) (hd.aa 1 2 (by decide)) (hd.aa 0 2 (by decide))
  · exact card_triple (hd.aa 2 3 (by decide)) (hd.aa 3 4 (by decide)) (hd.aa 2 4 (by decide))
  · exact card_triple (hd.aa 4 5 (by decide)) (hd.aa 5 0 (by decide)) (hd.aa 4 0 (by decide))

theorem cross_res_hex (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    ∀ t ∈ hexCross a, cliqueEdges t ⊆ famEdges 𝒞 := fun t ht _ hg =>
  routed_sub_famEdges hd hf (cross_sub_routed (f := f) t ht hg)

theorem tri_sub_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)
    (S : Finset V) : hexPattern x a C D S ⊆ S := by
  rcases pattern_spec (f := f) hd hf S with h | h
  · rw [h]; exact Finset.empty_subset _
  · exact h.1

theorem tri_card_hex (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)
    (S : Finset V) : hexPattern x a C D S = ∅ ∨ (hexPattern x a C D S).card = 3 := by
  rcases pattern_spec (f := f) hd hf S with h | h
  · exact Or.inl h
  · exact Or.inr h.2.1

theorem le_consumed_hex (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) (S : Finset V) :
    cliqueEdges (hexPattern x a C D S) ⊆ routedEdges (hexEdges x) f (hexCross a) := by
  rcases pattern_spec (f := f) hd hf S with h | h
  · rw [h]
    intro g hg
    simp [cliqueEdges] at hg
  · exact h.2.2

theorem consumed_le_hex {E : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    ∀ S ∈ 𝒞, ∀ g ∈ routedEdges (hexEdges x) f (hexCross a), g ∈ cliqueEdges S →
      g ∈ cliqueEdges (hexPattern x a C D S) := by
  intro S hS g hg hgS
  obtain ⟨C₁, hC₁, hg1, hg2⟩ := routed_home hd hf hg
  rw [cluster_unique_of_mem h𝒞 hS hC₁ hgS hg1]
  exact hg2

/-- **The hexagon web closes.**  Under the overlap demand `BKLO.HexWebData`, the apex covering of
the six-cycle together with the three cross triangles of the octahedron trade is a triangle web:
each of the seven active clusters gives back exactly one triangle. -/
theorem isTriangleWeb_hex {E : Finset (Sym2 V)} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hd : HexWebData 𝒞 x a C D) (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i) :
    IsTriangleWeb 𝒞 (hexEdges x) f (hexCross a) (hexPattern x a C D) where
  apex := isApexAssignment_hex hd hf
  legs := legs_hex hd hf
  cross_card := cross_card_hex hd
  cross_res := cross_res_hex hd hf
  cross_disj := cross_disj_hex hd
  cross_legs := cross_legs_hex hd hf
  tri_sub := fun S _ => tri_sub_hex hd hf S
  tri_card := fun S _ => tri_card_hex hd hf S
  consumed_le := consumed_le_hex h𝒞 hd hf
  le_consumed := fun S _ => le_consumed_hex hd hf S

end HexWebData

/-! ### The gadget absorbs the six-cycle -/

section Absorb

variable {𝒞 : Finset (Finset V)} {x a : Fin 6 → V} {C : Fin 6 → Finset V} {D : Finset V}

/-- An apex assignment realizing a prescribed apex for every edge of the six-cycle exists: the six
edges of a hexagon on distinct vertices are distinct. -/
theorem exists_hex_apexFun (hx : ∀ i j : Fin 6, i ≠ j → x i ≠ x j) (a : Fin 6 → V) :
    ∃ f : Sym2 V → V, ∀ i : Fin 6, f s(x i, x (i + 1)) = a i := by
  classical
  refine ⟨fun e => if h : ∃ i : Fin 6, e = s(x i, x (i + 1)) then a h.choose else a 0, ?_⟩
  intro i
  show (if h : ∃ j : Fin 6, s(x i, x (i + 1)) = s(x j, x (j + 1)) then a h.choose else a 0) = a i
  split
  · rename_i h
    exact congrArg a (hexMap_inj hx h.choose_spec).symm
  · rename_i h
    exact absurd ⟨i, rfl⟩ h

/-- **A cluster reservoir carrying the overlap structure absorbs the six-cycle.**  This is the
smallest case in which a triangle web is genuinely needed, and it closes. -/
theorem triDecomp_hex_absorb {E : Finset (Sym2 V)} {f : Sym2 V → V}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : HexWebData 𝒞 x a C D)
    (hf : ∀ i : Fin 6, f s(x i, x (i + 1)) = a i)
    (hdisj : Disjoint (famEdges 𝒞) (hexEdges x)) :
    TriDecomp (famEdges 𝒞 ∪ hexEdges x) :=
  triDecomp_of_crossPatch h𝒞 hdisj
    (isCrossPatch_of_triangleWeb (HexWebData.isTriangleWeb_hex h𝒞 hd hf))

/-! ### The demand isolated

`BKLO.HexWebReservoir` names exactly what is still missing for six-cycle leftovers: a reservoir
that, for every six-cycle it does not already meet, supplies apexes and the seven overlapping
clusters of `BKLO.HexWebData`.  `BKLO.triDecomp_hexagon_of_reservoir` shows that this demand is
*sufficient* — no further routing argument is needed. -/

/-- **What a reservoir still has to supply for six-cycle leftovers.** -/
def HexWebReservoir (𝒞 : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ x : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → x i ≠ x j) → (∀ i, x i ∈ S) →
    Disjoint (famEdges 𝒞) (hexEdges x) →
      ∃ (a : Fin 6 → V) (C : Fin 6 → Finset V) (D : Finset V), HexWebData 𝒞 x a C D

/-- **The demand is sufficient.**  A cluster family meeting `BKLO.HexWebReservoir` absorbs every
six-cycle on `S` that is edge-disjoint from it. -/
theorem triDecomp_hexagon_of_reservoir {E : Finset (Sym2 V)} {S : Finset V}
    {𝒞 : Finset (Finset V)} {x : Fin 6 → V} (h𝒞 : ClusterFamilyIn E 𝒞)
    (hR : HexWebReservoir 𝒞 S) (hx : ∀ i j : Fin 6, i ≠ j → x i ≠ x j) (hxS : ∀ i, x i ∈ S)
    (hdisj : Disjoint (famEdges 𝒞) (hexEdges x)) :
    TriDecomp (famEdges 𝒞 ∪ hexEdges x) := by
  obtain ⟨a, C, D, hd⟩ := hR x hx hxS hdisj
  obtain ⟨f, hf⟩ := exists_hex_apexFun hx a
  exact triDecomp_hex_absorb (f := f) h𝒞 hd hf hdisj


end Absorb


end BKLO
