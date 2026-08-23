/-
# A packing reservoir: the bounded-leftover absorber from a *single* combinatorial statement.

This file records a second — and considerably cleaner — reduction of the bounded-leftover absorber
`BKLO.AbsorberDenseK3BoundedLeftover` (`BKLO/BoundedLeftoverInterface.lean`).

The reservoir is taken to be the edge set of an **edge-disjoint family of triangles** (a triangle
packing) `P` inside the host, `R = famEdges P`.  Such an `R` is automatically

* triangle-decomposable (`TriFamilyIn.triDecomp`), hence of even degrees and with `3 ∣ |R|`;
* contained in the host, and of maximum degree `≤ γ|S|` as soon as no vertex lies in more than
  `γ|S|/2` triangles of `P`.

For such a reservoir the absorbing requirement collapses to a single, purely combinatorial
condition on the *usage pattern*: the part of the reservoir consumed while absorbing the leftover
`H` should be the edge set of a **subfamily** `Q ⊆ P`.  Indeed, what is then left of the reservoir
is `famEdges (P \ Q)` — the edges of the untouched triangles — which is decomposable for free
(`famEdges_sdiff_subfamily`).  No separate "self-repair" hypothesis is needed:

  `TriDecomp (famEdges Q ∪ H)` for some `Q ⊆ P`  ⟹  `TriDecomp (famEdges P ∪ H)`.

The arithmetic works out exactly: `3 ∣ |R|` because `R` is a triangle packing, so the divisibility
hypothesis `3 ∣ |R ∪ H|` of the target forces `3 ∣ |H|`, which is precisely what
`TriDecomp (famEdges Q ∪ H)` needs.

The remaining gap is thus isolated as the single statement `BKLO.PackingReservoirExistence` below,
which replaces the pair `(BoundedLeftoverCoverDown, CoreAbsorberExistence)` of the earlier
reduction — equivalently `ApexReservoirExistence`.  Everything in this file is `sorry`-free.

A concrete way to produce the local decomposition `TriDecomp (famEdges Q ∪ H)` is to cover every
edge of `H` by an apex triangle whose two reserved edges are consumed, and to arrange the consumed
edges to close up into whole reserved triangles: this is `triDecomp_union_of_apexUsage`, and
`BKLO/PackingExample.lean` carries it out explicitly for a `6`-cycle leftover.  That apex form is
strictly more special than the criterion used here — for instance a leftover triangle is covered by
itself, using no reserved edge at all, which no apex assignment can do.
-/
import BKLO.ApexCover
import BKLO.BoundedLeftoverInterface

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Subfamilies of a triangle packing -/

/-- A subfamily of an edge-disjoint triangle family inside `E` is again one. -/
theorem TriFamilyIn.subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (h : TriFamilyIn E P) (hQP : Q ⊆ P) : TriFamilyIn E Q :=
  ⟨fun t ht => h.1 t (hQP ht), fun t ht => h.2.1 t (hQP ht),
    fun t ht t' ht' hne => h.2.2 t (hQP ht) t' (hQP ht') hne⟩

/-- **Removing a subfamily of a packing removes exactly its edges.**  For an edge-disjoint triangle
family `P` and a subfamily `Q ⊆ P`, the edges of `P` not used by `Q` are exactly the edges of the
untouched triangles `P \ Q`. -/
theorem famEdges_sdiff_subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQP : Q ⊆ P) :
    famEdges P \ famEdges Q = famEdges (P \ Q) := by
  classical
  ext e
  simp only [Finset.mem_sdiff, famEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨t, htP, het⟩, hnot⟩
    exact ⟨t, ⟨htP, fun htQ => hnot ⟨t, htQ, het⟩⟩, het⟩
  · rintro ⟨t, ⟨htP, htQ⟩, het⟩
    refine ⟨⟨t, htP, het⟩, ?_⟩
    rintro ⟨t', ht'Q, het'⟩
    have hne : t ≠ t' := by rintro rfl; exact htQ ht'Q
    exact (Finset.disjoint_left.1 (hP.2.2 t htP t' (hQP ht'Q) hne)) het het'

/-- What remains of a packing reservoir after a subfamily has been consumed is
triangle-decomposable. -/
theorem triDecomp_famEdges_sdiff_subfamily {E : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQP : Q ⊆ P) : TriDecomp (famEdges P \ famEdges Q) := by
  rw [famEdges_sdiff_subfamily hP hQP]
  exact (hP.subfamily Finset.sdiff_subset).triDecomp

theorem famEdges_mono {P Q : Finset (Finset V)} (hQP : Q ⊆ P) : famEdges Q ⊆ famEdges P := by
  intro e he
  obtain ⟨t, htQ, het⟩ := Finset.mem_biUnion.1 he
  exact Finset.mem_biUnion.2 ⟨t, hQP htQ, het⟩

/-! ### The absorbing step for a packing reservoir -/

/-- **The absorbing step.**  If some subfamily `Q` of the packing `P` absorbs the leftover `H` —
that is, `famEdges Q ∪ H` is triangle-decomposable — then so does the whole reservoir: the
untouched triangles `P \ Q` decompose the rest. -/
theorem triDecomp_union_of_usage {E H : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    (hP : TriFamilyIn E P) (hQP : Q ⊆ P) (hdisj : Disjoint (famEdges P) H)
    (hcov : TriDecomp (famEdges Q ∪ H)) : TriDecomp (famEdges P ∪ H) := by
  classical
  have hQP' : famEdges Q ⊆ famEdges P := famEdges_mono hQP
  have hsplit : famEdges P ∪ H = (famEdges Q ∪ H) ∪ (famEdges P \ famEdges Q) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hP' | hH)
      · by_cases hQ : e ∈ famEdges Q
        · exact Or.inl (Or.inl hQ)
        · exact Or.inr ⟨hP', hQ⟩
      · exact Or.inl (Or.inr hH)
    · rintro ((hQ | hH) | ⟨hP', _⟩)
      · exact Or.inl (hQP' hQ)
      · exact Or.inr hH
      · exact Or.inl hP'
  have hd : Disjoint (famEdges Q ∪ H) (famEdges P \ famEdges Q) := by
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_sdiff, ?_⟩
    exact Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj.symm
  rw [hsplit]
  exact TriDecomp.union hd hcov (triDecomp_famEdges_sdiff_subfamily hP hQP)

/-- **The apex form of the absorbing step.**  Covering every edge of `H` by an apex triangle whose
reserved edges close up into whole triangles of the packing produces the local decomposition
required by `triDecomp_union_of_usage`. -/
theorem triDecomp_union_of_apexUsage {H : Finset (Sym2 V)} {Q : Finset (Finset V)}
    {f : Sym2 V → V} (hass : IsApexAssignment H f) (hused : apexEdges H f = famEdges Q) :
    TriDecomp (famEdges Q ∪ H) := by
  have h := triDecomp_apexCover hass
  rw [apexCover_eq_union hass.nondiag, hused] at h
  rwa [Finset.union_comm]

/-- The packing version, via an apex assignment. -/
theorem triDecomp_union_of_packing {E H : Finset (Sym2 V)} {P Q : Finset (Finset V)}
    {f : Sym2 V → V} (hP : TriFamilyIn E P) (hQP : Q ⊆ P) (hass : IsApexAssignment H f)
    (hdisj : Disjoint (famEdges P) H) (hused : apexEdges H f = famEdges Q) :
    TriDecomp (famEdges P ∪ H) :=
  triDecomp_union_of_usage hP hQP hdisj (triDecomp_union_of_apexUsage hass hused)

/-! ### Counting: the arithmetic of the criterion -/

/-- The edge set of an edge-disjoint triangle family has `3 |P|` edges. -/
theorem card_famEdges_of_triFamily {E : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hP : TriFamilyIn E P) : (famEdges P).card = 3 * P.card := by
  classical
  rw [famEdges, Finset.card_biUnion hP.2.2]
  rw [Finset.sum_congr rfl (fun t ht => cliqueEdges_card_three (hP.1 t ht))]
  simp [Nat.mul_comm]

/-- An apex assignment covers `3 |H|` edges: the covering triangles are pairwise edge-disjoint and
one per edge of `H`. -/
theorem card_apexCover {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) : (apexCover H f).card = 3 * H.card := by
  classical
  have hinj : Set.InjOn (fun e => apexTri e (f e)) H := by
    intro e he e' he' hEq
    by_contra hne
    have hdis := hass.edge_disjoint e he e' he' hne
    have hmem : e ∈ cliqueEdges (apexTri e (f e)) := mem_cliqueEdges_apexTri (hass.nondiag e he)
    have hEq' : apexTri e (f e) = apexTri e' (f e') := hEq
    have hmem' : e ∈ cliqueEdges (apexTri e' (f e')) := hEq' ▸ hmem
    exact (Finset.disjoint_left.1 hdis) hmem hmem'
  have hdisj : ∀ t ∈ apexFam H f, ∀ t' ∈ apexFam H f, t ≠ t' →
      Disjoint (cliqueEdges t) (cliqueEdges t') := by
    intro t ht t' ht' hne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 ht'
    exact hass.edge_disjoint e he e' he' (fun hc => hne (by rw [hc]))
  have hcards : ∀ t ∈ apexFam H f, (cliqueEdges t).card = 3 := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    exact cliqueEdges_card_three (card_apexTri (hass.nondiag e he) (hass.apex_notMem e he))
  rw [apexCover, famEdges, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcards]
  simp [apexFam, Finset.card_image_of_injOn hinj, Nat.mul_comm]

/-- An apex assignment consumes exactly `2 |H|` reserved edges. -/
theorem card_apexEdges {H : Finset (Sym2 V)} {f : Sym2 V → V}
    (hass : IsApexAssignment H f) : (apexEdges H f).card = 2 * H.card := by
  classical
  have hsub : H ⊆ apexCover H f := subset_apexCover hass.nondiag
  have hc : (apexEdges H f).card = (apexCover H f).card - H.card := by
    rw [apexEdges, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
  rw [hc, card_apexCover hass]
  omega

/-- **Coherence of the apex form.**  If the reserved edges consumed by an apex assignment are
exactly the edges of a triangle family `Q`, then `3 |Q| = 2 |H|`; in particular `3 ∣ |H|`, which is
why the divisibility hypothesis in `PackingReservoirExistence` is exactly the right one. -/
theorem three_dvd_card_of_apexEdges_eq {E H : Finset (Sym2 V)} {Q : Finset (Finset V)}
    {f : Sym2 V → V} (hQ : TriFamilyIn E Q) (hass : IsApexAssignment H f)
    (hused : apexEdges H f = famEdges Q) : 3 * Q.card = 2 * H.card ∧ 3 ∣ H.card := by
  have h : 3 * Q.card = 2 * H.card := by
    rw [← card_famEdges_of_triFamily hQ, ← hused, card_apexEdges hass]
  exact ⟨h, by omega⟩

/-! ### The remaining gap, as a single statement -/

/-- **The packing reservoir (the single remaining gap).**

For every `γ > 0` and every constant `D` there is a threshold beyond which every large dense
triangle-divisible host `E ⊆ cliqueEdges S` contains an edge-disjoint family of triangles `P` whose
edge set has maximum degree at most `γ|S|` and which is *usage-closed* for bounded-degree
leftovers: every even `H ⊆ E \ famEdges P` of maximum degree at most `D` with `3 ∣ |H|` is absorbed
by a subfamily, i.e. `famEdges Q ∪ H` is triangle-decomposable for some `Q ⊆ P`.

This single statement implies the bounded-leftover absorber
(`absorberDenseK3BoundedLeftover_of_packingReservoir`).  It is *not* proved here; it is the precise
content that is still missing.  Two features distinguish it from the earlier reduction
(`ApexReservoirExistence` of `BKLO/CoverDownReduction.lean`): the reservoir is a triangle packing,
so its own decomposability, even degrees and divisibility are automatic; and the "self-repair"
clause disappears, because whatever is not used is a subfamily of the packing. -/
def PackingReservoirExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ D : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S → TriDivisible E →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ P : Finset (Finset V), TriFamilyIn E P ∧
        (∀ v : V, (edeg (famEdges P) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges P → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
          3 ∣ H.card → ∃ Q : Finset (Finset V), Q ⊆ P ∧ TriDecomp (famEdges Q ∪ H)

/-- **The bounded-leftover absorber follows from the packing reservoir.**

Given the packing `P`, the reservoir is `R = famEdges P`: it lies in the host, has even degrees and
maximum degree at most `γ|S|`, and `3 ∣ |R|`, so the divisibility hypothesis `3 ∣ |R ∪ H|` supplies
`3 ∣ |H|`.  The usage-closure clause then produces a subfamily absorbing `H`, and
`triDecomp_union_of_usage` finishes. -/
theorem absorberDenseK3BoundedLeftover_of_packingReservoir
    (h : PackingReservoirExistence) : AbsorberDenseK3BoundedLeftover := by
  classical
  intro γ hγ D
  obtain ⟨n₀, hmain⟩ := h γ hγ D
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES hdiv hdeg
  obtain ⟨P, hP, hPdeg, huse⟩ := hmain E S hn hES hdiv hdeg
  have hPE : famEdges P ⊆ E := famEdges_subset_of_triFamilyIn hP
  have hPdec : TriDecomp (famEdges P) := hP.triDecomp
  refine ⟨famEdges P, hPE, hPdec.triDivisible.1, hPdeg, ?_⟩
  intro H hHsub hHeven hHdeg hdvd
  have hdisj : Disjoint (famEdges P) H :=
    Finset.disjoint_right.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
  have hcard : (famEdges P ∪ H).card = (famEdges P).card + H.card :=
    Finset.card_union_of_disjoint hdisj
  have hdvdH : 3 ∣ H.card := by
    have h3 : 3 ∣ (famEdges P).card := hPdec.triDivisible.2
    rw [hcard] at hdvd
    omega
  obtain ⟨Q, hQP, hcov⟩ := huse H hHsub hHeven hHdeg hdvdH
  exact triDecomp_union_of_usage hP hQP hdisj hcov

end BKLO
