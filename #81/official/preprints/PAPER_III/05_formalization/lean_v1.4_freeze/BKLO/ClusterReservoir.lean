/-
# Cluster reservoirs: `K₇`s carrying a Fano plane, and the reduction of the target to routing.

The reservoir of `BKLO/PackingAbsorb.lean` is a triangle packing.  A *generic* triangle packing is
too rigid: a reserved triangle that loses one edge leaves a residue that nothing local repairs
(`BOUNDED_LEFTOVER_STATUS.md` §8).  This file implements the designed reservoir: an edge-disjoint
family `𝒞` of `7`-sets ("clusters"), each carrying the seven lines of a Steiner triple system
(`BKLO/Fano.lean`).

Three things are gained.

* The reservoir is *still* a triangle packing: the union of the lines of all clusters is an
  edge-disjoint triangle family whose edge set is exactly the union of the clusters
  (`BKLO.ClusterFamilyIn.triFamilyIn_lines`, `BKLO.famEdges_clusterLines`).  So all the
  consequences of `BKLO/PackingAbsorb.lean` apply verbatim, and the reservoir may be given back in
  whole or in part.
* Whatever is consumed inside a cluster, as long as it is a **union of lines**, leaves a residue
  which is again a union of lines and hence triangle-decomposable — fact (b) of `BKLO/Fano.lean`.
  In the subfamily language this is `BKLO.exists_subfamily_of_lineUnion`.
* Because a cluster is a *complete* graph and every triple of a `7`-set is a line of *some*
  Steiner triple system on it (`BKLO.triDecomp_cliqueEdges_sdiff_triangle`), a cluster can absorb
  the loss of **any** triangle of legs, not just of one of its own lines: consume the whole cluster
  and give back a Steiner triple system adapted to what was taken.  This is
  `BKLO.triDecomp_reservoir_of_triangle_legs`, the working form of the mechanism.

What remains is therefore a single statement, `BKLO.ClusterUsageRouting`: a pair-covering cluster
reservoir absorbs every even bounded-degree leftover with `3 ∣ |H|`.  Everything else on this route
is proved: `BKLO.clusterReservoirExistence_holds` (`BKLO/ClusterCompletion.lean`) constructs the
reservoir, and `BKLO.absorberDenseK3BoundedLeftover_of_cluster` derives the target from the two.

`BKLO.ClusterPatternRouting` states the routing in the concrete form in which it should be
attacked — consume, inside every cluster, a pattern the cluster can give back (nothing, a triangle
or a six-cycle) — and `BKLO.clusterUsageRouting_of_patternRouting` shows that this suffices.
Everything in this file is `sorry`-free.
-/
import BKLO.Fano
import BKLO.PackingReservoir

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Cluster families -/

/-- A **cluster family** inside the host `E`: a finite family of `7`-sets whose complete graphs lie
in `E` and are pairwise edge-disjoint.  The reservoir is the union of their edges, `famEdges 𝒞`. -/
def ClusterFamilyIn (E : Finset (Sym2 V)) (𝒞 : Finset (Finset V)) : Prop :=
  (∀ C ∈ 𝒞, C.card = 7) ∧ (∀ C ∈ 𝒞, cliqueEdges C ⊆ E) ∧
    (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint (cliqueEdges C) (cliqueEdges C'))

/-- The triangle packing carried by a cluster family: all lines of all clusters. -/
def clusterLines (ell : Finset V → Finset (Finset V)) (𝒞 : Finset (Finset V)) : Finset (Finset V) :=
  𝒞.biUnion ell

/-- Every `7`-set of the family can be equipped with a Steiner triple system. -/
theorem exists_sts_choice {𝒞 : Finset (Finset V)} (h7 : ∀ C ∈ 𝒞, C.card = 7) :
    ∃ ell : Finset V → Finset (Finset V), (∀ C ∈ 𝒞, IsSTS C (ell C)) ∧
      ∀ C ∈ 𝒞, (ell C).card = 7 := by
  classical
  refine ⟨fun C => if h : C.card = 7 then (exists_isSTS_of_card_seven h).choose else ∅, ?_, ?_⟩
  · intro C hC
    simp only [dif_pos (h7 C hC)]
    exact (exists_isSTS_of_card_seven (h7 C hC)).choose_spec.1
  · intro C hC
    simp only [dif_pos (h7 C hC)]
    exact (exists_isSTS_of_card_seven (h7 C hC)).choose_spec.2

/-- The edges of the lines of all clusters are exactly the edges of the clusters. -/
theorem famEdges_clusterLines {𝒞 : Finset (Finset V)} {ell : Finset V → Finset (Finset V)}
    (hsts : ∀ C ∈ 𝒞, IsSTS C (ell C)) : famEdges (clusterLines ell 𝒞) = famEdges 𝒞 := by
  classical
  rw [clusterLines, famEdges, Finset.biUnion_biUnion]
  refine Finset.biUnion_congr rfl ?_
  intro C hC
  exact (hsts C hC).2.2

/-- A line of a cluster is contained in that cluster, hence its edges lie inside the cluster. -/
theorem cliqueEdges_line_subset {𝒞 : Finset (Finset V)} {ell : Finset V → Finset (Finset V)}
    (hsts : ∀ C ∈ 𝒞, IsSTS C (ell C)) {C : Finset V} (hC : C ∈ 𝒞) {t : Finset V}
    (ht : t ∈ ell C) : cliqueEdges t ⊆ cliqueEdges C := by
  rw [← (hsts C hC).2.2]
  exact Finset.subset_biUnion_of_mem cliqueEdges ht

/-- **A cluster family carries a triangle packing.**  The lines of all clusters form an
edge-disjoint family of triangles inside the host. -/
theorem ClusterFamilyIn.triFamilyIn_lines {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {ell : Finset V → Finset (Finset V)} (h : ClusterFamilyIn E 𝒞)
    (hsts : ∀ C ∈ 𝒞, IsSTS C (ell C)) : TriFamilyIn E (clusterLines ell 𝒞) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨C, hC, htC⟩ := Finset.mem_biUnion.1 ht
    exact (hsts C hC).1 t htC
  · intro t ht
    obtain ⟨C, hC, htC⟩ := Finset.mem_biUnion.1 ht
    exact (cliqueEdges_line_subset hsts hC htC).trans (h.2.1 C hC)
  · intro t ht t' ht' hne
    obtain ⟨C, hC, htC⟩ := Finset.mem_biUnion.1 ht
    obtain ⟨C', hC', htC'⟩ := Finset.mem_biUnion.1 ht'
    by_cases hCC' : C = C'
    · subst hCC'
      exact (hsts C hC).2.1 t htC t' htC' hne
    · exact Finset.disjoint_of_subset_left (cliqueEdges_line_subset hsts hC htC)
        (Finset.disjoint_of_subset_right (cliqueEdges_line_subset hsts hC' htC')
          (h.2.2 C hC C' hC' hCC'))

/-! ### Per-cluster line-unions are subfamilies -/

/-- **Fact (b), globally.**  If the consumed set `U` meets every cluster in a union of that
cluster's lines, then `U` is the edge set of a subfamily of the packing carried by the clusters —
so what is *not* consumed is again a union of lines, hence triangle-decomposable. -/
theorem exists_subfamily_of_lineUnion {𝒞 : Finset (Finset V)}
    {ell : Finset V → Finset (Finset V)} {U : Finset (Sym2 V)} (hU : U ⊆ famEdges 𝒞)
    {lam : Finset V → Finset (Finset V)} (hlam : ∀ C ∈ 𝒞, lam C ⊆ ell C)
    (hused : ∀ C ∈ 𝒞, U ∩ cliqueEdges C = famEdges (lam C)) :
    ∃ Q : Finset (Finset V), Q ⊆ clusterLines ell 𝒞 ∧ famEdges Q = U := by
  classical
  refine ⟨𝒞.biUnion lam, ?_, ?_⟩
  · intro t ht
    obtain ⟨C, hC, htC⟩ := Finset.mem_biUnion.1 ht
    exact Finset.mem_biUnion.2 ⟨C, hC, hlam C hC htC⟩
  · ext e
    constructor
    · intro he
      obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 he
      obtain ⟨C, hC, htC⟩ := Finset.mem_biUnion.1 ht
      have hlamC : e ∈ famEdges (lam C) := Finset.mem_biUnion.2 ⟨t, htC, het⟩
      rw [← hused C hC] at hlamC
      exact (Finset.mem_inter.1 hlamC).1
    · intro he
      obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.1 (hU he)
      have hlamC : e ∈ famEdges (lam C) := by
        rw [← hused C hC]; exact Finset.mem_inter.2 ⟨he, heC⟩
      obtain ⟨t, ht, het⟩ := Finset.mem_biUnion.1 hlamC
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨C, hC, ht⟩, het⟩

/-! ### Giving the reservoir back, cluster by cluster -/

/-- A pairwise edge-disjoint union of triangle-decomposable edge sets is triangle-decomposable. -/
theorem triDecomp_biUnion {ι : Type*} [DecidableEq ι] {s : Finset ι} {F : ι → Finset (Sym2 V)}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (F i) (F j))
    (hdec : ∀ i ∈ s, TriDecomp (F i)) : TriDecomp (s.biUnion F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (triDecomp_empty : TriDecomp (∅ : Finset (Sym2 V)))
  | insert i s hi ih =>
    rw [Finset.biUnion_insert]
    have hdisj' : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (F a) (F b) := fun a ha b hb hab =>
      hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdec' : ∀ a ∈ s, TriDecomp (F a) := fun a ha => hdec a (Finset.mem_insert_of_mem ha)
    refine TriDecomp.union ?_ (hdec i (Finset.mem_insert_self i s)) (ih hdisj' hdec')
    refine Finset.disjoint_left.2 ?_
    intro e he he'
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.1 he'
    exact (Finset.disjoint_left.1 (hdisj i (Finset.mem_insert_self i s)
      j (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj))) he hej

/-- The part of a cluster reservoir left unused splits along the clusters. -/
theorem famEdges_sdiff_eq_biUnion (𝒞 : Finset (Finset V)) (X : Finset (Sym2 V)) :
    famEdges 𝒞 \ X = 𝒞.biUnion (fun C => cliqueEdges C \ X) := by
  classical
  ext e
  simp only [famEdges, Finset.mem_sdiff, Finset.mem_biUnion]
  tauto

/-- **Absorbing with the whole reservoir given back.**  If some set `U` of reserved edges absorbs
the leftover, and every cluster can re-decompose what is left of it, then the *entire* reservoir
together with the leftover is triangle-decomposable.  Nothing has to be a line here: the unused
part of a cluster is re-decomposed from scratch. -/
theorem triDecomp_reservoir_of_clusterwise_residue {E H U : Finset (Sym2 V)}
    {𝒞 : Finset (Finset V)} (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (hU : U ⊆ famEdges 𝒞) (hcov : TriDecomp (U ∪ H))
    (hres : ∀ C ∈ 𝒞, TriDecomp (cliqueEdges C \ U)) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  have hsplit : famEdges 𝒞 ∪ H = (U ∪ H) ∪ (famEdges 𝒞 \ U) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hR | hH)
      · by_cases hUe : e ∈ U
        · exact Or.inl (Or.inl hUe)
        · exact Or.inr ⟨hR, hUe⟩
      · exact Or.inl (Or.inr hH)
    · rintro ((hUe | hH) | ⟨hR, _⟩)
      · exact Or.inl (hU hUe)
      · exact Or.inr hH
      · exact Or.inl hR
  have hd : Disjoint (U ∪ H) (famEdges 𝒞 \ U) := by
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_sdiff, ?_⟩
    exact Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj.symm
  rw [hsplit]
  refine TriDecomp.union hd hcov ?_
  rw [famEdges_sdiff_eq_biUnion]
  refine triDecomp_biUnion (fun C hC C' hC' hne => ?_) hres
  exact Finset.disjoint_of_subset_left Finset.sdiff_subset
    (Finset.disjoint_of_subset_right Finset.sdiff_subset (h𝒞.2.2 C hC C' hC' hne))

/-- **The working form of the mechanism.**  If the reserved edges consumed inside each cluster form
a triangle (or nothing at all), the reservoir absorbs the leftover: a cluster that loses a triangle
gives back a Steiner triple system having that triangle as a line, minus that line.  Note that the
triangle is *arbitrary* — the cluster's own Steiner triple system plays no role, which is exactly
what makes a `K₇` cluster more flexible than a reserved triangle. -/
theorem triDecomp_reservoir_of_triangle_usage {E H U : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H) (hU : U ⊆ famEdges 𝒞)
    (hcov : TriDecomp (U ∪ H))
    (hused : ∀ C ∈ 𝒞, U ∩ cliqueEdges C = ∅ ∨
      ∃ t : Finset V, t ⊆ C ∧ t.card = 3 ∧ U ∩ cliqueEdges C = cliqueEdges t) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  refine triDecomp_reservoir_of_clusterwise_residue h𝒞 hdisj hU hcov ?_
  intro C hC
  have hsplit : cliqueEdges C \ U = cliqueEdges C \ (U ∩ cliqueEdges C) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rcases hused C hC with hempty | ⟨t, htC, ht3, hteq⟩
  · rw [hsplit, hempty]
    simpa using triDecomp_cliqueEdges_of_card_seven (h𝒞.1 C hC)
  · rw [hsplit, hteq]
    exact triDecomp_cliqueEdges_sdiff_triangle (h𝒞.1 C hC) htC ht3

/-- **The apex form.**  Covering every leftover edge by an apex triangle with two reserved legs,
with the legs consumed in each cluster forming a triangle, absorbs the leftover.

Note that an apex assignment for *all* of `H` is not always possible with triangular leg patterns:
a leftover triangle `abc` covered by three apexes contributes six legs forming a six-cycle, which
no grouping into cluster triangles can accommodate (`a`, `b`, `c` cannot share a cluster, since
their edges are not reserved).  The general criterion above therefore has to be used for such
pieces — a leftover triangle is decomposed by itself, consuming nothing. -/
theorem triDecomp_reservoir_of_triangle_legs {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    {f : Sym2 V → V} (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H)
    (hass : IsApexAssignment H f) (hleg : apexEdges H f ⊆ famEdges 𝒞)
    (hlegs : ∀ C ∈ 𝒞, apexEdges H f ∩ cliqueEdges C = ∅ ∨
      ∃ t : Finset V, t ⊆ C ∧ t.card = 3 ∧ apexEdges H f ∩ cliqueEdges C = cliqueEdges t) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  refine triDecomp_reservoir_of_triangle_usage h𝒞 hdisj hleg ?_ hlegs
  have h := triDecomp_apexCover hass
  rwa [apexCover_eq_union hass.nondiag, Finset.union_comm] at h

/-! ### The patterns a cluster can give back -/

/-- The **patterns** a cluster can give back: nothing, a triangle, or a six-cycle.  These are the
consumed sets `F ⊆ cliqueEdges C` for which the unused part `cliqueEdges C \ F` is again
triangle-decomposable and which the routing can realistically produce.  Every pattern is even and
of size divisible by three, as it must be; but not every such set is a pattern — a pair of
vertex-disjoint triangles is not (`BKLO.not_triDecomp_sdiff_twoTriangles7`). -/
def IsClusterPattern (C : Finset V) (F : Finset (Sym2 V)) : Prop :=
  F = ∅ ∨ (∃ t : Finset V, t ⊆ C ∧ t.card = 3 ∧ F = cliqueEdges t) ∨
    ∃ a b c d e f : V, ({a, b, c, d, e, f} : Finset V) ⊆ C ∧
      ({a, b, c, d, e, f} : Finset V).card = 6 ∧
      F = {s(a, b), s(b, c), s(c, d), s(d, e), s(e, f), s(f, a)}

/-- A cluster gives back everything outside a pattern. -/
theorem triDecomp_cliqueEdges_sdiff_pattern {C : Finset V} (hC : C.card = 7)
    {F : Finset (Sym2 V)} (hF : IsClusterPattern C F) : TriDecomp (cliqueEdges C \ F) := by
  rcases hF with rfl | ⟨t, htC, ht3, rfl⟩ | ⟨a, b, c, d, e, f, hsub, hcard, rfl⟩
  · simpa using triDecomp_cliqueEdges_of_card_seven hC
  · exact triDecomp_cliqueEdges_sdiff_triangle hC htC ht3
  · exact triDecomp_cliqueEdges_sdiff_sixCycle hC hsub hcard

/-- **The general criterion.**  If the reserved edges consumed inside every cluster form a pattern
that cluster can give back, the reservoir absorbs the leftover. -/
theorem triDecomp_reservoir_of_pattern_usage {E H U : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hdisj : Disjoint (famEdges 𝒞) H) (hU : U ⊆ famEdges 𝒞)
    (hcov : TriDecomp (U ∪ H)) (hused : ∀ C ∈ 𝒞, IsClusterPattern C (U ∩ cliqueEdges C)) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  refine triDecomp_reservoir_of_clusterwise_residue h𝒞 hdisj hU hcov ?_
  intro C hC
  have hsplit : cliqueEdges C \ U = cliqueEdges C \ (U ∩ cliqueEdges C) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hsplit]
  exact triDecomp_cliqueEdges_sdiff_pattern (h𝒞.1 C hC) (hused C hC)

/-! ### The two statements the target needs -/

/-- **Existence of a sparse pair-covering cluster reservoir.**

For every `γ > 0` and every `K`, every large dense host contains an edge-disjoint family of `K₇`s
whose union has maximum degree at most `γ|S|` and in which every pair of vertices of `S` has at
least `K` common reserved neighbours.  This is proved in `BKLO/ClusterCompletion.lean`
(`BKLO.clusterReservoirExistence_holds`). -/
def ClusterReservoirExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ K : ℕ, ∃ n₀ : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V),
      n₀ ≤ S.card → E ⊆ cliqueEdges S →
      (∀ v ∈ S, (9 / 10 + γ) * (S.card : ℝ) ≤ (edeg E v : ℝ)) →
      ∃ 𝒞 : Finset (Finset V), ClusterFamilyIn E 𝒞 ∧
        (∀ v : V, (edeg (famEdges 𝒞) v : ℝ) ≤ γ * (S.card : ℝ)) ∧
        ∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card

/-- **The routing statement (the single remaining gap).**

For every leftover degree bound `D` there is a covering multiplicity `K` such that every
pair-covering cluster reservoir absorbs every even leftover `H` of maximum degree at most `D` with
`3 ∣ |H|` that is edge-disjoint from it. -/
def ClusterUsageRouting : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (𝒞 : Finset (Finset V)),
      E ⊆ cliqueEdges S → ClusterFamilyIn E 𝒞 →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card → TriDecomp (famEdges 𝒞 ∪ H)

/-- **The routing statement, in the concrete form in which it should be attacked.**

Choose the edges consumed inside the reservoir so that they cover the leftover and meet every
cluster in a pattern the cluster can give back — nothing, a triangle, or a six-cycle.
`BKLO.clusterUsageRouting_of_patternRouting` shows that this suffices.

Two constraints shape what is achievable.  First, covering one leftover edge by an apex triangle
consumes one leg in each of *two* clusters (the two legs of a covering triangle can never lie in
the same cluster, since the leftover edge itself is not reserved), so the `2|H|` legs have to be
grouped into `2|H|/3` patterns of three legs, or `|H|/3` patterns of six — integers exactly because
`3 ∣ |H|`.  Second, the pattern inside a cluster must be *connected*: a pair of vertex-disjoint
triangles is even and of the right size but cannot be given back
(`BKLO.not_triDecomp_sdiff_twoTriangles7`). -/
def ClusterPatternRouting : Prop :=
  ∀ D : ℕ, ∃ K : ℕ,
    ∀ {V : Type} [DecidableEq V] (E : Finset (Sym2 V)) (S : Finset V) (𝒞 : Finset (Finset V)),
      E ⊆ cliqueEdges S → ClusterFamilyIn E 𝒞 →
      (∀ e ∈ cliqueEdges S, K ≤ (apexSet (famEdges 𝒞) S e).card) →
      ∀ H : Finset (Sym2 V), H ⊆ E \ famEdges 𝒞 → EvenDegrees H → (∀ v : V, edeg H v ≤ D) →
        3 ∣ H.card →
        ∃ U : Finset (Sym2 V), U ⊆ famEdges 𝒞 ∧ TriDecomp (U ∪ H) ∧
          ∀ C ∈ 𝒞, IsClusterPattern C (U ∩ cliqueEdges C)

/-- Cluster patterns suffice. -/
theorem clusterUsageRouting_of_patternRouting (h : ClusterPatternRouting) :
    ClusterUsageRouting := by
  intro D
  obtain ⟨K, hK⟩ := h D
  refine ⟨K, ?_⟩
  intro V _ E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  obtain ⟨U, hU, hcovU, hpat⟩ := hK E S 𝒞 hES h𝒞 hcov H hHsub hHeven hHdeg hHdvd
  have hdisj : Disjoint (famEdges 𝒞) H :=
    Finset.disjoint_right.2 fun e he he' => (Finset.mem_sdiff.1 (hHsub he)).2 he'
  exact triDecomp_reservoir_of_pattern_usage h𝒞 hdisj hU hcovU hpat

/-! ### The reduction -/

/-- **The packing reservoir from a cluster reservoir plus routing.**  The lines of the clusters
form the triangle packing, and the routed absorption consumes it in whole. -/
theorem packingReservoirExistence_of_cluster (hex : ClusterReservoirExistence)
    (hroute : ClusterUsageRouting) : PackingReservoirExistence := by
  classical
  intro γ hγ D
  obtain ⟨K, hK⟩ := hroute D
  obtain ⟨n₀, hres⟩ := hex γ hγ K
  refine ⟨n₀, ?_⟩
  intro V _ E S hn hES _ hdeg
  obtain ⟨𝒞, h𝒞, h𝒞deg, h𝒞cov⟩ := hres E S hn hES hdeg
  obtain ⟨ell, hsts, _⟩ := exists_sts_choice h𝒞.1
  have hfam : famEdges (clusterLines ell 𝒞) = famEdges 𝒞 := famEdges_clusterLines hsts
  refine ⟨clusterLines ell 𝒞, h𝒞.triFamilyIn_lines hsts, ?_, ?_⟩
  · intro v; rw [hfam]; exact h𝒞deg v
  · intro H hHsub hHeven hHdeg hHdvd
    rw [hfam] at hHsub
    refine ⟨clusterLines ell 𝒞, Finset.Subset.refl _, ?_⟩
    rw [hfam]
    exact hK E S 𝒞 hES h𝒞 h𝒞cov H hHsub hHeven hHdeg hHdvd

/-- **The bounded-leftover absorber from a cluster reservoir plus routing.** -/
theorem absorberDenseK3BoundedLeftover_of_cluster (hex : ClusterReservoirExistence)
    (hroute : ClusterUsageRouting) : AbsorberDenseK3BoundedLeftover :=
  absorberDenseK3BoundedLeftover_of_packingReservoir
    (packingReservoirExistence_of_cluster hex hroute)

end BKLO
