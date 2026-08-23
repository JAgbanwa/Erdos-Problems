/-
# The cross-patch gadget: a leftover hexagon absorbed with no cluster pairing two legs

`BKLO/CornerLimit.lean`, `BKLO/CornerHexagon.lean` and `BKLO/HexWall.lean` refute the *corner*
mechanism, in which the two legs at a leftover vertex are paired **inside one cluster**.  The
surviving mechanism, isolated in `BKLO/ClusterWeb.lean`, is the **cross-patch** regime: the two
legs at a leftover vertex lie in two *distinct* clusters, each of which repairs its parity defect
with a patch edge belonging to a cross triangle.

Nothing so far showed that this mechanism ever *closes*: the patch edges create new defects in new
clusters, and the question left open was whether the resulting web of trades terminates.  This
file settles that question positively, by exhibiting a complete, closed cross-patch gadget for a
leftover hexagon.

The gadget uses `24` vertices, indexed `0, …, 23`:

* `x i = i`      (`i < 6`) — the six leftover vertices, carrying the hexagon `cxH`;
* `a i = 6 + i`  — the apex of the leftover edge `x i x (i+1)`;
* `w i = 12 + i`, `v i = 18 + i` — the patch vertices.

and `19` clusters, each of which consumes exactly one triangle (`cxClusters`):

* `A i = {x i, a (i-1), w i}` and `B i = {x i, a i, v i}` — the two clusters holding the two legs
  at `x i`.  They are distinct, so **no cluster pairs two legs at a leftover vertex**
  (`cx_cross_regime`): this is the cross-patch regime, not the corner regime.
* `G i = {v (i-1), w i, v i}` — the clusters carrying the patch triangles;
* `P = {v 0, v 2, v 4}` — the single cluster that closes the reserved hexagon `v 0 … v 5`.

The consumed set `cxU` is exactly the union of the nineteen cluster triangles, and `cxU ∪ cxH` is
partitioned by twenty-one triangles (`cxTris`): six apex triangles `x i x (i+1) a i`, six patch
triangles `x i w i v i`, six trade triangles `a i v i w (i+1)`, and three triangles closing the
reserved hexagon against `P`.  All of this is checked by `decide`.

`BKLO.triDecomp_of_crossHexGadget` turns the configuration into the conclusion the routing needs:
if a cluster family contains the nineteen clusters in the prescribed incidence pattern, then
`TriDecomp (famEdges 𝒞 ∪ H)` for the leftover hexagon `H`.  The leftover vertices span no consumed
edge (`cx_leftover_independent`), so the gadget is compatible with an adversarial leftover, whose
vertices span no reserved edge at all.

What the gadget does **not** do is meet the demand for *every* hexagon: its nineteen clusters have
only `24 - 19 = 5` degrees of freedom once the leftover hexagon is prescribed, one short of the six
needed to serve all `n⁶` hexagons.  See `CROSS_PATCH_REPORT.md` for that count and for the
Euler-characteristic identity behind it.

Everything in this file is `sorry`-free.
-/
import BKLO.ClusterReservoir
import BKLO.MapTransport

set_option maxRecDepth 100000

open Finset

namespace BKLO

/-! ### The gadget, at the level of the index set `{0, …, 23}` -/

/-- The nineteen clusters of the gadget, each given by the triangle it consumes. -/
def cxClusters : Finset (Finset ℕ) :=
  {{0, 11, 12}, {1, 6, 13}, {2, 7, 14}, {3, 8, 15}, {4, 9, 16}, {5, 10, 17},
   {0, 6, 18}, {1, 7, 19}, {2, 8, 20}, {3, 9, 21}, {4, 10, 22}, {5, 11, 23},
   {12, 18, 23}, {13, 18, 19}, {14, 19, 20}, {15, 20, 21}, {16, 21, 22}, {17, 22, 23},
   {18, 20, 22}}

/-- The twenty-one triangles decomposing the consumed set together with the leftover hexagon. -/
def cxTris : Finset (Finset ℕ) :=
  {{0, 1, 6}, {1, 2, 7}, {2, 3, 8}, {3, 4, 9}, {4, 5, 10}, {0, 5, 11},
   {0, 12, 18}, {1, 13, 19}, {2, 14, 20}, {3, 15, 21}, {4, 16, 22}, {5, 17, 23},
   {6, 13, 18}, {7, 14, 19}, {8, 15, 20}, {9, 16, 21}, {10, 17, 22}, {11, 12, 23},
   {18, 19, 20}, {20, 21, 22}, {18, 22, 23}}

/-- The leftover hexagon on the six leftover vertices `0, …, 5`. -/
def cxH : Finset (Sym2 ℕ) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(0, 5)}

/-- The consumed set: the nineteen cluster triangles. -/
def cxU : Finset (Sym2 ℕ) := famEdges cxClusters

/-- The twelve legs: the leftover edge `x i x (i+1)` is covered by the apex triangle through
`a i = 6 + i`, whose two reserved edges are the legs at `x i` and at `x (i+1)`. -/
def cxLegs : Finset (Sym2 ℕ) :=
  {s(0, 6), s(1, 7), s(2, 8), s(3, 9), s(4, 10), s(5, 11),
   s(1, 6), s(2, 7), s(3, 8), s(4, 9), s(5, 10), s(0, 11)}

/-! ### The finite checks -/

theorem cx_clusters_card : cxClusters.card = 19 := by decide +kernel

theorem cx_clusters_card3 : ∀ c ∈ cxClusters, c.card = 3 := by decide +kernel

theorem cx_clusters_lt : ∀ c ∈ cxClusters, ∀ i ∈ c, i < 24 := by decide +kernel

/-- Two clusters of the gadget share at most one vertex: the configuration is realisable inside a
family of edge-disjoint `K₇`s. -/
theorem cx_clusters_meet : ∀ c ∈ cxClusters, ∀ c' ∈ cxClusters, c ≠ c' → (c ∩ c').card ≤ 1 := by
  decide +kernel

theorem cx_clusters_disj :
    ∀ c ∈ cxClusters, ∀ c' ∈ cxClusters, c ≠ c' → Disjoint (cliqueEdges c) (cliqueEdges c') := by
  decide +kernel

theorem cx_tris_card3 : ∀ t ∈ cxTris, t.card = 3 := by decide +kernel

theorem cx_tris_disj :
    ∀ t ∈ cxTris, ∀ t' ∈ cxTris, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t') := by decide +kernel

/-- **The gadget closes.**  The twenty-one triangles partition the consumed set together with the
leftover hexagon. -/
theorem cx_tris_famEdges : famEdges cxTris = cxU ∪ cxH := by decide +kernel

theorem cx_U_disj_H : Disjoint cxU cxH := by decide +kernel

theorem cx_supp_lt : ∀ i ∈ supp (cxU ∪ cxH), i < 24 := by decide +kernel

/-- **The cross-patch regime.**  No cluster of the gadget contains two legs at the same leftover
vertex: at each leftover vertex the two legs are consumed by two *distinct* clusters.  This is
exactly the condition the corner mechanism violates. -/
theorem cx_cross_regime :
    ∀ c ∈ cxClusters, ∀ i < 6, ((cxLegs.filter (fun e => i ∈ e)) ∩ cliqueEdges c).card ≤ 1 := by
  decide +kernel

/-- The six leftover vertices span no consumed edge: the gadget never uses a reserved edge between
two leftover vertices, so it is available for a leftover whose vertices span no reserved edge at
all. -/
theorem cx_leftover_independent : ∀ i < 6, ∀ j < 6, s(i, j) ∉ cxU := by decide +kernel

/-- The leftover is a hexagon: six edges, every vertex of even degree. -/
theorem cx_H_card : cxH.card = 6 := by decide +kernel

theorem cx_H_even : ∀ v ∈ supp cxH, Even (edeg cxH v) := by decide +kernel

/-! ### Transport to an arbitrary host -/

variable {V : Type*} [DecidableEq V]

/-- The image of a gadget triangle is a triangle of the host. -/
private theorem cx_image_card {p : ℕ → V} (hp : ∀ u < 24, ∀ v < 24, p u = p v → u = v)
    {c : Finset ℕ} (hc : c ∈ cxClusters) : (c.image p).card = 3 := by
  rw [Finset.card_image_of_injOn, cx_clusters_card3 c hc]
  intro u hu v hv huv
  exact hp u (cx_clusters_lt c hc u hu) v (cx_clusters_lt c hc v hv) huv

private theorem cx_cliqueEdges_image {p : ℕ → V} (hp : ∀ u < 24, ∀ v < 24, p u = p v → u = v)
    {c : Finset ℕ} (hc : c ∈ cxClusters) :
    cliqueEdges (c.image p) = (cliqueEdges c).image (Sym2.map p) := by
  refine cliqueEdges_image_injOn ?_
  intro u hu v hv huv
  exact hp u (cx_clusters_lt c hc u hu) v (cx_clusters_lt c hc v hv) huv

/-- **The cross-patch gadget absorbs a leftover hexagon.**

Let `𝒞` be a cluster family in the host, let `p` place the twenty-four gadget vertices injectively,
and let `Cl` assign to each of the nineteen gadget clusters a cluster of `𝒞` containing its three
vertices, distinct clusters for distinct gadget clusters.  Then the reservoir absorbs the leftover
hexagon carried by the six leftover vertices: `famEdges 𝒞 ∪ H` is triangle-decomposable.

The routing is the one described at the top of the file; in particular no cluster consumes two legs
at a leftover vertex (`cx_cross_regime`), so this is a genuine cross-patch routing, in the regime
left open by the refutation of the corner mechanism. -/
theorem triDecomp_of_crossHexGadget {E H : Finset (Sym2 V)} {𝒞 : Finset (Finset V)}
    (h𝒞 : ClusterFamilyIn E 𝒞) (p : ℕ → V) (hp : ∀ u < 24, ∀ v < 24, p u = p v → u = v)
    (Cl : Finset ℕ → Finset V) (hmem : ∀ c ∈ cxClusters, Cl c ∈ 𝒞)
    (hsub : ∀ c ∈ cxClusters, c.image p ⊆ Cl c)
    (hCl : ∀ c ∈ cxClusters, ∀ c' ∈ cxClusters, c ≠ c' → Cl c ≠ Cl c')
    (hH : H = cxH.image (Sym2.map p)) (hdisj : Disjoint (famEdges 𝒞) H) :
    TriDecomp (famEdges 𝒞 ∪ H) := by
  classical
  set U : Finset (Sym2 V) := cxU.image (Sym2.map p) with hU
  -- every consumed edge lies in the cluster that consumes it
  have hmemU : ∀ e ∈ U, ∃ c ∈ cxClusters, e ∈ cliqueEdges (c.image p) := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨c, hc, hec⟩ := Finset.mem_biUnion.1 he₀
    exact ⟨c, hc, by rw [cx_cliqueEdges_image hp hc]; exact Finset.mem_image_of_mem _ hec⟩
  have hclass : ∀ c ∈ cxClusters, cliqueEdges (c.image p) ⊆ U := by
    intro c hc e he
    rw [cx_cliqueEdges_image hp hc] at he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.2 ⟨c, hc, he₀⟩)
  -- (1) the consumed set is reserved
  have hUsub : U ⊆ famEdges 𝒞 := by
    intro e he
    obtain ⟨c, hc, hec⟩ := hmemU e he
    exact Finset.mem_biUnion.2 ⟨Cl c, hmem c hc, cliqueEdges_mono (hsub c hc) hec⟩
  -- (2) the consumed set together with the leftover is triangle-decomposable
  have hcov : TriDecomp (U ∪ H) := by
    have hD0 : TriDecomp (cxU ∪ cxH) := by
      rw [← cx_tris_famEdges]
      exact ⟨cxTris, cx_tris_card3, cx_tris_disj, rfl⟩
    have hinj : ∀ u ∈ supp (cxU ∪ cxH), ∀ v ∈ supp (cxU ∪ cxH), p u = p v → u = v := by
      intro u hu v hv huv
      exact hp u (cx_supp_lt u hu) v (cx_supp_lt v hv) huv
    have := hD0.mapOn hinj
    rwa [Finset.image_union, ← hU, ← hH] at this
  -- (3) each cluster consumes a pattern it can give back
  have hpat : ∀ C ∈ 𝒞, IsClusterPattern C (U ∩ cliqueEdges C) := by
    intro C hC
    by_cases hex : ∃ c ∈ cxClusters, Cl c = C
    · obtain ⟨c, hc, rfl⟩ := hex
      have heq : U ∩ cliqueEdges (Cl c) = cliqueEdges (c.image p) := by
        apply Finset.Subset.antisymm
        · intro e he
          obtain ⟨heU, heC⟩ := Finset.mem_inter.1 he
          obtain ⟨c', hc', hec'⟩ := hmemU e heU
          by_cases hcc : c' = c
          · exact hcc ▸ hec'
          · exact absurd (Finset.disjoint_left.1
              (h𝒞.2.2 (Cl c') (hmem c' hc') (Cl c) (hmem c hc) (hCl c' hc' c hc hcc))
              (cliqueEdges_mono (hsub c' hc') hec')) (by simpa using heC)
        · intro e he
          exact Finset.mem_inter.2 ⟨hclass c hc he, cliqueEdges_mono (hsub c hc) he⟩
      rw [heq]
      exact Or.inr (Or.inl ⟨c.image p, hsub c hc, cx_image_card hp hc, rfl⟩)
    · push_neg at hex
      have : U ∩ cliqueEdges C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨heU, heC⟩ := Finset.mem_inter.1 he
        obtain ⟨c, hc, hec⟩ := hmemU e heU
        exact Finset.disjoint_left.1
          (h𝒞.2.2 (Cl c) (hmem c hc) C hC (hex c hc)) (cliqueEdges_mono (hsub c hc) hec) heC
      rw [this]
      exact Or.inl rfl
  exact triDecomp_reservoir_of_pattern_usage h𝒞 hdisj hUsub hcov hpat

end BKLO
