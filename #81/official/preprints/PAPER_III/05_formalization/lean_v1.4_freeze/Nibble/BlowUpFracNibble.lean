/-
# Nibble — the blow-up theorem from the **weighted nibble with slack**

`Nibble.AX1.nu3_blowUp_ge_general` (`Nibble.CoreGapBlowUpSelect`) turns an optimal *fractional*
triangle packing of a host `H` into an integral edge-disjoint triangle packing of the blow-up
`H[q]`, but only for `q` beyond a threshold `q₀` that depends on `H`: the proof rounds the
fractional weights to integral multiplicities `⌊w_t q⌋`, and that rounding is useless unless `q` is
large compared with the number of *triangles* of `H`.  For the block-allocation route that is fatal:
there the blow-up factor `q` is the number of blocks per cluster, which the residual caps at
`≈ 1/ε₁`, while the number of clusters — hence the size of the host — is a tower function of `1/ε₁`.

This file removes the dependence of the threshold on the host.  The engine is
`Nibble.fracNibble_withSlack`, the weighted nibble that needs no regularity, only

* `wLoad ≤ 1` — which is *literally* the fractional packing constraint,
* small weighted codegrees — two distinct edges of a graph lie in at most one triangle, so the
  weighted codegree is bounded by the largest weight, and the lifted weights are `≤ 1/q`,
* enough slack — obtained by scaling the packing down by a constant factor.

* `Nibble.AX1.triWt` — the weight a triangle weighting induces on the edge-type triangle
  hypergraph, together with its total, its loads and its codegrees;
* `Nibble.AX1.exists_edgeDisjoint_triangles_blowUp` — **the blow-up theorem with a host-independent
  threshold**: for every `ε > 0` there is a `q₀` such that for *every* host `H` and every `q ≥ q₀`
  the blow-up `H[q]` carries a family of pairwise edge-disjoint triangles of size at least
  `q²·ν₃*(H) − ε·|V(H[q])|²`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlowUpSelect
import Nibble.FracNibbleSlack

open Finset SimpleGraph Hypergraph Nibble.YusterE
open scoped Classical

namespace Nibble.AX1

/-! ### The weight induced on the edge-type triangle hypergraph -/

section TriWt

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The weight that a weighting `f` of the triangles of `G` induces on the edge-type triangle
hypergraph `Nibble.YusterE.triangleHypergraphSub`. -/
noncomputable def triWt (f : Finset V → ℝ) : Finset (EdgeV G) → ℝ :=
  fun T => ∑ t ∈ (G.cliqueFinset 3).filter (fun t => edgeTriple G t = T), f t

theorem triWt_nonneg {f : Finset V → ℝ} (hf : ∀ t, 0 ≤ f t) (T : Finset (EdgeV G)) :
    0 ≤ triWt G f T :=
  Finset.sum_nonneg fun t _ => hf t

/-- The fibre of a hyperedge of the edge-type triangle hypergraph is a single triangle. -/
theorem triWt_of_mem {f : Finset V → ℝ} {t : Finset V} (ht : t ∈ G.cliqueFinset 3) :
    triWt G f (edgeTriple G t) = f t := by
  classical
  have hfib : (G.cliqueFinset 3).filter (fun s => edgeTriple G s = edgeTriple G t) = {t} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hst⟩
      exact edgeTriple_injOn G (by simpa using hs) (by simpa using ht) hst
    · rintro rfl
      exact ⟨ht, rfl⟩
  rw [triWt, hfib, Finset.sum_singleton]

/-- The total induced weight is the total weight. -/
theorem sum_triWt (f : Finset V → ℝ) :
    ∑ T ∈ triangleHypergraphSub G, triWt G f T = ∑ t ∈ G.cliqueFinset 3, f t := by
  classical
  refine Finset.sum_fiberwise_of_maps_to (g := edgeTriple G) (fun t ht => ?_) f
  exact triFam_subset G (Finset.Subset.refl _) (Finset.mem_image_of_mem _ ht)

/-- The induced load of an edge is the total weight of the triangles through it. -/
theorem triWt_load (f : Finset V → ℝ) (E : EdgeV G) :
    ∑ T ∈ (triangleHypergraphSub G).filter (fun T => E ∈ T), triWt G f T
      = ∑ t ∈ (G.cliqueFinset 3).filter (fun t => E.val ⊆ t), f t := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := edgeTriple G) (s := (G.cliqueFinset 3).filter (fun t => E.val ⊆ t))
    (t := (triangleHypergraphSub G).filter (fun T => E ∈ T)) (fun t ht => ?_) f]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [triWt]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext s
    simp only [Finset.mem_filter]
    rw [Finset.mem_filter] at hT
    constructor
    · rintro ⟨hs, hsT⟩
      exact ⟨⟨hs, by rw [← mem_edgeTriple, hsT]; exact hT.2⟩, hsT⟩
    · rintro ⟨⟨hs, -⟩, hsT⟩
      exact ⟨hs, hsT⟩
  · rw [Finset.mem_filter] at ht
    rw [Finset.mem_filter]
    exact ⟨triFam_subset G (Finset.Subset.refl _) (Finset.mem_image_of_mem _ ht.1),
      (mem_edgeTriple G t E).mpr ht.2⟩

/-- The induced weighted codegree of two distinct edges is at most the largest weight: two distinct
edges lie in at most one triangle. -/
theorem triWt_codegree_le {f : Finset V → ℝ} {c : ℝ} (hc : ∀ t, f t ≤ c)
    (hc0 : 0 ≤ c) {E E' : EdgeV G} (hEE' : E ≠ E') :
    ∑ T ∈ (triangleHypergraphSub G).filter (fun T => E ∈ T ∧ E' ∈ T), triWt G f T ≤ c := by
  classical
  have hcard : #((triangleHypergraphSub G).filter (fun T => E ∈ T ∧ E' ∈ T)) ≤ 1 :=
    triangleHypergraphSub_codegree_le_one G hEE'
  have hterm : ∀ T ∈ (triangleHypergraphSub G).filter (fun T => E ∈ T ∧ E' ∈ T),
      triWt G f T ≤ c := by
    intro T hT
    rw [Finset.mem_filter, triangleHypergraphSub, Finset.mem_image] at hT
    obtain ⟨⟨t, ht, rfl⟩, -⟩ := hT
    rw [show ((t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) = edgeTriple G t from rfl,
      triWt_of_mem G ht]
    exact hc t
  rcases Finset.card_le_one.mp hcard with h
  rcases Finset.eq_empty_or_nonempty ((triangleHypergraphSub G).filter
      (fun T => E ∈ T ∧ E' ∈ T)) with he | ⟨T₀, hT₀⟩
  · rw [he, Finset.sum_empty]; exact hc0
  · have hsingle : (triangleHypergraphSub G).filter (fun T => E ∈ T ∧ E' ∈ T) = {T₀} := by
      ext T
      simp only [Finset.mem_singleton]
      exact ⟨fun hT => h T hT T₀ hT₀, fun hT => hT ▸ hT₀⟩
    rw [hsingle, Finset.sum_singleton]
    exact hterm T₀ hT₀

end TriWt

/-! ### The blow-up theorem with a host-independent threshold -/

/-- The final arithmetic of the host-independent blow-up theorem. -/
private theorem blowUpFrac_arith {ε q2 nu val e Wc M : ℝ}
    (hε : 0 < ε) (hq2 : 0 < q2) (hval0 : 0 ≤ val)
    (hval : nu - ε / 8 ≤ val) (hvalnu : val ≤ nu) (hnuW : 3 * nu ≤ Wc)
    (hWc : 1 ≤ Wc) (he : e ≤ q2 * Wc)
    (hone : 1 ≤ ε / 8 * q2)
    (hM : (1 - ε / 8) * ((1 - ε / 8) * (q2 * val)) - ε / 8 * e - 1 ≤ M) :
    q2 * nu - ε * (q2 * Wc) ≤ M := by
  have hb : (0:ℝ) < ε / 8 := by linarith only [hε]
  have hqW : 0 < q2 * Wc := by nlinarith only [hWc, hone, hb]
  -- expand
  have hexp : (1 - ε / 8) * ((1 - ε / 8) * (q2 * val))
      = q2 * val - (ε / 4 - ε ^ 2 / 64) * (q2 * val) := by ring
  have hkey : q2 * nu - q2 * val ≤ q2 * (ε / 8) := by nlinarith only [hq2, hval]
  have hqv0 : 0 ≤ q2 * val := by positivity
  have hlossa : (ε / 4 - ε ^ 2 / 64) * (q2 * val) ≤ ε / 4 * (q2 * val) := by nlinarith only [hqv0, sq_nonneg ε]
  have hvalW : 3 * val ≤ Wc := by linarith only [hvalnu, hnuW]
  have hqval : q2 * val ≤ q2 * Wc / 3 := by nlinarith only [hone, hb, hvalW]
  have hloss : (ε / 4 - ε ^ 2 / 64) * (q2 * val) ≤ ε / 12 * (q2 * Wc) := by nlinarith only [hb, hlossa, hqval]
  have he8 : ε / 8 * e ≤ ε / 8 * (q2 * Wc) := by nlinarith only [hval, hvalnu, he]
  have hqeps : q2 * (ε / 8) ≤ ε / 8 * (q2 * Wc) := by nlinarith
  have h1 : (1:ℝ) ≤ ε / 8 * (q2 * Wc) := by nlinarith
  nlinarith only [hM, hexp, hkey, hloss, he8, hqeps, h1]

set_option maxHeartbeats 1600000 in
/-- **The blow-up theorem with a host-independent threshold.**  For every accuracy `ε` there is a
`q₀`, depending on `ε` alone, such that for *every* host `H` and every `q ≥ q₀` the blow-up `H[q]`
carries a family of pairwise edge-disjoint triangles of size at least
`q²·ν₃*(H) − ε·(q·|V(H)|)²`.

This is `Nibble.AX1.nu3_blowUp_ge_general` with the dependence of the threshold on the host removed;
the engine is the weighted nibble with slack, applied directly to the lifted fractional packing
instead of to a rounded multiplicity system. -/
theorem exists_edgeDisjoint_triangles_blowUp {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, 0 < q₀ ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        (q : ℕ), q₀ ≤ q →
        ∃ S : Finset (Finset (W × Fin q)),
          S ⊆ (blowUp H q).cliqueFinset 3 ∧
          (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → #(t ∩ t') ≤ 1) ∧
          (q : ℝ) ^ 2 * nu3star H - ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 ≤ (#S : ℝ) := by
  classical
  obtain ⟨γ, hγ, hnib⟩ := fracNibble_withSlack (ε / 8) (by linarith)
  refine ⟨⌈1 / γ⌉₊ + ⌈8 / (ε * γ)⌉₊ + ⌈8 / ε⌉₊ + 1, by omega, ?_⟩
  intro W _ _ H _ q hq
  have hq0 : 0 < q := by omega
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq0
  -- the three numerical consequences of `q ≥ q₀`
  have hqγ : 1 / (q:ℝ) ≤ γ := by
    have h1 : (⌈1 / γ⌉₊ : ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : ⌈1 / γ⌉₊ ≤ q)
    have h2 : 1 / γ ≤ (q:ℝ) := le_trans (Nat.le_ceil _) h1
    rw [div_le_iff₀ hqR]
    rw [div_le_iff₀ hγ] at h2
    linarith
  have hqslack : 1 / γ ≤ ε / 8 * (q:ℝ) ^ 2 := by
    have h1 : (⌈8 / (ε * γ)⌉₊ : ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : ⌈8 / (ε * γ)⌉₊ ≤ q)
    have h2 : 8 / (ε * γ) ≤ (q:ℝ) := le_trans (Nat.le_ceil _) h1
    have hεγ : 0 < ε * γ := by positivity
    rw [div_le_iff₀ hεγ] at h2
    have hq2 : (q:ℝ) ≤ (q:ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ hγ]
    nlinarith
  have hone : (1:ℝ) ≤ ε / 8 * (q:ℝ) ^ 2 := by
    have h1 : (⌈8 / ε⌉₊ : ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : ⌈8 / ε⌉₊ ≤ q)
    have h2 : 8 / ε ≤ (q:ℝ) := le_trans (Nat.le_ceil _) h1
    rw [div_le_iff₀ hε] at h2
    have hq2 : (q:ℝ) ≤ (q:ℝ) ^ 2 := by nlinarith
    nlinarith
  by_cases hex : ∃ a b : W, H.Adj a b
  · obtain ⟨a, b, hab⟩ := hex
    have hWpos : (1:ℝ) ≤ (Fintype.card W : ℝ) := by
      have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨a⟩
      exact_mod_cast this
    -- a nearly optimal fractional packing of the host
    have hSne : ({x : ℝ | ∃ w, IsFracPacking H w ∧
        x = ∑ T ∈ triangleHypergraphE H, w T}).Nonempty := by
      refine ⟨0, ⟨fun _ => 0, ?_, by simp⟩⟩
      exact ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩
    have hlt : nu3star H - ε / 8 < sSup {x : ℝ | ∃ w, IsFracPacking H w ∧
        x = ∑ T ∈ triangleHypergraphE H, w T} := by
      have : nu3star H = sSup {x : ℝ | ∃ w, IsFracPacking H w ∧
          x = ∑ T ∈ triangleHypergraphE H, w T} := rfl
      rw [← this]; linarith
    obtain ⟨x, hxmem, hxlt⟩ := exists_lt_of_lt_csSup hSne hlt
    obtain ⟨wH, hwH, rfl⟩ := hxmem
    set val : ℝ := ∑ T ∈ triangleHypergraphE H, wH T with hvaldef
    have hval0 : 0 ≤ val := Finset.sum_nonneg fun T _ => hwH.1 T
    have hvalnu : val ≤ nu3star H :=
      le_csSup (nu3star_bddAbove H) ⟨wH, hwH, rfl⟩
    -- the weighting of the triangles of the blow-up
    set B : SimpleGraph (W × Fin q) := blowUp H q with hB
    set f : Finset (W × Fin q) → ℝ :=
      fun t => (1 - ε / 8) * liftWeight H q wH (t.powersetCard 2) with hf
    have hlift := isFracPacking_liftWeight H hq0 hwH
    -- we may assume `ε ≤ 1`: otherwise the statement is trivial
    rcases le_or_gt ε 1 with hεle | hεgt
    · have h18 : (0:ℝ) < 1 - ε / 8 := by linarith
      have hfnn : ∀ t, 0 ≤ f t := fun t => mul_nonneg (by linarith) (hlift.1 _)
      have hfle : ∀ t, f t ≤ 1 / (q:ℝ) := by
        intro t
        have hle : liftWeight H q wH (t.powersetCard 2) ≤ 1 / (q:ℝ) := by
          rw [liftWeight]
          split_ifs with hmem
          · rw [div_le_div_iff_of_pos_right hqR]
            -- a fractional packing puts weight at most `1` on a single triangle
            set e2 := (((vtxSet (t.powersetCard 2)).image Prod.fst).powersetCard 2) with he2
            by_cases hmem2 : e2 ∈ triangleHypergraphE H
            · rw [triangleHypergraphE, Finset.mem_image] at hmem2
              obtain ⟨s, hs, hse⟩ := hmem2
              have hscl := SimpleGraph.mem_cliqueFinset_iff.mp hs
              obtain ⟨e, he⟩ : (s.powersetCard 2).Nonempty := by
                rw [← Finset.card_pos, Finset.card_powersetCard, hscl.card_eq]; decide
              have hsum := hwH.2.2 e
              have hmemf : s.powersetCard 2 ∈ (triangleHypergraphE H).filter (fun T => e ∈ T) := by
                rw [Finset.mem_filter]
                exact ⟨Finset.mem_image_of_mem _ hs, he⟩
              have hsingle := Finset.single_le_sum
                (f := wH) (fun T _ => hwH.1 T) hmemf
              rw [← hse]
              linarith
            · rw [hwH.2.1 _ hmem2]; norm_num
          · positivity
        calc f t = (1 - ε / 8) * liftWeight H q wH (t.powersetCard 2) := rfl
          _ ≤ 1 * (1 / (q:ℝ)) := by
              apply mul_le_mul (by linarith) hle (hlift.1 _) zero_le_one
          _ = 1 / (q:ℝ) := by ring
      -- the hypergraph and its weighting
      set K : Finset (Finset (EdgeV B)) := triangleHypergraphSub B with hK
      set w : Finset (EdgeV B) → ℝ := triWt B f with hw
      have hunif : IsUniform K 3 := triangleHypergraphSub_uniform B
      have hwnn : ∀ T, 0 ≤ w T := fun T => triWt_nonneg B hfnn T
      -- the loads
      have hloadle : ∀ E : EdgeV B, Slack.wLoad K w E ≤ 1 - ε / 8 := by
        intro E
        rw [Slack.wLoad, hw, hK, triWt_load B f E]
        obtain ⟨hcl, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp E.2
        have hsum : ∑ t ∈ (B.cliqueFinset 3).filter (fun t => E.val ⊆ t), f t
            = (1 - ε / 8) * ∑ T ∈ (triangleHypergraphE B).filter (fun T => E.val ∈ T),
                liftWeight H q wH T := by
          rw [sum_triangleHypergraphE_filter B hcard (liftWeight H q wH), Finset.mul_sum]
        rw [hsum]
        have hle := hlift.2.2 E.val
        nlinarith [hle]
      have hload1 : ∀ E : EdgeV B, Slack.wLoad K w E ≤ 1 := by
        intro E; have := hloadle E; linarith
      -- the codegrees
      have hcod : ∀ E E' : EdgeV B, E ≠ E' →
          ∑ T ∈ K.filter (fun T => E ∈ T ∧ E' ∈ T), w T ≤ γ := by
        intro E E' hEE'
        exact triWt_codegree_le B (fun t => le_trans (hfle t) hqγ) hγ.le hEE'
      -- the number of vertices of the hypergraph
      have hcardX : (Fintype.card (EdgeV B) : ℝ) = (#(B.cliqueFinset 2) : ℝ) := by
        exact_mod_cast card_EdgeV B
      have hXge : ((q:ℝ)) ^ 2 ≤ (Fintype.card (EdgeV B) : ℝ) := by
        rw [hcardX]
        have := card_edges_blowUp_ge H q hab
        have h2 : ((q ^ 2 : ℕ) : ℝ) ≤ (#((blowUp H q).cliqueFinset 2) : ℝ) := by exact_mod_cast this
        push_cast at h2
        exact h2
      have hXle : (Fintype.card (EdgeV B) : ℝ) ≤ (q:ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2 := by
        rw [hcardX]
        have hcard : (Fintype.card (W × Fin q) : ℝ) = (q : ℝ) * (Fintype.card W : ℝ) := by
          simp [Fintype.card_prod]; ring
        have hle := edge_card_le_card_sq B
        rw [hcard] at hle
        calc (#(B.cliqueFinset 2) : ℝ) ≤ ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := hle
          _ = (q : ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2 := by ring
      -- the slack
      have hslack : 1 / γ ≤ (Fintype.card (EdgeV B) : ℝ) - ∑ E : EdgeV B, Slack.wLoad K w E := by
        have hsum : ∑ E : EdgeV B, Slack.wLoad K w E
            ≤ (Fintype.card (EdgeV B) : ℝ) * (1 - ε / 8) := by
          calc ∑ E : EdgeV B, Slack.wLoad K w E ≤ ∑ _E : EdgeV B, (1 - ε / 8) :=
              Finset.sum_le_sum (fun E _ => hloadle E)
            _ = (Fintype.card (EdgeV B) : ℝ) * (1 - ε / 8) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : ε / 8 * (q:ℝ) ^ 2 ≤ ε / 8 * (Fintype.card (EdgeV B) : ℝ) := by nlinarith
        linarith
      -- the total weight
      have htot : ∑ T ∈ K, w T = (1 - ε / 8) * ((q:ℝ) ^ 2 * val) := by
        rw [hw, hK, sum_triWt B f, hf]
        rw [← Finset.mul_sum]
        rw [← sum_triangleHypergraphE B (liftWeight H q wH), sum_liftWeight H hq0 wH]
      -- the nibble
      obtain ⟨M, hM, hMcard⟩ := hnib K w hunif hwnn hload1 hcod hslack
      -- back to a family of triangles
      refine ⟨(B.cliqueFinset 3).filter (fun t => edgeTriple B t ∈ M), Finset.filter_subset _ _,
        ?_, ?_⟩
      · intro t ht t' ht' hne
        rw [Finset.mem_filter] at ht ht'
        by_contra hcon
        push_neg at hcon
        obtain ⟨e, hesub, hecard⟩ := Finset.exists_subset_card_eq (by omega : 2 ≤ #(t ∩ t'))
        have hetcl : B.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht.1
        have hedge : e ∈ B.cliqueFinset 2 := by
          rw [SimpleGraph.mem_cliqueFinset_iff]
          exact ⟨hetcl.isClique.subset (fun x hx =>
            Finset.mem_of_mem_inter_left (hesub hx)), hecard⟩
        have hne' : edgeTriple B t ≠ edgeTriple B t' := by
          intro h
          exact hne (edgeTriple_injOn B (by simpa using ht.1) (by simpa using ht'.1) h)
        have hdisj := hM.disjoint _ ht.2 _ ht'.2 hne'
        have hmem1 : (⟨e, hedge⟩ : EdgeV B) ∈ edgeTriple B t :=
          (mem_edgeTriple B t _).mpr (fun x hx => Finset.mem_of_mem_inter_left (hesub hx))
        have hmem2 : (⟨e, hedge⟩ : EdgeV B) ∈ edgeTriple B t' :=
          (mem_edgeTriple B t' _).mpr (fun x hx => Finset.mem_of_mem_inter_right (hesub hx))
        exact (Finset.disjoint_left.mp hdisj hmem1) hmem2
      · -- the size
        have hcardS : (#((B.cliqueFinset 3).filter (fun t => edgeTriple B t ∈ M)) : ℝ)
            = (#M : ℝ) := by
          congr 1
          refine Finset.card_bij (fun t _ => edgeTriple B t) (fun t ht => (Finset.mem_filter.mp ht).2)
            (fun t ht t' ht' h => edgeTriple_injOn B
              (by simpa using (Finset.mem_filter.mp ht).1)
              (by simpa using (Finset.mem_filter.mp ht').1) h) ?_
          intro T hT
          have hTsub := hM.subset hT
          rw [hK, triangleHypergraphSub, Finset.mem_image] at hTsub
          obtain ⟨t, ht, rfl⟩ := hTsub
          exact ⟨t, Finset.mem_filter.mpr ⟨ht, hT⟩, rfl⟩
        rw [hcardS]
        have hnuW : 3 * nu3star H ≤ (Fintype.card W : ℝ) ^ 2 := by
          have h1 := nu3star_le H
          have h2 := edge_card_le_card_sq H
          linarith
        have hWc : (1:ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by nlinarith
        have hq2pos : (0:ℝ) < (q:ℝ) ^ 2 := by positivity
        have hMcard' : (1 - ε / 8) * ((1 - ε / 8) * ((q:ℝ) ^ 2 * val))
            - ε / 8 * (Fintype.card (EdgeV B) : ℝ) - 1 ≤ (#M : ℝ) := by
          rw [htot] at hMcard
          linarith
        have hgoal := blowUpFrac_arith (ε := ε) (q2 := (q:ℝ) ^ 2) (nu := nu3star H)
          (val := val) (e := (Fintype.card (EdgeV B) : ℝ)) (Wc := (Fintype.card W : ℝ) ^ 2)
          (M := (#M : ℝ)) hε hq2pos hval0 (by linarith) hvalnu hnuW hWc
          hXle hone hMcard'
        calc (q:ℝ) ^ 2 * nu3star H - ε * ((q:ℝ) * (Fintype.card W : ℝ)) ^ 2
            = (q:ℝ) ^ 2 * nu3star H - ε * ((q:ℝ) ^ 2 * (Fintype.card W : ℝ) ^ 2) := by ring
          _ ≤ (#M : ℝ) := hgoal
    · -- `ε > 1`: the empty family already works
      refine ⟨∅, by simp, by simp, ?_⟩
      have h1 := nu3star_le H
      have h2 := edge_card_le_card_sq H
      have h3 : nu3star H ≤ (Fintype.card W : ℝ) ^ 2 := by linarith
      have h4 : (0:ℝ) ≤ nu3star H := by
        have : (0:ℝ) ∈ {x : ℝ | ∃ w, IsFracPacking H w ∧ x = ∑ T ∈ triangleHypergraphE H, w T} :=
          ⟨fun _ => 0, ⟨fun _ => le_rfl, fun _ _ => rfl, fun e => by simp⟩, by simp⟩
        exact le_csSup (nu3star_bddAbove H) this
      have hWpos2 : (0:ℝ) ≤ (Fintype.card W : ℝ) := Nat.cast_nonneg _
      simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith [sq_nonneg ((q:ℝ) * (Fintype.card W : ℝ))]
  · -- no edges at all
    push_neg at hex
    refine ⟨∅, by simp, by simp, ?_⟩
    have hempty : H.cliqueFinset 2 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      obtain ⟨hcl, hcard⟩ := SimpleGraph.mem_cliqueFinset_iff.mp hs
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
      exact hex u v (hcl (by simp) (by simp) huv)
    have hstar : nu3star H ≤ 0 := by
      have := nu3star_le H
      rw [hempty] at this
      simpa using this
    have h1 : (q : ℝ) ^ 2 * nu3star H ≤ 0 := by nlinarith [sq_nonneg ((q : ℝ))]
    have h2 : (0 : ℝ) ≤ ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := by positivity
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.exists_edgeDisjoint_triangles_blowUp

end AxCheck

end Nibble.AX1
