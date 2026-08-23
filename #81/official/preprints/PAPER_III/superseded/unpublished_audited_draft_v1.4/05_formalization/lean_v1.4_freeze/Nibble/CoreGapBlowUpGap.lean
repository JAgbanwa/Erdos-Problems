/-
# Nibble — the **blow-up gap theorem** `ν₃(H[q]) ≥ q²·ν₃*(H) − ε·|V(H[q])|²`

STEP 2 of the Yuster blow-up route.  `Nibble.CoreGapBlowUp` proved the LP identity
`ν₃*(H[q]) = q²·ν₃*(H)`.  Here the *integral* packing number of the blow-up is brought within
`ε·|V(H[q])|²` of it, by feeding the blow-up to the proved regular nibble
(`Nibble.nibbleTheorem_holds`).

The point of the blow-up is that it makes the nibble *applicable*: the nibble needs the triangle
hypergraph of the host graph to be nearly `d`-regular with `d` above an absolute threshold `d₀` and
codegree `≤ μ·d`.  In the `q`-blow-up every edge sits in exactly `q` times as many triangles as the
edge below it (`Nibble.AX1.degree_blowUp_edge`), so

* near-regularity of `H`'s triangle hypergraph transfers verbatim, at scale `q·d`
  (`Nibble.AX1.nearlyRegular_blowUp`), and
* the codegree bound `μ·(q·d) ≥ 1` — the triangle hypergraph has codegree `≤ 1` — becomes free once
  `q` is large.

So a *fixed* near-regular `H`, however small, is pushed into the nibble's asymptotic range by
blowing it up.

* `Nibble.AX1.nu3_ge_nibble_uniform` — the nibble lower bound `ν₃ ≥ (1-β)|E|/3` with the tolerance
  `μ` and the scale `d₀` chosen *before* the graph (the graph-uniform repackaging of
  `Nibble.YusterE.nu3_ge_nibble`, needed because here the graph `H[q]` depends on `q`).
* `Nibble.AX1.nu3_blowUp_ge` — the blow-up gap theorem.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.CoreGapBlowUp
import Nibble.TightNibble
import Nibble.YusterSubBridge
import Nibble.YusterSubDegreeChar
import Nibble.YusterSubRegular
import Nibble.YusterFracUpper

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### The nibble lower bound, with the tolerance chosen before the graph -/

/-- **Graph-uniform nibble lower bound.** `Nibble.YusterE.nu3_ge_nibble` fixes the graph before
producing the tolerance `μ` and the scale `d₀`; the blow-up route needs them the other way round,
since the graph `H[q]` it applies them to depends on `q` (and `q` has to be chosen large enough to
reach the scale `d₀`).  The underlying nibble `Nibble.nibbleTheorem_holds` is already uniform in the
vertex type, so this is a repackaging. -/
theorem nu3_ge_nibble_uniform {β : ℝ} (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ},
        0 < d → d₀ ≤ d → NearlyRegular (triangleHypergraphSub G) d μ →
          CodegreeBounded (triangleHypergraphSub G) (μ * d) →
          (1 - β) * (((G.cliqueFinset 2).card : ℝ) / 3) ≤ (nu3 G : ℝ) := by
  classical
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nibbleTheorem_holds 3 (by norm_num) β hβ
  refine ⟨μ, hμ, d₀, hd₀, ?_⟩
  intro V _ _ G _ d hd hd0 hReg hCod
  obtain ⟨M, hM, hcard⟩ :=
    hmain (triangleHypergraphSub G) d hd hd0 (triangleHypergraphSub_uniform G) hReg hCod
  rw [card_EdgeV] at hcard
  exact le_trans hcard (by exact_mod_cast sub_matching_card_le_nu3 G hM)

/-! ### Triangle degrees in the blow-up -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The common neighbourhood of a blow-up edge is the `q`-fold cover of the common neighbourhood of
the edge below it. -/
theorem card_commonNbr_blowUp (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ}
    {x y : W × Fin q} (hxy : H.Adj x.1 y.1) :
    #(univ.filter (fun z : W × Fin q =>
        z ∉ ({x, y} : Finset (W × Fin q)) ∧ (blowUp H q).IsNClique 3 (insert z {x, y})))
      = q * #(univ.filter (fun c : W =>
        c ∉ ({x.1, y.1} : Finset W) ∧ H.IsNClique 3 (insert c {x.1, y.1}))) := by
  classical
  have hne : x.1 ≠ y.1 := hxy.ne
  have hiff : ∀ z : W × Fin q,
      (z ∉ ({x, y} : Finset (W × Fin q)) ∧ (blowUp H q).IsNClique 3 (insert z {x, y}))
        ↔ (z.1 ∉ ({x.1, y.1} : Finset W) ∧ H.IsNClique 3 (insert z.1 {x.1, y.1})) := by
    intro z
    constructor
    · rintro ⟨hz, hcl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      rw [Finset.insert_eq, ← Finset.insert_eq] at hcl
      have hzx : (blowUp H q).Adj z x := hcl.1 (by simp) (by simp) hz.1
      have hzy : (blowUp H q).Adj z y := hcl.1 (by simp) (by simp) hz.2
      rw [blowUp_adj] at hzx hzy
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hzx.ne, hzy.ne⟩
      · rw [Finset.insert_eq, ← Finset.insert_eq]
        exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hzx, hzy, hxy⟩
    · rintro ⟨hz, hcl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      rw [Finset.insert_eq, ← Finset.insert_eq] at hcl
      obtain ⟨hzx, hzy, -⟩ := SimpleGraph.is3Clique_triple_iff.mp hcl
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hz.1 (by rw [h]), fun h => hz.2 (by rw [h])⟩
      · rw [Finset.insert_eq, ← Finset.insert_eq]
        exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hzx, hzy, hxy⟩
  have hset : (univ.filter (fun z : W × Fin q =>
        z ∉ ({x, y} : Finset (W × Fin q)) ∧ (blowUp H q).IsNClique 3 (insert z {x, y})))
      = (univ.filter (fun c : W =>
        c ∉ ({x.1, y.1} : Finset W) ∧ H.IsNClique 3 (insert c {x.1, y.1}))) ×ˢ univ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, hiff z]
    tauto
  rw [hset, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Triangle degrees scale by `q`.** An edge of the blow-up lies in exactly `q` times as many
triangles as the edge of `H` below it. -/
theorem degree_blowUp_edge (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ}
    (E' : EdgeV (blowUp H q)) :
    ∃ E : EdgeV H, degree (triangleHypergraphSub (blowUp H q)) E'
      = q * degree (triangleHypergraphSub H) E := by
  classical
  obtain ⟨e', he'⟩ := E'
  rw [SimpleGraph.mem_cliqueFinset_iff] at he'
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he'.card_eq
  have hadj : H.Adj x.1 y.1 := by
    have := he'.1 (by simp : x ∈ ({x, y} : Finset (W × Fin q)))
      (by simp : y ∈ ({x, y} : Finset (W × Fin q))) hxy
    rwa [blowUp_adj] at this
  have hE : H.IsNClique 2 ({x.1, y.1} : Finset W) := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all [hadj.symm]
    · rw [Finset.card_insert_of_notMem (by simp [hadj.ne]), Finset.card_singleton]
  refine ⟨⟨{x.1, y.1}, SimpleGraph.mem_cliqueFinset_iff.mpr hE⟩, ?_⟩
  rw [triangleHypergraphSub_degree_eq_commonNbr, triangleHypergraphSub_degree_eq_commonNbr]
  exact card_commonNbr_blowUp H hadj

/-- **Near-regularity transfers to the blow-up**, at scale `q·d`. -/
theorem nearlyRegular_blowUp (H : SimpleGraph W) [DecidableRel H.Adj] {q : ℕ} {d μ : ℝ}
    (hreg : NearlyRegular (triangleHypergraphSub H) d μ) :
    NearlyRegular (triangleHypergraphSub (blowUp H q)) ((q : ℝ) * d) μ := by
  intro E'
  obtain ⟨E, hEeq⟩ := degree_blowUp_edge H E'
  have h1 := hreg E
  rw [hEeq]
  push_cast
  constructor
  · calc (1 - μ) * ((q : ℝ) * d) = (q : ℝ) * ((1 - μ) * d) := by ring
      _ ≤ (q : ℝ) * (degree (triangleHypergraphSub H) E : ℝ) :=
          mul_le_mul_of_nonneg_left h1.1 (Nat.cast_nonneg q)
  · calc (q : ℝ) * (degree (triangleHypergraphSub H) E : ℝ) ≤ (q : ℝ) * ((1 + μ) * d) :=
          mul_le_mul_of_nonneg_left h1.2 (Nat.cast_nonneg q)
      _ = (1 + μ) * ((q : ℝ) * d) := by ring

/-! ### The blow-up gap theorem -/

/-- **The blow-up gap theorem.**  For every `ε > 0` there are a near-regularity tolerance `μ > 0`
and a scale `D > 0` such that: whenever the triangle hypergraph of `H` is `(1±μ)`-nearly
`d`-regular and the blown-up scale `q·d` exceeds `D`, the `q`-blow-up of `H` carries an integral
edge-disjoint triangle packing of size at least `q²·ν₃*(H) − ε·|V(H[q])|²`.

Combined with `Nibble.AX1.nu3star_blowUp` (`ν₃*(H[q]) = q²·ν₃*(H)`) this says that the integrality
gap of the triangle packing LP vanishes, relative to `|V|²`, along blow-ups of a near-regular
graph. -/
theorem nu3_blowUp_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ D : ℝ, 0 < D ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        {d : ℝ} {q : ℕ}, 0 < q → 0 < d → D ≤ (q : ℝ) * d →
        NearlyRegular (triangleHypergraphSub H) d μ →
        (q : ℝ) ^ 2 * nu3star H - ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2
          ≤ (nu3 (blowUp H q) : ℝ) := by
  classical
  obtain ⟨μ, hμ, d₀, hd₀, hmain⟩ := nu3_ge_nibble_uniform (β := 3 * ε) (by linarith)
  refine ⟨μ, hμ, max d₀ (1 / μ), lt_of_lt_of_le hd₀ (le_max_left _ _), ?_⟩
  intro W _ _ H _ d q hq hd hD hreg
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hqd : (0:ℝ) < (q : ℝ) * d := mul_pos hqR hd
  have hd₀le : d₀ ≤ (q : ℝ) * d := le_trans (le_max_left _ _) hD
  have hμd : (1:ℝ) ≤ μ * ((q : ℝ) * d) := by
    have h1 : 1 / μ ≤ (q : ℝ) * d := le_trans (le_max_right _ _) hD
    rw [div_le_iff₀ hμ] at h1
    linarith only [h1]
  have hcod : CodegreeBounded (triangleHypergraphSub (blowUp H q)) (μ * ((q : ℝ) * d)) :=
    triangleHypergraphSub_codegreeBounded _ hμd
  have hnib := hmain (blowUp H q) hqd hd₀le (nearlyRegular_blowUp H hreg) hcod
  have hstar : (q : ℝ) ^ 2 * nu3star H ≤ nu3star (blowUp H q) := nu3star_blowUp_ge H hq
  have hle : nu3star (blowUp H q) ≤ ((((blowUp H q).cliqueFinset 2).card : ℝ)) / 3 :=
    nu3star_le _
  have hcard : (Fintype.card (W × Fin q) : ℝ) = (q : ℝ) * (Fintype.card W : ℝ) := by
    simp [Fintype.card_prod]; ring
  have hEb : ((((blowUp H q).cliqueFinset 2).card : ℝ)) ≤ ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := by
    have := edge_card_le_card_sq (blowUp H q)
    rwa [hcard] at this
  have hεE : ε * ((((blowUp H q).cliqueFinset 2).card : ℝ))
      ≤ ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hEb hε.le
  linarith only [hnib, hstar, hle, hεE]

/-- **The blow-up gap theorem, gap form.** Under the same hypotheses, the integrality gap of the
triangle packing LP on the blow-up is at most `ε·|V(H[q])|²`.  This is the form STEP 2 of the route
asks for; it combines `Nibble.AX1.nu3_blowUp_ge` with the exact scaling
`Nibble.AX1.nu3star_blowUp`. -/
theorem nu3star_sub_nu3_blowUp_le {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ D : ℝ, 0 < D ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
        {d : ℝ} {q : ℕ}, 0 < q → 0 < d → D ≤ (q : ℝ) * d →
        NearlyRegular (triangleHypergraphSub H) d μ →
        nu3star (blowUp H q) - (nu3 (blowUp H q) : ℝ)
          ≤ ε * (Fintype.card (W × Fin q) : ℝ) ^ 2 := by
  classical
  obtain ⟨μ, hμ, D, hD, hmain⟩ := nu3_blowUp_ge hε
  refine ⟨μ, hμ, D, hD, ?_⟩
  intro W _ _ H _ d q hq hd hDle hreg
  have hcard : (Fintype.card (W × Fin q) : ℝ) = (q : ℝ) * (Fintype.card W : ℝ) := by
    simp [Fintype.card_prod]; ring
  rw [hcard, nu3star_blowUp H hq]
  linarith only [hmain H hq hd hDle hreg]

/-! ### A witness that the near-regularity hypothesis is satisfiable -/

/-- Every edge of a complete graph on `m` vertices lies in exactly `m - 2` triangles. -/
theorem degree_triangleHypergraphSub_top {W : Type} [Fintype W] [DecidableEq W]
    (E : EdgeV (⊤ : SimpleGraph W)) :
    degree (triangleHypergraphSub (⊤ : SimpleGraph W)) E = Fintype.card W - 2 := by
  classical
  rw [triangleHypergraphSub_degree_eq_commonNbr]
  have hE2 : #E.val = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  have hset : (univ.filter
      (fun c : W => c ∉ E.val ∧ (⊤ : SimpleGraph W).IsNClique 3 (insert c E.val)))
      = (E.val)ᶜ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      refine ⟨h, ?_, ?_⟩
      · intro u hu v hv huv
        simpa using huv
      · rw [Finset.card_insert_of_notMem h, hE2]
  rw [hset, Finset.card_compl, hE2]

/-- **The blow-up gap theorem is not vacuous**: the complete graph satisfies the near-regularity
hypothesis (exactly, for every tolerance), so the blow-up bound applies to complete multipartite
graphs `K_m[q]`. -/
theorem nu3_blowUp_ge_complete {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] {q : ℕ}, 0 < q → 3 ≤ Fintype.card W →
        D ≤ (q : ℝ) * ((Fintype.card W : ℝ) - 2) →
        (q : ℝ) ^ 2 * nu3star (⊤ : SimpleGraph W)
            - ε * ((q : ℝ) * (Fintype.card W : ℝ)) ^ 2
          ≤ (nu3 (blowUp (⊤ : SimpleGraph W) q) : ℝ) := by
  classical
  obtain ⟨μ, hμ, D, hD, hmain⟩ := nu3_blowUp_ge hε
  refine ⟨D, hD, ?_⟩
  intro W _ _ q hq hcard hDle
  have hd : (0:ℝ) < (Fintype.card W : ℝ) - 2 := by
    have : (3:ℝ) ≤ (Fintype.card W : ℝ) := by exact_mod_cast hcard
    linarith
  have hreg : NearlyRegular (triangleHypergraphSub (⊤ : SimpleGraph W))
      ((Fintype.card W : ℝ) - 2) μ := by
    intro E
    rw [degree_triangleHypergraphSub_top E]
    have hcast : ((Fintype.card W - 2 : ℕ) : ℝ) = (Fintype.card W : ℝ) - 2 := by
      have h2 : 2 ≤ Fintype.card W := by omega
      push_cast [Nat.cast_sub h2]
      ring
    rw [hcast]
    constructor <;> nlinarith only [hd, hμ]
  exact hmain (⊤ : SimpleGraph W) hq hd hDle hreg


/-! ### Axiom check -/

section AxCheck

#print axioms Nibble.AX1.nu3_blowUp_ge
#print axioms Nibble.AX1.nu3star_sub_nu3_blowUp_le
#print axioms Nibble.AX1.nu3_blowUp_ge_complete

end AxCheck

end Nibble.AX1
