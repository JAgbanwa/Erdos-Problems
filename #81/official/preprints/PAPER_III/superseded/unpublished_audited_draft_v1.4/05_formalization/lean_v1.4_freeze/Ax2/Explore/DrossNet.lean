/-
  Instantiation of the general MFMC (`Ax2.RouteB.maxflow_eq_mincut`) on Dross's auxiliary
  network Ĝ (Dross, SIAM 30 (2016), §2), toward `dross_fractional` / `no_deficient_cut`.

  Ĝ (Dross): nodes = edges of G, plus a supersource `src` and supersink `snk`.
    • edge–edge arc  e₁—e₂  with capacity  c = 2wΔ/(3(1−δ)n−3)  iff {e₁,e₂} is the disjoint
      pair of a rooted K₄ (the 4 endpoints form a clique and e₁,e₂ are vertex-disjoint);
    • src → e  with capacity  (Tₑ·wΔ − 1)₊   (a "source" edge, when Tₑ·wΔ > 1);
    • e → snk  with capacity  (1 − Tₑ·wΔ)₊   (a "sink"  edge, when Tₑ·wΔ < 1).
  Demand  M = Σ_e (Tₑ·wΔ − 1)₊  (total source-arc capacity).

  This file: the network definition, the instantiation of `maxflow_eq_mincut`, and the two
  bridge lemmas isolated as targets:
    (I)  `decomp_of_maxflowM` — a flow of value M yields a fractional decomposition;
    (II) `cut_ge_M`          — every s–t cut has capacity ≥ M (the deficient-cut analysis,
                               consuming the K₄ counting A6 / extremization A7 / bound A8).
-/
import Ax2.Explore.MFMC
import Ax2.Basic
import Ax2.PartA.Flow
import Ax2.PartA.Spine
import Ax2.PartB.BKLO.Gadget

namespace Ax2.DrossNet

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Triangles of `G` through the edge `e` (Dross's `Tₑ`). -/
def triThrough (G : SimpleGraph V) [DecidableRel G.Adj] (e : Sym2 V) : ℕ :=
  ((G.cliqueFinset 3).filter (fun t => e ∈ triEdges t)).card

/-- Nodes of `Ĝ`: the edges of `G`, plus supersource and supersink. -/
inductive Ghat (V : Type*) where
  | src : Ghat V
  | snk : Ghat V
  | edge : Sym2 V → Ghat V
  deriving DecidableEq

instance [Fintype V] : Fintype (Ghat V) where
  elems := {Ghat.src, Ghat.snk} ∪ (Finset.univ.image Ghat.edge)
  complete := by rintro (_ | _ | e) <;> simp

/-- `{e₁,e₂}` is the disjoint pair of a rooted `K₄`: vertex-disjoint edges whose four
endpoints induce a clique in `G`. -/
def K4pair (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : Sym2 V) : Prop :=
  ∃ a b c d : V, e₁ = s(a, b) ∧ e₂ = s(c, d) ∧
    ({a, b, c, d} : Finset V).card = 4 ∧ G.IsNClique 4 {a, b, c, d}

instance (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : Sym2 V) :
    Decidable (K4pair G e₁ e₂) := by unfold K4pair; infer_instance

/-- The per-arc capacity `c` of the edge–edge arcs. -/
noncomputable def cc (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) : ℝ :=
  2 * wΔ / (3 * (G.minDegree : ℝ) - 3)

/-- Capacities of `Ĝ`. All wrapped in `max _ 0` so nonnegativity is immediate. -/
noncomputable def dcap (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) :
    Ghat V → Ghat V → ℝ
  | Ghat.src, Ghat.edge e => max ((triThrough G e : ℝ) * wΔ - 1) 0
  | Ghat.edge e, Ghat.snk => max (1 - (triThrough G e : ℝ) * wΔ) 0
  | Ghat.edge e₁, Ghat.edge e₂ => if K4pair G e₁ e₂ then max (cc G wΔ) 0 else 0
  | _, _ => 0

/-- Dross's auxiliary network `Ĝ` as a `RouteB.Network`. -/
noncomputable def drossNet (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) :
    RouteB.Network (Ghat V) where
  cap := dcap G wΔ
  capNonneg u v := by
    cases u <;> cases v <;> simp only [dcap] <;> positivity
  s := Ghat.src
  t := Ghat.snk
  st := by simp

/-- Dross's demand `M`: the total capacity of the source arcs. -/
noncomputable def demand (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, max ((triThrough G e : ℝ) * wΔ - 1) 0

/-- **Triangle–edge handshake.** Summing `Tₑ` over all edges triple-counts the triangles. -/
theorem handshake (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ e ∈ G.edgeFinset, triThrough G e = 3 * (G.cliqueFinset 3).card := by
  simp_rw [triThrough, Finset.card_filter]
  rw [Finset.sum_comm,
      show 3 * (G.cliqueFinset 3).card = ∑ _t ∈ G.cliqueFinset 3, 3 by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Ax2.triEdges_subset_edgeFinset G ht)]
  exact Ax2.BKLO.triEdges_card_of_isNClique G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)

/-- **Balance of the demand.** For the balanced weight `wΔ = m/(3·#triangles)` (with triangles
present), the total signed excess `∑ₑ(Tₑ·wΔ − 1)` vanishes — i.e. total source excess = total sink
deficit. This is what makes Dross's flow feasible (the demand `M` is well-posed). -/
theorem balance (G : SimpleGraph V) [DecidableRel G.Adj] {wΔ : ℝ}
    (hT : 0 < (G.cliqueFinset 3).card)
    (hwΔ : wΔ = (G.edgeFinset.card : ℝ) / (3 * (G.cliqueFinset 3).card)) :
    ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0 := by
  have hsum : (∑ e ∈ G.edgeFinset, (triThrough G e : ℝ)) = 3 * (G.cliqueFinset 3).card := by
    rw [← Nat.cast_sum, handshake]; push_cast; ring
  have h3T : (3 : ℝ) * (G.cliqueFinset 3).card ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, hsum, hwΔ,
    nsmul_eq_mul, mul_one]
  field_simp
  ring

/-- A sum over `Ghat V` splits into the source term, the sink term, and the edge terms. -/
lemma sum_Ghat (f : Ghat V → ℝ) :
    ∑ v, f v = f Ghat.src + f Ghat.snk + ∑ e : Sym2 V, f (Ghat.edge e) := by
  have huniv : (Finset.univ : Finset (Ghat V))
      = insert Ghat.src (insert Ghat.snk ((Finset.univ : Finset (Sym2 V)).image Ghat.edge)) := by
    ext v; cases v <;> simp
  rw [huniv, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_image (by intro a _ b _ h; injection h)]
  ring

/-- An edge not in `G` is in no triangle, so `Tₑ = 0`. -/
lemma triThrough_eq_zero_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∉ G.edgeFinset) : triThrough G e = 0 := by
  rw [triThrough, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht hmem
  exact he (Ax2.triEdges_subset_edgeFinset G ht hmem)

/-- The flow value is the total flow along the source arcs. -/
lemma value_eq_source_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) :
    F.value = ∑ e : Sym2 V, F.f Ghat.src (Ghat.edge e) := by
  have h1 : F.f Ghat.src Ghat.src = 0 := by have := F.skew Ghat.src Ghat.src; linarith
  have h2 : F.f Ghat.src Ghat.snk = 0 := by
    have hle : F.f Ghat.src Ghat.snk ≤ 0 := F.capacitated Ghat.src Ghat.snk
    have hge : F.f Ghat.snk Ghat.src ≤ 0 := F.capacitated Ghat.snk Ghat.src
    have hsk := F.skew Ghat.src Ghat.snk
    linarith
  show ∑ v, F.f Ghat.src v = _
  rw [sum_Ghat (fun v => F.f Ghat.src v), h1, h2]; ring

/-- **Source arcs are saturated.** When the flow value equals the demand `M`, every source arc
carries its full capacity `(Tₑ·wΔ − 1)₊`. (Total source capacity = `M` = value, forcing equality
term by term.) -/
theorem source_saturated (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ) :
    ∀ e : Sym2 V, F.f Ghat.src (Ghat.edge e) = max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
  have hle : ∀ e : Sym2 V, F.f Ghat.src (Ghat.edge e) ≤ max ((triThrough G e : ℝ) * wΔ - 1) 0 :=
    fun e => F.capacitated Ghat.src (Ghat.edge e)
  have hdemand : demand G wΔ = ∑ e : Sym2 V, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [demand]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    rw [triThrough_eq_zero_of_notMem G he]; simp
  have hsum : ∑ e : Sym2 V, F.f Ghat.src (Ghat.edge e)
      = ∑ e : Sym2 V, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [← value_eq_source_sum, hF, hdemand]
  intro e
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum e (Finset.mem_univ e)

/-- The flow value also equals the total flow into the sink arcs (over all edge-nodes). Dual of
`value_eq_source_sum`: the whole antisymmetric matrix sums to `0`, and only the source and sink
rows survive (every edge-node is conserved). -/
lemma value_eq_sink_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) :
    F.value = ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk := by
  have hsrcsnk : F.f Ghat.src Ghat.snk = 0 := by
    have hle : F.f Ghat.src Ghat.snk ≤ 0 := F.capacitated Ghat.src Ghat.snk
    have hge : F.f Ghat.snk Ghat.src ≤ 0 := F.capacitated Ghat.snk Ghat.src
    have hsk := F.skew Ghat.src Ghat.snk; linarith
  have hsnksnk : F.f Ghat.snk Ghat.snk = 0 := by have := F.skew Ghat.snk Ghat.snk; linarith
  -- the whole antisymmetric matrix sums to zero
  have htot : ∑ u : Ghat V, ∑ v : Ghat V, F.f u v = 0 := by
    have hSS : (∑ u : Ghat V, ∑ v : Ghat V, F.f u v)
        = - ∑ u : Ghat V, ∑ v : Ghat V, F.f u v := by
      calc ∑ u : Ghat V, ∑ v : Ghat V, F.f u v
          = ∑ u : Ghat V, ∑ v : Ghat V, - F.f v u :=
            Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => F.skew u v))
        _ = ∑ v : Ghat V, ∑ u : Ghat V, - F.f v u := Finset.sum_comm
        _ = - ∑ v : Ghat V, ∑ u : Ghat V, F.f v u := by
            simp only [Finset.sum_neg_distrib]
    linarith
  -- split the outer sum; edge rows vanish by conservation
  have hrows : ∑ u : Ghat V, ∑ v : Ghat V, F.f u v
      = (∑ v, F.f Ghat.src v) + (∑ v, F.f Ghat.snk v)
        + ∑ e : Sym2 V, ∑ v, F.f (Ghat.edge e) v := sum_Ghat (fun u => ∑ v, F.f u v)
  have hedgesum0 : ∑ e : Sym2 V, ∑ v, F.f (Ghat.edge e) v = 0 :=
    Finset.sum_eq_zero (fun e _ => F.conserved (Ghat.edge e) (by simp [drossNet]) (by simp [drossNet]))
  -- the sink row equals `-∑ₑ f(edge e)(snk)`
  have hsnkrow : ∑ v, F.f Ghat.snk v = - ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk := by
    rw [sum_Ghat (fun v => F.f Ghat.snk v)]
    have h1 : F.f Ghat.snk Ghat.src = - F.f Ghat.src Ghat.snk := F.skew Ghat.snk Ghat.src
    rw [h1, hsrcsnk, hsnksnk, ← Finset.sum_neg_distrib]
    simp only [neg_zero, add_zero, zero_add]
    exact Finset.sum_congr rfl (fun e _ => F.skew Ghat.snk (Ghat.edge e))
  rw [hrows, hedgesum0, hsnkrow, add_zero] at htot
  have hval : F.value = ∑ v, F.f Ghat.src v := rfl
  rw [hval]; linarith

/-- The reconstructed fractional weight of a 3-clique `t` from a flow `F` on `Ĝ` (Dross's step I):
the uniform weight `wΔ` adjusted by the net K₄-move transfer. For each edge `e` of `t`, a K₄-arc
`(e, e')` on which `e` is a "root" and whose fourth vertex completes `t` (i.e. `t`'s third vertex
lies on `e'`) removes `½·f(e)(e')` from `t`. -/
noncomputable def triWeight (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) (t : Finset V) : ℝ :=
  if t ∈ G.cliqueFinset 3 then
    wΔ - (1 / 2) * ∑ e ∈ triEdges t, ∑ e' : Sym2 V,
      (if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0)
  else 0

/-- The four literals of a cardinality-4 finset are pairwise distinct. -/
private lemma card4_pairwise {a b c d : V} (h : ({a, b, c, d} : Finset V).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hb3 : ({b, c, d} : Finset V).card ≤ 3 := by
    have h1 := Finset.card_insert_le b ({c, d} : Finset V)
    have h2 := Finset.card_insert_le c ({d} : Finset V)
    simp only [Finset.card_singleton] at h1 h2; omega
  have ha : a ∉ ({b, c, d} : Finset V) := fun hmem => by
    rw [Finset.card_insert_of_mem hmem] at h; omega
  have hbcd : ({b, c, d} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem ha] at h; omega
  have hb : b ∉ ({c, d} : Finset V) := fun hmem => by
    rw [Finset.card_insert_of_mem hmem] at hbcd
    have h2 := Finset.card_insert_le c ({d} : Finset V)
    simp only [Finset.card_singleton] at h2; omega
  have hcd1 : ({c, d} : Finset V).card = 2 := by
    rw [Finset.card_insert_of_notMem hb] at hbcd; omega
  have hc : c ≠ d := by
    intro hmem; rw [hmem] at hcd1; simp at hcd1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  exact ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc⟩

/-- A rooted-K₄ pair on `uv` is exactly a 4-clique on the four endpoints. -/
theorem k4pair_iff_clique (G : SimpleGraph V) [DecidableRel G.Adj] (u v c d : V) :
    K4pair G (s(u, v)) (s(c, d)) ↔ G.IsNClique 4 {u, v, c, d} := by
  constructor
  · rintro ⟨a, b, c', d', hab, hcd, hcard, hclq⟩
    have hset : ({a, b, c', d'} : Finset V) = {u, v, c, d} := by
      rw [Sym2.eq_iff] at hab hcd
      ext x
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
    rwa [hset] at hclq
  · intro hclq
    exact ⟨u, v, c, d, rfl, rfl, hclq.card_eq, hclq⟩

/-- The rooted-K₄ pair relation is symmetric. -/
theorem k4pair_symm (G : SimpleGraph V) [DecidableRel G.Adj] (e₁ e₂ : Sym2 V) :
    K4pair G e₁ e₂ ↔ K4pair G e₂ e₁ := by
  have hone : ∀ f₁ f₂ : Sym2 V, K4pair G f₁ f₂ → K4pair G f₂ f₁ := by
    rintro f₁ f₂ ⟨a, b, c, d, h1, h2, hcard, hclq⟩
    have hset : ({c, d, a, b} : Finset V) = {a, b, c, d} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact ⟨c, d, a, b, h2, h1, by rw [hset]; exact hcard, by rw [hset]; exact hclq⟩
  exact ⟨hone e₁ e₂, hone e₂ e₁⟩

/-- A non-edge is in no rooted-K₄ pair: its endpoints would have to be adjacent (in the 4-clique). -/
lemma not_K4pair_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∉ G.edgeFinset) (e' : Sym2 V) : ¬ K4pair G e e' := by
  rintro ⟨a, b, c, d, hab, _, hcard, hclq⟩
  apply he
  have hne : a ≠ b := (card4_pairwise hcard).1
  have hadj : G.Adj a b := hclq.1 (by simp) (by simp) hne
  rw [hab, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj

/-- At a **non-edge** node the flow to the sink vanishes: there are no K₄-arcs and the source arc has
capacity `0`, so conservation forces `f(edge e)(snk) = 0`. -/
lemma sinkflow_zero_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) {e : Sym2 V} (he : e ∉ G.edgeFinset) :
    F.f (Ghat.edge e) Ghat.snk = 0 := by
  have hT0 : triThrough G e = 0 := triThrough_eq_zero_of_notMem G he
  -- every K₄-arc out of `e` carries no flow
  have hk0 : ∀ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') = 0 := by
    intro e'
    have hle : F.f (Ghat.edge e) (Ghat.edge e') ≤ 0 := by
      have := F.capacitated (Ghat.edge e) (Ghat.edge e')
      simp only [drossNet, dcap, if_neg (not_K4pair_of_notMem G he e')] at this; exact this
    have hge : F.f (Ghat.edge e') (Ghat.edge e) ≤ 0 := by
      have := F.capacitated (Ghat.edge e') (Ghat.edge e)
      simp only [drossNet, dcap,
        if_neg (fun hp => not_K4pair_of_notMem G he e' ((k4pair_symm G e' e).mp hp))] at this
      exact this
    have hsk := F.skew (Ghat.edge e) (Ghat.edge e'); linarith
  -- source arc into `e` carries no flow (capacity `0` since `Tₑ = 0`)
  have hsrc0 : F.f (Ghat.edge e) Ghat.src = 0 := by
    have hle : F.f Ghat.src (Ghat.edge e) ≤ 0 := by
      have := F.capacitated Ghat.src (Ghat.edge e)
      simp only [drossNet, dcap, hT0, Nat.cast_zero, zero_mul, zero_sub] at this
      rwa [max_eq_right (by norm_num)] at this
    have hge : F.f (Ghat.edge e) Ghat.src ≤ 0 := F.capacitated (Ghat.edge e) Ghat.src
    have hsk := F.skew Ghat.src (Ghat.edge e); linarith
  have hsnkge : 0 ≤ F.f (Ghat.edge e) Ghat.snk := by
    have hge : F.f Ghat.snk (Ghat.edge e) ≤ 0 := F.capacitated Ghat.snk (Ghat.edge e)
    have hsk := F.skew Ghat.snk (Ghat.edge e); linarith
  have hcons := F.conserved (Ghat.edge e) (by simp [drossNet]) (by simp [drossNet])
  rw [sum_Ghat (fun v => F.f (Ghat.edge e) v), Finset.sum_eq_zero (fun e' _ => hk0 e'),
    hsrc0, add_zero, zero_add] at hcons
  linarith

/-- **Sink arcs are saturated (on real edges).** When the flow value equals the demand `M` and the
demand is balanced (`hbal`), every sink arc of a real edge carries its full capacity
`(1 − Tₑ·wΔ)₊`. -/
theorem sink_saturated (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ) :
    ∀ e ∈ G.edgeFinset, F.f (Ghat.edge e) Ghat.snk = max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
  have hle : ∀ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk ≤ max (1 - (triThrough G e : ℝ) * wΔ) 0 :=
    fun e => F.capacitated (Ghat.edge e) Ghat.snk
  -- total sink capacity over real edges equals the demand (via `hbal`)
  have hcap : ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 = demand G wΔ := by
    rw [demand]
    have hpt : ∀ e, max (1 - (triThrough G e : ℝ) * wΔ) 0
        = max ((triThrough G e : ℝ) * wΔ - 1) 0 + (1 - (triThrough G e : ℝ) * wΔ) := by
      intro e
      rcases le_total ((triThrough G e : ℝ) * wΔ) 1 with hc | hc
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib]
    have hb2 : ∑ e ∈ G.edgeFinset, (1 - (triThrough G e : ℝ) * wΔ) = 0 := by
      have h := hbal
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib] at h
      rw [← h]; exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hb2, add_zero]
  -- the sink-flow sum over real edges equals the value = demand
  have hsumeq : ∑ e ∈ G.edgeFinset, F.f (Ghat.edge e) Ghat.snk
      = ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
    rw [hcap]
    have hall : ∑ e ∈ G.edgeFinset, F.f (Ghat.edge e) Ghat.snk
        = ∑ e : Sym2 V, F.f (Ghat.edge e) Ghat.snk :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun e _ he => sinkflow_zero_of_notMem G wΔ F he))
    rw [hall, ← value_eq_sink_sum, hF]
  intro e he
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsumeq e he

/-- **Edge-node conservation.** At a real edge-node `f₀`, the net K₄-flow to all other edge-nodes
equals the signed source excess `Tₑ·wΔ − 1`. (Flow conservation at `f₀` plus source/sink
saturation: `max(z,0) − max(−z,0) = z`.) -/
lemma edgeNode_flow_sum (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    {f₀ : Sym2 V} (hf₀ : f₀ ∈ G.edgeFinset) :
    ∑ e' : Sym2 V, F.f (Ghat.edge f₀) (Ghat.edge e') = (triThrough G f₀ : ℝ) * wΔ - 1 := by
  have hcons := F.conserved (Ghat.edge f₀) (by simp [drossNet]) (by simp [drossNet])
  rw [sum_Ghat (fun v => F.f (Ghat.edge f₀) v)] at hcons
  have hsrc : F.f (Ghat.edge f₀) Ghat.src = -(max ((triThrough G f₀ : ℝ) * wΔ - 1) 0) := by
    rw [F.skew (Ghat.edge f₀) Ghat.src, source_saturated G wΔ F hF f₀]
  have hsnk : F.f (Ghat.edge f₀) Ghat.snk = max (1 - (triThrough G f₀ : ℝ) * wΔ) 0 :=
    sink_saturated G wΔ hbal F hF f₀ hf₀
  rw [hsrc, hsnk] at hcons
  have hmax : max ((triThrough G f₀ : ℝ) * wΔ - 1) 0 - max (1 - (triThrough G f₀ : ℝ) * wΔ) 0
      = (triThrough G f₀ : ℝ) * wΔ - 1 := by
    rcases le_total 0 ((triThrough G f₀ : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  linarith [hcons, hmax]

set_option maxHeartbeats 1600000 in
/-- **Heavy nucleus (nonnegativity).** For a triangle `t`, the total K₄-transfer out of its three
edges is `≤ 2wΔ`. Proof uses `hNoHDT`: some vertex `z ∈ t` has `deg z ≤ minDegree + 1`, so each edge
of `t` has `≤ deg z − 2 ≤ minDegree − 1` K₄-partners (all fourth vertices lie in `N(z)`), each
K₄-arc carrying `≤ cc = 2wΔ/(3(minDegree−1))`; hence `≤ 3·(minDegree−1)·cc = 2wΔ`. (Proved.) -/
theorem triWeight_transfer_le (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hmd2 : 2 ≤ G.minDegree) (F : RouteB.Flow (drossNet G wΔ))
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False)
    (t : Finset V) (ht : t ∈ G.cliqueFinset 3) :
    (∑ e ∈ triEdges t, ∑ e' : Sym2 V,
      (if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0)) ≤ 2 * wΔ := by
  have hmd2R : (2:ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hmd2
  have hden : (0:ℝ) < 3 * (G.minDegree : ℝ) - 3 := by nlinarith
  have hcc_nn : 0 ≤ cc G wΔ := by rw [cc]; positivity
  have hccval : (3 * ((G.minDegree : ℝ) - 1)) * cc G wΔ = 2 * wΔ := by
    have hne : (3 * (G.minDegree : ℝ) - 3) ≠ 0 := ne_of_gt hden
    rw [cc, show (3 * ((G.minDegree : ℝ) - 1)) = (3 * (G.minDegree : ℝ) - 3) from by ring,
      div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hne, mul_one]
  have htcard : (triEdges t).card = 3 :=
    Ax2.BKLO.triEdges_card_of_isNClique G ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
  -- `hNoHDT` forces a low-degree vertex of the triangle `t`
  obtain ⟨z, hzt, hzdeg⟩ : ∃ z ∈ t, G.degree z ≤ G.minDegree + 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, c, hab, hac, hbc, hts⟩ := is3Clique_iff.mp ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
    subst hts
    exact hNoHDT a b c hab hac hbc
      (by have := hcon a (by simp); omega) (by have := hcon b (by simp); omega)
      (by have := hcon c (by simp); omega)
  -- **Combinatorial core [DELEGATED].** For each edge of `t`, the number of K₄-partner arcs is
  -- `≤ minDegree − 1` (all fourth vertices lie in `N(z)`, and `deg z − 2 ≤ minDegree − 1`).
  have hcount : ∀ e ∈ triEdges t,
      (((Finset.univ : Finset (Sym2 V)).filter
        (fun e' => K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e)).card : ℝ)
        ≤ (G.minDegree : ℝ) - 1 := by
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      is3Clique_iff.mp ((SimpleGraph.mem_cliqueFinset_iff).mp ht)
    have hab' : a ≠ b := hab.ne
    have hac' : a ≠ c := hac.ne
    have hbc' : b ≠ c := hbc.ne
    have hcase (p q r : V) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
        (hpqA : G.Adj p q) (hprA : G.Adj p r) (hqrA : G.Adj q r)
        (hz : z ∈ ({p,q,r} : Finset V)) :
        ((Finset.univ.filter (fun e' : Sym2 V =>
          K4pair G (s(p,q)) e' ∧ ∃ v, v ∈ ({p,q,r} : Finset V) ∧ v ∈ e' ∧ v ∉ s(p,q))).card : ℝ)
          ≤ (G.minDegree : ℝ) - 1 := by
      let W := G.neighborFinset z \ (({p,q,r} : Finset V).erase z)
      let S := Finset.univ.filter (fun e' : Sym2 V =>
        K4pair G (s(p,q)) e' ∧ ∃ v, v ∈ ({p,q,r} : Finset V) ∧ v ∈ e' ∧ v ∉ s(p,q))
      have hsub : S ⊆ W.image (fun w => s(r,w)) := by
        intro e' he'
        have hh := (Finset.mem_filter.mp he').2
        rcases hh.2 with ⟨v, hvtri, hve', hvnot⟩
        have hv : v = r := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hvtri
          simp only [Sym2.mem_iff, not_or] at hvnot
          aesop
        subst v
        induction e' using Sym2.inductionOn with | _ x y =>
          simp only [Sym2.mem_iff] at hve'
          have hcl := (k4pair_iff_clique G p q x y).mp hh.1
          have hdist := card4_pairwise hcl.card_eq
          rcases hve' with hxr | hyr
          · subst x
            refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
            apply Finset.mem_sdiff.mpr
            have hpy : p ≠ y := hdist.2.2.1
            have hqy : q ≠ y := hdist.2.2.2.2.1
            have hry : r ≠ y := hdist.2.2.2.2.2
            have hapy : G.Adj p y := hcl.1 (by simp) (by simp) hpy
            have haqy : G.Adj q y := hcl.1 (by simp) (by simp) hqy
            have hary : G.Adj r y := hcl.1 (by simp) (by simp) hry
            rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
            · exact ⟨(G.mem_neighborFinset _ _).mpr hapy, by intro hy; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy; aesop⟩
            · exact ⟨(G.mem_neighborFinset _ _).mpr haqy, by intro hy; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy; aesop⟩
            · exact ⟨(G.mem_neighborFinset _ _).mpr hary, by intro hy; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hy; aesop⟩
          · subst y
            refine Finset.mem_image.mpr ⟨x, ?_, by rw [Sym2.eq_iff]; aesop⟩
            apply Finset.mem_sdiff.mpr
            have hpx : p ≠ x := hdist.2.1
            have hqx : q ≠ x := hdist.2.2.2.1
            have hxr : x ≠ r := hdist.2.2.2.2.2
            have hapx : G.Adj p x := hcl.1 (by simp) (by simp) hpx
            have haqx : G.Adj q x := hcl.1 (by simp) (by simp) hqx
            have harx : G.Adj r x := hcl.1 (by simp) (by simp) hxr.symm
            rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
            · exact ⟨(G.mem_neighborFinset _ _).mpr hapx, by intro hx; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx; aesop⟩
            · exact ⟨(G.mem_neighborFinset _ _).mpr haqx, by intro hx; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx; aesop⟩
            · exact ⟨(G.mem_neighborFinset _ _).mpr harx, by intro hx; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx; aesop⟩
      have hcard : S.card ≤ W.card := calc
        S.card ≤ (W.image (fun w => s(r,w))).card := Finset.card_le_card hsub
        _ ≤ W.card := Finset.card_image_le
      have htriCard : (({p,q,r} : Finset V).erase z).card = 2 := by
        have ht3 : ({p,q,r} : Finset V).card = 3 := by simp [hpq, hpr, hqr]
        rw [Finset.card_erase_of_mem hz, ht3]
      have heraseSub : ({p,q,r} : Finset V).erase z ⊆ G.neighborFinset z := by
        intro u hu
        have hut := (Finset.mem_erase.mp hu).2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hut
        rcases (show z = p ∨ z = q ∨ z = r by simpa using hz) with rfl | rfl | rfl
        · rcases hut with rfl | rfl | rfl
          · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
          · exact (G.mem_neighborFinset _ _).mpr hpqA
          · exact (G.mem_neighborFinset _ _).mpr hprA
        · rcases hut with rfl | rfl | rfl
          · exact (G.mem_neighborFinset _ _).mpr hpqA.symm
          · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
          · exact (G.mem_neighborFinset _ _).mpr hqrA
        · rcases hut with rfl | rfl | rfl
          · exact (G.mem_neighborFinset _ _).mpr hprA.symm
          · exact (G.mem_neighborFinset _ _).mpr hqrA.symm
          · exact False.elim ((Finset.mem_erase.mp hu).1 rfl)
      have hW : W.card = G.degree z - 2 := by
        dsimp [W]
        rw [Finset.card_sdiff_of_subset heraseSub, G.card_neighborFinset_eq_degree, htriCard]
      have hn : S.card ≤ G.minDegree - 1 := by rw [hW] at hcard; omega
      have hnR : (S.card : ℝ) ≤ ((G.minDegree - 1 : ℕ) : ℝ) := by exact_mod_cast hn
      rw [Nat.cast_sub (by omega : 1 ≤ G.minDegree)] at hnR
      simpa [S] using hnR
    have hedge : triEdges {a, b, c} = {s(a,b), s(a,c), s(b,c)} := by
      ext f
      induction f using Sym2.inductionOn with | _ x y =>
        simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
          Sym2.mk_isDiag_iff, Sym2.eq_iff]
        aesop
    intro e he
    rw [hedge] at he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hcase a b c hab' hac' hbc' hab hac hbc hzt
    · simpa [Finset.insert_comm, Finset.pair_comm] using
        hcase a c b hac' hab' hbc'.symm hac hab hbc.symm
          (by simp only [Finset.mem_insert, Finset.mem_singleton] at hzt ⊢; tauto)
    · simpa [Finset.insert_comm, Finset.pair_comm] using
        hcase b c a hbc' hab'.symm hac'.symm hbc hab.symm hac.symm
          (by simp only [Finset.mem_insert, Finset.mem_singleton] at hzt ⊢; tauto)
  -- per-edge: inner sum ≤ (minDegree−1)·cc
  have hper : ∀ e ∈ triEdges t,
      (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0) ≤ ((G.minDegree : ℝ) - 1) * cc G wΔ := by
    intro e he
    set Se := (Finset.univ : Finset (Sym2 V)).filter
      (fun e' => K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e) with hSe
    calc (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0)
        = ∑ e' ∈ Se, F.f (Ghat.edge e) (Ghat.edge e') := by rw [hSe, Finset.sum_filter]
      _ ≤ ∑ _e' ∈ Se, cc G wΔ := by
          apply Finset.sum_le_sum
          intro e' he'
          have hk4 : K4pair G e e' := (Finset.mem_filter.mp he').2.1
          have hcap := F.capacitated (Ghat.edge e) (Ghat.edge e')
          simp only [drossNet, dcap, if_pos hk4] at hcap
          rwa [max_eq_left hcc_nn] at hcap
      _ = (Se.card : ℝ) * cc G wΔ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((G.minDegree : ℝ) - 1) * cc G wΔ :=
          mul_le_mul_of_nonneg_right (hcount e he) hcc_nn
  calc (∑ e ∈ triEdges t, ∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
          F.f (Ghat.edge e) (Ghat.edge e') else 0)
      ≤ ∑ _e ∈ triEdges t, ((G.minDegree : ℝ) - 1) * cc G wΔ := Finset.sum_le_sum hper
    _ = ((triEdges t).card : ℝ) * (((G.minDegree : ℝ) - 1) * cc G wΔ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * wΔ := by rw [htcard]; push_cast; linarith [hccval]

/-- For a fixed pair of edges, the triangles through the first edge whose third vertex lies on
the second edge are precisely the two triangles obtained from the endpoints of the second edge,
when the two edges form a rooted `K₄`; otherwise there are none. -/
private lemma two_apex_count (G : SimpleGraph V) [DecidableRel G.Adj] (e e' : Sym2 V) :
    ((G.cliqueFinset 3).filter (fun t =>
      K4pair G e e' ∧ e ∈ triEdges t ∧
        ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e)).card =
      if K4pair G e e' then 2 else 0 := by
  induction e using Sym2.inductionOn with | _ a b =>
  induction e' using Sym2.inductionOn with | _ x y =>
  by_cases hk : K4pair G (s(a,b)) (s(x,y))
  · have hcl := (k4pair_iff_clique G a b x y).mp hk
    have hd := card4_pairwise hcl.card_eq
    rw [if_pos hk]
    have heq :
        (G.cliqueFinset 3).filter (fun t =>
          K4pair G (s(a,b)) (s(x,y)) ∧ s(a,b) ∈ triEdges t ∧
            ∃ v, v ∈ t ∧ v ∈ s(x,y) ∧ v ∉ s(a,b)) =
          {{a,b,x}, {a,b,y}} := by
      ext t
      simp only [Finset.mem_filter, hk, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hedge, v, hvt, hvxy, hvab⟩
        have habt : a ∈ t ∧ b ∈ t := by
          exact (show (a ∈ t ∧ b ∈ t) ∧ ¬s(a,b).IsDiag from
            (by simpa only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff] using hedge)).1
        have hv : v = x ∨ v = y := by simpa only [Sym2.mem_iff] using hvxy
        rcases hv with hv | hv
        · subst v
          left
          symm
          apply Finset.eq_of_subset_of_card_le
          · exact fun z hz => by
              rcases (show z = a ∨ z = b ∨ z = x by simpa using hz) with hza | hzb | hzx
              · simpa [hza] using habt.1
              · simpa [hzb] using habt.2
              · simpa [hzx] using hvt
          · rw [((SimpleGraph.mem_cliqueFinset_iff).mp ht).card_eq]
            simp [hd.1, hd.2.1, hd.2.2.2.1]
        · subst v
          right
          symm
          apply Finset.eq_of_subset_of_card_le
          · exact fun z hz => by
              rcases (show z = a ∨ z = b ∨ z = y by simpa using hz) with hza | hzb | hzy
              · simpa [hza] using habt.1
              · simpa [hzb] using habt.2
              · simpa [hzy] using hvt
          · rw [((SimpleGraph.mem_cliqueFinset_iff).mp ht).card_eq]
            simp [hd.1, hd.2.2.1, hd.2.2.2.2.1]
      · intro ht
        rcases ht with rfl | rfl
        · refine ⟨?_, ?_, x, by simp, by simp, ?_⟩
          · rw [SimpleGraph.mem_cliqueFinset_iff]
            apply is3Clique_iff.mpr
            exact ⟨a, b, x,
              hcl.1 (by simp) (by simp) hd.1,
              hcl.1 (by simp) (by simp) hd.2.1,
              hcl.1 (by simp) (by simp) hd.2.2.2.1, rfl⟩
          · simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
            exact ⟨⟨by simp, by simp⟩, by simpa [Sym2.mk_isDiag_iff] using hd.1⟩
          · simpa only [Sym2.mem_iff, not_or] using ⟨hd.2.1.symm, hd.2.2.2.1.symm⟩
        · refine ⟨?_, ?_, y, by simp, by simp, ?_⟩
          · rw [SimpleGraph.mem_cliqueFinset_iff]
            apply is3Clique_iff.mpr
            exact ⟨a, b, y,
              hcl.1 (by simp) (by simp) hd.1,
              hcl.1 (by simp) (by simp) hd.2.2.1,
              hcl.1 (by simp) (by simp) hd.2.2.2.2.1, rfl⟩
          · simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff]
            exact ⟨⟨by simp, by simp⟩, by simpa [Sym2.mk_isDiag_iff] using hd.1⟩
          · simpa only [Sym2.mem_iff, not_or] using ⟨hd.2.2.1.symm, hd.2.2.2.2.1.symm⟩
    rw [heq]
    rw [Finset.card_pair]
    have hne : ({a,b,x} : Finset V) ≠ {a,b,y} := by
      intro hxy
      have hy : y ∈ ({a,b,x} : Finset V) := hxy ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hya | hyb | hyx
      · exact hd.2.2.1 hya.symm
      · exact hd.2.2.2.2.1 hyb.symm
      · exact hd.2.2.2.2.2 hyx.symm
    exact hne
  · rw [if_neg hk]
    simp [hk]

/-- **hkey — doubling half.** The `e''=e` contribution: summed over triangles `t ∋ e`, the on-`e`
transfer counts each `K₄`-partner edge `e'` twice (once per apex vertex of `t` lying on `e'`, i.e. the
two endpoints of the `K₄`-diagonal), giving `2·∑_{e'} f(e)(e')`. [DELEGATED — two-apex double count:
for `e=s(a,b)`, a triangle `t={a,b,c}∋e` forces apex `v=c∈e'`; each `e'=s(x,y)` with `{a,b,x,y}` a
`K₄` is hit by exactly the two apices `c=x` and `c=y`, and `f(edge e)(edge e')=0` off `K4pair`.] -/
theorem hkey_double (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0)
      = 2 * ∑ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') := by
  have hzero : ∀ x y : Sym2 V, ¬ K4pair G x y →
      F.f (Ghat.edge x) (Ghat.edge y) = 0 := by
    intro x y hxy
    have hle : F.f (Ghat.edge x) (Ghat.edge y) ≤ 0 := by
      have h := F.capacitated (Ghat.edge x) (Ghat.edge y)
      simpa [drossNet, dcap, hxy] using h
    have hyx : ¬ K4pair G y x := by
      intro hyx
      exact hxy ((k4pair_symm G x y).mpr hyx)
    have hge : F.f (Ghat.edge y) (Ghat.edge x) ≤ 0 := by
      have h := F.capacitated (Ghat.edge y) (Ghat.edge x)
      simpa [drossNet, dcap, hyx] using h
    have hsk := F.skew (Ghat.edge x) (Ghat.edge y)
    linarith
  have hswap :
      (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (∑ e' : Sym2 V, if K4pair G e e' ∧
          ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0) =
      ∑ e' : Sym2 V, ∑ t ∈ G.cliqueFinset 3,
        if K4pair G e e' ∧ e ∈ triEdges t ∧
          ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
            F.f (Ghat.edge e) (Ghat.edge e') else 0 := by
    calc
      _ = ∑ t ∈ G.cliqueFinset 3, ∑ e' : Sym2 V,
          if K4pair G e e' ∧ e ∈ triEdges t ∧
            ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
              F.f (Ghat.edge e) (Ghat.edge e') else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            by_cases het : e ∈ triEdges t <;> simp [het]
      _ = _ := by rw [Finset.sum_comm]
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' _
  by_cases hk : K4pair G e e'
  · have hc := two_apex_count G e e'
    rw [if_pos hk] at hc
    rw [← Finset.sum_filter, Finset.sum_const, hc, nsmul_eq_mul]
    norm_num
  · have hf := hzero e e' hk
    simp [hk, hf]

/-- Flow vanishes off `K4pair` (capacity 0 + skew). -/
private lemma hzero_cancel (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) (x y : Sym2 V) (hxy : ¬ K4pair G x y) :
    F.f (Ghat.edge x) (Ghat.edge y) = 0 := by
  have hle : F.f (Ghat.edge x) (Ghat.edge y) ≤ 0 := by
    have h := F.capacitated (Ghat.edge x) (Ghat.edge y)
    simp only [drossNet, dcap, if_neg hxy] at h; exact h
  have hge : F.f (Ghat.edge y) (Ghat.edge x) ≤ 0 := by
    have h := F.capacitated (Ghat.edge y) (Ghat.edge x)
    simp only [drossNet, dcap, if_neg (fun hp => hxy ((k4pair_symm G y x).mp hp))] at h; exact h
  have hsk := F.skew (Ghat.edge x) (Ghat.edge y); linarith

/-- **Key fact.** Two distinct edges `e, e2` of a triangle `t` cover its three vertices:
`e.toFinset ∪ e2.toFinset = t`. Used for both involution obligations. -/
private lemma tri_eq_edge_union (G : SimpleGraph V) [DecidableRel G.Adj] {t : Finset V}
    {e e2 : Sym2 V} (htc : t ∈ G.cliqueFinset 3) (het : e ∈ triEdges t)
    (he2 : e2 ∈ (triEdges t).erase e) : e.toFinset ∪ e2.toFinset = t := by
  have ht3 : t.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htc).card_eq
  have hsube : e.toFinset ⊆ t := fun z hz =>
    (Finset.mem_sym2_iff.mp (by rw [triEdges, Finset.mem_filter] at het; exact het.1)) z
      (Sym2.mem_toFinset.mp hz)
  have hsub2 : e2.toFinset ⊆ t := fun z hz =>
    (Finset.mem_sym2_iff.mp (by
      have := (Finset.mem_erase.mp he2).2; rw [triEdges, Finset.mem_filter] at this; exact this.1)) z
      (Sym2.mem_toFinset.mp hz)
  have hsub : e.toFinset ∪ e2.toFinset ⊆ t := Finset.union_subset hsube hsub2
  have hne : e ≠ e2 := (Finset.mem_erase.mp he2).1.symm
  have hec : e.toFinset.card = 2 := by
    induction e using Sym2.inductionOn with | _ a b =>
      rw [triEdges, Finset.mem_filter, Sym2.mk_isDiag_iff] at het
      rw [Sym2.toFinset_mk_eq]; simp [Sym2.mk_isDiag_iff.not.mp (by simpa using het.2)]
  have hpc : e2.toFinset.card = 2 := by
    induction h : e2 using Sym2.inductionOn with | _ a b =>
      have hd : ¬ (Sym2.mk (a, b)).IsDiag := by
        have := (Finset.mem_erase.mp he2).2; rw [triEdges, Finset.mem_filter, h] at this; exact this.2
      simp [h, Sym2.toFinset_mk_eq, Sym2.mk_isDiag_iff.not.mp hd]
  have hcard3 : (e.toFinset ∪ e2.toFinset).card = 3 := by
    have hle : (e.toFinset ∪ e2.toFinset).card ≤ 3 := (Finset.card_le_card hsub).trans_eq ht3
    have hinter : (e.toFinset ∩ e2.toFinset).card ≤ 1 := by
      by_contra hh
      push_neg at hh
      have heq : e.toFinset = e2.toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          have hii : e.toFinset ∩ e2.toFinset = e.toFinset :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
          rw [← hii] at hz; exact (Finset.mem_inter.mp hz).2
        · omega
      exact hne (Sym2.ext fun z => by simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp heq z)
    have hun := Finset.card_union_add_card_inter e.toFinset e2.toFinset
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [ht3, hcard3])

/-- **hkey — cancelling half.** The `e''≠e` contributions cancel in pairs under the involution that
swaps the apex and the `K₄`-partner vertex — `(t={a,b,c}, e''=s(a,c), e'=s(b,d)) ↦ (t'={a,b,d},
e''=s(b,d), e'=s(a,c))` — whose flow values are skew-negatives (`F.skew`). [DELEGATED — skew
involution via `Finset.sum_involution`.] -/
theorem hkey_cancel (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (F : RouteB.Flow (drossNet G wΔ)) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
        if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0)
      = 0 := by
  classical
  -- Reindex to a sum over the product `(cliqueFinset 3) × Sym2 × Sym2` filtered by the full config
  -- predicate `P t e'' e' := e ∈ triEdges t ∧ e'' ∈ (triEdges t).erase e ∧ K4pair e'' e' ∧ apex`.
  -- Config Finset (flattened product filtered by the full predicate):
  set Cfg : Finset (Finset V × Sym2 V × Sym2 V) :=
    ((G.cliqueFinset 3) ×ˢ (Finset.univ : Finset (Sym2 V)) ×ˢ (Finset.univ : Finset (Sym2 V))).filter
      (fun p => e ∈ triEdges p.1 ∧ p.2.1 ∈ (triEdges p.1).erase e ∧ K4pair G p.2.1 p.2.2 ∧
        ∃ v, v ∈ p.1 ∧ v ∈ p.2.2 ∧ v ∉ p.2.1) with hCfgdef
  have hflat : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
        if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0)
      = ∑ p ∈ Cfg, F.f (Ghat.edge p.2.1) (Ghat.edge p.2.2) := by
    rw [hCfgdef, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_product]
    by_cases het : e ∈ triEdges t
    · rw [if_pos het]
      rw [show (∑ e'' : Sym2 V, ∑ e' : Sym2 V,
            if e ∈ triEdges t ∧ e'' ∈ (triEdges t).erase e ∧ K4pair G e'' e' ∧
                (∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'') then F.f (Ghat.edge e'') (Ghat.edge e') else 0)
          = ∑ e'' : Sym2 V, if e'' ∈ (triEdges t).erase e then
              (∑ e' : Sym2 V, if K4pair G e'' e' ∧ (∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'') then
                F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0 from ?_]
      · rw [Finset.sum_ite_mem, Finset.univ_inter]
      · refine Finset.sum_congr rfl fun e'' _ => ?_
        by_cases hee : e'' ∈ (triEdges t).erase e
        · rw [if_pos hee]
          refine Finset.sum_congr rfl fun e' _ => ?_
          exact if_congr ⟨fun h => h.2.2, fun h => ⟨het, hee, h⟩⟩ rfl rfl
        · rw [if_neg hee]
          refine Finset.sum_eq_zero fun e' _ => ?_
          exact if_neg fun h => hee h.2.1
    · rw [if_neg het]
      refine (Finset.sum_eq_zero fun e'' _ => Finset.sum_eq_zero fun e' _ => ?_).symm
      exact if_neg fun h => het h.1
  rw [hflat]
  refine Finset.sum_involution
    (fun p _ => ((e.toFinset ∪ p.2.2.toFinset, p.2.2, p.2.1) : Finset V × Sym2 V × Sym2 V))
    ?_ ?_ ?_ ?_
  · -- h: skew-negatives sum to zero (holds for ALL p — pure `F.skew`)
    intro p _
    show F.f (Ghat.edge p.2.1) (Ghat.edge p.2.2) + F.f (Ghat.edge p.2.2) (Ghat.edge p.2.1) = 0
    rw [F.skew (Ghat.edge p.2.1) (Ghat.edge p.2.2)]; ring
  · -- g_ne: fixed-point-free on nonzero terms (`f p ≠ 0 ⇒ p.2.1 ≠ p.2.2`)
    intro p _ hfp
    have hne : p.2.1 ≠ p.2.2 := by
      intro h
      apply hfp
      rw [h]
      have hs := F.skew (Ghat.edge p.2.2) (Ghat.edge p.2.2)
      linarith
    intro hcontra
    rw [Prod.ext_iff, Prod.ext_iff] at hcontra
    exact hne hcontra.2.1.symm
  · -- g_mem: σ maps configs to configs (the K₄ argument, `k4pair_symm`)
    -- REMAINING (~60 lines, 4 cases): with `p.1 = {a,b,u}` (apex `u`), `e = s(u, s)` (`s ∈ {a,b}`),
    -- `p.2.2 = s(u, w)` (`w ∉ p.1`), show `σp.1 = {s, u, w}` is a 3-clique (⊆ the K₄) with
    -- `e ∈ triEdges σp.1`, `p.2.2 ∈ (triEdges σp.1).erase e`, `K4pair p.2.2 p.2.1` (`k4pair_symm`),
    -- and apex `s ∈ σp.1 ∩ p.2.1 \ p.2.2`. Reuse `tri_eq_edge_union` and the K₄ from `hk`.
    intro p hp
    simp only [hCfgdef, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      true_and] at hp ⊢
    obtain ⟨htc, hetri, herase, hk, u, huT, huY, huX⟩ := hp
    have hk' : K4pair G p.2.2 p.2.1 := (k4pair_symm G p.2.1 p.2.2).mp hk
    have hkey := tri_eq_edge_union G htc hetri herase
    let X := p.2.1.toFinset
    let Y := p.2.2.toFinset
    let E := e.toFinset
    let T := p.1
    let N := E ∪ Y
    have hT3 : T.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htc).card_eq
    have heND : ¬ e.IsDiag := by
      rw [triEdges, Finset.mem_filter] at hetri
      exact hetri.2
    have hE2 : E.card = 2 := by
      induction e using Sym2.inductionOn with | _ a b =>
        rw [Sym2.mk_isDiag_iff] at heND
        simp [E, Sym2.toFinset_mk_eq, heND]
    obtain ⟨a, b, c, d, hx, hy, hcard4, hclq⟩ := hk
    have hpw : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
      have ha : a ∉ ({b, c, d} : Finset V) := by
        intro ha
        rw [Finset.card_insert_of_mem ha] at hcard4
        have := (Finset.card_le_three : ({b, c, d} : Finset V).card ≤ 3)
        omega
      have hb : b ∉ ({c, d} : Finset V) := by
        intro hb
        have hab : a ∉ ({b, c, d} : Finset V) := ha
        rw [Finset.card_insert_of_notMem hab, Finset.card_insert_of_mem hb] at hcard4
        have := (Finset.card_le_two : ({c, d} : Finset V).card ≤ 2)
        omega
      have hc : c ≠ d := by
        intro hcd
        subst d
        have hfour : ({a, b, c} : Finset V).card = 4 := by simpa using hcard4
        have hle : ({a, b, c} : Finset V).card ≤ 3 := Finset.card_le_three
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
      exact ⟨ha.1, ha.2.1, ha.2.2, hb.1, hb.2, hc⟩
    have hX : X = {a, b} := by
      simp [X, hx, Sym2.toFinset_mk_eq]
    have hY : Y = {c, d} := by
      simp [Y, hy, Sym2.toFinset_mk_eq]
    have hX2 : X.card = 2 := by simp [hX, hpw.1]
    have hY2 : Y.card = 2 := by simp [hY, hpw.2.2.2.2.2]
    have hdisj : Disjoint X Y := by
      rw [Finset.disjoint_left]
      rw [hX, hY]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      grind
    have hXY : X ∪ Y = {a, b, c, d} := by
      ext z
      simp only [hX, hY, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hTX : X ⊆ T := by
      change p.2.1.toFinset ⊆ p.1
      rw [← hkey]
      exact Finset.subset_union_right
    have huE : u ∈ E := by
      have : u ∈ E ∪ X := by simpa [E, X, T, hkey] using huT
      exact (Finset.mem_union.mp this).resolve_right (by simpa [X] using huX)
    have hTE : E ⊆ T := by
      change e.toFinset ⊆ p.1
      rw [← hkey]
      exact Finset.subset_union_left
    have hTuX : T = insert u X := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        by_cases hzx : z ∈ X
        · simp [hzx]
        · have hcardXz : (insert z X).card = 3 := by simp [hzx, hX2]
          have hsub : insert z X ⊆ T := by
            intro q hq
            simp only [Finset.mem_insert] at hq
            rcases hq with rfl | hq
            · exact hz
            · exact hTX hq
          have heq : insert z X = T := Finset.eq_of_subset_of_card_le hsub (by omega)
          have huins : u ∈ insert z X := by rw [heq]; exact huT
          rcases Finset.mem_insert.mp huins with huz | huX'
          · simpa [huz]
          · have huXnot : u ∉ X := by simpa [X] using huX
            exact False.elim (huXnot huX')
      · have huX' : u ∉ X := by simpa [X] using huX
        rw [Finset.card_insert_of_notMem huX', hX2, hT3]
    have hTXY : T ⊆ X ∪ Y := by
      rw [hTuX]
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Finset.mem_union_right X (by simpa [Y] using huY)
      · exact Finset.mem_union_left Y hz
    have hEYinter : E ∩ Y = {u} := by
      ext z
      constructor
      · intro hz
        have hzE := (Finset.mem_inter.mp hz).1
        have hzY := (Finset.mem_inter.mp hz).2
        have hzT : z ∈ T := hTE hzE
        rw [hTuX] at hzT
        rcases Finset.mem_insert.mp hzT with rfl | hzX
        · simp
        · exact False.elim ((Finset.disjoint_left.mp hdisj) hzX hzY)
      · intro hz
        have : z = u := by simpa using hz
        subst z
        exact Finset.mem_inter.mpr ⟨huE, by simpa [Y] using huY⟩
    have hN3 : N.card = 3 := by
      have hun := Finset.card_union_add_card_inter E Y
      have hinter : (E ∩ Y).card = 1 := by simp [hEYinter]
      simp only [N]
      omega
    have hNsub : N ⊆ ({a, b, c, d} : Finset V) := by
      rw [← hXY]
      exact Finset.union_subset (hTE.trans hTXY) (Finset.subset_union_right)
    have hNc : N ∈ G.cliqueFinset 3 := by
      rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
      refine ⟨hclq.1.subset ?_, hN3⟩
      intro z hz
      exact hNsub hz
    have heN : e ∈ triEdges N := by
      rw [triEdges, Finset.mem_filter]
      refine ⟨?_, heND⟩
      rw [Finset.mem_sym2_iff]
      intro z hz
      exact Finset.mem_union_left Y (by simpa [E] using (Sym2.mem_toFinset.mpr hz))
    have hyND : ¬ p.2.2.IsDiag := by
      rw [hy, Sym2.mk_isDiag_iff]
      exact hpw.2.2.2.2.2
    have hyN : p.2.2 ∈ triEdges N := by
      rw [triEdges, Finset.mem_filter]
      refine ⟨?_, hyND⟩
      rw [Finset.mem_sym2_iff]
      intro z hz
      exact Finset.mem_union_right E (by simpa [Y] using (Sym2.mem_toFinset.mpr hz))
    have hene : e ≠ p.2.2 := by
      intro heq
      have hEY : E = Y := by simp [E, Y, heq]
      have : N.card = 2 := by simp [N, hEY, hY2]
      omega
    have hyErase : p.2.2 ∈ (triEdges N).erase e := Finset.mem_erase.mpr ⟨hene.symm, hyN⟩
    have hex : ∃ z, z ∈ E ∧ z ∉ Y := by
      by_contra hn
      push_neg at hn
      have hsub : E ⊆ Y := hn
      have hle := Finset.card_le_card hsub
      have heq : E = Y := Finset.eq_of_subset_of_card_le hsub (by omega)
      rw [heq] at hEYinter
      have : Y.card = 1 := by
        calc
          Y.card = (Y ∩ Y).card := by simp
          _ = ({u} : Finset V).card := congrArg Finset.card hEYinter
          _ = 1 := by simp
      omega
    obtain ⟨v, hvE, hvY⟩ := hex
    have hvT : v ∈ T := hTE hvE
    have hvX : v ∈ X := by
      rw [hTuX] at hvT
      rcases Finset.mem_insert.mp hvT with rfl | hvX
      · exact False.elim (hvY (by simpa [Y] using huY))
      · exact hvX
    refine ⟨by simpa [N, E, Y] using hNc, by simpa [N] using heN,
      by simpa [N] using hyErase, hk', v, ?_, ?_, ?_⟩
    · exact Finset.mem_union_left Y hvE
    · simpa [X] using (Sym2.mem_toFinset.mp hvX)
    · simpa [Y, Sym2.mem_toFinset] using hvY
  · -- g_inv: σ∘σ = id on configs (the key fact `t = e ∪ e''`)
    intro p hp
    simp only [hCfgdef, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      true_and] at hp
    obtain ⟨htc, hetri, herase, _hk, _hap⟩ := hp
    have ht3 : p.1.card = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htc).card_eq
    -- both edges' vertices lie in the triangle p.1
    have hsube : e.toFinset ⊆ p.1 := by
      intro z hz
      rw [Sym2.mem_toFinset] at hz
      have h1 : e ∈ p.1.sym2 := by
        rw [triEdges, Finset.mem_filter] at hetri; exact hetri.1
      exact (Finset.mem_sym2_iff.mp h1) z hz
    have hsube'' : p.2.1.toFinset ⊆ p.1 := by
      intro z hz
      rw [Sym2.mem_toFinset] at hz
      have h1 : p.2.1 ∈ p.1.sym2 := by
        have := (Finset.mem_erase.mp herase).2
        rw [triEdges, Finset.mem_filter] at this; exact this.1
      exact (Finset.mem_sym2_iff.mp h1) z hz
    have hsub : e.toFinset ∪ p.2.1.toFinset ⊆ p.1 := Finset.union_subset hsube hsube''
    -- the two edges are distinct, so their vertex-union has 3 elements = |p.1|
    have hne : e ≠ p.2.1 := (Finset.mem_erase.mp herase).1.symm
    have hcard3 : (e.toFinset ∪ p.2.1.toFinset).card = 3 := by
      have hec : e.toFinset.card = 2 := by
        induction e using Sym2.inductionOn with | _ a b =>
          rw [triEdges, Finset.mem_filter, Sym2.mk_isDiag_iff] at hetri
          rw [Sym2.toFinset_mk_eq]; simp [Sym2.mk_isDiag_iff.not.mp (by simpa using hetri.2)]
      have hpc : p.2.1.toFinset.card = 2 := by
        induction h : p.2.1 using Sym2.inductionOn with | _ a b =>
          have hd : ¬ (Sym2.mk (a,b)).IsDiag := by
            have := (Finset.mem_erase.mp herase).2
            rw [triEdges, Finset.mem_filter, h] at this; exact this.2
          simp [h, Sym2.toFinset_mk_eq, Sym2.mk_isDiag_iff.not.mp hd]
      -- union ⊆ p.1 (card ≤ 3); the union has ≥ card(e.toFinset)=2 and adds the third vertex.
      have hle : (e.toFinset ∪ p.2.1.toFinset).card ≤ 3 := by
        calc (e.toFinset ∪ p.2.1.toFinset).card ≤ p.1.card := Finset.card_le_card hsub
          _ = 3 := ht3
      have hinter : (e.toFinset ∩ p.2.1.toFinset).card ≤ 1 := by
        by_contra hh
        push_neg at hh
        have : e.toFinset = p.2.1.toFinset := by
          apply Finset.eq_of_subset_of_card_le
          · intro z hz
            have : (e.toFinset ∩ p.2.1.toFinset) = e.toFinset := by
              apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_left)
              omega
            rw [← this] at hz; exact (Finset.mem_inter.mp hz).2
          · omega
        exact hne (by
          exact Sym2.ext fun z => by simpa [Sym2.mem_toFinset] using Finset.ext_iff.mp this z)
      have hun := Finset.card_union_add_card_inter e.toFinset p.2.1.toFinset
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [ht3, hcard3])
    apply Prod.ext
    · exact heq
    · rfl


/-- **Heavy nucleus (coverage).** [DELEGATED] For a fixed edge `e`, the total K₄-transfer through
`e` — summed over all triangles containing `e` — equals `2·(Tₑ·wΔ − 1)`. This is flow conservation
at edge-node `e` together with source saturation (`source_saturated`, `value_eq_source_sum`). -/
theorem triWeight_transfer_eq (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
        (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0)
      = 2 * ((triThrough G e : ℝ) * wΔ - 1) := by
  -- Combinatorial reindexing (the transfer through `e` equals twice the net K₄-flow at `e`):
  -- summing over triangles `t ∋ e`, their edges `e''`, and 4th vertices, the pair
  -- `(c,d) ↦ (d,c)` is an involution under which the two off-`e` terms are skew-negatives (cancel)
  -- and the on-`e` term `f(edge e)(edge s(c,d))` doubles. [DELEGATED — pure flow/K₄ combinatorics.]
  have hkey : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
      (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
        (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
          F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0)
      = 2 * ∑ e' : Sym2 V, F.f (Ghat.edge e) (Ghat.edge e') := by
    have hsplit : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
        (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
          (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0)
        = (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
            (∑ e' : Sym2 V, if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
              F.f (Ghat.edge e) (Ghat.edge e') else 0) else 0)
          + (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
            (∑ e'' ∈ (triEdges t).erase e, ∑ e' : Sym2 V,
              if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
                F.f (Ghat.edge e'') (Ghat.edge e') else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      by_cases het : e ∈ triEdges t
      · rw [if_pos het, if_pos het, if_pos het,
          ← Finset.add_sum_erase (triEdges t) _ het]
      · rw [if_neg het, if_neg het, if_neg het, add_zero]
    rw [hsplit, hkey_double G wΔ F e, hkey_cancel G wΔ F e, add_zero]
  rw [hkey, edgeNode_flow_sum G wΔ hbal F hF he]

/-- **(I) Coverage (TARGET).** The reconstructed weights cover every edge exactly once:
`∑_{t ∋ e} triWeight t = 1`. Reduces (locally) to the conservation nucleus `triWeight_transfer_eq`:
`∑_{t∋e} wΔ = Tₑ·wΔ` and the transfer sum is `2(Tₑ·wΔ − 1)`, so the total is `Tₑ·wΔ − (Tₑ·wΔ − 1) = 1`. -/
theorem triWeight_coverage (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then triWeight G wΔ F t else 0) = 1 := by
  -- unfold `triWeight` under the (true) triangle gate
  have hrw : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then triWeight G wΔ F t else 0)
      = ∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then
          (wΔ - (1 / 2) * (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
            (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
              F.f (Ghat.edge e'') (Ghat.edge e') else 0))) else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [triWeight, if_pos ht]
  rw [hrw]
  -- split `if c then (wΔ − X) else 0` into the `wΔ` part and the transfer part
  have hsplit : ∀ t : Finset V,
      (if e ∈ triEdges t then
        (wΔ - (1 / 2) * (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
          (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
            F.f (Ghat.edge e'') (Ghat.edge e') else 0))) else 0)
      = (if e ∈ triEdges t then wΔ else 0)
        - (1 / 2) * (if e ∈ triEdges t then
            (∑ e'' ∈ triEdges t, ∑ e' : Sym2 V,
              (if K4pair G e'' e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e'' then
                F.f (Ghat.edge e'') (Ghat.edge e') else 0)) else 0) := by
    intro t; by_cases hc : e ∈ triEdges t <;> simp [hc]
  rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [triWeight_transfer_eq G wΔ hwΔ hbal F hF e he]
  -- `∑ t, if e ∈ triEdges t then wΔ else 0 = Tₑ · wΔ`
  have hA : (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then wΔ else 0)
      = (triThrough G e : ℝ) * wΔ := by
    rw [← Finset.sum_filter, Finset.sum_const, triThrough, nsmul_eq_mul]
  rw [hA]; ring

/-- **(I) Nonnegativity (TARGET).** Each reconstructed weight is nonnegative: the K₄-arc capacity
`cc` bounds each transfer so no triangle weight drops below `0`. -/
theorem triWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hmd2 : 2 ≤ G.minDegree)
    (F : RouteB.Flow (drossNet G wΔ))
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False)
    (t : Finset V) :
    0 ≤ triWeight G wΔ F t := by
  rw [triWeight]
  split_ifs with ht
  · -- `t` is a triangle: bound the transfer by the heavy nucleus, then `wΔ − (1/2)·2wΔ = 0 ≤ …`.
    have hb := triWeight_transfer_le G wΔ hwΔ hmd2 F hNoHDT t ht
    linarith
  · exact le_refl 0

theorem decomp_of_maxflowM (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hmd2 : 2 ≤ G.minDegree)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (F : RouteB.Flow (drossNet G wΔ)) (hF : F.value = demand G wΔ)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G :=
  ⟨triWeight G wΔ F, triWeight_nonneg G wΔ hwΔ hmd2 F hNoHDT,
    fun e he => triWeight_coverage G wΔ hwΔ hbal F hF e he⟩


/-- For an edge `cd`, the rooted-K₄ pair condition with `uv` (`u~v`) reduces to `c,d` being
common neighbours of `u` and `v`. -/
theorem k4pair_edge_iff (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    {c d : V} (hcd : G.Adj c d) :
    K4pair G (s(u, v)) (s(c, d)) ↔
      (c ∈ G.neighborFinset u ∩ G.neighborFinset v ∧ d ∈ G.neighborFinset u ∩ G.neighborFinset v) := by
  rw [k4pair_iff_clique, SimpleGraph.isNClique_iff]
  simp only [Finset.mem_inter, mem_neighborFinset]
  constructor
  · rintro ⟨hcl, hcard⟩
    obtain ⟨_, hac, had, hbc, hbd, _⟩ := card4_pairwise hcard
    exact ⟨⟨hcl (by simp) (by simp) hac, hcl (by simp) (by simp) hbc⟩,
      hcl (by simp) (by simp) had, hcl (by simp) (by simp) hbd⟩
  · rintro ⟨⟨huc, hvc⟩, hud, hvd⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | assumption
          | (exact huv) | exact huv.symm
          | exact huc | exact huc.symm | exact hud | exact hud.symm
          | exact hvc | exact hvc.symm | exact hvd | exact hvd.symm
          | exact hcd | exact hcd.symm
    · have : u ≠ v := huv.ne
      have : u ≠ c := huc.ne
      have : u ≠ d := hud.ne
      have : v ≠ c := hvc.ne
      have : v ≠ d := hvd.ne
      have : c ≠ d := hcd.ne
      rw [show ({u, v, c, d} : Finset V).card = 4 from by
        rw [Finset.card_insert_of_notMem (by simp_all), Finset.card_insert_of_notMem (by simp_all),
          Finset.card_insert_of_notMem (by simp_all), Finset.card_singleton]]

/-- **Bridge #K₄-partners = numK4Through.** For an edge `uv`, the number of edges forming a
rooted-K₄ pair with it equals `numK4Through G u v` (Spine's K₄ count, bounded below by A6). -/
theorem k4pair_count_eq (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    (G.edgeFinset.filter (fun e' => K4pair G (s(u, v)) e')).card = numK4Through G u v := by
  rw [numK4Through]
  congr 1
  apply Finset.filter_congr
  intro e' he'
  rw [SimpleGraph.mem_edgeFinset] at he'
  induction e' using Sym2.inductionOn with
  | hf c d =>
    rw [SimpleGraph.mem_edgeSet] at he'
    rw [k4pair_edge_iff G huv he']
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]

/-- **Bridge T_e = codeg.** The number of triangles through an edge `uv` equals the number of
common neighbours of `u` and `v` (Dross's `Tₑ`). This links `triThrough` to A6 (`Spine`). -/
theorem triThrough_edge (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) :
    triThrough G (s(u, v)) = codeg G u v := by
  rw [triThrough, codeg]
  symm
  have hnuv : u ≠ v := huv.ne
  apply Finset.card_bij (fun w _ => ({u, v, w} : Finset V))
  · -- maps into the triangle set
    intro w hw
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
    obtain ⟨hwu, hwv⟩ := hw
    rw [Finset.mem_filter, mem_cliqueFinset_iff]
    refine ⟨is3Clique_iff.2 ⟨u, v, w, huv, hwu, hwv, rfl⟩, ?_⟩
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.isDiag_iff_proj_eq]
    exact ⟨⟨by simp, by simp⟩, hnuv⟩
  · -- injective
    intro w1 hw1 w2 hw2 heq
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw1 hw2
    have h1 : w1 ∈ ({u, v, w2} : Finset V) := heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h | h
    · exact absurd h.symm hw1.1.ne
    · exact absurd h.symm hw1.2.ne
    · exact h
  · -- surjective
    intro t ht
    rw [Finset.mem_filter, mem_cliqueFinset_iff] at ht
    obtain ⟨hclique, hedge⟩ := ht
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff] at hedge
    obtain ⟨⟨hut, hvt⟩, _⟩ := hedge
    have hsub : ({u, v} : Finset V) ⊆ t := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hc2 : ({u, v} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hnuv]), Finset.card_singleton]
    have hc1 : (t \ ({u, v} : Finset V)).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hclique.card_eq, hc2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
    have hwt : w ∈ t := (Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)).1
    have hwnuv : w ∉ ({u, v} : Finset V) := (Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)).2
    have hwu : w ≠ u := fun h => hwnuv (by simp [h])
    have hwv : w ≠ v := fun h => hwnuv (by simp [h])
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact ⟨(hclique.1 hut hwt (Ne.symm hwu)), (hclique.1 hvt hwt (Ne.symm hwv))⟩
    · -- {u,v,w} = t
      have : t = insert u (insert v {w}) := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          by_cases hxuv : x ∈ ({u, v} : Finset V)
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv ⊢; tauto
          · have : x ∈ t \ ({u, v} : Finset V) := Finset.mem_sdiff.mpr ⟨hx, hxuv⟩
            rw [hw, Finset.mem_singleton] at this; simp [this]
        · rw [hclique.card_eq]
          have e1 := Finset.card_insert_le u (insert v {w} : Finset V)
          have e2 := Finset.card_insert_le v ({w} : Finset V)
          simp only [Finset.card_singleton] at e2
          omega
      exact this.symm

/-- Edges of `G` whose node lies on the source side `A` of the cut. -/
def cutA (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (C : RouteB.Cut (drossNet G wΔ)) :
    Finset (Sym2 V) := G.edgeFinset.filter (fun e => Ghat.edge e ∈ C.S)

/-- Edges of `G` whose node lies on the sink side `B` of the cut. -/
def cutB (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) (C : RouteB.Cut (drossNet G wΔ)) :
    Finset (Sym2 V) := G.edgeFinset.filter (fun e => Ghat.edge e ∉ C.S)

/-- **Capacity decomposition (lower bound).** The capacity of any s–t cut is at least the sum of
its three arc families: source→B, A→sink, and the K₄ arcs from A to B. (Non-edge nodes and the
`src→snk` arc only add nonnegative slack, hence a lower bound.) -/
theorem capacity_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ)
    (C : RouteB.Cut (drossNet G wΔ)) :
    (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
      + (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
      + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
          if K4pair G e e' then max (cc G wΔ) 0 else 0)
      ≤ C.capacity := by
  have hnn : ∀ u v, 0 ≤ dcap G wΔ u v := (drossNet G wΔ).capNonneg
  have hinj : ∀ a ∈ cutA G wΔ C, ∀ b ∈ cutA G wΔ C, Ghat.edge a = Ghat.edge b → a = b :=
    fun a _ b _ hab => by injection hab
  have hinjB : ∀ a ∈ cutB G wΔ C, ∀ b ∈ cutB G wΔ C, Ghat.edge a = Ghat.edge b → a = b :=
    fun a _ b _ hab => by injection hab
  -- S0 ⊆ C.S : source node plus the A-side edge nodes
  have hsrc_notin : Ghat.src ∉ (cutA G wΔ C).image Ghat.edge := by simp
  have hsub : insert Ghat.src ((cutA G wΔ C).image Ghat.edge) ⊆ C.S := by
    rw [Finset.insert_subset_iff]
    refine ⟨C.hs, fun x hx => ?_⟩
    rw [Finset.mem_image] at hx; obtain ⟨e, he, rfl⟩ := hx
    exact (Finset.mem_filter.mp he).2
  -- capacity ≥ sum over S0
  have step1 : ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
      ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v ≤ C.capacity :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun u _ _ => Finset.sum_nonneg (fun v _ => hnn u v))
  -- split the S0-sum into the source row and the A-edge rows
  have hS0 : ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
        ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v
      = (∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v)
        + ∑ e ∈ cutA G wΔ C, ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v := by
    rw [Finset.sum_insert hsrc_notin, Finset.sum_image hinj]
  -- source row ≥ source→B sum
  have hsubB : (cutB G wΔ C).image Ghat.edge ⊆ Finset.univ \ C.S := by
    intro x hx
    rw [Finset.mem_image] at hx; obtain ⟨e, he, rfl⟩ := hx
    rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  have hsrcrow : ∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0
      ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v := by
    calc ∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0
        = ∑ e ∈ cutB G wΔ C, dcap G wΔ Ghat.src (Ghat.edge e) := rfl
      _ = ∑ v ∈ (cutB G wΔ C).image Ghat.edge, dcap G wΔ Ghat.src v :=
          (Finset.sum_image hinjB).symm
      _ ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun v _ _ => hnn _ _)
  -- each A-edge row ≥ (sink term) + (K₄ arcs to B)
  have hedgerow : ∀ e ∈ cutA G wΔ C,
      max (1 - (triThrough G e : ℝ) * wΔ) 0
        + (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
      ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v := by
    intro e _
    have hsnk_notin : Ghat.snk ∉ (cutB G wΔ C).image Ghat.edge := by simp
    have hunion_sub : insert Ghat.snk ((cutB G wΔ C).image Ghat.edge) ⊆ Finset.univ \ C.S := by
      rw [Finset.insert_subset_iff]
      refine ⟨by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, C.ht⟩, ?_⟩
      intro x hx
      rw [Finset.mem_image] at hx; obtain ⟨e', he', rfl⟩ := hx
      rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
    calc max (1 - (triThrough G e : ℝ) * wΔ) 0
            + (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = dcap G wΔ (Ghat.edge e) Ghat.snk
            + ∑ e' ∈ cutB G wΔ C, dcap G wΔ (Ghat.edge e) (Ghat.edge e') := rfl
      _ = dcap G wΔ (Ghat.edge e) Ghat.snk
            + ∑ v ∈ (cutB G wΔ C).image Ghat.edge, dcap G wΔ (Ghat.edge e) v := by
          rw [Finset.sum_image hinjB]
      _ = ∑ v ∈ insert Ghat.snk ((cutB G wΔ C).image Ghat.edge), dcap G wΔ (Ghat.edge e) v := by
          rw [Finset.sum_insert hsnk_notin]
      _ ≤ ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v :=
          Finset.sum_le_sum_of_subset_of_nonneg hunion_sub (fun v _ _ => hnn _ _)
  calc (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
            if K4pair G e e' then max (cc G wΔ) 0 else 0)
      = (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + ∑ e ∈ cutA G wΔ C, (max (1 - (triThrough G e : ℝ) * wΔ) 0
            + ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0) := by
        rw [Finset.sum_add_distrib]; ring
    _ ≤ (∑ v ∈ Finset.univ \ C.S, dcap G wΔ Ghat.src v)
        + ∑ e ∈ cutA G wΔ C, ∑ v ∈ Finset.univ \ C.S, dcap G wΔ (Ghat.edge e) v :=
        add_le_add hsrcrow (Finset.sum_le_sum hedgerow)
    _ = ∑ u ∈ insert Ghat.src ((cutA G wΔ C).image Ghat.edge),
          ∑ v ∈ Finset.univ \ C.S, dcap G wΔ u v := hS0.symm
    _ ≤ C.capacity := step1

/-- **K₄ arcs crossing the cut.** The number of `B`-side K₄-partners of an `A`-side edge `uv` is
at least `numK4Through G u v − |A|` (all its `numK4Through` partners lie in `A ⊔ B`, at most `|A|`
in `A`). Combined with A6 this lower-bounds the K₄-arc contribution to the cut. -/
theorem k4count_cutB_ge (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (wΔ : ℝ) (C : RouteB.Cut (drossNet G wΔ)) :
    (numK4Through G u v : ℝ) - ((cutA G wΔ C).card : ℝ)
      ≤ (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
  -- partners over edgeFinset split disjointly across cutA and cutB
  have hpart : G.edgeFinset.filter (fun e' => K4pair G (s(u, v)) e')
      = (cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')
        ∪ (cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e') := by
    unfold cutA cutB
    rw [Finset.filter_filter, Finset.filter_filter, ← Finset.filter_or]
    apply Finset.filter_congr
    intro e' _
    tauto
  have hdisj : Disjoint ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e'))
      ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter, cutA, Finset.mem_filter] at he
    rw [Finset.mem_filter, cutB, Finset.mem_filter] at he'
    exact he'.1.2 he.1.2
  have hcard : numK4Through G u v
      = ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card
        + ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card := by
    rw [← k4pair_count_eq G huv, hpart, Finset.card_union_of_disjoint hdisj]
  have hAle : ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card ≤ (cutA G wΔ C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have : (numK4Through G u v : ℝ)
      = (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ)
        + (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
    rw [hcard]; push_cast; ring
  have hAle' : (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ)
      ≤ ((cutA G wΔ C).card : ℝ) := by exact_mod_cast hAle
  linarith

/-- Symmetric count: a `B`-side edge has at least `numK4Through − |B|` K₄-partners in `A`. -/
theorem k4count_cutA_ge (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (wΔ : ℝ) (C : RouteB.Cut (drossNet G wΔ)) :
    (numK4Through G u v : ℝ) - ((cutB G wΔ C).card : ℝ)
      ≤ (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
  have hpart : G.edgeFinset.filter (fun e' => K4pair G (s(u, v)) e')
      = (cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')
        ∪ (cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e') := by
    unfold cutA cutB
    rw [Finset.filter_filter, Finset.filter_filter, ← Finset.filter_or]
    apply Finset.filter_congr
    intro e' _
    tauto
  have hdisj : Disjoint ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e'))
      ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter, cutA, Finset.mem_filter] at he
    rw [Finset.mem_filter, cutB, Finset.mem_filter] at he'
    exact he'.1.2 he.1.2
  have hcard : numK4Through G u v
      = ((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card
        + ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card := by
    rw [← k4pair_count_eq G huv, hpart, Finset.card_union_of_disjoint hdisj]
  have hBle : ((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card ≤ (cutB G wΔ C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hnum : (numK4Through G u v : ℝ)
      = (((cutA G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ)
        + (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ) := by
    rw [hcard]; push_cast; ring
  have hBle' : (((cutB G wΔ C).filter (fun e' => K4pair G (s(u, v)) e')).card : ℝ)
      ≤ ((cutB G wΔ C).card : ℝ) := by exact_mod_cast hBle
  linarith

/-- **Convex averaging (finite Jensen for `T ↦ T(T − c₀)`).** For a nonempty finite `A`, the sum
of `T e (T e − c₀)` dominates `|A|` times `T_A (T_A − c₀)` with `T_A` the average. (Proved via
Cauchy–Schwarz; the linear part cancels exactly.) -/
theorem convex_avg {α : Type*} {A : Finset α} (hA : A.Nonempty) (T : α → ℝ) (c₀ : ℝ) :
    (A.card : ℝ) * ((∑ e ∈ A, T e / A.card) * ((∑ e ∈ A, T e / A.card) - c₀))
      ≤ ∑ e ∈ A, T e * (T e - c₀) := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast (Finset.card_pos.mpr hA)
  have havg_sq := (sum_div_card_sq_le_sum_sq_div_card (s := A) (f := T))
  have havg : (∑ e ∈ A, T e / A.card) = (∑ e ∈ A, T e) / A.card := by rw [Finset.sum_div]
  have hlin : (A.card : ℝ) * ((∑ e ∈ A, T e) / A.card) = ∑ e ∈ A, T e := by field_simp
  have hquad : (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2) ≤ ∑ e ∈ A, T e ^ 2 := by
    calc _ ≤ (A.card : ℝ) * ((∑ e ∈ A, T e ^ 2) / A.card) :=
            mul_le_mul_of_nonneg_left havg_sq hcard.le
      _ = _ := by field_simp
  have hlhs : (A.card : ℝ) * ((∑ e ∈ A, T e / A.card) * ((∑ e ∈ A, T e / A.card) - c₀))
      = (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2) - c₀ * (∑ e ∈ A, T e) := by
    rw [havg]
    calc _ = (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2)
              - c₀ * ((A.card : ℝ) * ((∑ e ∈ A, T e) / A.card)) := by ring
      _ = _ := by rw [hlin]
  have hexpand : (∑ e ∈ A, T e * (T e - c₀)) = (∑ e ∈ A, T e ^ 2) - c₀ * (∑ e ∈ A, T e) := by
    simp_rw [mul_sub, mul_comm (T _) c₀, ← pow_two]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlhs, hexpand]; linarith

/-- **Codegree lower bound.** In a dense graph (`δ ≥ (9/10)n`), adjacent vertices have at least
`(8/10)n` common neighbours — Dross's `Tₑ ≥ n − 2δn` bound (`δ = 1/10`). -/
theorem codeg_ge_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (u v : V) :
    8 * Fintype.card V ≤ 10 * codeg G u v := by
  have hdu : 9 * Fintype.card V ≤ 10 * G.degree u :=
    le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree u))
  have hdv : 9 * Fintype.card V ≤ 10 * G.degree v :=
    le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree v))
  have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
    le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
  have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
  rw [codeg]
  omega

/-- **A6 in real form, per edge.** For an edge `uv`, the K₄ count through it dominates
`Tₑ(Tₑ − n/10)/2` (`Tₑ = triThrough`). Combines A6 (`k4_lower_bound`), `triThrough_edge`, and
the codegree bound, with the Nat→ℝ casting justified by `codeg ≥ d`. -/
theorem numK4_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) {u v : V} (huv : G.Adj u v) :
    (triThrough G (s(u, v)) : ℝ) * ((triThrough G (s(u, v)) : ℝ) - (Fintype.card V : ℝ) / 10)
      ≤ 2 * (numK4Through G u v : ℝ) := by
  set d := Fintype.card V - G.minDegree with hd
  have hddef : ∀ w, Fintype.card V - G.degree w ≤ d :=
    fun w => Nat.sub_le_sub_left (G.minDegree_le_degree w) _
  have hA6 := k4_lower_bound G huv d hddef
  have hcodeg := codeg_ge_of_dense G h u v
  have hmc : G.minDegree ≤ Fintype.card V :=
    le_trans (G.minDegree_le_degree u)
      (by rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_univ _)
  have hd_le : 10 * d ≤ Fintype.card V := by omega
  have hcd : d ≤ codeg G u v := by omega
  rw [triThrough_edge G huv]
  rw [← Nat.cast_le (α := ℝ)] at hA6
  push_cast [Nat.cast_sub hcd] at hA6
  have hd_real : (d : ℝ) ≤ (Fintype.card V : ℝ) / 10 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    calc (d : ℝ) * 10 = ((10 * d : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Fintype.card V : ℝ) := by exact_mod_cast hd_le
  have hnn : (0 : ℝ) ≤ (codeg G u v : ℝ) := by positivity
  nlinarith [hA6, mul_nonneg hnn (show (0 : ℝ) ≤ (Fintype.card V : ℝ) / 10 - d by linarith)]

/-- **A6 in real form, per edge, with an arbitrary deficiency `δ`.** Generalises `numK4_lower`:
for any `δ` bounding the max non-degree ratio (`n − minDegree ≤ δ·n`), `Tₑ(Tₑ − δn) ≤ 2·numK4Through`.
Used with the tighter `δ = 1/10 − ε` in the ε-reparametrisation. -/
theorem numK4_lower_delta (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (δ : ℝ)
    (hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * Fintype.card V)
    {u v : V} (huv : G.Adj u v) :
    (triThrough G (s(u, v)) : ℝ) * ((triThrough G (s(u, v)) : ℝ) - δ * (Fintype.card V : ℝ))
      ≤ 2 * (numK4Through G u v : ℝ) := by
  set d := Fintype.card V - G.minDegree with hd
  have hddef : ∀ w, Fintype.card V - G.degree w ≤ d :=
    fun w => Nat.sub_le_sub_left (G.minDegree_le_degree w) _
  have hA6 := k4_lower_bound G huv d hddef
  have hcodeg := codeg_ge_of_dense G h u v
  have hmc : G.minDegree ≤ Fintype.card V :=
    le_trans (G.minDegree_le_degree u)
      (by rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_univ _)
  have hd_le : 10 * d ≤ Fintype.card V := by omega
  have hcd : d ≤ codeg G u v := by omega
  rw [triThrough_edge G huv]
  rw [← Nat.cast_le (α := ℝ)] at hA6
  push_cast [Nat.cast_sub hcd] at hA6
  have hd_real : (d : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
    rw [hd, Nat.cast_sub hmc]; exact hδ_deg
  have hnn : (0 : ℝ) ≤ (codeg G u v : ℝ) := by positivity
  nlinarith [hA6, mul_nonneg hnn (show (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) - d by linarith)]

/-- **Per-edge `Tₑ` bounds.** In a dense graph, every edge lies in between `(8/10)n` and `n`
triangles. -/
theorem triThrough_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) {u v : V} (huv : G.Adj u v) :
    (8 / 10) * (Fintype.card V : ℝ) ≤ (triThrough G (s(u, v)) : ℝ)
      ∧ (triThrough G (s(u, v)) : ℝ) ≤ (Fintype.card V : ℝ) := by
  rw [triThrough_edge G huv]
  refine ⟨?_, ?_⟩
  · have hc : (8 : ℝ) * Fintype.card V ≤ 10 * codeg G u v := by
      exact_mod_cast codeg_ge_of_dense G h u v
    linarith
  · have hc : codeg G u v ≤ Fintype.card V := by
      rw [codeg]; exact le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
    exact_mod_cast hc

/-- **Per-edge `Tₑ` bounds with an arbitrary deficiency `δ`.** `Tₑ ∈ [(1−2δ)n, n]` from
`codeg ≥ 2·minDegree − n ≥ (1−2δ)n`. Used in the ε-reparametrisation (tighter than `0.8n`). -/
theorem triThrough_bounds_delta (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)
    (hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * Fintype.card V)
    {u v : V} (huv : G.Adj u v) :
    (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G (s(u, v)) : ℝ)
      ∧ (triThrough G (s(u, v)) : ℝ) ≤ (Fintype.card V : ℝ) := by
  rw [triThrough_edge G huv]
  refine ⟨?_, ?_⟩
  · have hie : G.degree u + G.degree v ≤ Fintype.card V + codeg G u v := by
      rw [codeg]
      have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
        le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
      have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
      omega
    have hdu : G.minDegree ≤ G.degree u := G.minDegree_le_degree u
    have hdv : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
    have hier : (G.degree u : ℝ) + G.degree v ≤ Fintype.card V + codeg G u v := by
      exact_mod_cast hie
    have hdur : (G.minDegree : ℝ) ≤ G.degree u := by exact_mod_cast hdu
    have hdvr : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast hdv
    nlinarith [hier, hdur, hdvr, hδ_deg]
  · have hc : codeg G u v ≤ Fintype.card V := by
      rw [codeg]; exact le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
    exact_mod_cast hc

/-- **Dross (5)+(6) ⇒ (7)** (scalar). Chaining the two cut inequalities through `2k`, the constant
`2/c` term cancels and `2wΔ = c·(3n(1−δ)−3)` turns the `(2/c)·T·wΔ` terms into `(3n(1−δ)−3)·T`.
(Proved by Aristotle, gate-clean.) -/
theorem dross_5_6_to_7 (n m k T_A T_B c wΔ : ℝ) (hc : 0 < c) (hwΔ : 0 < wΔ)
    (hrel : 2 * wΔ = c * (3 * n * (1 - 1/10) - 3))
    (h5 : T_A * (T_A - (1/10) * n) + (2 / c) * (1 - T_A * wΔ) < 2 * k)
    (h6 : 2 * k < 2 * m - T_B * (T_B - (1/10) * n) + (2 / c) * (1 - T_B * wΔ)) :
    T_A * (T_A - (1/10) * n) - (3 * n * (1 - 1/10) - 3) * T_A
      < 2 * m - T_B * (T_B - (1/10) * n) - (3 * n * (1 - 1/10) - 3) * T_B := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hratio : 2 * wΔ / c = 3 * n * (1 - 1/10) - 3 :=
    (div_eq_iff hc0).2 (by simpa [mul_comm] using hrel)
  have hsub (x : ℝ) : (2 / c) * (1 - x * wΔ) = 2 / c - (3 * n * (1 - 1/10) - 3) * x := by
    rw [← hratio]; field_simp [hc0]
  rw [hsub T_A] at h5
  rw [hsub T_B] at h6
  linarith

/-- **Dross (3)+(4) ⇒ ⊥** (scalar core of the deficient-cut analysis, δ = 1/10). From the averaged
cut inequalities plus the triangle-free edge bound, a contradiction for `n ≥ 20`. (Proved by
Aristotle, gate-clean; the convex extremization is discharged by `nlinarith` with the box product
hints.) -/
theorem dross_3_4_to_false (n m k cc wΔ T_A T_B : ℝ)
    (hn : 20 ≤ n) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - 1/10) - 3))
    (hTA1 : (8/10) * n ≤ T_A) (hTA2 : T_A ≤ n)
    (hTB1 : (8/10) * n ≤ T_B) (hTB2 : T_B ≤ n)
    (mbound : 2 * m ≤ (1 - 1/10 + 2 * (1/10)^2) * n^2 + 4 + n - 6 * (1/10) * n)
    (ineq3 : cc * (T_A * (T_A - (1/10) * n) / 2 - k) < T_A * wΔ - 1)
    (ineq4 : cc * (T_B * (T_B - (1/10) * n) / 2 - (m - k)) < 1 - T_B * wΔ) :
    False := by
  have hprodA : 0 ≤ (n - T_A) * ((18/10) * n - 3 - T_A) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  have hprodB : 0 ≤ (T_B - (8/10) * n) * (T_B + (34/10) * n - 3) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  nlinarith

/-- **ε-robust scalar core** (Dross (3)+(4) ⇒ ⊥ with deficiency `δ < 1/10`). At `δ = 1/10` the
coefficient `1−11δ+10δ²` vanishes (K₂₁ integrality bites); for `δ < 1/10` it is `> 0`, giving a
`Θ((1/10−δ)n²)` margin that absorbs integer rounding. (Proved by Aristotle, gate-clean.) -/
theorem dross_3_4_to_false_eps (n m k cc wΔ T_A T_B δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1/10) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hn : 0 < n)
    (hTA1 : (1 - 2 * δ) * n ≤ T_A) (hTA2 : T_A ≤ n)
    (hTB1 : (1 - 2 * δ) * n ≤ T_B) (hTB2 : T_B ≤ n)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ^2) * n^2 + 4 + 2 * n - 6 * δ * n)
    (hbig : 4 + 2 * n - 12 * δ * n ≤ (1 - 11 * δ + 10 * δ^2) * n^2)
    (ineq3 : cc * (T_A * (T_A - δ * n) / 2 - k) < T_A * wΔ - 1)
    (ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (m - k)) < 1 - T_B * wΔ) :
    False := by
  have hcoef : 0 < 1 - 11 * δ + 10 * δ^2 := by
    nlinarith [mul_pos (show 0 < 1 - δ by linarith) (show 0 < 1 - 10 * δ by linarith)]
  have hn3 : 3 < (1 - 2 * δ) * n := by
    by_contra h
    have hle : (1 - 2 * δ) * n ≤ 3 := le_of_not_gt h
    nlinarith [mul_nonneg (show 0 ≤ n by linarith) (show 0 ≤ 3 - (1 - 2 * δ) * n by linarith),
      sq_nonneg (n - 2), sq_nonneg (δ * n - 1)]
  have hAleft : 0 ≤ n - T_A := by linarith
  have hAright : 0 ≤ 2 * (1 - δ) * n - 3 - T_A := by nlinarith
  have hAprod : 0 ≤ (n - T_A) * (2 * (1 - δ) * n - 3 - T_A) :=
    mul_nonneg hAleft hAright
  have hBleft : 0 ≤ T_B - (1 - 2 * δ) * n := by linarith
  have hBright : 0 ≤ T_B + (4 - 6 * δ) * n - 3 := by nlinarith
  have hBprod : 0 ≤ (T_B - (1 - 2 * δ) * n) * (T_B + (4 - 6 * δ) * n - 3) :=
    mul_nonneg hBleft hBright
  have hsum :
      cc * ((2 - 12 * δ + 12 * δ^2) * n^2 + 6 * δ * n - 2 * m) < 0 := by
    nlinarith [ineq3, ineq4, hAprod, hBprod]
  have height : (2 - 12 * δ + 12 * δ^2) * n^2 < 2 * m - 6 * δ * n := by
    nlinarith [mul_pos hcc (show 0 < 2 * m - 6 * δ * n - (2 - 12 * δ + 12 * δ^2) * n^2 by
      nlinarith [hsum])]
  nlinarith

/-- **Exact-threshold scalar core** (Dross (3)+(4) ⇒ ⊥ for the actual deficiency `δ ≤ 1/10`, using
the fine `+n` m-bound). Unlike the ε-version this needs **no** `hbig` hypothesis: the closing
inequality `4 + n − 12δn ≤ (1−11δ+10δ²)n²` is *provable* for `δ ∈ (0, 1/10]`, `n ≥ 20` — it
factors as `(n−20)/5 + (1−10δ)·n·(n(1−δ)−1.2)`, both summands `≥ 0` (the coefficient
`1−11δ+10δ²` vanishes at `δ = 1/10`, but the strict deficient-cut inequality still closes it). -/
theorem dross_3_4_to_false_exact (n m k cc wΔ T_A T_B δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/10) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hn : 20 ≤ n)
    (hTA1 : (1 - 2 * δ) * n ≤ T_A) (hTA2 : T_A ≤ n)
    (hTB1 : (1 - 2 * δ) * n ≤ T_B) (hTB2 : T_B ≤ n)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ^2) * n^2 + 4 + n - 6 * δ * n)
    (ineq3 : cc * (T_A * (T_A - δ * n) / 2 - k) < T_A * wΔ - 1)
    (ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (m - k)) < 1 - T_B * wΔ) :
    False := by
  have hnpos : (0:ℝ) ≤ n := by linarith
  have hδn_le : δ * n ≤ n / 10 := by
    have := mul_le_mul_of_nonneg_right hδ1 hnpos; linarith
  have hn3 : 3 < (1 - 2 * δ) * n := by nlinarith
  have hAleft : 0 ≤ n - T_A := by linarith
  have hAright : 0 ≤ 2 * (1 - δ) * n - 3 - T_A := by nlinarith
  have hAprod : 0 ≤ (n - T_A) * (2 * (1 - δ) * n - 3 - T_A) := mul_nonneg hAleft hAright
  have hBleft : 0 ≤ T_B - (1 - 2 * δ) * n := by linarith
  have hBright : 0 ≤ T_B + (4 - 6 * δ) * n - 3 := by nlinarith
  have hBprod : 0 ≤ (T_B - (1 - 2 * δ) * n) * (T_B + (4 - 6 * δ) * n - 3) :=
    mul_nonneg hBleft hBright
  have hsum : cc * ((2 - 12 * δ + 12 * δ^2) * n^2 + 6 * δ * n - 2 * m) < 0 := by
    nlinarith [ineq3, ineq4, hAprod, hBprod]
  have height : (2 - 12 * δ + 12 * δ^2) * n^2 < 2 * m - 6 * δ * n := by
    nlinarith [mul_pos hcc (show 0 < 2 * m - 6 * δ * n - (2 - 12 * δ + 12 * δ^2) * n^2 by
      nlinarith [hsum])]
  have hnd : (0:ℝ) ≤ n * (1 - δ) - 1.2 := by nlinarith [hδn_le, hn]
  have h10δ : (0:ℝ) ≤ 1 - 10 * δ := by linarith
  have hfac : (0:ℝ) ≤ (1 - 10 * δ) * n * (n * (1 - δ) - 1.2) :=
    mul_nonneg (mul_nonneg h10δ hnpos) hnd
  have hclose : 4 + n - 12 * δ * n ≤ (1 - 11 * δ + 10 * δ^2) * n^2 := by
    nlinarith [hfac, hn]
  nlinarith [height, mbound, hclose]

/-- **Deficient-cut finish** (convex averaging + scalar core). The two summed Dross inequalities
over the cut sides `A`, `B` (with per-edge `Tₑ ∈ [0.8n, n]`) contradict the triangle-free bound:
`convex_avg` on each side yields the averaged (3),(4), which `dross_3_4_to_false` refutes. (Proved
by Aristotle, gate-clean.) -/
theorem deficient_finish {α : Type*} [DecidableEq α] (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (T : α → ℝ) (n m cc wΔ : ℝ)
    (hn : 20 ≤ n) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - 1/10) - 3))
    (hcard : (A.card : ℝ) + (B.card : ℝ) = m)
    (hTA : ∀ e ∈ A, (8/10) * n ≤ T e ∧ T e ≤ n)
    (hTB : ∀ e ∈ B, (8/10) * n ≤ T e ∧ T e ≤ n)
    (mbound : 2 * m ≤ (1 - 1/10 + 2 * (1/10)^2) * n^2 + 4 + n - 6 * (1/10) * n)
    (ineq1 : cc * (∑ e ∈ A, (T e * (T e - (1/10) * n) / 2 - A.card)) < ∑ e ∈ A, (T e * wΔ - 1))
    (ineq2 : cc * (∑ e ∈ B, (T e * (T e - (1/10) * n) / 2 - B.card)) < ∑ e ∈ B, (1 - T e * wΔ)) :
    False := by
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBcard : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  set T_A := (∑ e ∈ A, T e) / A.card with hT_A_def
  set T_B := (∑ e ∈ B, T e) / B.card with hT_B_def
  have hTA_lower : (0.8 : ℝ) * n ≤ T_A := by
    have h : A.card • ((0.8 : ℝ) * n) ≤ ∑ e ∈ A, T e :=
      Finset.card_nsmul_le_sum A T ((0.8 : ℝ) * n) (fun e he => by linarith [(hTA e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (le_div_iff₀ hAcard).mpr h
  have hTA_upper : T_A ≤ n := by
    have h : ∑ e ∈ A, T e ≤ A.card • n :=
      Finset.sum_le_card_nsmul A T n (fun e he => (hTA e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (div_le_iff₀ hAcard).mpr h
  have hTB_lower : (0.8 : ℝ) * n ≤ T_B := by
    have h : B.card • ((0.8 : ℝ) * n) ≤ ∑ e ∈ B, T e :=
      Finset.card_nsmul_le_sum B T ((0.8 : ℝ) * n) (fun e he => by linarith [(hTB e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (le_div_iff₀ hBcard).mpr h
  have hTB_upper : T_B ≤ n := by
    have h : ∑ e ∈ B, T e ≤ B.card • n :=
      Finset.sum_le_card_nsmul B T n (fun e he => (hTB e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (div_le_iff₀ hBcard).mpr h
  have hunivA := convex_avg hA (fun e => T e) ((1/10) * n)
  have hunivB := convex_avg hB (fun e => T e) ((1/10) * n)
  rw [← Finset.sum_div] at hunivA hunivB
  have ineq1' : cc * ((∑ e ∈ A, T e * (T e - 1/10 * n) / 2) - (A.card : ℝ) * A.card) < (∑ e ∈ A, T e * wΔ) - A.card := by
    have lhs_eq : ∑ e ∈ A, (T e * (T e - 1/10 * n) / 2 - (A.card : ℝ)) =
        (∑ e ∈ A, T e * (T e - 1/10 * n) / 2) - A.card * A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ A, (T e * wΔ - 1) = (∑ e ∈ A, T e * wΔ) - A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [lhs_eq, rhs_eq] at ineq1
    exact ineq1
  have ineq2' : cc * ((∑ e ∈ B, T e * (T e - 1/10 * n) / 2) - (B.card : ℝ) * B.card) < (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
    have lhs_eq : ∑ e ∈ B, (T e * (T e - 1/10 * n) / 2 - (B.card : ℝ)) =
        (∑ e ∈ B, T e * (T e - 1/10 * n) / 2) - B.card * B.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ B, (1 - T e * wΔ) = (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
      rw [Finset.sum_sub_distrib]
    rw [lhs_eq, rhs_eq] at ineq2
    exact ineq2
  have ineq3 : cc * (T_A * (T_A - (1/10) * n) / 2 - (A.card : ℝ)) < T_A * wΔ - 1 := by
    have hunivA_simp : T_A * (T_A - (1/10) * n) ≤ (∑ e ∈ A, T e * (T e - 1/10 * n)) / A.card := by
      have h := hunivA
      simp only [hT_A_def] at h ⊢
      rw [le_div_iff₀ hAcard]
      linarith
    have h_quad_bound : T_A * (T_A - (1/10) * n) / 2 ≤ (∑ e ∈ A, T e * (T e - 1/10 * n) / 2) / A.card := by
      have h1 : (∑ e ∈ A, T e * (T e - 1/10 * n) / 2) = (∑ e ∈ A, T e * (T e - 1/10 * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_A * (T_A - (1/10) * n) ≤ (∑ e ∈ A, T e * (T e - 1/10 * n)) / A.card := hunivA_simp
      have h3 : T_A * (T_A - (1/10) * n) / 2 ≤ (∑ e ∈ A, T e * (T e - 1/10 * n)) / A.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have ineq1_div : cc * ((∑ e ∈ A, T e * (T e - 1/10 * n) / 2) / A.card - A.card) <
        T_A * wΔ - 1 := by
      have key : (cc * (∑ e ∈ A, T e * (T e - 1/10 * n) / 2 - A.card * A.card)) / A.card <
          ((∑ e ∈ A, T e * wΔ) - A.card) / A.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ A, T e * (T e - 1/10 * n) / 2 - A.card * A.card)) / A.card =
          cc * ((∑ e ∈ A, T e * (T e - 1/10 * n) / 2) / A.card - A.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hAcard)]
      have rhs_eq : ((∑ e ∈ A, T e * wΔ) - A.card) / A.card = T_A * wΔ - 1 := by
        rw [sub_div, div_self (ne_of_gt hAcard)]
        congr 1
        rw [← Finset.sum_mul]
        rw [hT_A_def, mul_div_assoc]
        ring
      linarith
    have h_le : cc * (T_A * (T_A - (1/10) * n) / 2 - A.card) ≤
        cc * ((∑ e ∈ A, T e * (T e - 1/10 * n) / 2) / A.card - A.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq1_div]
  have ineq4 : cc * (T_B * (T_B - (1/10) * n) / 2 - (B.card : ℝ)) < 1 - T_B * wΔ := by
    have hunivB_simp : T_B * (T_B - (1/10) * n) ≤ (∑ e ∈ B, T e * (T e - 1/10 * n)) / B.card := by
      have h := hunivB
      simp only [hT_B_def] at h ⊢
      rw [le_div_iff₀ hBcard]
      linarith
    have h_quad_bound : T_B * (T_B - (1/10) * n) / 2 ≤ (∑ e ∈ B, T e * (T e - 1/10 * n) / 2) / B.card := by
      have h1 : (∑ e ∈ B, T e * (T e - 1/10 * n) / 2) = (∑ e ∈ B, T e * (T e - 1/10 * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_B * (T_B - (1/10) * n) ≤ (∑ e ∈ B, T e * (T e - 1/10 * n)) / B.card := hunivB_simp
      have h3 : T_B * (T_B - (1/10) * n) / 2 ≤ (∑ e ∈ B, T e * (T e - 1/10 * n)) / B.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have sumB_one : (∑ e ∈ B, (1 : ℝ)) = 1 * B.card := by simp
    have TBwΔ_eq : T_B * wΔ = (∑ e ∈ B, T e * wΔ) / B.card := by
      rw [hT_B_def]
      rw [← Finset.sum_mul]
      ring
    have ineq2_div : cc * ((∑ e ∈ B, T e * (T e - 1/10 * n) / 2) / B.card - B.card) <
        (∑ e ∈ B, (1 : ℝ)) / B.card - T_B * wΔ := by
      have key : (cc * (∑ e ∈ B, T e * (T e - 1/10 * n) / 2 - B.card * B.card)) / B.card <
          ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ B, T e * (T e - 1/10 * n) / 2 - B.card * B.card)) / B.card =
          cc * ((∑ e ∈ B, T e * (T e - 1/10 * n) / 2) / B.card - B.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hBcard)]
      have rhs_eq : ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card =
          1 - T_B * wΔ := by
        rw [sub_div, sumB_one, one_mul, div_self (ne_of_gt hBcard), TBwΔ_eq]
      rw [lhs_eq, rhs_eq] at key
      convert key using 1
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have sumB_one' : (∑ e ∈ B, (1 : ℝ)) / B.card = 1 := by
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have ineq2_div' : cc * ((∑ e ∈ B, T e * (T e - 1/10 * n) / 2) / B.card - B.card) < 1 - T_B * wΔ := by
      simpa only [sumB_one'] using ineq2_div
    have h_le : cc * (T_B * (T_B - (1/10) * n) / 2 - B.card) ≤
        cc * ((∑ e ∈ B, T e * (T e - 1/10 * n) / 2) / B.card - B.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq2_div']
  have hBcard_eq : (B.card : ℝ) = m - (A.card : ℝ) := by linarith
  have ineq4' : cc * (T_B * (T_B - (1/10) * n) / 2 - (m - (A.card : ℝ))) < 1 - T_B * wΔ := by
    rw [hBcard_eq] at ineq4
    exact ineq4
  have hTA1 : (8/10 : ℝ) * n ≤ T_A := by norm_num at hTA_lower ⊢; exact hTA_lower
  have hTA2 : T_A ≤ n := hTA_upper
  have hTB1 : (8/10 : ℝ) * n ≤ T_B := by norm_num at hTB_lower ⊢; exact hTB_lower
  have hTB2 : T_B ≤ n := hTB_upper
  exact dross_3_4_to_false n m (A.card : ℝ) cc wΔ T_A T_B hn hcc hwΔ hccrel hTA1 hTA2 hTB1 hTB2 mbound ineq3 ineq4'

/-- **ε-robust deficient-cut finish.** Same as `deficient_finish` but with deficiency `δ < 1/10`.
Adapt the reference `deficient_finish` proof above: replace `1/10` by `δ`, the lower bound `0.8`
(=8/10) by `(1-2*δ)`, use the `+2n` `mbound` and `hbig`, and call `dross_3_4_to_false_eps` (with
`δ, hδ0, hδ1, hn, hbig`) instead of `dross_3_4_to_false`. -/
theorem deficient_finish_eps {α : Type*} [DecidableEq α] (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (T : α → ℝ) (n m cc wΔ δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1/10) (hn : 0 < n) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hcard : (A.card : ℝ) + (B.card : ℝ) = m)
    (hTA : ∀ e ∈ A, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (hTB : ∀ e ∈ B, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ^2) * n^2 + 4 + 2 * n - 6 * δ * n)
    (hbig : 4 + 2 * n - 12 * δ * n ≤ (1 - 11 * δ + 10 * δ^2) * n^2)
    (ineq1 : cc * (∑ e ∈ A, (T e * (T e - δ * n) / 2 - A.card)) < ∑ e ∈ A, (T e * wΔ - 1))
    (ineq2 : cc * (∑ e ∈ B, (T e * (T e - δ * n) / 2 - B.card)) < ∑ e ∈ B, (1 - T e * wΔ)) :
    False := by
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBcard : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  set T_A := (∑ e ∈ A, T e) / A.card with hT_A_def
  set T_B := (∑ e ∈ B, T e) / B.card with hT_B_def
  have hTA_lower : (1 - 2 * δ : ℝ) * n ≤ T_A := by
    have h : A.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ A, T e :=
      Finset.card_nsmul_le_sum A T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTA e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (le_div_iff₀ hAcard).mpr h
  have hTA_upper : T_A ≤ n := by
    have h : ∑ e ∈ A, T e ≤ A.card • n :=
      Finset.sum_le_card_nsmul A T n (fun e he => (hTA e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (div_le_iff₀ hAcard).mpr h
  have hTB_lower : (1 - 2 * δ : ℝ) * n ≤ T_B := by
    have h : B.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ B, T e :=
      Finset.card_nsmul_le_sum B T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTB e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (le_div_iff₀ hBcard).mpr h
  have hTB_upper : T_B ≤ n := by
    have h : ∑ e ∈ B, T e ≤ B.card • n :=
      Finset.sum_le_card_nsmul B T n (fun e he => (hTB e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (div_le_iff₀ hBcard).mpr h
  have hunivA := convex_avg hA (fun e => T e) (δ * n)
  have hunivB := convex_avg hB (fun e => T e) (δ * n)
  rw [← Finset.sum_div] at hunivA hunivB
  have ineq1' : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) - (A.card : ℝ) * A.card) < (∑ e ∈ A, T e * wΔ) - A.card := by
    have lhs_eq : ∑ e ∈ A, (T e * (T e - δ * n) / 2 - (A.card : ℝ)) =
        (∑ e ∈ A, T e * (T e - δ * n) / 2) - A.card * A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ A, (T e * wΔ - 1) = (∑ e ∈ A, T e * wΔ) - A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [lhs_eq, rhs_eq] at ineq1
    exact ineq1
  have ineq2' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) - (B.card : ℝ) * B.card) < (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
    have lhs_eq : ∑ e ∈ B, (T e * (T e - δ * n) / 2 - (B.card : ℝ)) =
        (∑ e ∈ B, T e * (T e - δ * n) / 2) - B.card * B.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ B, (1 - T e * wΔ) = (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
      rw [Finset.sum_sub_distrib]
    rw [lhs_eq, rhs_eq] at ineq2
    exact ineq2
  have ineq3 : cc * (T_A * (T_A - δ * n) / 2 - (A.card : ℝ)) < T_A * wΔ - 1 := by
    have hunivA_simp : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := by
      have h := hunivA
      simp only [hT_A_def] at h ⊢
      rw [le_div_iff₀ hAcard]
      linarith
    have h_quad_bound : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card := by
      have h1 : (∑ e ∈ A, T e * (T e - δ * n) / 2) = (∑ e ∈ A, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := hunivA_simp
      have h3 : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have ineq1_div : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) <
        T_A * wΔ - 1 := by
      have key : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card <
          ((∑ e ∈ A, T e * wΔ) - A.card) / A.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card =
          cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hAcard)]
      have rhs_eq : ((∑ e ∈ A, T e * wΔ) - A.card) / A.card = T_A * wΔ - 1 := by
        rw [sub_div, div_self (ne_of_gt hAcard)]
        congr 1
        rw [← Finset.sum_mul]
        rw [hT_A_def, mul_div_assoc]
        ring
      linarith
    have h_le : cc * (T_A * (T_A - δ * n) / 2 - A.card) ≤
        cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq1_div]
  have ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (B.card : ℝ)) < 1 - T_B * wΔ := by
    have hunivB_simp : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := by
      have h := hunivB
      simp only [hT_B_def] at h ⊢
      rw [le_div_iff₀ hBcard]
      linarith
    have h_quad_bound : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card := by
      have h1 : (∑ e ∈ B, T e * (T e - δ * n) / 2) = (∑ e ∈ B, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := hunivB_simp
      have h3 : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have sumB_one : (∑ e ∈ B, (1 : ℝ)) = 1 * B.card := by simp
    have TBwΔ_eq : T_B * wΔ = (∑ e ∈ B, T e * wΔ) / B.card := by
      rw [hT_B_def]
      rw [← Finset.sum_mul]
      ring
    have ineq2_div : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) <
        (∑ e ∈ B, (1 : ℝ)) / B.card - T_B * wΔ := by
      have key : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card <
          ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card =
          cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hBcard)]
      have rhs_eq : ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card =
          1 - T_B * wΔ := by
        rw [sub_div, sumB_one, one_mul, div_self (ne_of_gt hBcard), TBwΔ_eq]
      rw [lhs_eq, rhs_eq] at key
      convert key using 1
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have sumB_one' : (∑ e ∈ B, (1 : ℝ)) / B.card = 1 := by
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have ineq2_div' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) < 1 - T_B * wΔ := by
      simpa only [sumB_one'] using ineq2_div
    have h_le : cc * (T_B * (T_B - δ * n) / 2 - B.card) ≤
        cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq2_div']
  have hBcard_eq : (B.card : ℝ) = m - (A.card : ℝ) := by linarith
  have ineq4' : cc * (T_B * (T_B - δ * n) / 2 - (m - (A.card : ℝ))) < 1 - T_B * wΔ := by
    rw [hBcard_eq] at ineq4
    exact ineq4
  have hTA1 : (1 - 2 * δ : ℝ) * n ≤ T_A := by norm_num at hTA_lower ⊢; exact hTA_lower
  have hTA2 : T_A ≤ n := hTA_upper
  have hTB1 : (1 - 2 * δ : ℝ) * n ≤ T_B := by norm_num at hTB_lower ⊢; exact hTB_lower
  have hTB2 : T_B ≤ n := hTB_upper
  exact dross_3_4_to_false_eps n m (A.card : ℝ) cc wΔ T_A T_B δ hδ0 hδ1 hcc hwΔ hccrel hn hTA1 hTA2 hTB1 hTB2 mbound hbig ineq3 ineq4'

theorem deficient_finish_exact {α : Type*} [DecidableEq α] (A B : Finset α)
    (hA : A.Nonempty) (hB : B.Nonempty) (T : α → ℝ) (n m cc wΔ δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/10) (hn : 20 ≤ n) (hcc : 0 < cc) (hwΔ : 0 < wΔ)
    (hccrel : 2 * wΔ = cc * (3 * n * (1 - δ) - 3))
    (hcard : (A.card : ℝ) + (B.card : ℝ) = m)
    (hTA : ∀ e ∈ A, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (hTB : ∀ e ∈ B, (1 - 2 * δ) * n ≤ T e ∧ T e ≤ n)
    (mbound : 2 * m ≤ (1 - δ + 2 * δ^2) * n^2 + 4 + n - 6 * δ * n)
    (ineq1 : cc * (∑ e ∈ A, (T e * (T e - δ * n) / 2 - A.card)) < ∑ e ∈ A, (T e * wΔ - 1))
    (ineq2 : cc * (∑ e ∈ B, (T e * (T e - δ * n) / 2 - B.card)) < ∑ e ∈ B, (1 - T e * wΔ)) :
    False := by
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBcard : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  set T_A := (∑ e ∈ A, T e) / A.card with hT_A_def
  set T_B := (∑ e ∈ B, T e) / B.card with hT_B_def
  have hTA_lower : (1 - 2 * δ : ℝ) * n ≤ T_A := by
    have h : A.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ A, T e :=
      Finset.card_nsmul_le_sum A T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTA e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (le_div_iff₀ hAcard).mpr h
  have hTA_upper : T_A ≤ n := by
    have h : ∑ e ∈ A, T e ≤ A.card • n :=
      Finset.sum_le_card_nsmul A T n (fun e he => (hTA e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_A_def]
    exact (div_le_iff₀ hAcard).mpr h
  have hTB_lower : (1 - 2 * δ : ℝ) * n ≤ T_B := by
    have h : B.card • ((1 - 2 * δ : ℝ) * n) ≤ ∑ e ∈ B, T e :=
      Finset.card_nsmul_le_sum B T ((1 - 2 * δ : ℝ) * n) (fun e he => by linarith [(hTB e he).1])
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (le_div_iff₀ hBcard).mpr h
  have hTB_upper : T_B ≤ n := by
    have h : ∑ e ∈ B, T e ≤ B.card • n :=
      Finset.sum_le_card_nsmul B T n (fun e he => (hTB e he).2)
    rw [nsmul_eq_mul, mul_comm] at h
    rw [hT_B_def]
    exact (div_le_iff₀ hBcard).mpr h
  have hunivA := convex_avg hA (fun e => T e) (δ * n)
  have hunivB := convex_avg hB (fun e => T e) (δ * n)
  rw [← Finset.sum_div] at hunivA hunivB
  have ineq1' : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) - (A.card : ℝ) * A.card) < (∑ e ∈ A, T e * wΔ) - A.card := by
    have lhs_eq : ∑ e ∈ A, (T e * (T e - δ * n) / 2 - (A.card : ℝ)) =
        (∑ e ∈ A, T e * (T e - δ * n) / 2) - A.card * A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ A, (T e * wΔ - 1) = (∑ e ∈ A, T e * wΔ) - A.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [lhs_eq, rhs_eq] at ineq1
    exact ineq1
  have ineq2' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) - (B.card : ℝ) * B.card) < (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
    have lhs_eq : ∑ e ∈ B, (T e * (T e - δ * n) / 2 - (B.card : ℝ)) =
        (∑ e ∈ B, T e * (T e - δ * n) / 2) - B.card * B.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have rhs_eq : ∑ e ∈ B, (1 - T e * wΔ) = (∑ e ∈ B, (1 : ℝ)) - (∑ e ∈ B, T e * wΔ) := by
      rw [Finset.sum_sub_distrib]
    rw [lhs_eq, rhs_eq] at ineq2
    exact ineq2
  have ineq3 : cc * (T_A * (T_A - δ * n) / 2 - (A.card : ℝ)) < T_A * wΔ - 1 := by
    have hunivA_simp : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := by
      have h := hunivA
      simp only [hT_A_def] at h ⊢
      rw [le_div_iff₀ hAcard]
      linarith
    have h_quad_bound : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card := by
      have h1 : (∑ e ∈ A, T e * (T e - δ * n) / 2) = (∑ e ∈ A, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_A * (T_A - δ * n) ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card := hunivA_simp
      have h3 : T_A * (T_A - δ * n) / 2 ≤ (∑ e ∈ A, T e * (T e - δ * n)) / A.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have ineq1_div : cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) <
        T_A * wΔ - 1 := by
      have key : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card <
          ((∑ e ∈ A, T e * wΔ) - A.card) / A.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ A, T e * (T e - δ * n) / 2 - A.card * A.card)) / A.card =
          cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hAcard)]
      have rhs_eq : ((∑ e ∈ A, T e * wΔ) - A.card) / A.card = T_A * wΔ - 1 := by
        rw [sub_div, div_self (ne_of_gt hAcard)]
        congr 1
        rw [← Finset.sum_mul]
        rw [hT_A_def, mul_div_assoc]
        ring
      linarith
    have h_le : cc * (T_A * (T_A - δ * n) / 2 - A.card) ≤
        cc * ((∑ e ∈ A, T e * (T e - δ * n) / 2) / A.card - A.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq1_div]
  have ineq4 : cc * (T_B * (T_B - δ * n) / 2 - (B.card : ℝ)) < 1 - T_B * wΔ := by
    have hunivB_simp : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := by
      have h := hunivB
      simp only [hT_B_def] at h ⊢
      rw [le_div_iff₀ hBcard]
      linarith
    have h_quad_bound : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card := by
      have h1 : (∑ e ∈ B, T e * (T e - δ * n) / 2) = (∑ e ∈ B, T e * (T e - δ * n)) / 2 := by
        rw [← Finset.sum_div]
      rw [h1, div_div]
      have h2 : T_B * (T_B - δ * n) ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card := hunivB_simp
      have h3 : T_B * (T_B - δ * n) / 2 ≤ (∑ e ∈ B, T e * (T e - δ * n)) / B.card / 2 :=
        div_le_div_of_nonneg_right h2 zero_le_two
      convert h3 using 1
      ring
    have sumB_one : (∑ e ∈ B, (1 : ℝ)) = 1 * B.card := by simp
    have TBwΔ_eq : T_B * wΔ = (∑ e ∈ B, T e * wΔ) / B.card := by
      rw [hT_B_def]
      rw [← Finset.sum_mul]
      ring
    have ineq2_div : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) <
        (∑ e ∈ B, (1 : ℝ)) / B.card - T_B * wΔ := by
      have key : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card <
          ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card := by
        gcongr
      have lhs_eq : (cc * (∑ e ∈ B, T e * (T e - δ * n) / 2 - B.card * B.card)) / B.card =
          cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
        rw [mul_div_assoc]
        congr 1
        rw [sub_div, mul_div_assoc, mul_div_cancel₀ _ (ne_of_gt hBcard)]
      have rhs_eq : ((∑ e ∈ B, (1 : ℝ)) - ∑ e ∈ B, T e * wΔ) / B.card =
          1 - T_B * wΔ := by
        rw [sub_div, sumB_one, one_mul, div_self (ne_of_gt hBcard), TBwΔ_eq]
      rw [lhs_eq, rhs_eq] at key
      convert key using 1
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have sumB_one' : (∑ e ∈ B, (1 : ℝ)) / B.card = 1 := by
      rw [sumB_one, one_mul, div_self (ne_of_gt hBcard)]
    have ineq2_div' : cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) < 1 - T_B * wΔ := by
      simpa only [sumB_one'] using ineq2_div
    have h_le : cc * (T_B * (T_B - δ * n) / 2 - B.card) ≤
        cc * ((∑ e ∈ B, T e * (T e - δ * n) / 2) / B.card - B.card) := by
      apply mul_le_mul_of_nonneg_left _ hcc.le
      linarith [h_quad_bound]
    linarith [h_le, ineq2_div']
  have hBcard_eq : (B.card : ℝ) = m - (A.card : ℝ) := by linarith
  have ineq4' : cc * (T_B * (T_B - δ * n) / 2 - (m - (A.card : ℝ))) < 1 - T_B * wΔ := by
    rw [hBcard_eq] at ineq4
    exact ineq4
  have hTA1 : (1 - 2 * δ : ℝ) * n ≤ T_A := by norm_num at hTA_lower ⊢; exact hTA_lower
  have hTA2 : T_A ≤ n := hTA_upper
  have hTB1 : (1 - 2 * δ : ℝ) * n ≤ T_B := by norm_num at hTB_lower ⊢; exact hTB_lower
  have hTB2 : T_B ≤ n := hTB_upper
  exact dross_3_4_to_false_exact n m (A.card : ℝ) cc wΔ T_A T_B δ hδ0 hδ1 hcc hwΔ hccrel hn hTA1 hTA2 hTB1 hTB2 mbound ineq3 ineq4'

/-- **(II) No deficient cut (TARGET).** Under `δ(G) ≥ (9/10)n`, every s–t cut of `Ĝ` has
capacity at least `M`. This is Dross's cut analysis: the K₄ counting (A6), convex extremization
(A7), and triangle-free/closing contradiction (A8) rule out a deficient cut, using
`capacity_lower_bound` and the bridges `triThrough_edge`, `k4pair_edge_iff`. -/
theorem cut_ge_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1/10) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + 2 * (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ))
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
      ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2)
    (C : RouteB.Cut (drossNet G wΔ)) :
    demand G wΔ ≤ C.capacity := by
  have hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * (Fintype.card V : ℝ) := le_of_eq hδ_eq
  by_contra hlt
  push_neg at hlt
  -- capacity ≥ the three arc sums
  have hcap := capacity_lower_bound G wΔ C
  -- demand splits over the cut into A-side and B-side source excess
  have hdemand : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0) := by
    rw [demand, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- reduced deficient-cut inequality: sink(A) + K₄-arcs(A→B) < source-excess(A)
  have hred : (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [hdemand] at hlt
    linarith
  -- source excess − sink deficit = signed excess (z₊ − (−z)₊ = z)
  have hid : (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        - (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
      = ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  -- K₄-arc sum < signed source excess over A
  have hred2 : (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
        if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- demand > 0 forces an edge, hence card ≥ 2, hence cc > 0
  have hcapnn : 0 ≤ C.capacity :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => (drossNet G wΔ).capNonneg u v
  have hdpos : 0 < demand G wΔ := lt_of_le_of_lt hcapnn hlt
  have hcard2 : 2 ≤ Fintype.card V := by
    by_contra hc
    push_neg at hc
    have : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.inductionOn with
      | hf a b =>
        have : a ≠ b := (show G.Adj a b from he).ne
        have h2 : 2 ≤ Fintype.card V :=
          Finset.one_lt_card.mpr ⟨a, Finset.mem_univ _, b, Finset.mem_univ _, this⟩
        omega
    rw [demand, this] at hdpos; simp at hdpos
  have hden_pos : 0 < 3 * (G.minDegree : ℝ) - 3 := by
    have : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hmd2
    nlinarith
  have hcc_pos : 0 < cc G wΔ := by rw [cc]; positivity
  have hcc_nn : 0 ≤ cc G wΔ := le_of_lt hcc_pos
  -- S_K4 lower bound: each A-edge contributes ≥ cc·(T_e(T_e−δn)/2 − |A|)
  have hSK4 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have he_edge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    -- inner sum = cc · #(cutB K4-partners)
    have hinner : (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutB G wΔ C).filter (fun e' => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he_edge
      have hk4 := k4count_cutB_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (1) in sum form
  have hineq1 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- ==================== B side (symmetric) ====================
  -- balance ⇒ total sink deficit = M, split over the cut
  have hsinktotal : demand G wΔ = ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
    have hid_all : (∑ e ∈ G.edgeFinset, max ((triThrough G e : ℝ) * wΔ - 1) 0)
          - (∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        = ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
      · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    rw [hbal] at hid_all
    rw [demand]; linarith
  have hsink : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0) := by
    rw [hsinktotal, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- B-side S_K4 lower bound
  have hSK4B : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e' he'
    have he'_edge : e' ∈ G.edgeFinset := (Finset.mem_filter.mp he').1
    have hinner : (∑ e ∈ cutA G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutA G wΔ C).filter (fun e => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he'_edge
    induction e' using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he'_edge
      have hfilt : (cutA G wΔ C).filter (fun e => K4pair G e (s(u, v)))
          = (cutA G wΔ C).filter (fun e => K4pair G (s(u, v)) e) := by
        apply Finset.filter_congr; intro e _; rw [k4pair_symm]
      rw [hfilt]
      have hk4 := k4count_cutA_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (2) in sum form
  have hidB : (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        - (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
      = ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  have hineq2 : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      < ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    linarith
  -- ==================== finish: apply deficient_finish ====================
  rcases (cutA G wΔ C).eq_empty_or_nonempty with hAe | hAne
  · rw [hAe] at hineq1; simp at hineq1
  rcases (cutB G wΔ C).eq_empty_or_nonempty with hBe | hBne
  · rw [hBe] at hineq2; simp at hineq2
  have hccrel : 2 * wΔ = cc G wΔ * (3 * (Fintype.card V : ℝ) * (1 - δ) - 3) := by
    rw [cc, show 3 * (Fintype.card V : ℝ) * (1 - δ) - 3
          = 3 * (G.minDegree : ℝ) - 3 from by linear_combination 3 * hδ_eq]
    exact (div_mul_cancel₀ _ (ne_of_gt hden_pos)).symm
  have hTA : ∀ e ∈ cutA G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hTB : ∀ e ∈ cutB G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hcard_m : ((cutA G wΔ C).card : ℝ) + ((cutB G wΔ C).card : ℝ)
      = (G.edgeFinset.card : ℝ) := by
    rw [cutA, cutB]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
      (fun e => Ghat.edge e ∈ C.S)
  have hn_pos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcard2
    linarith
  exact deficient_finish_eps (cutA G wΔ C) (cutB G wΔ C) hAne hBne (fun e => (triThrough G e : ℝ))
    (Fintype.card V : ℝ) (G.edgeFinset.card : ℝ) (cc G wΔ) wΔ δ hδ0 hδ1 hn_pos hcc_pos hwΔ
    hccrel hcard_m hTA hTB hmbound hbig hineq1 hineq2

theorem cut_ge_M_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/10) (hn20 : 20 ≤ Fintype.card V) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ))
    (C : RouteB.Cut (drossNet G wΔ)) :
    demand G wΔ ≤ C.capacity := by
  have hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * (Fintype.card V : ℝ) := le_of_eq hδ_eq
  by_contra hlt
  push_neg at hlt
  -- capacity ≥ the three arc sums
  have hcap := capacity_lower_bound G wΔ C
  -- demand splits over the cut into A-side and B-side source excess
  have hdemand : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        + (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0) := by
    rw [demand, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- reduced deficient-cut inequality: sink(A) + K₄-arcs(A→B) < source-excess(A)
  have hred : (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0 := by
    rw [hdemand] at hlt
    linarith
  -- source excess − sink deficit = signed excess (z₊ − (−z)₊ = z)
  have hid : (∑ e ∈ cutA G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
        - (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
      = ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  -- K₄-arc sum < signed source excess over A
  have hred2 : (∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C,
        if K4pair G e e' then max (cc G wΔ) 0 else 0)
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- demand > 0 forces an edge, hence card ≥ 2, hence cc > 0
  have hcapnn : 0 ≤ C.capacity :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => (drossNet G wΔ).capNonneg u v
  have hdpos : 0 < demand G wΔ := lt_of_le_of_lt hcapnn hlt
  have hcard2 : 2 ≤ Fintype.card V := by
    by_contra hc
    push_neg at hc
    have : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.inductionOn with
      | hf a b =>
        have : a ≠ b := (show G.Adj a b from he).ne
        have h2 : 2 ≤ Fintype.card V :=
          Finset.one_lt_card.mpr ⟨a, Finset.mem_univ _, b, Finset.mem_univ _, this⟩
        omega
    rw [demand, this] at hdpos; simp at hdpos
  have hden_pos : 0 < 3 * (G.minDegree : ℝ) - 3 := by
    have : (2 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hmd2
    nlinarith
  have hcc_pos : 0 < cc G wΔ := by rw [cc]; positivity
  have hcc_nn : 0 ≤ cc G wΔ := le_of_lt hcc_pos
  -- S_K4 lower bound: each A-edge contributes ≥ cc·(T_e(T_e−δn)/2 − |A|)
  have hSK4 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have he_edge : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    -- inner sum = cc · #(cutB K4-partners)
    have hinner : (∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutB G wΔ C).filter (fun e' => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he_edge
      have hk4 := k4count_cutB_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (1) in sum form
  have hineq1 : cc G wΔ * (∑ e ∈ cutA G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutA G wΔ C).card))
      < ∑ e ∈ cutA G wΔ C, ((triThrough G e : ℝ) * wΔ - 1) := by
    linarith
  -- ==================== B side (symmetric) ====================
  -- balance ⇒ total sink deficit = M, split over the cut
  have hsinktotal : demand G wΔ = ∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0 := by
    have hid_all : (∑ e ∈ G.edgeFinset, max ((triThrough G e : ℝ) * wΔ - 1) 0)
          - (∑ e ∈ G.edgeFinset, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        = ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
      · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
    rw [hbal] at hid_all
    rw [demand]; linarith
  have hsink : demand G wΔ
      = (∑ e ∈ cutA G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        + (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0) := by
    rw [hsinktotal, cutA, cutB]
    exact (Finset.sum_filter_add_sum_filter_not G.edgeFinset _ _).symm
  -- B-side S_K4 lower bound
  have hSK4B : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      ≤ ∑ e ∈ cutA G wΔ C, ∑ e' ∈ cutB G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e' he'
    have he'_edge : e' ∈ G.edgeFinset := (Finset.mem_filter.mp he').1
    have hinner : (∑ e ∈ cutA G wΔ C, if K4pair G e e' then max (cc G wΔ) 0 else 0)
        = cc G wΔ * (((cutA G wΔ C).filter (fun e => K4pair G e e')).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, max_eq_left hcc_nn, mul_comm]
    rw [hinner]
    rw [SimpleGraph.mem_edgeFinset] at he'_edge
    induction e' using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := he'_edge
      have hfilt : (cutA G wΔ C).filter (fun e => K4pair G e (s(u, v)))
          = (cutA G wΔ C).filter (fun e => K4pair G (s(u, v)) e) := by
        apply Finset.filter_congr; intro e _; rw [k4pair_symm]
      rw [hfilt]
      have hk4 := k4count_cutA_ge G huv wΔ C
      have hnum := numK4_lower_delta G h δ hδ_deg huv
      apply mul_le_mul_of_nonneg_left _ hcc_nn
      linarith
  -- Dross (2) in sum form
  have hidB : (∑ e ∈ cutB G wΔ C, max (1 - (triThrough G e : ℝ) * wΔ) 0)
        - (∑ e ∈ cutB G wΔ C, max ((triThrough G e : ℝ) * wΔ - 1) 0)
      = ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rcases le_total 0 ((triThrough G e : ℝ) * wΔ - 1) with hz | hz
    · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hz, max_eq_left (by linarith)]; ring
  have hineq2 : cc G wΔ * (∑ e ∈ cutB G wΔ C,
        ((triThrough G e : ℝ) * ((triThrough G e : ℝ) - δ * (Fintype.card V : ℝ)) / 2
          - (cutB G wΔ C).card))
      < ∑ e ∈ cutB G wΔ C, (1 - (triThrough G e : ℝ) * wΔ) := by
    linarith
  -- ==================== finish: apply deficient_finish ====================
  rcases (cutA G wΔ C).eq_empty_or_nonempty with hAe | hAne
  · rw [hAe] at hineq1; simp at hineq1
  rcases (cutB G wΔ C).eq_empty_or_nonempty with hBe | hBne
  · rw [hBe] at hineq2; simp at hineq2
  have hccrel : 2 * wΔ = cc G wΔ * (3 * (Fintype.card V : ℝ) * (1 - δ) - 3) := by
    rw [cc, show 3 * (Fintype.card V : ℝ) * (1 - δ) - 3
          = 3 * (G.minDegree : ℝ) - 3 from by linear_combination 3 * hδ_eq]
    exact (div_mul_cancel₀ _ (ne_of_gt hden_pos)).symm
  have hTA : ∀ e ∈ cutA G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hTB : ∀ e ∈ cutB G wΔ C, (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G e : ℝ)
      ∧ (triThrough G e : ℝ) ≤ (Fintype.card V : ℝ) := by
    intro e he
    have he_edge := (Finset.mem_filter.mp he).1
    rw [SimpleGraph.mem_edgeFinset] at he_edge
    induction e using Sym2.inductionOn with
    | hf u v => exact triThrough_bounds_delta G δ hδ_deg he_edge
  have hcard_m : ((cutA G wΔ C).card : ℝ) + ((cutB G wΔ C).card : ℝ)
      = (G.edgeFinset.card : ℝ) := by
    rw [cutA, cutB]
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
      (fun e => Ghat.edge e ∈ C.S)
  have hn20R : (20 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn20
  exact deficient_finish_exact (cutA G wΔ C) (cutB G wΔ C) hAne hBne (fun e => (triThrough G e : ℝ))
    (Fintype.card V : ℝ) (G.edgeFinset.card : ℝ) (cc G wΔ) wΔ δ hδ0 hδ1 hn20R hcc_pos hwΔ
    hccrel hcard_m hTA hTB hmbound hineq1 hineq2

/-- The trivial cut `{src}` has capacity exactly `M` (its outgoing arcs are the source arcs). -/
theorem srcCut_capacity (G : SimpleGraph V) [DecidableRel G.Adj] (wΔ : ℝ) :
    (⟨{Ghat.src}, by simp [drossNet], by simp [drossNet]⟩ : RouteB.Cut (drossNet G wΔ)).capacity = demand G wΔ := by
  show ∑ u ∈ {Ghat.src}, ∑ v ∈ Finset.univ \ {Ghat.src}, dcap G wΔ u v = demand G wΔ
  rw [Finset.sum_singleton, Finset.sum_sdiff_eq_sub (by simp), Finset.sum_singleton]
  -- dcap src src = 0
  have hss : dcap G wΔ Ghat.src Ghat.src = 0 := rfl
  rw [hss, sub_zero, sum_Ghat (fun v => dcap G wΔ Ghat.src v)]
  -- dcap src src = 0, dcap src snk = 0, dcap src (edge e) = max (T_e wΔ - 1) 0
  simp only [hss, show dcap G wΔ Ghat.src Ghat.snk = 0 from rfl, zero_add,
    show ∀ e, dcap G wΔ Ghat.src (Ghat.edge e) = max ((triThrough G e : ℝ) * wΔ - 1) 0 from fun _ => rfl]
  -- reduce sum over all Sym2 V to sum over edgeFinset (non-edges give 0)
  rw [demand]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  rw [triThrough_eq_zero_of_notMem G he]
  simp

/-- **Assembly: Ĝ carries a max flow of value exactly `M`.** From `maxflow_eq_mincut`: the max
flow equals some min cut, which by (II) is ≥ M and by the source cut is ≤ M. -/
theorem exists_flow_M (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1/10) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + 2 * (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ))
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
      ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2) :
    ∃ F : RouteB.Flow (drossNet G wΔ), F.value = demand G wΔ := by
  obtain ⟨F, C, hFC⟩ := RouteB.maxflow_eq_mincut (drossNet G wΔ)
  refine ⟨F, le_antisymm ?_ ?_⟩
  · have hsrc := RouteB.value_le_capacity F ⟨{Ghat.src}, by simp [drossNet], by simp [drossNet]⟩
    rwa [srcCut_capacity] at hsrc
  · rw [hFC]; exact cut_ge_M G h wΔ hwΔ hbal δ hδ0 hδ1 hmd2 hδ_eq hmbound hbig C


theorem exists_flow_M_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (wΔ : ℝ) (hwΔ : 0 < wΔ)
    (hbal : ∑ e ∈ G.edgeFinset, ((triThrough G e : ℝ) * wΔ - 1) = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1/10) (hn20 : 20 ≤ Fintype.card V) (hmd2 : 2 ≤ G.minDegree)
    (hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hmbound : 2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ)) :
    ∃ F : RouteB.Flow (drossNet G wΔ), F.value = demand G wΔ := by
  obtain ⟨F, C, hFC⟩ := RouteB.maxflow_eq_mincut (drossNet G wΔ)
  refine ⟨F, le_antisymm ?_ ?_⟩
  · have hsrc := RouteB.value_le_capacity F ⟨{Ghat.src}, by simp [drossNet], by simp [drossNet]⟩
    rwa [srcCut_capacity] at hsrc
  · rw [hFC]; exact cut_ge_M_exact G h wΔ hwΔ hbal δ hδ0 hδ1 hn20 hmd2 hδ_eq hmbound C

/-- If every edge lies in the same positive number `T` of triangles, uniform triangle weights
`1/T` form a fractional triangle decomposition. -/
theorem fractional_of_constant_triThrough (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : ℕ) (hT : 0 < T) (hconst : ∀ e ∈ G.edgeFinset, triThrough G e = T) :
    FractionalTriangleDecomp G := by
  refine ⟨fun _ => 1 / (T : ℝ), fun _ => by positivity, ?_⟩
  intro e he
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  show (triThrough G e : ℝ) * (1 / (T : ℝ)) = 1
  rw [hconst e he]
  have : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

/-- A dense graph (`δ ≥ (9/10)n`) with at least one edge contains a triangle. -/
theorem exists_triangle_of_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hm : G.edgeFinset.Nonempty) :
    0 < (G.cliqueFinset 3).card := by
  rw [Finset.card_pos]
  obtain ⟨e, he⟩ := hm
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := he
    have hcardV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    have hdu : 9 * Fintype.card V ≤ 10 * G.degree u :=
      le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree u))
    have hdv : 9 * Fintype.card V ≤ 10 * G.degree v :=
      le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree v))
    have hinter : (G.neighborFinset u ∩ G.neighborFinset v).Nonempty := by
      rw [← Finset.card_pos]
      have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
        le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ))
      have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
      omega
    obtain ⟨w, hw⟩ := hinter
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
    exact ⟨{u, v, w}, SimpleGraph.mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_iff.mpr ⟨u, v, w, huv, hw.1, hw.2, rfl⟩)⟩

/-- **Small dense case of Dross.** For `card < 20` and `δ ≥ (9/10)n`, `G` is complete (min degree
`≥ 0.9n > n−2` for `n<20` forces every vertex adjacent to all others), so every edge lies in
exactly `n−2` triangles, and uniform weights `1/(n−2)` give a fractional triangle decomposition.

STRATEGY. (1) `h` forces `card ≥ 10` (since `minDegree ≤ card−1`, so `9·card ≤ 10(card−1)`).
(2) For `card < 20`: `minDegree ≥ card−1` (else `10·minDegree ≤ 10(card−2) < 9·card`), so every
vertex has degree `card−1` = adjacent to all others → `G` complete: `∀ u v, u ≠ v → G.Adj u v`.
(3) For an edge `s(u,v)`, `triThrough G (s(u,v)) = #{w | {u,v,w} triangle} = #{w | w ≠ u ∧ w ≠ v}
= card − 2` (all other vertices form a triangle, since complete). (4) Apply
`fractional_of_constant_triThrough` with `T = card − 2` (`> 0` since `card ≥ 10`).

(Proved below; sorry-free, no native_decide/admit/axioms.) -/
theorem dross_fractional_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hlt : Fintype.card V < 20) :
    FractionalTriangleDecomp G := by
  -- minDegree ≤ card - 1 (since max degree is card - 1)
  have h_deg_bound : G.minDegree ≤ Fintype.card V - 1 := by
    by_cases hV : Fintype.card V = 0
    · simp only [hV, Nat.zero_sub]
      haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      simp [SimpleGraph.minDegree]
    · obtain ⟨v⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
      have hdeg : G.degree v ≤ Fintype.card V - 1 := by
        rw [SimpleGraph.degree]
        calc (G.neighborFinset v).card ≤ (Finset.univ \ {v}).card := by
              apply Finset.card_le_card
              intro u hu
              simp only [Finset.mem_sdiff, Finset.mem_singleton]
              refine ⟨Finset.mem_univ _, ?_⟩
              intro h
              rw [h] at hu
              simp only [SimpleGraph.mem_neighborFinset] at hu
              exact G.loopless.irrefl v hu
          _ = Fintype.card V - 1 := by rw [card_sdiff] <;> simp
      exact G.minDegree_le_degree v |> Nat.le_trans <| hdeg
  -- Handle card = 0 case (trivial since no edges)
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    exact ⟨fun _ => 1, fun _ => by norm_num, by simp⟩
  -- From h and h_deg_bound, we get card ≥ 10
  have hcard_ge_10 : 10 ≤ Fintype.card V := by
    -- 9 * card ≤ 10 * minDegree ≤ 10 * (card - 1) = 10 * card - 10
    -- So 10 ≤ card
    have := Nat.mul_le_mul_left 10 h_deg_bound
    omega
  -- From h and card < 20, we get minDegree ≥ card - 1
  have hmin_ge : G.minDegree ≥ Fintype.card V - 1 := by
    have h1 : 90 ≤ 10 * G.minDegree := by
      calc 90 = 9 * 10 := by norm_num
        _ ≤ 9 * Fintype.card V := by exact Nat.mul_le_mul_left 9 hcard_ge_10
        _ ≤ 10 * G.minDegree := h
    have hcard : Fintype.card V ≤ 19 := by omega
    have h2 : 9 * Fintype.card V ≤ 10 * G.minDegree := h
    -- G.minDegree ≥ (9 * card) / 10, and for card ≤ 19, (9 * card) / 10 ≥ card - 1
    interval_cases Fintype.card V <;> omega
  -- So minDegree = card - 1
  have hmin_eq : G.minDegree = Fintype.card V - 1 := by omega
  -- Every vertex has degree card - 1, so G is complete
  have hdeg_le : ∀ u : V, G.degree u ≤ Fintype.card V - 1 := by
    intro u
    rw [SimpleGraph.degree]
    calc (G.neighborFinset u).card ≤ (Finset.univ \ {u}).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro h
          rw [h] at hv
          simp only [SimpleGraph.mem_neighborFinset] at hv
          exact G.loopless.irrefl u hv
      _ = Fintype.card V - 1 := by rw [card_sdiff] <;> simp
  have hcomplete : ∀ u v : V, u ≠ v → G.Adj u v := by
    intro u v huv
    have hdeg_u : G.degree u ≥ Fintype.card V - 1 := hmin_eq ▸ G.minDegree_le_degree u
    have hdeg_u_eq : G.degree u = Fintype.card V - 1 := Nat.le_antisymm (hdeg_le u) hdeg_u
    -- neighborFinset u has size card - 1 = size of univ \ {u}
    -- So neighborFinset u = univ \ {u}, hence v ∈ neighborFinset u
    have hsub : G.neighborFinset u ⊆ Finset.univ \ {u} := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h
      rw [h] at hw
      simp only [SimpleGraph.mem_neighborFinset] at hw
      exact G.loopless.irrefl u hw
    have hcard_nei : (G.neighborFinset u).card = (Finset.univ \ {u}).card := by
      rw [SimpleGraph.degree] at hdeg_u_eq
      rw [hdeg_u_eq, card_sdiff] <;> simp
    have hneq : G.neighborFinset u = Finset.univ \ {u} := by
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_nei])
    have hv_in_nei : v ∈ G.neighborFinset u := by
      rw [hneq]
      simp [Ne.symm huv]
    exact G.mem_neighborFinset u v |>.mp hv_in_nei
  -- triThrough G e = card - 2 for every edge e
  have htri : ∀ e ∈ G.edgeFinset, triThrough G e = Fintype.card V - 2 := by
    intro e he
    rw [triThrough]
    -- Extract endpoints from edge
    simp only [SimpleGraph.mem_edgeFinset] at he
    -- e ∈ G.edgeSet means e = s(u, v) for some u ≠ v with G.Adj u v
    rcases e with ⟨u, v⟩
    -- Get that u ≠ v and G.Adj u v from he
    have hadj : G.Adj u v := by
      rw [SimpleGraph.mem_edgeSet] at he
      exact he
    have hne : u ≠ v := by
      intro h
      rw [h] at hadj
      have hloop := G.loopless.irrefl v
      contradiction
    -- triThrough = counting 3-cliques containing edge s(u,v)
    -- For complete graph, this equals the number of 3-element subsets containing {u,v}
    -- which is card - 2 (one for each w ∉ {u, v})
    have hG_complete : G.cliqueFinset 3 = (Finset.univ : Finset V).powersetCard 3 := by
      ext t
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter, Finset.mem_powersetCard]
      simp_rw [SimpleGraph.isNClique_iff]
      -- Need: t ∈ univ ∧ G.IsClique (↑t) ∧ #t = 3 ↔ t ⊆ univ ∧ #t = 3
      -- Since t ∈ univ and t ⊆ univ are always true, this reduces to showing IsClique for any t
      simp [SimpleGraph.IsClique]
      intro hcard x hx y hy hxy
      exact hcomplete x y hxy
    -- Now count cliques containing s(u, v)
    rw [hG_complete]
    -- triEdges t contains s(u,v) iff u ∈ t and v ∈ t (since u ≠ v)
    have htri_mem : ∀ t : Finset V, Quot.mk (Sym2.Rel V) (u, v) ∈ triEdges t ↔ u ∈ t ∧ v ∈ t := by
      intro t
      simp only [triEdges]
      rw [Finset.mem_filter]
      simp_all [Sym2.IsDiag]
    simp_rw [htri_mem]
    -- Count of 3-element subsets containing both u and v = card - 2
    -- Use a bijection with V \ {u, v}
    have huv_ne : u ≠ v := hne
    have hS_card : (Finset.univ \ (insert u {v} : Finset V)).card = Fintype.card V - 2 := by
      rw [card_sdiff] <;> simp [Finset.card_pair huv_ne]
    -- Bijection between {t ∈ powersetCard 3 univ | u ∈ t ∧ v ∈ t} and V \ {u, v}
    -- Given by t ↦ t \ {u, v} (which has exactly 1 element)
    -- Inverse: w ↦ {u, v, w}
    have hcard : ((Finset.powersetCard 3 Finset.univ).filter (fun t => u ∈ t ∧ v ∈ t)).card = (Finset.univ \ (insert u {v} : Finset V)).card := by
      have heq : ((Finset.powersetCard 3 Finset.univ).filter (fun t => u ∈ t ∧ v ∈ t)) =
        (Finset.univ \ (insert u {v} : Finset V)).image (fun w => insert u (insert v {w})) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image,
          Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro ⟨⟨ht1, ht2⟩, hut, hvt⟩
          have hsub : ({u, v} : Finset V) ⊆ t := by
            simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
            exact ⟨hut, hvt⟩
          have hcard_diff : (t \ (insert u {v} : Finset V)).card = 1 := by
            rw [Finset.card_sdiff_of_subset hsub]
            simp [Finset.card_pair huv_ne, ht2]
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_diff
          use w
          have hw_mem : w ∈ t \ (insert u {v} : Finset V) := hw ▸ Finset.mem_singleton_self _
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw_mem
          have hwnu : w ≠ u := fun h => hw_mem.2 (Or.inl h)
          have hwnv : w ≠ v := fun h => hw_mem.2 (Or.inr h)
          refine ⟨by tauto, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hxt : x ∈ t ↔ x = u ∨ x = v ∨ x = w := by
            constructor
            · intro hx
              by_contra hc
              push_neg at hc
              have hxn : x ∉ (insert u {v} : Finset V) := by simp_all [Finset.mem_insert, Finset.mem_singleton]
              have : x ∈ t \ (insert u {v} : Finset V) := Finset.mem_sdiff.mpr ⟨hx, hxn⟩
              rw [hw] at this; simp at this; tauto
            · intro hx
              rcases hx with rfl | rfl | rfl <;> [exact hut; exact hvt; exact (hw ▸ Finset.mem_singleton_self _ |> Finset.mem_sdiff.mp |>.1)]
          exact hxt.symm
        · rintro ⟨w, ⟨hwnu, hw4⟩⟩
          rw [← hw4]
          simp at hwnu
          refine ⟨⟨Finset.subset_univ _, ?_⟩, by simp, by simp⟩
          have hcard_uv : ({u, v} : Finset V).card = 2 := by simp [huv_ne]
          have hwn : w ∉ ({u, v} : Finset V) := by simp [hwnu.1, hwnu.2]
          rw [show ({u, v, w} : Finset V) = {u, v} ∪ {w} by ext x; simp]
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hwn)]
          rw [hcard_uv, Finset.card_singleton]
      rw [heq, Finset.card_image_of_injOn]
      intro w1 hw1 w2 hw2 heq
      -- heq : insert u (insert v {w1}) = insert u (insert v {w2})
      simp at hw1 heq
      -- w1 ≠ u ∧ w1 ≠ v
      have hmem : w1 ∈ ({u, v, w1} : Finset V) := by simp
      rw [heq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | h | rfl <;> tauto
    rw [hcard, hS_card]
  -- Apply fractional_of_constant_triThrough with T = card - 2
  have hT_pos : 0 < Fintype.card V - 2 := by omega
  exact fractional_of_constant_triThrough G (Fintype.card V - 2) hT_pos htri

/-- **V_b cardinality bound (Mantel argument), loose integer form.** If `G` has no triangle whose
three vertices all have degree `≥ minDegree + 2` (`hNoHDT`), then `Vb = {v | deg v ≥ minDegree+2}`
has `|Vb| ≤ 2(n − minDegree)`. (The tighter `+4` slack is false with the actual deficiency — e.g.
K₂₀ has `|Vb|=0` but `2(n−minDegree)=2`; this loose bound holds: `0 ≤ 2`. See FINDINGS.md.) -/
theorem nb_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hn20 : 20 ≤ Fintype.card V)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    (Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card
      ≤ 2 * (Fintype.card V - G.minDegree) := by
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVb
  by_cases hVb_empty : Vb.card = 0
  · simp [hVb_empty]
  · by_contra h
    push_neg at h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hVb_empty)
    set Nvb := fun v => G.neighborFinset v ∩ Vb with hNvb
    have hNvb_lower : (Nvb v).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
      have hvdeg : G.degree v ≥ G.minDegree + 2 := by
        rw [hVb] at hv
        exact Finset.mem_filter.mp hv |>.2
      have hsub : G.neighborFinset v \ Vb ⊆ Finset.univ \ Vb := by
        simp [Finset.sdiff_subset_sdiff]
      have hVb_bound : Vb.card ≤ Fintype.card V := Finset.card_le_univ Vb
      have hcard_outside : (G.neighborFinset v \ Vb).card ≤ Fintype.card V - Vb.card := by
        calc (G.neighborFinset v \ Vb).card ≤ (Finset.univ \ Vb).card := Finset.card_le_card hsub
          _ = Fintype.card V - Vb.card := by simp [Finset.card_sdiff]
      have hunion : G.neighborFinset v = (G.neighborFinset v ∩ Vb) ∪ (G.neighborFinset v \ Vb) := by
        ext x; simp; tauto
      have hdisj : Disjoint (G.neighborFinset v ∩ Vb) (G.neighborFinset v \ Vb) := by
        rw [Finset.disjoint_left]
        intro x hx hxn
        have hxb := (Finset.mem_inter.mp hx).2
        exact (Finset.mem_sdiff.mp hxn).2 hxb
      have hcard_n : (G.neighborFinset v).card = (G.neighborFinset v ∩ Vb).card + (G.neighborFinset v \ Vb).card := by
        conv_lhs => rw [hunion]
        rw [Finset.card_union_of_disjoint hdisj]
      have hcard_eq : (Nvb v).card = G.degree v - (G.neighborFinset v \ Vb).card := by
        simp only [hNvb]
        have hdeg : G.degree v = (G.neighborFinset v).card := rfl
        omega
      rw [hcard_eq]
      have h_combined : G.degree v - (G.neighborFinset v \ Vb).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
        have h1 : G.degree v ≥ G.minDegree + 2 := hvdeg
        have h2 : (G.neighborFinset v \ Vb).card ≤ Fintype.card V - Vb.card := hcard_outside
        omega
      exact h_combined
    have hNvb_pos : (Nvb v).card > 0 := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hNvb_pos
    simp [hNvb] at hu
    obtain ⟨huv, huVb⟩ := hu
    have hdisjoint : Disjoint (Nvb u) (Nvb v) := by
      rw [Finset.disjoint_left]
      intro w hwv hww
      simp [hNvb] at hwv hww
      exact hNoHDT u v w huv.symm hwv.1 hww.1
        (by rw [hVb] at huVb; exact Finset.mem_filter.mp huVb |>.2)
        (by rw [hVb] at hv; exact Finset.mem_filter.mp hv |>.2)
        (by rw [hVb] at hwv; exact Finset.mem_filter.mp hwv.2 |>.2)
    have hNvb_u_lower : (Nvb u).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
      have huVb' : G.minDegree + 2 ≤ G.degree u := by rw [hVb] at huVb; exact Finset.mem_filter.mp huVb |>.2
      have hsub_u : G.neighborFinset u \ Vb ⊆ Finset.univ \ Vb := by simp [Finset.sdiff_subset_sdiff]
      have hcard_outside_u : (G.neighborFinset u \ Vb).card ≤ Fintype.card V - Vb.card := by
        calc (G.neighborFinset u \ Vb).card ≤ (Finset.univ \ Vb).card := Finset.card_le_card hsub_u
          _ = Fintype.card V - Vb.card := by simp [Finset.card_sdiff]
      have hdisj_u : Disjoint (G.neighborFinset u ∩ Vb) (G.neighborFinset u \ Vb) := by
        rw [Finset.disjoint_left]
        intro x hx hxs
        have hxb := (Finset.mem_inter.mp hx).2
        exact (Finset.mem_sdiff.mp hxs).2 hxb
      have hunion_u : G.neighborFinset u = (G.neighborFinset u ∩ Vb) ∪ (G.neighborFinset u \ Vb) := by
        ext x; simp; tauto
      have hcard_n_u : (G.neighborFinset u).card = (G.neighborFinset u ∩ Vb).card + (G.neighborFinset u \ Vb).card := by
        conv_lhs => rw [hunion_u]
        rw [Finset.card_union_of_disjoint hdisj_u]
      have hcard_eq_u : (Nvb u).card = G.degree u - (G.neighborFinset u \ Vb).card := by
        simp only [hNvb]
        have hdeg : G.degree u = (G.neighborFinset u).card := rfl
        omega
      rw [hcard_eq_u]
      have h1 : G.degree u ≥ G.minDegree + 2 := huVb'
      have h2 : (G.neighborFinset u \ Vb).card ≤ Fintype.card V - Vb.card := hcard_outside_u
      have h3 : (G.neighborFinset u ∩ Vb).card = (G.neighborFinset u).card - (G.neighborFinset u \ Vb).card := by
        rw [hcard_n_u, Nat.add_sub_cancel_right]
      have hVb_le : Vb.card ≤ Fintype.card V := Finset.card_le_univ Vb
      have hdeg_eq : G.degree u = (G.neighborFinset u).card := rfl
      omega
    have hUnion_sub : (Nvb u ∪ Nvb v) ⊆ Vb := by
      intro x hx
      simp at hx
      cases hx with
      | inl hx => simp [hNvb] at hx; exact hx.2
      | inr hx => simp [hNvb] at hx; exact hx.2
    have hUnion_card : (Nvb u ∪ Nvb v).card = (Nvb u).card + (Nvb v).card :=
      Finset.card_union_of_disjoint hdisjoint
    have hVb_card_ge : Vb.card ≥ (Nvb u).card + (Nvb v).card := by
      rw [← hUnion_card]
      exact Finset.card_le_card hUnion_sub
    have h_sum : (Nvb u).card + (Nvb v).card ≥ 2 * (G.minDegree + 2 + Vb.card - Fintype.card V) := by
      have := hNvb_lower
      have := hNvb_u_lower
      omega
    omega

theorem nb_bound_tight (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hn20 : 20 ≤ Fintype.card V)
    (hdef2 : 2 ≤ Fintype.card V - G.minDegree)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    (Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card
      ≤ 2 * (Fintype.card V - G.minDegree) - 4 := by
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVb
  by_cases hVb_empty : Vb.card = 0
  · rw [hVb_empty]; omega
  · by_contra h
    push_neg at h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hVb_empty)
    set Nvb := fun v => G.neighborFinset v ∩ Vb with hNvb
    have hNvb_lower : (Nvb v).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
      have hvdeg : G.degree v ≥ G.minDegree + 2 := by
        rw [hVb] at hv
        exact Finset.mem_filter.mp hv |>.2
      have hsub : G.neighborFinset v \ Vb ⊆ Finset.univ \ Vb := by
        simp [Finset.sdiff_subset_sdiff]
      have hVb_bound : Vb.card ≤ Fintype.card V := Finset.card_le_univ Vb
      have hcard_outside : (G.neighborFinset v \ Vb).card ≤ Fintype.card V - Vb.card := by
        calc (G.neighborFinset v \ Vb).card ≤ (Finset.univ \ Vb).card := Finset.card_le_card hsub
          _ = Fintype.card V - Vb.card := by simp [Finset.card_sdiff]
      have hunion : G.neighborFinset v = (G.neighborFinset v ∩ Vb) ∪ (G.neighborFinset v \ Vb) := by
        ext x; simp; tauto
      have hdisj : Disjoint (G.neighborFinset v ∩ Vb) (G.neighborFinset v \ Vb) := by
        rw [Finset.disjoint_left]
        intro x hx hxn
        have hxb := (Finset.mem_inter.mp hx).2
        exact (Finset.mem_sdiff.mp hxn).2 hxb
      have hcard_n : (G.neighborFinset v).card = (G.neighborFinset v ∩ Vb).card + (G.neighborFinset v \ Vb).card := by
        conv_lhs => rw [hunion]
        rw [Finset.card_union_of_disjoint hdisj]
      have hcard_eq : (Nvb v).card = G.degree v - (G.neighborFinset v \ Vb).card := by
        simp only [hNvb]
        have hdeg : G.degree v = (G.neighborFinset v).card := rfl
        omega
      rw [hcard_eq]
      have h_combined : G.degree v - (G.neighborFinset v \ Vb).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
        have h1 : G.degree v ≥ G.minDegree + 2 := hvdeg
        have h2 : (G.neighborFinset v \ Vb).card ≤ Fintype.card V - Vb.card := hcard_outside
        omega
      exact h_combined
    have hNvb_pos : (Nvb v).card > 0 := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hNvb_pos
    simp [hNvb] at hu
    obtain ⟨huv, huVb⟩ := hu
    have hdisjoint : Disjoint (Nvb u) (Nvb v) := by
      rw [Finset.disjoint_left]
      intro w hwv hww
      simp [hNvb] at hwv hww
      exact hNoHDT u v w huv.symm hwv.1 hww.1
        (by rw [hVb] at huVb; exact Finset.mem_filter.mp huVb |>.2)
        (by rw [hVb] at hv; exact Finset.mem_filter.mp hv |>.2)
        (by rw [hVb] at hwv; exact Finset.mem_filter.mp hwv.2 |>.2)
    have hNvb_u_lower : (Nvb u).card ≥ G.minDegree + 2 + Vb.card - Fintype.card V := by
      have huVb' : G.minDegree + 2 ≤ G.degree u := by rw [hVb] at huVb; exact Finset.mem_filter.mp huVb |>.2
      have hsub_u : G.neighborFinset u \ Vb ⊆ Finset.univ \ Vb := by simp [Finset.sdiff_subset_sdiff]
      have hcard_outside_u : (G.neighborFinset u \ Vb).card ≤ Fintype.card V - Vb.card := by
        calc (G.neighborFinset u \ Vb).card ≤ (Finset.univ \ Vb).card := Finset.card_le_card hsub_u
          _ = Fintype.card V - Vb.card := by simp [Finset.card_sdiff]
      have hdisj_u : Disjoint (G.neighborFinset u ∩ Vb) (G.neighborFinset u \ Vb) := by
        rw [Finset.disjoint_left]
        intro x hx hxs
        have hxb := (Finset.mem_inter.mp hx).2
        exact (Finset.mem_sdiff.mp hxs).2 hxb
      have hunion_u : G.neighborFinset u = (G.neighborFinset u ∩ Vb) ∪ (G.neighborFinset u \ Vb) := by
        ext x; simp; tauto
      have hcard_n_u : (G.neighborFinset u).card = (G.neighborFinset u ∩ Vb).card + (G.neighborFinset u \ Vb).card := by
        conv_lhs => rw [hunion_u]
        rw [Finset.card_union_of_disjoint hdisj_u]
      have hcard_eq_u : (Nvb u).card = G.degree u - (G.neighborFinset u \ Vb).card := by
        simp only [hNvb]
        have hdeg : G.degree u = (G.neighborFinset u).card := rfl
        omega
      rw [hcard_eq_u]
      have h1 : G.degree u ≥ G.minDegree + 2 := huVb'
      have h2 : (G.neighborFinset u \ Vb).card ≤ Fintype.card V - Vb.card := hcard_outside_u
      have h3 : (G.neighborFinset u ∩ Vb).card = (G.neighborFinset u).card - (G.neighborFinset u \ Vb).card := by
        rw [hcard_n_u, Nat.add_sub_cancel_right]
      have hVb_le : Vb.card ≤ Fintype.card V := Finset.card_le_univ Vb
      have hdeg_eq : G.degree u = (G.neighborFinset u).card := rfl
      omega
    have hUnion_sub : (Nvb u ∪ Nvb v) ⊆ Vb := by
      intro x hx
      simp at hx
      cases hx with
      | inl hx => simp [hNvb] at hx; exact hx.2
      | inr hx => simp [hNvb] at hx; exact hx.2
    have hUnion_card : (Nvb u ∪ Nvb v).card = (Nvb u).card + (Nvb v).card :=
      Finset.card_union_of_disjoint hdisjoint
    have hVb_card_ge : Vb.card ≥ (Nvb u).card + (Nvb v).card := by
      rw [← hUnion_card]
      exact Finset.card_le_card hUnion_sub
    have h_sum : (Nvb u).card + (Nvb v).card ≥ 2 * (G.minDegree + 2 + Vb.card - Fintype.card V) := by
      have := hNvb_lower
      have := hNvb_u_lower
      omega
    omega

/-- **V_b degree-sum bound (given the `nb` bound).** With the ACTUAL deficiency `δ` (so the
high-degree threshold `minDegree + 2` is an integer — no integrality gap, unlike Dross's real
`(1−δ)n+2`), and given `nb = |{v : deg v ≥ minDegree+2}| ≤ 2δn − 4`, the edge count satisfies the
triangle-free bound. Vertices in `V_b` contribute `≤ n−1`, the rest `≤ minDegree+1 = (1−δ)n+1`. -/
theorem mbound_of_nb (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hn20 : 20 ≤ Fintype.card V)
    (hδeq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hnb : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
        ≤ 2 * δ * (Fintype.card V : ℝ)) :
    2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + 2 * (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ) := by
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVbdef
  have hdeg_le : ∀ v : V, G.degree v ≤ Fintype.card V - 1 := by
    intro v
    have := G.degree_lt_card_verts v
    omega
  have h2m : 2 * G.edgeFinset.card = ∑ v, G.degree v := by
    rw [← G.sum_degrees_eq_twice_card_edges]
  have hsplit : ∑ v, G.degree v
      = (∑ v ∈ Vb, G.degree v) + ∑ v ∈ Vbᶜ, G.degree v := by
    rw [← Finset.sum_add_sum_compl Vb]
  have hVbbound : ∑ v ∈ Vb, G.degree v ≤ Vb.card * (Fintype.card V - 1) := by
    calc ∑ v ∈ Vb, G.degree v ≤ ∑ _v ∈ Vb, (Fintype.card V - 1) :=
          Finset.sum_le_sum (fun v _ => hdeg_le v)
      _ = Vb.card * (Fintype.card V - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompbound : ∑ v ∈ Vbᶜ, G.degree v ≤ Vbᶜ.card * (G.minDegree + 1) := by
    calc ∑ v ∈ Vbᶜ, G.degree v ≤ ∑ _v ∈ Vbᶜ, (G.minDegree + 1) := by
          apply Finset.sum_le_sum
          intro v hv
          simp only [hVbdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
            true_and, not_le] at hv
          omega
      _ = Vbᶜ.card * (G.minDegree + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompcard : Vbᶜ.card = Fintype.card V - Vb.card := Finset.card_compl Vb
  -- push to reals
  have hVble : Vb.card ≤ Fintype.card V := Finset.card_le_univ _
  have h2mr : 2 * (G.edgeFinset.card : ℝ)
      ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1)
        + ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
    have := hsplit
    have hb1 : (∑ v ∈ Vb, G.degree v : ℝ) ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      have := hVbbound
      have hcast : ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ)
          = (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]; push_cast; ring
      calc (∑ v ∈ Vb, G.degree v : ℝ) ≤ ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ) := by
            exact_mod_cast hVbbound
        _ = _ := hcast
    have hb2 : (∑ v ∈ Vbᶜ, G.degree v : ℝ)
        ≤ ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
      have hcast : ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ)
          = ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
        rw [Nat.cast_mul, hcompcard, Nat.cast_sub hVble]; push_cast; ring
      calc (∑ v ∈ Vbᶜ, G.degree v : ℝ) ≤ ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ) := by
            exact_mod_cast hcompbound
        _ = _ := hcast
    have h2mR : 2 * (G.edgeFinset.card : ℝ) = ∑ v, (G.degree v : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h2m
    rw [h2mR, ← Finset.sum_add_sum_compl Vb (fun v => (G.degree v : ℝ))]
    linarith [hb1, hb2]
  -- minDegree = (1-δ)n from hδeq
  have hmd : (G.minDegree : ℝ) = (Fintype.card V : ℝ) - δ * Fintype.card V := by linarith [hδeq]
  have hnR : (20 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn20
  have hVbleR : (Vb.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hVble
  have hmle : G.minDegree ≤ Fintype.card V := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    exact le_trans (G.minDegree_le_degree v) (le_trans (hdeg_le v) (by omega))
  have hδn0 : (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
    rw [← hδeq]
    have hml : (G.minDegree : ℝ) ≤ Fintype.card V := by exact_mod_cast hmle
    linarith
  have hδsmall : δ * (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) / 10 := by
    rw [← hδeq]
    have : (9 : ℝ) * Fintype.card V ≤ 10 * G.minDegree := by exact_mod_cast h
    linarith
  -- expand the nonlinear cross terms of h2mr using minDeg = (1-δ)n
  have hVbmd : (Vb.card : ℝ) * (G.minDegree : ℝ)
      = (Vb.card : ℝ) * (Fintype.card V : ℝ) - (Vb.card : ℝ) * (δ * Fintype.card V) := by
    rw [hmd]; ring
  have hnmd : (Fintype.card V : ℝ) * (G.minDegree : ℝ)
      = (Fintype.card V : ℝ)^2 - δ * (Fintype.card V : ℝ)^2 := by rw [hmd]; ring
  nlinarith [h2mr, hnb, hmd, hnR, hVbleR, hδn0, hVbmd, hnmd,
    mul_nonneg (show (0:ℝ) ≤ 2 * δ * (Fintype.card V:ℝ) - (Vb.card:ℝ) by linarith [hnb]) hδn0,
    mul_nonneg (show (0:ℝ) ≤ (Vb.card:ℝ) by positivity) hδn0, hδsmall]

theorem mbound_tight (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (hn20 : 20 ≤ Fintype.card V)
    (hδeq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hδn2 : (2:ℝ) ≤ δ * (Fintype.card V : ℝ))
    (hnb : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
        ≤ 2 * δ * (Fintype.card V : ℝ) - 4) :
    2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ) := by
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVbdef
  have hdeg_le : ∀ v : V, G.degree v ≤ Fintype.card V - 1 := by
    intro v
    have := G.degree_lt_card_verts v
    omega
  have h2m : 2 * G.edgeFinset.card = ∑ v, G.degree v := by
    rw [← G.sum_degrees_eq_twice_card_edges]
  have hsplit : ∑ v, G.degree v
      = (∑ v ∈ Vb, G.degree v) + ∑ v ∈ Vbᶜ, G.degree v := by
    rw [← Finset.sum_add_sum_compl Vb]
  have hVbbound : ∑ v ∈ Vb, G.degree v ≤ Vb.card * (Fintype.card V - 1) := by
    calc ∑ v ∈ Vb, G.degree v ≤ ∑ _v ∈ Vb, (Fintype.card V - 1) :=
          Finset.sum_le_sum (fun v _ => hdeg_le v)
      _ = Vb.card * (Fintype.card V - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompbound : ∑ v ∈ Vbᶜ, G.degree v ≤ Vbᶜ.card * (G.minDegree + 1) := by
    calc ∑ v ∈ Vbᶜ, G.degree v ≤ ∑ _v ∈ Vbᶜ, (G.minDegree + 1) := by
          apply Finset.sum_le_sum
          intro v hv
          simp only [hVbdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
            true_and, not_le] at hv
          omega
      _ = Vbᶜ.card * (G.minDegree + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompcard : Vbᶜ.card = Fintype.card V - Vb.card := Finset.card_compl Vb
  -- push to reals
  have hVble : Vb.card ≤ Fintype.card V := Finset.card_le_univ _
  have h2mr : 2 * (G.edgeFinset.card : ℝ)
      ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1)
        + ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
    have := hsplit
    have hb1 : (∑ v ∈ Vb, G.degree v : ℝ) ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      have := hVbbound
      have hcast : ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ)
          = (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]; push_cast; ring
      calc (∑ v ∈ Vb, G.degree v : ℝ) ≤ ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ) := by
            exact_mod_cast hVbbound
        _ = _ := hcast
    have hb2 : (∑ v ∈ Vbᶜ, G.degree v : ℝ)
        ≤ ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
      have hcast : ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ)
          = ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
        rw [Nat.cast_mul, hcompcard, Nat.cast_sub hVble]; push_cast; ring
      calc (∑ v ∈ Vbᶜ, G.degree v : ℝ) ≤ ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ) := by
            exact_mod_cast hcompbound
        _ = _ := hcast
    have h2mR : 2 * (G.edgeFinset.card : ℝ) = ∑ v, (G.degree v : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h2m
    rw [h2mR, ← Finset.sum_add_sum_compl Vb (fun v => (G.degree v : ℝ))]
    linarith [hb1, hb2]
  -- minDegree = (1-δ)n from hδeq
  have hmd : (G.minDegree : ℝ) = (Fintype.card V : ℝ) - δ * Fintype.card V := by linarith [hδeq]
  have hnR : (20 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn20
  have hVbleR : (Vb.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hVble
  have hmle : G.minDegree ≤ Fintype.card V := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    exact le_trans (G.minDegree_le_degree v) (le_trans (hdeg_le v) (by omega))
  have hδn0 : (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
    rw [← hδeq]
    have hml : (G.minDegree : ℝ) ≤ Fintype.card V := by exact_mod_cast hmle
    linarith
  have hδsmall : δ * (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) / 10 := by
    rw [← hδeq]
    have : (9 : ℝ) * Fintype.card V ≤ 10 * G.minDegree := by exact_mod_cast h
    linarith
  -- expand the nonlinear cross terms of h2mr using minDeg = (1-δ)n
  have hVbmd : (Vb.card : ℝ) * (G.minDegree : ℝ)
      = (Vb.card : ℝ) * (Fintype.card V : ℝ) - (Vb.card : ℝ) * (δ * Fintype.card V) := by
    rw [hmd]; ring
  have hnmd : (Fintype.card V : ℝ) * (G.minDegree : ℝ)
      = (Fintype.card V : ℝ)^2 - δ * (Fintype.card V : ℝ)^2 := by rw [hmd]; ring
  nlinarith [h2mr, hnb, hmd, hnR, hVbleR, hδn0, hVbmd, hnmd, hδn2,
    mul_nonneg (show (0:ℝ) ≤ 2 * δ * (Fintype.card V:ℝ) - 4 - (Vb.card:ℝ) by linarith [hnb])
      (show (0:ℝ) ≤ δ * (Fintype.card V:ℝ) - 2 by linarith [hδn2]),
    mul_nonneg (show (0:ℝ) ≤ (Vb.card:ℝ) by positivity) hδn0, hδsmall]

/-- **Dross's Theorem 5 (via the flow route).** If `δ(G) ≥ (9/10)n`, `G` has a fractional
triangle decomposition, using the balanced weight `wΔ = m/(3·#triangles)`. -/

-- Complete graph (minDegree = card-1, card >= 10): uniform weights give a fractional decomp.
theorem complete_fractional (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin_eq : G.minDegree = Fintype.card V - 1) (hcard_ge_10 : 10 ≤ Fintype.card V) :
    FractionalTriangleDecomp G := by
  have hdeg_le : ∀ u : V, G.degree u ≤ Fintype.card V - 1 := by
    intro u
    rw [SimpleGraph.degree]
    calc (G.neighborFinset u).card ≤ (Finset.univ \ {u}).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_sdiff, Finset.mem_singleton]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro h
          rw [h] at hv
          simp only [SimpleGraph.mem_neighborFinset] at hv
          exact G.loopless.irrefl u hv
      _ = Fintype.card V - 1 := by rw [card_sdiff] <;> simp
  have hcomplete : ∀ u v : V, u ≠ v → G.Adj u v := by
    intro u v huv
    have hdeg_u : G.degree u ≥ Fintype.card V - 1 := hmin_eq ▸ G.minDegree_le_degree u
    have hdeg_u_eq : G.degree u = Fintype.card V - 1 := Nat.le_antisymm (hdeg_le u) hdeg_u
    -- neighborFinset u has size card - 1 = size of univ \ {u}
    -- So neighborFinset u = univ \ {u}, hence v ∈ neighborFinset u
    have hsub : G.neighborFinset u ⊆ Finset.univ \ {u} := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h
      rw [h] at hw
      simp only [SimpleGraph.mem_neighborFinset] at hw
      exact G.loopless.irrefl u hw
    have hcard_nei : (G.neighborFinset u).card = (Finset.univ \ {u}).card := by
      rw [SimpleGraph.degree] at hdeg_u_eq
      rw [hdeg_u_eq, card_sdiff] <;> simp
    have hneq : G.neighborFinset u = Finset.univ \ {u} := by
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_nei])
    have hv_in_nei : v ∈ G.neighborFinset u := by
      rw [hneq]
      simp [Ne.symm huv]
    exact G.mem_neighborFinset u v |>.mp hv_in_nei
  -- triThrough G e = card - 2 for every edge e
  have htri : ∀ e ∈ G.edgeFinset, triThrough G e = Fintype.card V - 2 := by
    intro e he
    rw [triThrough]
    -- Extract endpoints from edge
    simp only [SimpleGraph.mem_edgeFinset] at he
    -- e ∈ G.edgeSet means e = s(u, v) for some u ≠ v with G.Adj u v
    rcases e with ⟨u, v⟩
    -- Get that u ≠ v and G.Adj u v from he
    have hadj : G.Adj u v := by
      rw [SimpleGraph.mem_edgeSet] at he
      exact he
    have hne : u ≠ v := by
      intro h
      rw [h] at hadj
      have hloop := G.loopless.irrefl v
      contradiction
    -- triThrough = counting 3-cliques containing edge s(u,v)
    -- For complete graph, this equals the number of 3-element subsets containing {u,v}
    -- which is card - 2 (one for each w ∉ {u, v})
    have hG_complete : G.cliqueFinset 3 = (Finset.univ : Finset V).powersetCard 3 := by
      ext t
      simp only [SimpleGraph.cliqueFinset, Finset.mem_filter, Finset.mem_powersetCard]
      simp_rw [SimpleGraph.isNClique_iff]
      -- Need: t ∈ univ ∧ G.IsClique (↑t) ∧ #t = 3 ↔ t ⊆ univ ∧ #t = 3
      -- Since t ∈ univ and t ⊆ univ are always true, this reduces to showing IsClique for any t
      simp [SimpleGraph.IsClique]
      intro hcard x hx y hy hxy
      exact hcomplete x y hxy
    -- Now count cliques containing s(u, v)
    rw [hG_complete]
    -- triEdges t contains s(u,v) iff u ∈ t and v ∈ t (since u ≠ v)
    have htri_mem : ∀ t : Finset V, Quot.mk (Sym2.Rel V) (u, v) ∈ triEdges t ↔ u ∈ t ∧ v ∈ t := by
      intro t
      simp only [triEdges]
      rw [Finset.mem_filter]
      simp_all [Sym2.IsDiag]
    simp_rw [htri_mem]
    -- Count of 3-element subsets containing both u and v = card - 2
    -- Use a bijection with V \ {u, v}
    have huv_ne : u ≠ v := hne
    have hS_card : (Finset.univ \ (insert u {v} : Finset V)).card = Fintype.card V - 2 := by
      rw [card_sdiff] <;> simp [Finset.card_pair huv_ne]
    -- Bijection between {t ∈ powersetCard 3 univ | u ∈ t ∧ v ∈ t} and V \ {u, v}
    -- Given by t ↦ t \ {u, v} (which has exactly 1 element)
    -- Inverse: w ↦ {u, v, w}
    have hcard : ((Finset.powersetCard 3 Finset.univ).filter (fun t => u ∈ t ∧ v ∈ t)).card = (Finset.univ \ (insert u {v} : Finset V)).card := by
      have heq : ((Finset.powersetCard 3 Finset.univ).filter (fun t => u ∈ t ∧ v ∈ t)) =
        (Finset.univ \ (insert u {v} : Finset V)).image (fun w => insert u (insert v {w})) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image,
          Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro ⟨⟨ht1, ht2⟩, hut, hvt⟩
          have hsub : ({u, v} : Finset V) ⊆ t := by
            simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
            exact ⟨hut, hvt⟩
          have hcard_diff : (t \ (insert u {v} : Finset V)).card = 1 := by
            rw [Finset.card_sdiff_of_subset hsub]
            simp [Finset.card_pair huv_ne, ht2]
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard_diff
          use w
          have hw_mem : w ∈ t \ (insert u {v} : Finset V) := hw ▸ Finset.mem_singleton_self _
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hw_mem
          have hwnu : w ≠ u := fun h => hw_mem.2 (Or.inl h)
          have hwnv : w ≠ v := fun h => hw_mem.2 (Or.inr h)
          refine ⟨by tauto, ?_⟩
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hxt : x ∈ t ↔ x = u ∨ x = v ∨ x = w := by
            constructor
            · intro hx
              by_contra hc
              push_neg at hc
              have hxn : x ∉ (insert u {v} : Finset V) := by simp_all [Finset.mem_insert, Finset.mem_singleton]
              have : x ∈ t \ (insert u {v} : Finset V) := Finset.mem_sdiff.mpr ⟨hx, hxn⟩
              rw [hw] at this; simp at this; tauto
            · intro hx
              rcases hx with rfl | rfl | rfl <;> [exact hut; exact hvt; exact (hw ▸ Finset.mem_singleton_self _ |> Finset.mem_sdiff.mp |>.1)]
          exact hxt.symm
        · rintro ⟨w, ⟨hwnu, hw4⟩⟩
          rw [← hw4]
          simp at hwnu
          refine ⟨⟨Finset.subset_univ _, ?_⟩, by simp, by simp⟩
          have hcard_uv : ({u, v} : Finset V).card = 2 := by simp [huv_ne]
          have hwn : w ∉ ({u, v} : Finset V) := by simp [hwnu.1, hwnu.2]
          rw [show ({u, v, w} : Finset V) = {u, v} ∪ {w} by ext x; simp]
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hwn)]
          rw [hcard_uv, Finset.card_singleton]
      rw [heq, Finset.card_image_of_injOn]
      intro w1 hw1 w2 hw2 heq
      -- heq : insert u (insert v {w1}) = insert u (insert v {w2})
      simp at hw1 heq
      -- w1 ≠ u ∧ w1 ≠ v
      have hmem : w1 ∈ ({u, v, w1} : Finset V) := by simp
      rw [heq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | h | rfl <;> tauto
    rw [hcard, hS_card]
  -- Apply fractional_of_constant_triThrough with T = card - 2
  have hT_pos : 0 < Fintype.card V - 2 := by omega
  exact fractional_of_constant_triThrough G (Fintype.card V - 2) hT_pos htri

theorem dross_fractional_flow_noHDT (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (δ : ℝ) (hδdef : δ = ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V)
    (hδ1 : δ < 1/10)
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
        ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G := by
  -- small-n case (`card < 20`): `G` is complete, uniform weights work
  rcases lt_or_ge (Fintype.card V) 20 with hlt | hn20
  · exact dross_fractional_small G h hlt
  -- `card ≥ 20`: the flow argument
  by_cases hm : G.edgeFinset = ∅
  · -- no edges: the zero weighting is (vacuously) a fractional decomposition
    exact ⟨fun _ => 0, fun _ => le_refl 0, fun e he => absurd (hm ▸ he) (Finset.notMem_empty e)⟩
  · have hmne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hm
    have hT : 0 < (G.cliqueFinset 3).card := exists_triangle_of_edge G h hmne
    have hmpos : 0 < (G.edgeFinset.card : ℝ) := by
      have := Finset.card_pos.mpr hmne; exact_mod_cast this
    set wΔ : ℝ := (G.edgeFinset.card : ℝ) / (3 * (G.cliqueFinset 3).card) with hwΔeq
    have hwΔ : 0 < wΔ := by rw [hwΔeq]; positivity
    have hbal := balance G hT hwΔeq
    -- the ACTUAL deficiency ratio `δ = (n − minDegree)/n` (with `δ < 1/10` under the ε-margin the
    -- application supplies; this uses the real deficiency, so the K₂₁ integrality issue is avoided)
    have hcardpos : 0 < Fintype.card V := by omega
    have hcardposR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcardpos
    obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hcardpos
    have hmclt : G.minDegree < Fintype.card V := by
      have h1 : G.degree v0 < Fintype.card V := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_lt_card
        rw [Finset.ssubset_univ_iff]
        intro hcon
        have : v0 ∈ G.neighborFinset v0 := hcon ▸ Finset.mem_univ v0
        rw [G.mem_neighborFinset] at this; exact G.loopless.irrefl v0 this
      exact lt_of_le_of_lt (G.minDegree_le_degree v0) h1
    have hmd2 : 2 ≤ G.minDegree := by
      have h180 : 180 ≤ 10 * G.minDegree := le_trans (by omega) h; omega
    have hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ) := by
      rw [hδdef]; field_simp
    have hδ0 : 0 < δ := by
      rw [hδdef]; apply div_pos _ hcardposR
      have : (G.minDegree : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hmclt
      linarith
    -- `hmbound` (integrality-safe V_b bound under the WLOG no-high-degree-triangle reduction) is
    -- discharged below via `mbound_of_nb ∘ nb_bound`; `hδ1` and `hbig` are supplied by AX2's
    -- ε-margin and `n₀(ε)` respectively (hypotheses of this theorem).
    have hmbound : 2 * (G.edgeFinset.card : ℝ)
        ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + 2 * (Fintype.card V : ℝ)
          - 6 * δ * (Fintype.card V : ℝ) := by
      -- `hNoHDT` (no heavy triangle) is a hypothesis here; the top-level `dross_fractional_flow`
      -- supplies it via the WLOG heavy-triangle peeling induction. The real degree-sum analysis
      -- is discharged by `mbound_of_nb ∘ nb_bound`.
      have hnb_nat := nb_bound G h hn20 hNoHDT
      have hmle : G.minDegree ≤ Fintype.card V := le_of_lt hmclt
      have hcast : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
          ≤ 2 * δ * (Fintype.card V : ℝ) := by
        have hnb_R : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
            ≤ ((2 * (Fintype.card V - G.minDegree) : ℕ) : ℝ) := by exact_mod_cast hnb_nat
        have hcastR : ((2 * (Fintype.card V - G.minDegree) : ℕ) : ℝ)
            = 2 * ((Fintype.card V : ℝ) - G.minDegree) := by
          rw [Nat.cast_mul, Nat.cast_sub hmle]; push_cast; ring
        rw [hcastR] at hnb_R
        nlinarith [hnb_R, hδ_eq]
      exact mbound_of_nb G δ h hn20 hδ_eq hcast
    obtain ⟨F, hF⟩ := exists_flow_M G h wΔ hwΔ hbal δ hδ0 hδ1 hmd2 hδ_eq hmbound hbig
    exact decomp_of_maxflowM G wΔ hwΔ hmd2 hbal F hF hNoHDT


private lemma heavy_triangle_vertices_distinct (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  exact ⟨huv.ne, huw.ne, hvw.ne⟩

private lemma triEdges_heavy_triangle_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    triEdges {u, v, w} ⊆ G.edgeFinset := by
  simp only [subset_iff, Sym2.forall, triEdges, mem_filter, mem_sym2_iff,
    mem_insert, mem_singleton, mem_edgeFinset]
  rintro a b ⟨hab, hdiag⟩
  have ha : a = u ∨ a = v ∨ a = w := hab a (by simp)
  have hb : b = u ∨ b = v ∨ b = w := hab b (by simp)
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [SimpleGraph.mem_edgeSet, G.adj_comm]

private lemma triEdges_heavy_triangle_card (G : SimpleGraph V) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    #(triEdges {u, v, w}) = 3 := by
  have hne := heavy_triangle_vertices_distinct G huv huw hvw
  have heq : triEdges {u, v, w} = {s(u, v), s(u, w), s(v, w)} := by
    ext e
    induction e using Sym2.inductionOn with | _ a b =>
      simp only [triEdges, mem_filter, mem_sym2_iff, mem_insert, mem_singleton,
        Sym2.mk_isDiag_iff, Sym2.eq_iff]
      aesop
  rw [heq]
  simp [hne.1, hne.2.1, hne.2.2]

private lemma peeled_heavy_triangle_degree_add_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w x : V} :
    G.degree x ≤ (G.deleteEdges (triEdges {u, v, w})).degree x + 2 := by
  rw [← G.card_neighborFinset_eq_degree, ← (G.deleteEdges _).card_neighborFinset_eq_degree]
  let A := (G.deleteEdges (triEdges {u,v,w})).neighborFinset x
  let B := G.neighborFinset x
  have hAB : A ⊆ B := by
    intro y hy
    simp only [B, G.mem_neighborFinset]
    exact (deleteEdges_adj.mp ((G.deleteEdges _).mem_neighborFinset x y |>.mp
      (by simpa [A] using hy))).1
  have hBA : B \ A ⊆ ({u,v,w} : Finset V) := by
    intro y hy
    have hyadj : G.Adj x y := G.mem_neighborFinset x y |>.mp (mem_sdiff.mp hy).1
    simp only [mem_insert, mem_singleton]
    by_contra hn
    have hnot : s(x,y) ∉ triEdges {u,v,w} := by
      intro he
      have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) y (by simp)
      exact hn (by simpa using hall)
    apply (mem_sdiff.mp hy).2
    show y ∈ A
    simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
  have hcard : #(B \ A) ≤ 2 := by
    by_cases hempty : B \ A = ∅
    · simp [hempty]
    · obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hempty
      have hxmem : x ∈ ({u,v,w} : Finset V) := by
        have hyadj : G.Adj x y := G.mem_neighborFinset x y |>.mp (mem_sdiff.mp hy).1
        by_contra hx
        have hnot : s(x,y) ∉ triEdges {u,v,w} := by
          intro he
          have hall := (mem_sym2_iff.mp (mem_filter.mp he).1) x (by simp)
          exact hx (by simpa using hall)
        apply (mem_sdiff.mp hy).2
        show y ∈ A
        simp [A, (G.deleteEdges _).mem_neighborFinset, deleteEdges_adj, hyadj, hnot]
      have hsub : B \ A ⊆ ({u,v,w} : Finset V).erase x := by
        intro z hz
        refine mem_erase.mpr ⟨?_, hBA hz⟩
        exact (G.mem_neighborFinset x z |>.mp (mem_sdiff.mp hz).1).ne.symm
      have hc := card_le_card hsub
      have hthree : #({u,v,w} : Finset V) ≤ 3 := by
        calc
          #({u,v,w} : Finset V) ≤ #({v,w} : Finset V) + 1 := card_insert_le _ _
          _ ≤ (#{w} + 1) + 1 := by gcongr; exact card_insert_le _ _
          _ ≤ 3 := by simp
      have herase : #(({u,v,w} : Finset V).erase x) + 1 = #({u,v,w} : Finset V) :=
        card_erase_add_one hxmem
      omega
  rw [← card_sdiff_add_card_inter B A, inter_eq_right.mpr hAB]
  change #(B \ A) + #A ≤ #A + 2
  omega

private lemma peeled_heavy_triangle_minDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (hu : G.minDegree + 2 ≤ G.degree u)
    (hv : G.minDegree + 2 ≤ G.degree v)
    (hw : G.minDegree + 2 ≤ G.degree w) :
    (G.deleteEdges (triEdges {u, v, w})).minDegree = G.minDegree := by
  letI : Nonempty V := ⟨u⟩
  apply Nat.le_antisymm
  · exact minDegree_le_minDegree (deleteEdges_le _)
  · apply le_minDegree_of_forall_le_degree
    intro x
    by_cases hx : x = u ∨ x = v ∨ x = w
    · rcases hx with hx | hx | hx
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := u)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := v)
        subst x
        omega
      · have hb := peeled_heavy_triangle_degree_add_two G (u := u) (v := v) (w := w) (x := w)
        subst x
        omega
    · have hxu : x ≠ u := fun h => hx (Or.inl h)
      have hxv : x ≠ v := fun h => hx (Or.inr (Or.inl h))
      have hxw : x ≠ w := fun h => hx (Or.inr (Or.inr h))
      have hdeg : (G.deleteEdges (triEdges {u,v,w})).degree x = G.degree x := by
        rw [← G.card_neighborFinset_eq_degree,
          ← (G.deleteEdges _).card_neighborFinset_eq_degree]
        congr 1
        ext y
        simp only [mem_neighborFinset, deleteEdges_adj]
        constructor
        · exact And.left
        · intro hxy
          refine ⟨hxy, ?_⟩
          intro he
          have he' : s(x,y) ∈ (triEdges {u,v,w}) := he
          rw [triEdges, mem_filter] at he'
          have hxmem := (mem_sym2_iff.mp he'.1) x (by simp)
          simp only [mem_insert, mem_singleton] at hxmem
          exact hxmem.elim hxu (fun h => h.elim hxv hxw)
      rw [hdeg]
      exact G.minDegree_le_degree x

private lemma peeled_heavy_triangle_fewer_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (G.deleteEdges (triEdges {u, v, w})).edgeFinset.card < G.edgeFinset.card := by
  have hsub := triEdges_heavy_triangle_subset G huv huw hvw
  have hcard := triEdges_heavy_triangle_card G huv huw hvw
  rw [edgeFinset_deleteEdges, card_sdiff_of_subset hsub]
  apply Nat.sub_lt
  · have := card_le_card hsub
    omega
  · omega

private lemma cliqueFinset_deleteEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) :
    (G.deleteEdges S).cliqueFinset n ⊆ G.cliqueFinset n := by
  intro t ht
  rw [mem_cliqueFinset_iff] at ht ⊢
  exact ht.mono (deleteEdges_le _)

private lemma sum_truncated_cliques (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (n : ℕ) (a : Finset V → ℝ) (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset n,
      if e ∈ triEdges t then (if t ∈ (G.deleteEdges S).cliqueFinset n then a t else 0) else 0) =
    ∑ t ∈ (G.deleteEdges S).cliqueFinset n, if e ∈ triEdges t then a t else 0 := by
  rw [← sum_subset (cliqueFinset_deleteEdges_subset G S n)]
  · apply sum_congr rfl
    intro t ht
    simp [ht]
  · intro t htG htG'
    simp [htG']

private lemma deleted_edge_not_in_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) {e : Sym2 V} (heS : e ∈ S) {n : ℕ} {t : Finset V}
    (ht : t ∈ (G.deleteEdges S).cliqueFinset n) : e ∉ triEdges t := by
  intro het
  induction e using Sym2.inductionOn with | _ x y =>
    have hmem := mem_filter.mp het
    have hxt := mem_sym2_iff.mp hmem.1 x (by simp)
    have hyt := mem_sym2_iff.mp hmem.1 y (by simp)
    have hxy : x ≠ y := by simpa using hmem.2
    have hc := (mem_cliqueFinset_iff.mp ht).isClique hxt hyt hxy
    exact (deleteEdges_adj.mp hc).2 heS

private lemma triangle_indicator_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (e : Sym2 V) :
    (∑ t ∈ G.cliqueFinset 3, if e ∈ triEdges t then (if t = {u,v,w} then (1 : ℝ) else 0) else 0) =
      if e ∈ triEdges {u,v,w} then 1 else 0 := by
  have hT : {u,v,w} ∈ G.cliqueFinset 3 :=
    mem_cliqueFinset_iff.mpr (is3Clique_iff.mpr ⟨u,v,w,huv,huw,hvw,rfl⟩)
  rw [sum_eq_single {u,v,w}]
  · simp
  · intro t ht hne
    simp [hne]
  · intro hnot
    exact (hnot hT).elim

private lemma lift_fractional_decomp_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hdec : FractionalTriangleDecomp (G.deleteEdges (triEdges {u, v, w}))) :
    FractionalTriangleDecomp G := by
  classical
  let T : Finset V := {u,v,w}
  let G' := G.deleteEdges (triEdges T)
  rcases hdec with ⟨a, ha, hcov⟩
  refine ⟨fun t => (if t ∈ G'.cliqueFinset 3 then a t else 0) +
      (if t = T then 1 else 0), ?_, ?_⟩
  · intro t
    exact add_nonneg (by split <;> simp_all) (by split <;> norm_num)
  · intro e he
    have hsplit :
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then
            ((if t ∈ G'.cliqueFinset 3 then a t else 0) + (if t = T then 1 else 0)) else 0) =
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t ∈ G'.cliqueFinset 3 then a t else 0) else 0) +
        (∑ t ∈ G.cliqueFinset 3,
          if e ∈ triEdges t then (if t = T then 1 else 0) else 0) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t ht
      by_cases het : e ∈ triEdges t <;> simp [het]
    rw [hsplit, sum_truncated_cliques G (triEdges T) 3 a e,
      triangle_indicator_sum G huv huw hvw e]
    by_cases heT : e ∈ triEdges T
    · have hz : (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) = 0 := by
        apply sum_eq_zero
        intro t ht
        simp [deleted_edge_not_in_clique G (triEdges T) heT ht]
      change (∑ t ∈ G'.cliqueFinset 3, if e ∈ triEdges t then a t else 0) +
        (if e ∈ triEdges T then 1 else 0) = 1
      rw [hz, if_pos heT, zero_add]
    · have heG' : e ∈ G'.edgeFinset := by
        rw [edgeFinset_deleteEdges]
        exact mem_sdiff.mpr ⟨he, heT⟩
      simpa [G', T, heT] using hcov e heG'

/-- **Dross Theorem 5, exact 9/10 threshold, no-heavy-triangle case.** If `δ(G) ≥ (9/10)n` (i.e.
`9·card ≤ 10·minDegree`) and `G` has no heavy triangle (`hNoHDT`), then `G` has a fractional
triangle decomposition. Uses the *actual* deficiency `δ = (card−minDegree)/card ≤ 1/10` and the
fine `+n` m-bound (`mbound_tight`); near-complete graphs (`card−minDegree ≤ 1`, i.e. complete) are
handled by `complete_fractional`. No `hbig` / `n₀(ε)` needed. -/
theorem dross_fractional_flow_noHDT_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
      G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
      G.minDegree + 2 ≤ G.degree w → False) :
    FractionalTriangleDecomp G := by
  rcases lt_or_ge (Fintype.card V) 20 with hlt | hn20
  · exact dross_fractional_small G h hlt
  by_cases hm : G.edgeFinset = ∅
  · exact ⟨fun _ => 0, fun _ => le_refl 0, fun e he => absurd (hm ▸ he) (Finset.notMem_empty e)⟩
  · have hmne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hm
    have hT : 0 < (G.cliqueFinset 3).card := exists_triangle_of_edge G h hmne
    have hmpos : 0 < (G.edgeFinset.card : ℝ) := by
      have := Finset.card_pos.mpr hmne; exact_mod_cast this
    set wΔ : ℝ := (G.edgeFinset.card : ℝ) / (3 * (G.cliqueFinset 3).card) with hwΔeq
    have hwΔ : 0 < wΔ := by rw [hwΔeq]; positivity
    have hbal := balance G hT hwΔeq
    have hcardpos : 0 < Fintype.card V := by omega
    have hcardposR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hcardpos
    obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hcardpos
    have hmle : G.minDegree ≤ Fintype.card V - 1 := by
      have := G.degree_lt_card_verts v0
      exact le_trans (G.minDegree_le_degree v0) (by omega)
    have hmclt : G.minDegree < Fintype.card V := by omega
    have hmd2 : 2 ≤ G.minDegree := by
      have h180 : 180 ≤ 10 * G.minDegree := le_trans (by omega) h; omega
    set δ : ℝ := ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V with hδdef
    have hδ_eq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ) := by
      rw [hδdef]; field_simp
    have hδ0 : 0 < δ := by
      rw [hδdef]; apply div_pos _ hcardposR
      have : (G.minDegree : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hmclt
      linarith
    have hδ1 : δ ≤ 1/10 := by
      rw [hδdef, div_le_iff₀ hcardposR]
      have hc : (9:ℝ) * Fintype.card V ≤ 10 * G.minDegree := by exact_mod_cast h
      linarith
    rcases Nat.lt_or_ge (Fintype.card V - G.minDegree) 2 with hdef1 | hdef2
    · -- near-complete: `minDegree = card − 1`, so `G` is complete
      have hmin_eq : G.minDegree = Fintype.card V - 1 := by omega
      exact complete_fractional G hmin_eq (by omega)
    · -- genuine deficiency `card − minDegree ≥ 2`: the exact flow argument
      have hδn2 : (2:ℝ) ≤ δ * (Fintype.card V : ℝ) := by
        rw [← hδ_eq]
        have h1 : (2:ℝ) ≤ ((Fintype.card V - G.minDegree : ℕ) : ℝ) := by exact_mod_cast hdef2
        rwa [Nat.cast_sub (show G.minDegree ≤ Fintype.card V by omega)] at h1
      have hmbound : 2 * (G.edgeFinset.card : ℝ)
          ≤ (1 - δ + 2 * δ^2) * (Fintype.card V : ℝ)^2 + 4 + (Fintype.card V : ℝ)
            - 6 * δ * (Fintype.card V : ℝ) := by
        have hnb_nat := nb_bound_tight G h hn20 hdef2 hNoHDT
        have hcast : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
            ≤ 2 * δ * (Fintype.card V : ℝ) - 4 := by
          have hnb_R : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
              ≤ ((2 * (Fintype.card V - G.minDegree) - 4 : ℕ) : ℝ) := by exact_mod_cast hnb_nat
          have hcastR : ((2 * (Fintype.card V - G.minDegree) - 4 : ℕ) : ℝ)
              = 2 * ((Fintype.card V : ℝ) - G.minDegree) - 4 := by
            rw [Nat.cast_sub (show 4 ≤ 2 * (Fintype.card V - G.minDegree) by omega),
                Nat.cast_mul, Nat.cast_sub (show G.minDegree ≤ Fintype.card V by omega)]
            push_cast; ring
          rw [hcastR] at hnb_R
          nlinarith [hnb_R, hδ_eq]
        exact mbound_tight G δ h hn20 hδ_eq hδn2 hcast
      obtain ⟨F, hF⟩ := exists_flow_M_exact G h wΔ hwΔ hbal δ hδ0 hδ1 hn20 hmd2 hδ_eq hmbound
      exact decomp_of_maxflowM G wΔ hwΔ hmd2 hbal F hF hNoHDT

theorem dross_fractional_flow (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (δ : ℝ) (hδdef : δ = ((Fintype.card V : ℝ) - G.minDegree) / Fintype.card V)
    (hδ1 : δ < 1/10)
    (hbig : 4 + 2 * (Fintype.card V : ℝ) - 12 * δ * (Fintype.card V : ℝ)
        ≤ (1 - 11 * δ + 10 * δ^2) * (Fintype.card V : ℝ)^2) :
    FractionalTriangleDecomp G := by
  classical
  induction m : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
        G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
        G.minDegree + 2 ≤ G.degree w → False
    · exact dross_fractional_flow_noHDT G h δ hδdef hδ1 hbig hNoHDT
    · push_neg at hNoHDT
      obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw, _⟩ := hNoHDT
      let G' := G.deleteEdges (triEdges {u,v,w})
      have hmin : G'.minDegree = G.minDegree :=
        peeled_heavy_triangle_minDegree G hu hv hw
      have hlt : G'.edgeFinset.card < G.edgeFinset.card :=
        peeled_heavy_triangle_fewer_edges G huv huw hvw
      have hdec : FractionalTriangleDecomp G' := by
        apply ih G'.edgeFinset.card (by omega) G'
        · simpa [hmin] using h
        · simpa [hmin] using hδdef
        · rfl
      exact lift_fractional_decomp_triangle G huv huw hvw hdec

/-- **Dross's Theorem 5 (exact 9/10 threshold, full).** If `δ(G) ≥ (9/10)n` (i.e.
`9·card ≤ 10·minDegree`), then `G` has a fractional triangle decomposition. WLOG heavy-triangle
peeling reduces to the no-heavy-triangle case (`dross_fractional_flow_noHDT_exact`); no ε-margin or
`n₀(ε)` is needed — the argument uses the actual deficiency `δ ≤ 1/10` throughout. -/
theorem dross_fractional_flow_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    FractionalTriangleDecomp G := by
  classical
  induction m : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
        G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
        G.minDegree + 2 ≤ G.degree w → False
    · exact dross_fractional_flow_noHDT_exact G h hNoHDT
    · push_neg at hNoHDT
      obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw, _⟩ := hNoHDT
      let G' := G.deleteEdges (triEdges {u,v,w})
      have hmin : G'.minDegree = G.minDegree :=
        peeled_heavy_triangle_minDegree G hu hv hw
      have hlt : G'.edgeFinset.card < G.edgeFinset.card :=
        peeled_heavy_triangle_fewer_edges G huv huw hvw
      have hdec : FractionalTriangleDecomp G' := by
        apply ih G'.edgeFinset.card (by omega) G'
        · simpa [hmin] using h
        · rfl
      exact lift_fractional_decomp_triangle G huv huw hvw hdec

end Ax2.DrossNet
