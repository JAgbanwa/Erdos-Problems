/-
  General finite max-flow / min-cut, via augmenting paths (Route B core).

  Builds on the `Network`/`Flow`/`Cut` layer and weak duality in `Ax2.Explore.RouteB`.

  Decomposition:
    (1) saturated_cut_value  — flow=capacity for a residual-closed cut   [PROVED, no paths]
    (2) reachable_saturates  — the residual-reachable set is such a cut   [PROVED]
    (3) max_flow_exists      — a maximum-value flow exists (compactness)  [PROVED]
    (4) t_not_reachable      — max flow ⇒ sink unreachable (augment)      [PROVED]
    ⇒ maxflow_eq_mincut
-/
import Ax2.Explore.RouteB
import Ax2.Explore.NodupChain
import Ax2.Explore.PathBalance

namespace Ax2.RouteB

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Residual step: there is spare capacity on the (skew) edge `u → v`. -/
def ResStep (Net : Network N) (F : Flow Net) (u v : N) : Prop :=
  0 < Net.cap u v - F.f u v

/-- Residual reachability from the source. -/
def Reaches (Net : Network N) (F : Flow Net) (v : N) : Prop :=
  Relation.ReflTransGen (ResStep Net F) Net.s v

open scoped Classical in
/-- The set of nodes reachable from `s` in the residual graph. -/
noncomputable def reachableSet {Net : Network N} (F : Flow Net) : Finset N :=
  {v | Reaches Net F v}.toFinset

open scoped Classical in
@[simp] lemma mem_reachableSet {Net : Network N} (F : Flow Net) (v : N) :
    v ∈ reachableSet F ↔ Reaches Net F v := by
  unfold reachableSet; rw [Set.mem_toFinset]; rfl

/-- **(1) Saturated-cut value (PROVED).** If every edge leaving `S` is saturated, then the flow
value equals the cut capacity. No augmenting paths — pure flow/cut accounting. -/
lemma saturated_cut_value {Net : Network N} (F : Flow Net) (S : Finset N)
    (hs : Net.s ∈ S) (ht : Net.t ∉ S)
    (hsat : ∀ u ∈ S, ∀ v ∉ S, F.f u v = Net.cap u v) :
    F.value = (⟨S, hs, ht⟩ : Cut Net).capacity := by
  rw [F.value_eq_flow_across ⟨S, hs, ht⟩]
  unfold Cut.capacity
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_sdiff] at hv
  exact hsat u hu v hv.2

/-- **(2) The residual-reachable set saturates its outgoing edges (PROVED).** If a node `u` is
reachable and `v` is not, the edge `u → v` has no residual capacity, hence is saturated. -/
lemma reachable_saturates {Net : Network N} (F : Flow Net)
    {u v : N} (hu : u ∈ reachableSet F) (hv : v ∉ reachableSet F) :
    F.f u v = Net.cap u v := by
  have hnres : ¬ ResStep Net F u v := by
    intro hres
    apply hv
    rw [mem_reachableSet] at hu ⊢
    exact Relation.ReflTransGen.tail hu hres
  -- ¬ (0 < cap - f)  ⇒  cap ≤ f ; with f ≤ cap ⇒ f = cap
  unfold ResStep at hnres
  have h1 : Net.cap u v - F.f u v ≤ 0 := not_lt.mp hnres
  have h2 : F.f u v ≤ Net.cap u v := F.capacitated u v
  linarith

/-- The underlying set of feasible flow-functions of a network. -/
def FlowSet (Net : Network N) : Set (N → N → ℝ) :=
  {g | (∀ u v, g u v = - g v u) ∧ (∀ u v, g u v ≤ Net.cap u v) ∧
       (∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0)}

lemma flowSet_isClosed (Net : Network N) : IsClosed (FlowSet Net) := by
  unfold FlowSet
  have hskew : IsClosed {g : N → N → ℝ | ∀ u v, g u v = - g v u} := by
    rw [Set.setOf_forall]; refine isClosed_iInter (fun u => ?_)
    rw [Set.setOf_forall]; refine isClosed_iInter (fun v => ?_)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hcap : IsClosed {g : N → N → ℝ | ∀ u v, g u v ≤ Net.cap u v} := by
    rw [Set.setOf_forall]; refine isClosed_iInter (fun u => ?_)
    rw [Set.setOf_forall]; refine isClosed_iInter (fun v => ?_)
    exact isClosed_le (by fun_prop) continuous_const
  have hcons : IsClosed {g : N → N → ℝ | ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0} := by
    rw [Set.setOf_forall]; refine isClosed_iInter (fun u => ?_)
    by_cases hu : u ≠ Net.s ∧ u ≠ Net.t
    · have : {g : N → N → ℝ | u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0}
            = {g : N → N → ℝ | ∑ v, g u v = 0} := by
        ext g; simp [hu.1, hu.2]
      rw [this]; exact isClosed_eq (by fun_prop) continuous_const
    · have : {g : N → N → ℝ | u ≠ Net.s → u ≠ Net.t → ∑ v, g u v = 0} = Set.univ := by
        ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ hu
      rw [this]; exact isClosed_univ
  exact (hskew.inter (hcap.inter hcons))

lemma flowSet_isBounded (Net : Network N) : Bornology.IsBounded (FlowSet Net) := by
  -- every coordinate is pinned in [-cap v u, cap u v]; bound by the max capacity
  obtain ⟨M, hM⟩ := (Set.finite_range (fun p : N × N => Net.cap p.1 p.2)).bddAbove
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M ⊔ 0, ?_⟩
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (le_sup_right)]
  intro u
  rw [pi_norm_le_iff_of_nonneg (le_sup_right)]
  intro v
  rw [Real.norm_eq_abs, abs_le]
  have hup : g u v ≤ Net.cap u v := hg.2.1 u v
  have hlo : - g u v = g v u := (hg.1 u v).symm ▸ (neg_neg _)
  have hup2 : g v u ≤ Net.cap v u := hg.2.1 v u
  have hMuv : Net.cap u v ≤ M := hM ⟨(u, v), rfl⟩
  have hMvu : Net.cap v u ≤ M := hM ⟨(v, u), rfl⟩
  constructor
  · have : - g u v ≤ M := by rw [hlo]; linarith
    linarith [le_sup_left (a := M) (b := (0:ℝ))]
  · linarith [le_sup_left (a := M) (b := (0:ℝ))]

/-- **(3) A maximum-value flow exists (PROVED).** The flow polytope is compact (closed + bounded
in the finite-dimensional space `N → N → ℝ`) and `value` is continuous, so it is attained. -/
theorem max_flow_exists (Net : Network N) :
    ∃ F : Flow Net, ∀ F' : Flow Net, F'.value ≤ F.value := by
  have hcompact : IsCompact (FlowSet Net) :=
    Metric.isCompact_of_isClosed_isBounded (flowSet_isClosed Net) (flowSet_isBounded Net)
  have hne : (FlowSet Net).Nonempty := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
    · intro u v; simp
    · intro u v; simpa using Net.capNonneg u v
    · intro u _ _; simp
  have hcont : ContinuousOn (fun g : N → N → ℝ => ∑ v, g Net.s v) (FlowSet Net) := by
    fun_prop
  obtain ⟨g, hg, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  refine ⟨⟨g, hg.1, hg.2.1, hg.2.2⟩, ?_⟩
  intro F'
  exact hmax (show F'.f ∈ FlowSet Net from ⟨F'.skew, F'.capacitated, F'.conserved⟩)

/-- **Augmenting edge-set kernel (combinatorial).** If the sink is residual-reachable, a
simple residual `s→t` path yields a finite set `P` of directed residual edges with a uniform slack
`δ > 0`, no 2-cycles, and unit `s`-to-`t` degree balance (source has net out-degree `+1`, sink
`−1`, every other node balanced). This is pure path combinatorics — no flow content. -/
theorem augEdges_exists {Net : Network N} (F : Flow Net) (hreach : Reaches Net F Net.t) :
    ∃ (P : Finset (N × N)) (δ : ℝ), 0 < δ ∧
      (∀ p ∈ P, δ ≤ Net.cap p.1 p.2 - F.f p.1 p.2) ∧
      (∀ u v, (u, v) ∈ P → (v, u) ∉ P) ∧
      (∀ u, (∑ v, (if (u, v) ∈ P then (1 : ℝ) else 0))
              - (∑ v, if (v, u) ∈ P then (1 : ℝ) else 0)
            = (if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0)) := by
  -- (A) simple residual s→t path
  obtain ⟨l, hchain, hhead, hlast, hnd⟩ :=
    Ax2.NodupChain.exists_nodup_chain hreach Net.st
  set P := Ax2.PathBalance.pairs l with hP
  -- l has ≥ 2 elements, so P is nonempty
  have hl2 : l.zip l.tail ≠ [] := by
    intro he
    -- zip empty ⇒ l.tail = [] ⇒ l = [] or singleton ⇒ head = last ⇒ s = t
    have htail : l.tail = [] := by
      cases l with
      | nil => simp_all
      | cons a t =>
        cases t with
        | nil => rfl
        | cons b t' => simp [List.zip_cons_cons] at he
    have : l.length ≤ 1 := by
      cases l with
      | nil => simp
      | cons a t => simp only [List.tail_cons] at htail; simp [htail]
    interval_cases h : l.length
    · exact absurd (List.length_eq_zero_iff.mp h ▸ hhead) (by simp)
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      simp only [List.head?_cons, List.getLast?_singleton] at hhead hlast
      exact Net.st (by rw [← Option.some_inj.mp hhead, ← Option.some_inj.mp hlast])
  have hPne : P.Nonempty := by
    rw [hP, Ax2.PathBalance.pairs]
    obtain ⟨e, es, hz⟩ := List.exists_cons_of_ne_nil hl2
    rw [hz]; exact ⟨e, by simp⟩
  -- every edge of P is a residual edge
  have hpos : ∀ p ∈ P, 0 < Net.cap p.1 p.2 - F.f p.1 p.2 := by
    intro p hp
    have hr : ResStep Net F p.1 p.2 :=
      Ax2.PathBalance.pairs_rel l hchain (u := p.1) (v := p.2) (by rw [← hP]; simpa using hp)
    exact hr
  refine ⟨P, P.inf' hPne (fun p => Net.cap p.1 p.2 - F.f p.1 p.2), ?_, ?_, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]; exact hpos
  · intro p hp; exact Finset.inf'_le _ hp
  · intro u v huv; exact Ax2.PathBalance.pairs_antisymm l hnd huv
  · intro u
    have hb := Ax2.PathBalance.degree_balance l hnd u
    rw [hP, hb, hhead, hlast]
    simp only [Option.some.injEq, eq_comm]

/-- **(4) Maximality ⇒ sink unreachable (PROVED from the kernel).** Given the augmenting edge-set,
the pushed flow `F' = F + δ·(P − Pᵀ)` is feasible with value `F.value + δ > F.value`,
contradicting maximality. -/
theorem t_not_reachable_of_max {Net : Network N} (F : Flow Net)
    (hmax : ∀ F' : Flow Net, F'.value ≤ F.value) :
    Net.t ∉ reachableSet F := by
  rw [mem_reachableSet]
  intro hreach
  obtain ⟨P, δ, hδ, hres, hanti, hbal⟩ := augEdges_exists F hreach
  -- the augmenting push, skew by construction
  set push : N → N → ℝ :=
    fun u v => δ * ((if (u, v) ∈ P then 1 else 0) - (if (v, u) ∈ P then 1 else 0)) with hpush
  have push_skew : ∀ u v, push u v = - push v u := by
    intro u v; simp only [hpush]; ring
  -- row sums of the push follow the degree balance
  have hrowsum : ∀ u, ∑ v, push u v
      = δ * ((if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0)) := by
    intro u
    simp only [hpush]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    exact hbal u
  -- the augmented flow
  have cap' : ∀ u v, F.f u v + push u v ≤ Net.cap u v := by
    intro u v
    simp only [hpush]
    by_cases huv : (u, v) ∈ P
    · have hvu : (v, u) ∉ P := hanti u v huv
      simp only [huv, hvu, if_true, if_false]
      have := hres (u, v) huv
      simp only at this
      linarith
    · have hle : F.f u v ≤ Net.cap u v := F.capacitated u v
      by_cases hvu : (v, u) ∈ P
      · simp only [huv, hvu, if_true, if_false]; nlinarith [hδ]
      · simp only [huv, hvu, if_false]; linarith
  have cons' : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, (F.f u v + push u v) = 0 := by
    intro u hus hut
    rw [Finset.sum_add_distrib, F.conserved u hus hut, hrowsum u]
    simp [hus, hut]
  let F' : Flow Net :=
    { f := fun u v => F.f u v + push u v
      skew := by intro u v; rw [F.skew u v, push_skew u v]; ring
      capacitated := cap'
      conserved := cons' }
  -- value strictly increases by δ
  have hval : F'.value = F.value + δ := by
    show ∑ v, (F.f Net.s v + push Net.s v) = F.value + δ
    rw [Finset.sum_add_distrib, hrowsum Net.s, if_pos rfl, if_neg Net.st]
    simp only [Flow.value]
    ring
  have := hmax F'
  rw [hval] at this
  linarith

/-- **Max-flow / min-cut (assembled).** There is a flow and an s–t cut with equal value. -/
theorem maxflow_eq_mincut (Net : Network N) :
    ∃ (F : Flow Net) (C : Cut Net), F.value = C.capacity := by
  obtain ⟨F, hmax⟩ := max_flow_exists Net
  have ht : Net.t ∉ reachableSet F := t_not_reachable_of_max F hmax
  have hs : Net.s ∈ reachableSet F := by
    rw [mem_reachableSet]; exact Relation.ReflTransGen.refl
  refine ⟨F, ⟨reachableSet F, hs, ht⟩, ?_⟩
  exact saturated_cut_value F (reachableSet F) hs ht
    (fun u hu v hv => reachable_saturates F hu hv)

end Ax2.RouteB
