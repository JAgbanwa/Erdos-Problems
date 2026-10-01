/-
The edit route, Lemma K: a graph of rooted defect `≤ s` has `o(n^k)` labelled induced `k`-cycles, for every
fixed `k ≥ 4`.

`cycTuples G k` is the set of injective tuples `f : Fin k → Fin n` with `G.Adj (f i) (f j) ↔ (cycleGraph k).Adj i j`,
i.e. the labelled induced copies of `C_k`. If there were `δ n^k` of them, Erdős's theorem for k-partite k-graphs
(`PaperIV.ErdosKPartite.erdos_kpartite`, with `t = s + 1`) gives parts `W 0, …, W (k−1)` of size `s + 1` all of whose
transversals are induced cycles in that cyclic order. The parts are disjoint, since the tuples are injective.
Consecutive parts are complete to each other and non-consecutive parts have no edges between them. These are the
hypotheses of Lemma B (`PaperIV.EditRoute.noBlowup_of_rootedDefect`), which contradicts `RootedDefectAt G s`.

Layer E (unconditional): axiom target = {propext, Classical.choice, Quot.sound}.
-/
import PaperIV.ErdosKPartite
import PaperIV.EditRouteCliqueRecovery
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace PaperIV.EditRoute

open Finset PaperIV.RootedSimplicialDefect

/-- Arithmetic of the cyclic order: `(k − b + a) mod k = 1 ↔ (b + 1) mod k = a`. -/
theorem sub_mod_eq_one_iff {k a b : ℕ} (ha : a < k) (hb : b < k) (hk : 2 ≤ k) :
    (k - b + a) % k = 1 ↔ (b + 1) % k = a := by
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [Nat.mod_eq_of_lt (by omega)]
    rcases Nat.lt_or_ge (b + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have hb1 : b + 1 = k := by omega
      rw [hb1, Nat.mod_self]; omega
  · have e : k - b + a = (a - b) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rcases Nat.lt_or_ge (b + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · have hb1 : b + 1 = k := by omega
      rw [hb1, Nat.mod_self]; omega

/-- The cycle graph's adjacency in modular form. -/
theorem cycleGraph_adj_iff_mod {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) :
    (SimpleGraph.cycleGraph k).Adj i j ↔ (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val := by
  rw [SimpleGraph.cycleGraph_adj', Fin.val_sub, Fin.val_sub,
    sub_mod_eq_one_iff i.isLt j.isLt hk, sub_mod_eq_one_iff j.isLt i.isLt hk]
  tauto

/-- Labelled induced copies of `C_k`: injective tuples realizing the cycle adjacency exactly. -/
def cycTuples {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Finset (Fin k → Fin n) :=
  univ.filter (fun f => Function.Injective f ∧ ∀ i j, G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph k).Adj i j)

/-- A transversal through two prescribed vertices. -/
theorem exists_transversal {k n : ℕ} (W : Fin k → Finset (Fin n)) (hne : ∀ l, (W l).Nonempty)
    {i j : Fin k} {x y : Fin n} (hx : x ∈ W i) (hy : y ∈ W j) (hij : i ≠ j ∨ x = y) :
    ∃ f : Fin k → Fin n, (∀ l, f l ∈ W l) ∧ f i = x ∧ f j = y := by
  classical
  refine ⟨fun l => if l = i then x else if l = j then y else (hne l).choose, ?_, by simp, ?_⟩
  · intro l
    by_cases hli : l = i
    · subst hli; simpa using hx
    · by_cases hlj : l = j
      · subst hlj; simpa [hli] using hy
      · simpa [hli, hlj] using (hne l).choose_spec
  · by_cases hji : j = i
    · subst hji
      rcases hij with h | h
      · exact absurd rfl h
      · simp [h]
    · simp [hji]

/-- **Lemma K.** For fixed `s` and `k ≥ 4`, graphs of rooted defect `≤ s` have `o(n^k)` labelled induced `k`-cycles. -/
theorem lemmaK (s k : ℕ) (hk : 4 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
      ((cycTuples G k).card : ℝ) < δ * (n : ℝ) ^ k := by
  classical
  obtain ⟨N, hN⟩ := PaperIV.ErdosKPartite.erdos_kpartite (s + 1) k δ hδ
  refine ⟨N, fun n hn G _ hG => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨W, hWcard, hWcov⟩ := hN n hn (cycTuples G k) hlt
  have hne : ∀ l, (W l).Nonempty := fun l => card_pos.mp (by rw [hWcard l]; omega)
  have hmem : ∀ f : Fin k → Fin n, (∀ l, f l ∈ W l) →
      Function.Injective f ∧ ∀ i j, G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph k).Adj i j := fun f hf =>
    (mem_filter.mp (hWcov f hf)).2
  have hk2 : 2 ≤ k := by omega
  -- the parts, indexed by naturals as Lemma B expects
  let P : ℕ → Finset (Fin n) := fun i => if h : i < k then W ⟨i, h⟩ else ∅
  have hP : ∀ i (h : i < k), P i = W ⟨i, h⟩ := fun i h => by simp [P, h]
  apply noBlowup_of_rootedDefect hk P _ _ _ _ hG
  · intro i hi; rw [hP i hi, hWcard]
  · intro i hi j hj hij
    rw [hP i hi, hP j hj, Finset.disjoint_left]
    intro w hwi hwj
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hwi hwj (Or.inr rfl)
    have := (hmem f hf).1 (hfi.trans hfj.symm)
    exact hij (by simpa using congrArg Fin.val this)
  · intro i hi x hx y hy
    have hi' : (i + 1) % k < k := Nat.mod_lt _ (by omega)
    rw [hP i hi] at hx
    rw [hP _ hi'] at hy
    have hne' : (⟨i, hi⟩ : Fin k) ≠ ⟨(i + 1) % k, hi'⟩ := by
      intro h
      have h' := congrArg Fin.val h
      simp only at h'
      rcases Nat.lt_or_ge (i + 1) k with hlt' | hge
      · rw [Nat.mod_eq_of_lt hlt'] at h'; omega
      · have : i + 1 = k := by omega
        rw [this, Nat.mod_self] at h'; omega
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hx hy (Or.inl hne')
    have hadj := ((hmem f hf).2 ⟨i, hi⟩ ⟨(i + 1) % k, hi'⟩).mpr
      ((cycleGraph_adj_iff_mod hk2 _ _).mpr (Or.inl rfl))
    rwa [hfi, hfj] at hadj
  · intro i hi j hj hij hcons1 hcons2 x hx y hy
    rw [hP i hi] at hx
    rw [hP j hj] at hy
    have hne' : (⟨i, hi⟩ : Fin k) ≠ ⟨j, hj⟩ := fun h => hij (by simpa using congrArg Fin.val h)
    obtain ⟨f, hf, hfi, hfj⟩ := exists_transversal W hne hx hy (Or.inl hne')
    intro hadj
    rw [← hfi, ← hfj] at hadj
    have := (cycleGraph_adj_iff_mod hk2 _ _).mp (((hmem f hf).2 _ _).mp hadj)
    rcases this with h | h
    · exact hcons1 h
    · exact hcons2 h

end PaperIV.EditRoute
