import ErdosProblems.Problem84.Basic

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.SuccPred
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-!
# Graph constructions preserving or extending cycle spectra
-/

namespace ErdosProblem84

open SimpleGraph Walk

/-- An isolated final vertex in `Fin (m + 1)`. -/
def newVertex (m : ℕ) : Fin (m + 1) :=
  ⟨m, Nat.lt_succ_self m⟩

lemma newVertex_not_old (m : ℕ) : ¬ (newVertex m).val < m := by
  simp [newVertex]

lemma isOldVertex_iff_ne_new {m : ℕ} (v : Fin (m + 1)) :
    v.val < m ↔ v ≠ newVertex m := by
  obtain ⟨k, hk⟩ := v
  simp only [newVertex, Fin.ext_iff]
  constructor
  · intro hlt heq
    have hm : k = m := congrArg Fin.val heq
    omega
  · intro hne
    omega

/-- Embed `Fin m` into the initial segment of `Fin (m + 1)`. -/
def embedOld (m : ℕ) (v : Fin m) : Fin (m + 1) :=
  Fin.castAdd 1 v

lemma embedOld_injective (m : ℕ) : Function.Injective (embedOld m) :=
  Fin.castAdd_injective m 1

lemma embedOld_val (m : ℕ) (v : Fin m) : (embedOld m v).val = v.val := rfl

lemma isOldVertex_embedOld {m : ℕ} (v : Fin m) : (embedOld m v).val < m := by
  simpa [embedOld] using v.isLt

/-- Add an isolated final vertex to a graph on `Fin m`. -/
def addIsolatedVertex {m : ℕ} (G : SimpleGraph (Fin m)) : SimpleGraph (Fin (m + 1)) where
  Adj i j :=
    if hi : i.val < m then
      if hj : j.val < m then G.Adj (Fin.castLT i hi) (Fin.castLT j hj) else False
    else False
  symm := by
    intro i j h
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · exact G.adj_symm h
      · exact h
    · exact h
  loopless := by
    intro i h
    by_cases hi : i.val < m
    · exact G.loopless (Fin.castLT i hi) h
    · exact h

lemma addIsolatedVertex_embedOld_adj {m : ℕ} (G : SimpleGraph (Fin m)) (i j : Fin m) :
    (addIsolatedVertex G).Adj (embedOld m i) (embedOld m j) ↔ G.Adj i j := by
  simp [addIsolatedVertex, embedOld, isOldVertex_embedOld]

noncomputable def embedOldHom {m : ℕ} (G : SimpleGraph (Fin m)) :
    G →g addIsolatedVertex G where
  toFun := embedOld m
  map_rel' := fun h => (addIsolatedVertex_embedOld_adj G _ _).2 h

/-- Extend a graph on `Fin m` by two vertices creating a cycle of length `m + 2`. -/
def addMaxCycle {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) : SimpleGraph (Fin (m + 2)) where
  Adj i j :=
    let ai := i.val
    let aj := j.val
    if ai < m ∧ aj < m then
      G.Adj ⟨i, by omega⟩ ⟨j, by omega⟩
    else if ai = m ∧ aj = m + 1 then True
    else if aj = m ∧ ai = m + 1 then True
    else if ai = m ∧ aj = 0 then True
    else if aj = m ∧ ai = 0 then True
    else if ai = m + 1 ∧ aj = m - 1 then True
    else if aj = m + 1 ∧ ai = m - 1 then True
    else False
  symm := by
    intro i j; unfold Adj; grind
  loopless := by
    intro i h
    unfold Adj at h
    split_ifs at h
    · exact G.loopless _ h
    all_goals exact h

/-- The first new vertex in `Fin (m + 2)`. -/
def maxVertex (m : ℕ) : Fin (m + 2) :=
  ⟨m, Nat.lt_succ_self _⟩

/-- The second new vertex in `Fin (m + 2)`. -/
def maxVertexSucc (m : ℕ) : Fin (m + 2) :=
  ⟨m + 1, by omega⟩

lemma addIsolatedVertex_newVertex_adj' {m : ℕ} (G : SimpleGraph (Fin m)) (v : Fin (m + 1)) :
    ¬ (addIsolatedVertex G).Adj (newVertex m) v := by
  intro h
  by_cases hv : v.val < m <;> simp [addIsolatedVertex, newVertex, newVertex_not_old] at h <;> tauto

lemma addIsolatedVertex_newVertex_adj {m : ℕ} (G : SimpleGraph (Fin m)) (v : Fin (m + 1)) :
    ¬ (addIsolatedVertex G).Adj v (newVertex m) := by
  intro h
  by_cases hv : v.val < m <;> simp [addIsolatedVertex, newVertex, newVertex_not_old] at h <;> tauto

lemma addIsolatedVertex_degree_newVertex {m : ℕ} (G : SimpleGraph (Fin m)) :
    (addIsolatedVertex G).degree (newVertex m) = 0 := by
  rw [SimpleGraph.degree_eq_zero]
  intro w
  simp [SimpleGraph.IsIsolated, addIsolatedVertex, newVertex, newVertex_not_old]

lemma IsPath.count_support_eq_one {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) :
    p.support.count w = 1 :=
  List.count_eq_one_of_mem hp.support_nodup hw

lemma addIsolatedVertex_notMem_cycle_support {m : ℕ} (G : SimpleGraph (Fin m)) {u : Fin (m + 1)}
    (p : (addIsolatedVertex G).Walk u u) (hp : p.IsCycle) :
    newVertex m ∉ p.support := by
  intro hmem
  have hdeg := addIsolatedVertex_degree_newVertex G
  have hcount := IsPath.count_support_eq_one p hp.isPath_tail hmem
  rw [hdeg] at hcount
  cases p with
  | nil => exact hp.not_nil rfl
  | cons _ _ => simp at hcount

lemma addIsolatedVertex_notMem_support {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (p : (addIsolatedVertex G).Walk u v) (hp : p.IsPath) :
    newVertex m ∉ p.support := by
  intro hmem
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at hmem
    exact absurd hmem (ne_of_lt hu)
  | cons h q ih =>
    rw [mem_support_iff] at hmem
    rcases hmem with rfl | hmem
    · exact addIsolatedVertex_newVertex_adj' G _ h
    · exact ih (IsPath.of_cons hp) hmem

lemma mapWalk_embedOld {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin m} (p : G.Walk u v) :
    (p.map (embedOldHom G)).length = p.length := by
  simpa using Walk.length_map (f := embedOldHom G) (p := p)

lemma map_isCycle_embedOld {m : ℕ} (G : SimpleGraph (Fin m)) {u : Fin m} (p : G.Walk u u)
    (hp : p.IsCycle) :
    (p.map (embedOldHom G)).IsCycle :=
  IsCycle.map (embedOld_injective m) hp

lemma oldVertex_eq_embedOld {m : ℕ} {v : Fin (m + 1)} (hv : v.val < m) :
    ∃ w : Fin m, v = embedOld m w := by
  refine ⟨⟨v.val, hv⟩, Fin.ext rfl⟩

lemma walk_oldVertex_eq_map {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (hv : v.val < m) (p : (addIsolatedVertex G).Walk u v)
    (hold : ∀ w ∈ p.support, w.val < m) :
    ∃ (u' : Fin m) (v' : Fin m) (p' : G.Walk u' v'),
      u = embedOld m u' ∧ v = embedOld m v' ∧
        p = (p'.map (embedOldHom G)) := by
  obtain ⟨u', rfl⟩ := oldVertex_eq_embedOld hu
  obtain ⟨v', rfl⟩ := oldVertex_eq_embedOld hv
  induction p with
  | nil =>
    refine ⟨u', u', Walk.nil, rfl, rfl, by simp [Walk.map_nil]⟩
  | cons h q ih =>
    have holdq : ∀ w ∈ q.support, w.val < m := by
      intro w hw
      rw [support_cons, List.mem_cons] at hw
      exact hold w (by rw [mem_support_iff]; exact Or.inr hw)
    have hend : (q.getVert q.length).val < m :=
      hold q.end q.end_mem_support
    obtain ⟨u'', v'', q', rfl, rfl, hq⟩ := ih hend holdq
    have h' : G.Adj u'' v'' := by
      rw [← addIsolatedVertex_embedOld_adj G u'' v'']
      exact h
    refine ⟨u'', v'', Walk.cons h' q', rfl, rfl, ?_⟩
    simp [Walk.map, hq, addIsolatedVertex_embedOld_adj, h']

lemma cycleSpectrum_bot (n : ℕ) : cycleSpectrum (⊥ : SimpleGraph (Fin n)) = ∅ := by
  ext ℓ
  simp [cycleSpectrum, Set.mem_setOf_eq]
  intro u p hp
  exact hp.ne_bot rfl

lemma pathGraph_IsAcyclic (n : ℕ) : (pathGraph n).IsAcyclic := by
  intro u c hc
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hle : c.length ≤ n := by simpa [Fintype.card_fin] using IsCycle.length_le_card hc
  match n with
  | 0 => exact Fin.elim0 u
  | 1 | 2 => omega
  | 3 => fin_cases u; all_goals grind [pathGraph_adj, hc]
  | n + 4 => exact pathGraph_IsAcyclic (n + 3) u c hc

lemma cycleSpectrum_pathGraph (n : ℕ) :
    cycleSpectrum (pathGraph n) = ∅ := by
  ext ℓ
  simp [cycleSpectrum, Set.mem_setOf_eq]
  intro u p hp
  exact pathGraph_IsAcyclic n u p hp

lemma cycleSpectrum_addIsolatedVertex {m : ℕ} (G : SimpleGraph (Fin m)) :
    cycleSpectrum (addIsolatedVertex G) = cycleSpectrum G := by
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, p, hp, rfl⟩
    have htail := hp.isPath_tail
    have hu : u.val < m := by
      by_contra hge
      have heq : u = newVertex m := Fin.ext (by simp [newVertex, Nat.not_lt.mp hge])
      subst heq
      exact addIsolatedVertex_notMem_cycle_support G p hp Walk.start_mem_support
    have hold : ∀ w ∈ p.support, w.val < m := by
      intro w hw
      by_contra hge
      have heq : w = newVertex m := Fin.ext (by simp [newVertex, Nat.not_lt.mp hge])
      rw [heq] at hw
      exact addIsolatedVertex_notMem_support G hu p htail hw
    obtain ⟨u', v', p', rfl, rfl, rfl⟩ := walk_oldVertex_eq_map G hu hu p hold
    exact ⟨u', p', hp, rfl⟩
  · rintro ⟨u, p, hp, rfl⟩
    exact ⟨embedOld m u, p.map (embedOldHom G), map_isCycle_embedOld G p hp,
      (Walk.length_map (f := embedOldHom G) (p := p)).symm ▸ rfl⟩

/-- Embed `Fin m` into the initial segment of `Fin (m + 2)`. -/
def embedMaxOld (m : ℕ) (v : Fin m) : Fin (m + 2) :=
  Fin.castAdd 2 v

lemma embedMaxOld_val (m : ℕ) (v : Fin m) : (embedMaxOld m v).val = v.val := rfl

lemma embedMaxOld_injective (m : ℕ) : Function.Injective (embedMaxOld m) :=
  Fin.castAdd_injective m 2

lemma addMaxCycle_embedOld_adj {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) (i j : Fin m) :
    (addMaxCycle G hm).Adj (embedMaxOld m i) (embedMaxOld m j) ↔ G.Adj i j := by
  simp [addMaxCycle, embedMaxOld]

noncomputable def embedMaxOldHom {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    G →g addMaxCycle G hm where
  toFun := embedMaxOld m
  map_rel' := fun h => (addMaxCycle_embedOld_adj G hm _ _).2 h

lemma mapWalk_embedMaxOld {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) {u v : Fin m}
    (p : G.Walk u v) :
    (p.map (embedMaxOldHom G hm)).length = p.length := by
  simpa using Walk.length_map (f := embedMaxOldHom G hm) (p := p)

lemma map_isCycle_embedMaxOld {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) {u : Fin m}
    (p : G.Walk u u) (hp : p.IsCycle) :
    (p.map (embedMaxOldHom G hm)).IsCycle :=
  IsCycle.map (embedMaxOld_injective m) hp

lemma oldMax_eq_embedMaxOld {m : ℕ} {v : Fin (m + 2)} (hv : v.val < m) :
    ∃ w : Fin m, v = embedMaxOld m w := by
  refine ⟨⟨v.val, hv⟩, Fin.ext rfl⟩

lemma walk_oldMax_eq_map {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (hu : u.val < m) (hv : v.val < m)
    (p : (addMaxCycle G hm).Walk u v) (hold : ∀ w ∈ p.support, w.val < m) :
    ∃ (u' : Fin m) (v' : Fin m) (p' : G.Walk u' v'),
      u = embedMaxOld m u' ∧ v = embedMaxOld m v' ∧
        p = (p'.map (embedMaxOldHom G hm)) := by
  obtain ⟨u', rfl⟩ := oldMax_eq_embedMaxOld hu
  obtain ⟨v', rfl⟩ := oldMax_eq_embedMaxOld hv
  induction p with
  | nil =>
    refine ⟨u', u', Walk.nil, rfl, rfl, by simp [Walk.map_nil]⟩
  | cons h q ih =>
    have holdq : ∀ w ∈ q.support, w.val < m := by
      intro w hw
      rw [support_cons, List.mem_cons] at hw
      exact hold w (by rw [mem_support_iff]; exact Or.inr hw)
    have hend : (q.getVert q.length).val < m :=
      hold q.end q.end_mem_support
    obtain ⟨u'', v'', q', rfl, rfl, hq⟩ := ih hend holdq
    have h' : G.Adj u'' v'' := by
      rw [← addMaxCycle_embedOld_adj G hm u'' v'']
      exact h
    refine ⟨u'', v'', Walk.cons h' q', rfl, rfl, ?_⟩
    simp [Walk.map, hq, addMaxCycle_embedOld_adj, h']

lemma addMaxCycle_neighborFinset_maxVertex {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).neighborFinset (maxVertex m) =
      {(0 : Fin (m + 2)), maxVertexSucc m} := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  ext v
  simp [SimpleGraph.neighborFinset, SimpleGraph.mem_neighborSet, addMaxCycle, maxVertex,
    maxVertexSucc, Fin.ext_iff]
  constructor <;> intro h <;> simp_all (config := {decide := true}) <;> omega

lemma addMaxCycle_degree_maxVertex {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).degree (maxVertex m) = 2 := by
  rw [SimpleGraph.degree, addMaxCycle_neighborFinset_maxVertex]
  simp

lemma addMaxCycle_neighborFinset_maxVertexSucc {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).neighborFinset (maxVertexSucc m) =
      {maxVertex m, embedMaxOld m (Fin.last (m - 1))} := by
  ext v
  simp [SimpleGraph.neighborFinset, SimpleGraph.mem_neighborSet, addMaxCycle, maxVertex,
    maxVertexSucc, Fin.ext_iff]
  constructor <;> intro h <;> simp_all (config := {decide := true}) <;> omega

lemma addMaxCycle_degree_maxVertexSucc {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).degree (maxVertexSucc m) = 2 := by
  rw [SimpleGraph.degree, addMaxCycle_neighborFinset_maxVertexSucc]
  simp

lemma addMaxCycle_notMem_maxVertex_support {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u v) (hp : p.IsPath)
    (hlen : p.length ≠ m + 2) :
    maxVertex m ∉ p.support := by
  intro hmem
  have hne : u ≠ maxVertex m := by
    intro heq
    rw [heq] at hmem
    have hcount := IsPath.count_support_eq_one p hp hmem
    rw [addMaxCycle_degree_maxVertex G hm] at hcount
    cases p with
    | nil => simp at hcount
    | cons h q => simp at hcount
  have hcount := IsPath.count_support_eq_one p hp hmem
  rw [addMaxCycle_degree_maxVertex G hm] at hcount
  omega

lemma addMaxCycle_notMem_maxVertexSucc_support {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u v) (hp : p.IsPath)
    (hlen : p.length ≠ m + 2) :
    maxVertexSucc m ∉ p.support := by
  intro hmem
  have hne : u ≠ maxVertexSucc m := by
    intro heq
    rw [heq] at hmem
    have hcount := IsPath.count_support_eq_one p hp hmem
    rw [addMaxCycle_degree_maxVertexSucc G hm] at hcount
    cases p with
    | nil => simp at hcount
    | cons h q => simp at hcount
  have hcount := IsPath.count_support_eq_one p hp hmem
  rw [addMaxCycle_degree_maxVertexSucc G hm] at hcount
  omega

lemma addMaxCycle_support_old_of_cycle_ne {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u u) (hp : p.IsCycle)
    (hlen : p.length ≠ m + 2) :
    ∀ w ∈ p.support, w.val < m := by
  intro w hw
  by_contra hw'
  push_neg at hw'
  rcases w with ⟨k, hk⟩
  simp only [maxVertex, maxVertexSucc, Fin.ext_iff] at hw' ⊢
  have hk' : k = m ∨ k = m + 1 := by omega
  rcases hk' with rfl | rfl
  · exact addMaxCycle_notMem_maxVertex_support G hm p hp.isPath_tail hlen hw
  · exact addMaxCycle_notMem_maxVertexSucc_support G hm p hp.isPath_tail hlen hw

lemma pathGraph_castAdd_adj {n k : ℕ} {i j : Fin n} :
    (pathGraph (n + k)).Adj (Fin.castAdd k i) (Fin.castAdd k j) ↔ (pathGraph n).Adj i j := by
  simp [pathGraph_adj, Fin.ext_iff, Fin.val_castAdd]

noncomputable def pathGraph_castAddHom (n k : ℕ) : pathGraph n →g pathGraph (n + k) where
  toFun := Fin.castAdd k
  map_rel' := fun h => (pathGraph_castAdd_adj (n := n) (k := k)).2 h

lemma pathGraph_adj_succ {n : ℕ} {i : Fin n} (hi : i.val + 1 < n) :
    (pathGraph n).Adj i ⟨i.val + 1, hi⟩ := by
  simp [pathGraph_adj, Fin.ext_iff]

/-- Forward walk along `pathGraph (m + 1)` from `0` to `Fin.last m`. -/
noncomputable def pathGraph_fwdWalk (m : ℕ) :
    (pathGraph (m + 1)).Walk (0 : Fin (m + 1)) (Fin.last m) :=
  match m with
  | 0 =>
    Walk.nil
  | m + 1 =>
    have hi : (0 : Fin (m + 2)).val + 1 < m + 2 := by omega
    Walk.cons (pathGraph_adj_succ hi)
      ((pathGraph_fwdWalk m).map (pathGraph_castAddHom (m + 1) 1))

lemma pathGraph_fwdWalk_length (m : ℕ) :
    (pathGraph_fwdWalk m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [pathGraph_fwdWalk, Walk.length_cons, Walk.length_map, ih]

lemma pathGraph_fwdWalk_isPath (m : ℕ) :
    (pathGraph_fwdWalk m).IsPath := by
  induction m with
  | zero => simp [pathGraph_fwdWalk, Walk.isPath_def]
  | succ m ih =>
    simp [pathGraph_fwdWalk, Walk.isPath_def, Walk.edges_map, ih, pathGraph_adj_succ]

lemma pathGraph_hamiltonianPath (m : ℕ) (hm : 3 ≤ m) :
    ∃ p : (pathGraph m).Walk (0 : Fin m) (Fin.last (m - 1)),
      p.IsPath ∧ p.length = m - 1 := by
  haveI : NeZero m := ⟨by omega⟩
  exact ⟨pathGraph_fwdWalk (m - 1), pathGraph_fwdWalk_isPath (m - 1), pathGraph_fwdWalk_length (m - 1)⟩

lemma addMaxCycle_adj_max_zero {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertex m) (0 : Fin (m + 2)) := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  unfold addMaxCycle maxVertex
  split_ifs <;> try omega

lemma addMaxCycle_adj_max_succ {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertex m) (maxVertexSucc m) := by
  simp [addMaxCycle, maxVertex, maxVertexSucc]

lemma addMaxCycle_adj_succ_last {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertexSucc m) (Fin.last (m - 1) |>.castAdd 2) := by
  haveI : NeZero m := ⟨by omega⟩
  simp [addMaxCycle, maxVertexSucc, Fin.ext_iff]; omega

lemma addMaxCycle_maxWalk {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (0 : Fin m) (Fin.last (m - 1)), p.IsPath ∧ p.length = m - 1) :
    ∃ p : (addMaxCycle G hm).Walk (0 : Fin (m + 2)) (0 : Fin (m + 2)),
      p.IsCycle ∧ p.length = m + 2 := by
  obtain ⟨p0, hp0, hlen⟩ := hp
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (m + 2) := ⟨by omega⟩
  let p1 := p0.map (embedMaxOldHom G hm)
  have hadj1 := addMaxCycle_adj_max_zero G hm
  have hadj2 := addMaxCycle_adj_max_succ G hm
  have hadj3 := addMaxCycle_adj_succ_last G hm
  let G' := addMaxCycle G hm
  let tail := Walk.cons (G'.adj_symm hadj3) (Walk.cons (G'.adj_symm hadj2) (Walk.cons (G'.adj_symm hadj1) Walk.nil))
  refine ⟨p1.append tail, ?_, ?_⟩
  · simp [Walk.isCycle_def, Walk.isPath_def, Walk.length_append, Walk.length_cons, Walk.length_nil,
      hlen, Walk.length_map, hp0.support_nodup]
    grind
  · simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hlen, Walk.length_map]

lemma cycleSpectrum_addMaxCycle_pathGraph (m : ℕ) (hm : 3 ≤ m) :
    cycleSpectrum (addMaxCycle (pathGraph m) hm) = {m + 2} := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ :=
    addMaxCycle_maxWalk (pathGraph m) hm (pathGraph_hamiltonianPath m hm)
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, p, hp, hlen⟩
    by_cases hlen' : p.length = m + 2
    · exact hlen'.symm.trans hlen
    · exfalso
      by_cases hnew : ∃ w ∈ p.support, m ≤ w.val
      · rcases hnew with ⟨w, hw, _⟩
        have := addMaxCycle_support_old_of_cycle_ne (pathGraph m) hm p hp hlen'
        exact Nat.lt_irrefl m (this w hw)
      · push_neg at hnew
        have hold : ∀ w ∈ p.support, w.val < m := fun w hw => Nat.lt_of_not_ge (hnew w hw)
        have hu : u.val < m := hold u Walk.start_mem_support
        obtain ⟨u', v', p', heq, hv', hmap⟩ := walk_oldMax_eq_map (pathGraph m) hm hu hu p hold
        have hueq : u' = v' := by apply embedMaxOld_injective m; rw [← heq, ← hv']; exact hp.eq
        subst hueq
        have hp' : (pathGraph m).IsCycle u' p' := by rw [← map_isCycle_iff_of_injective (embedMaxOld_injective m), ← hmap]; exact hp
        exact pathGraph_IsAcyclic m u' p' hp'
  · intro hℓ
    subst hℓ
    exact ⟨0, pmax, hpmax, hlen⟩

lemma cycleSpectrum_addMaxCycle {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (0 : Fin m) (Fin.last (m - 1)), p.IsPath ∧ p.length = m - 1) :
    cycleSpectrum (addMaxCycle G hm) = cycleSpectrum G ∪ {m + 2} := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ := addMaxCycle_maxWalk G hm hp
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, p, hp', hlen'⟩
    by_cases hℓ : ℓ = m + 2
    · exact Or.inr hℓ
    · have hold := addMaxCycle_support_old_of_cycle_ne G hm p hp' (by intro h; exact hℓ (hlen'.trans h.symm))
      have hu : u.val < m := hold u (Walk.start_mem_support p)
      obtain ⟨u', v', p', heq, hv', hmap⟩ := walk_oldMax_eq_map G hm hu hu p hold
      have hueq : u' = v' := by apply embedMaxOld_injective m; rw [← heq, ← hv']; exact hp'.eq
      subst hueq
      have hp'' : p'.IsCycle := by rw [← map_isCycle_iff_of_injective (embedMaxOld_injective m), ← hmap]; exact hp'
      exact Or.inl ⟨u', p', hp'', hlen'⟩
  · intro h
    rcases h with h | h
    · obtain ⟨u, p, hp', hlen'⟩ := h
      exact ⟨embedMaxOld m u, p.map (embedMaxOldHom G hm), map_isCycle_embedMaxOld G hm p hp',
        by simpa [mapWalk_embedMaxOld] using hlen'⟩
    · subst h
      exact ⟨0, pmax, hpmax, hlen⟩

lemma cycleSpectrum_addMaxCycle_sup {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (0 : Fin m) (Fin.last (m - 1)), p.IsPath ∧ p.length = m - 1) :
    cycleSpectrum G ∪ {m + 2} ⊆ cycleSpectrum (addMaxCycle G hm) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ := addMaxCycle_maxWalk G hm hp
  intro ℓ h
  simp only [Set.mem_union, Set.mem_singleton_iff, cycleSpectrum, Set.mem_setOf_eq] at h ⊢
  rcases h with h | h
  · obtain ⟨u, p, hp', hlen'⟩ := h
    refine ⟨embedMaxOld m u, p.map (embedMaxOldHom G hm), map_isCycle_embedMaxOld G hm p hp', ?_⟩
    simpa [mapWalk_embedMaxOld] using hlen'
  · subst h
    exact ⟨0, pmax, hpmax, hlen⟩

end ErdosProblem84
