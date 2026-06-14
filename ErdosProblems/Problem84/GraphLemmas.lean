import ErdosProblems.Problem84.Basic

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.List.MinMax
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
    exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) (fun hm => hne (Fin.ext hm))

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
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · simp only [Adj, hi, hj] at h ⊢; exact G.adj_symm h
    all_goals simp only [Adj, *] at h ⊢ <;> split_ifs at h ⊢ <;> tauto
  loopless := ⟨fun i h => by
    by_cases hi : i.val < m
    · simp only [Adj, hi] at h; exact G.loopless.irrefl (Fin.castLT i hi) h
    · simp only [Adj, hi] at h; exact h⟩

lemma addIsolatedVertex_embedOld_adj {m : ℕ} (G : SimpleGraph (Fin m)) (i j : Fin m) :
    (addIsolatedVertex G).Adj (embedOld m i) (embedOld m j) ↔ G.Adj i j := by
  simp [addIsolatedVertex, embedOld, Fin.val_castAdd, Fin.castLT]

noncomputable def embedOldHom {m : ℕ} (G : SimpleGraph (Fin m)) :
    G →g addIsolatedVertex G where
  toFun := embedOld m
  map_rel' := fun h => (addIsolatedVertex_embedOld_adj G _ _).2 h

/-- Extend a graph on `Fin m` by two vertices creating a cycle of length `m + 2`. -/
def addMaxCycle {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) : SimpleGraph (Fin (m + 2)) where
  Adj i j :=
    if hi : i.val < m then
      if hj : j.val < m then G.Adj (Fin.castLT i hi) (Fin.castLT j hj) else False
    else if i.val = m ∧ j.val = m + 1 then True
    else if j.val = m ∧ i.val = m + 1 then True
    else if i.val = m ∧ j.val = 0 then True
    else if j.val = m ∧ i.val = 0 then True
    else if i.val = m + 1 ∧ j.val = m - 1 then True
    else if j.val = m + 1 ∧ i.val = m - 1 then True
    else False
  symm := by
    intro i j h
    by_cases hi : i.val < m <;> by_cases hj : j.val < m
    · simp only [Adj, hi, hj] at h ⊢; exact G.adj_symm h
    all_goals simp only [Adj, *] at h ⊢ <;> split_ifs at h ⊢ <;> (try exact absurd h) <;> (try exact G.adj_symm h) <;> omega
  loopless := ⟨fun i h => by
    by_cases hi : i.val < m
    · simp only [Adj, hi] at h; exact G.loopless.irrefl (Fin.castLT i hi) h
    · simp only [Adj, hi] at h; split_ifs at h <;> omega⟩

/-- The first new vertex in `Fin (m + 2)`. -/
def maxVertex (m : ℕ) : Fin (m + 2) :=
  ⟨m, by omega⟩

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

lemma addIsolatedVertex_adj_snd_old {m : ℕ} (G : SimpleGraph (Fin m)) {u w : Fin (m + 1)}
    (hu : u.val < m) (h : (addIsolatedVertex G).Adj u w) : w.val < m := by
  by_contra hge
  have heq : w = newVertex m := Fin.ext (by simp [newVertex]; omega)
  rw [heq] at h
  exact addIsolatedVertex_newVertex_adj G u h

lemma addIsolatedVertex_degree_newVertex {m : ℕ} (G : SimpleGraph (Fin m)) :
    (addIsolatedVertex G).degree (newVertex m) = 0 := by
  rw [SimpleGraph.degree_eq_zero]
  intro w; simp [addIsolatedVertex, newVertex, newVertex_not_old]

lemma IsPath.count_support_eq_one {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) :
    p.support.count w = 1 :=
  List.count_eq_one_of_mem hp.support_nodup hw

lemma addIsolatedVertex_notMem_support {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (p : (addIsolatedVertex G).Walk u v) :
    newVertex m ∉ p.support := by
  induction p with
  | nil =>
    intro hmem
    rw [mem_support_nil_iff] at hmem
    subst hmem
    exact absurd hu (newVertex_not_old m)
  | cons h q ih =>
    intro hmem
    rw [mem_support_iff] at hmem
    rcases hmem with heq | hmem
    · subst heq; exact addIsolatedVertex_newVertex_adj' G _ h
    · exact ih (addIsolatedVertex_adj_snd_old G hu h) hmem

lemma addIsolatedVertex_notMem_cycle_support {m : ℕ} (G : SimpleGraph (Fin m)) {u : Fin (m + 1)}
    (p : (addIsolatedVertex G).Walk u u) (hp : p.IsCycle) :
    newVertex m ∉ p.support := by
  intro hmem
  have hu : u.val < m := by
    by_contra hge
    have heq : u = newVertex m := Fin.ext (by simp [newVertex]; omega)
    subst heq
    cases p with
    | nil => exact hp.not_nil Walk.nil_nil
    | cons h' _ => exact addIsolatedVertex_newVertex_adj' G _ h'
  exact addIsolatedVertex_notMem_support G hu p hmem

lemma mapWalk_embedOld {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin m} (p : G.Walk u v) :
    (p.map (embedOldHom G)).length = p.length := by
  simpa using Walk.length_map (f := embedOldHom G) (p := p)

lemma map_isCycle_embedOld {m : ℕ} (G : SimpleGraph (Fin m)) {u : Fin m} (p : G.Walk u u)
    (hp : p.IsCycle) :
    (p.map (embedOldHom G)).IsCycle :=
  IsCycle.map (embedOld_injective m) hp

def unembedOldVert {m : ℕ} (v : Fin (m + 1)) (hv : v.val < m) : Fin m := ⟨v.val, hv⟩

lemma embedOld_unembedOldVert {m : ℕ} {u : Fin (m + 1)} (hu : u.val < m) :
    embedOld m (unembedOldVert u hu) = u := Fin.ext (by simp [embedOld, unembedOldVert])

noncomputable def unembedOldWalk {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (hv : v.val < m) (p : (addIsolatedVertex G).Walk u v) :
    G.Walk (unembedOldVert u hu) (unembedOldVert v hv) :=
  show G.Walk (unembedOldVert u hu) (unembedOldVert v hv) from match p with
  | nil => Walk.cast (by cases p; rfl) Walk.nil
  | cons h q =>
    have hv' := addIsolatedVertex_adj_snd_old G hu h
    Walk.cons
      ((addIsolatedVertex_embedOld_adj G (unembedOldVert u hu) (unembedOldVert _ hv')).mp h)
      (unembedOldWalk G hv' hv q)

lemma unembedOldWalk_map {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (hv : v.val < m) (p : (addIsolatedVertex G).Walk u v) :
    (unembedOldWalk G hu hv p).map (embedOldHom G) = p := by
  induction p with
  | nil => have huv : u = v := by cases p; rfl; simp [unembedOldWalk, Walk.map_nil, embedOldHom, embedOld, embedOld_unembedOldVert, huv]
  | cons h q ih =>
    have hv' := addIsolatedVertex_adj_snd_old G hu h
    simp only [unembedOldWalk, Walk.map_cons, ih, embedOld_unembedOldVert,
      addIsolatedVertex_embedOld_adj, embedOldHom, embedOld]

lemma walk_oldVertex_eq_map {m : ℕ} (G : SimpleGraph (Fin m)) {u v : Fin (m + 1)}
    (hu : u.val < m) (hv : v.val < m) (p : (addIsolatedVertex G).Walk u v)
    (_hold : ∀ w ∈ p.support, w.val < m) :
    ∃ (u' : Fin m) (v' : Fin m) (p' : G.Walk u' v'),
      u = embedOld m u' ∧ v = embedOld m v' ∧
        p = (p'.map (embedOldHom G)) := by
  refine ⟨unembedOldVert u hu, unembedOldVert v hv, unembedOldWalk G hu hv p, ?_, ?_, ?_⟩
  · exact embedOld_unembedOldVert hu
  · exact embedOld_unembedOldVert hv
  · rw [embedOld_unembedOldVert hu, embedOld_unembedOldVert hv]
    exact Eq.symm (unembedOldWalk_map G hu hv p)

lemma pathGraph_neighborFinset_zero {n : ℕ} (hn : 2 ≤ n) :
    (pathGraph n).neighborFinset (⟨0, by omega⟩ : Fin n) = ({⟨1, by omega⟩} : Finset (Fin n)) := by
  haveI : NeZero n := ⟨by omega⟩
  ext v
  simp only [SimpleGraph.mem_neighborFinset, pathGraph_adj, Fin.ext_iff, Finset.mem_singleton]
  constructor <;> intro h <;> omega

lemma pathGraph_degree_zero {n : ℕ} (hn : 2 ≤ n) :
    (pathGraph n).degree (⟨0, by omega⟩ : Fin n) = 1 := by
  classical
  rw [SimpleGraph.degree, pathGraph_neighborFinset_zero hn, Finset.card_singleton]

lemma IsPath.exists_adj_snd_of_mem_ne {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u w) (hp : p.IsPath) {x : V} (hx : x ∈ p.support) (hne : x ≠ u) :
    ∃ y, G.Adj x y ∧ y ∈ p.support := by
  induction p with
  | nil => simp [mem_support_nil_iff] at hx; contradiction
  | cons hadj p ih =>
    rw [mem_support_iff] at hx
    rcases hx with heq | htail
    · exact absurd heq hne
    · match p with
      | nil => exact ⟨w, hadj, by simp [mem_support_iff]⟩
      | cons hadj2 p2 =>
        rcases htail with hxw | hxrest
        · exact ⟨w, hadj2, by simp [mem_support_iff]⟩
        · exact ih hxrest (IsPath.of_cons hp hadj)

lemma notMem_support_of_degree_le_one {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [LocallyFinite G] {v : V} (hdeg : G.degree v ≤ 1) {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (hmem : v ∈ p.support) : False := by
  classical
  by_cases hv : v = u
  · subst hv
    have hcount := hp.count_support
    have hcardle : (G.neighborFinset u).card ≤ 1 := by rwa [SimpleGraph.degree]
    have huniq := (Finset.card_le_one.mp hcardle)
    have hsnd : p.snd ∈ G.neighborFinset u := by rwa [SimpleGraph.mem_neighborFinset, ← Walk.adj_snd hp.not_nil]
    have hsub : G.neighborFinset u ⊆ {p.snd} := fun x hx => Finset.mem_singleton.mpr (huniq hsnd hx)
    have hcard : G.neighborFinset u = {p.snd} := Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hsnd)
    rw [hcard, Finset.card_singleton] at hcount
    cases p with | nil => exact hp.not_nil Walk.nil_nil | cons _ q => cases q with | nil => simp at hcount | cons _ _ => simp at hcount
  · have hcount := hp.count_support_of_mem hmem hv
    have huniq := (Finset.card_le_one.mp (by rwa [SimpleGraph.degree]))
    have ht := hp.isPath_tail
    have hv_tail : v ∈ p.tail.support := by rw [mem_support_iff] at hmem ⊢; rcases hmem with h | htail; exact absurd h hv; exact htail
    by_cases hvs : v = p.snd
    · rw [SimpleGraph.degree] at hdeg; cases p with | nil => exact hp.not_nil Walk.nil_nil | cons _ q => cases q with | nil => simp at hcount | cons _ _ => simp at hcount
    · obtain ⟨w, hadj, hw⟩ := IsPath.exists_adj_snd_of_mem_ne p.tail ht hv_tail hvs
      have hw' : w ∈ G.neighborFinset v := by rwa [SimpleGraph.mem_neighborFinset]
      have hcard : G.neighborFinset v = {w} := by ext x; simp [Finset.mem_singleton]; constructor <;> intro hx <;> first | exact huniq hw' hx | subst hx; exact hw'
      rw [hcard, Finset.card_singleton] at hcount; simp at hcount

lemma pathGraph_pred_mem_cycle_support {n : ℕ} (hn : 2 ≤ n) {u k : Fin n}
    (p : (pathGraph n).Walk u u) (hp : p.IsCycle) (hk : k ∈ p.support) (hkpos : 0 < k.val) :
    (⟨k.val - 1, by omega⟩ : Fin n) ∈ p.support := by
  have hadj : (pathGraph n).Adj ⟨k.val - 1, by omega⟩ k := by
    simp [pathGraph_adj, Fin.ext_iff]; omega
  grind [hk, hkpos, pathGraph_adj, hn]

lemma pathGraph_zero_in_cycle_support {n : ℕ} (hn : 2 ≤ n) {u : Fin n}
    (p : (pathGraph n).Walk u u) (hp : p.IsCycle) : (⟨0, by omega⟩ : Fin n) ∈ p.support := by
  by_contra h0
  have hne : p.support ≠ [] := Walk.support_ne_nil p
  cases harg : List.argmin (fun (x : Fin n) => x.val) p.support with
  | none =>
    exact hne ((List.argmin_eq_none (f := fun (x : Fin n) => x.val)).1 harg)
  | some k =>
    obtain ⟨hkmem, hmin, _⟩ := (List.argmin_eq_some_iff (f := fun (x : Fin n) => x.val)).mp harg
    have hkpos : 0 < k.val := by
      by_contra hle
      have hle' : k.val = 0 := by omega
      have hk0 : k = (⟨0, by omega⟩ : Fin n) := Fin.ext hle'
      exact h0 (hk0 ▸ hkmem)
    have hkpred := pathGraph_pred_mem_cycle_support hn p hp hkmem hkpos
    have hlt : k.val - 1 < k.val := Nat.sub_lt hkpos (by omega)
    exact absurd hlt (Nat.not_lt.mpr (hmin _ hkpred))

lemma pathGraph_three_no_cycle {u : Fin 3} (c : (pathGraph 3).Walk u u) (hc : c.IsCycle) : False := by
  have hlen : c.length = 3 := by
    have h3 := hc.three_le_length
    have hle : c.length ≤ 3 := by simpa [Fintype.card_fin] using IsCycle.length_le_card hc
    omega
  cases c with
  | nil => exact hc.not_nil Walk.nil_nil
  | cons h q =>
    rw [Walk.length_cons] at hlen
    have hq : q.length = 2 := by omega
    cases q with
    | nil => simp at hq
    | cons h2 q2 =>
      rw [Walk.length_cons] at hq
      have hq2 : q2.length = 1 := by omega
      cases q2 with
      | nil => simp at hq2
      | cons h3 q3 =>
        rw [Walk.length_cons] at hq2
        have hq3 : q3.length = 0 := by omega
        cases q3 with
        | nil =>
          fin_cases u
          all_goals simp only [pathGraph_adj, Fin.ext_iff] at h h2 h3 <;> omega
        | cons _ _ => simp at hq3

lemma pathGraph_IsAcyclic (n : ℕ) : (pathGraph n).IsAcyclic := by
  intro u c hc
  have h3 := hc.three_le_length
  have hle : c.length ≤ n := by simpa [Fintype.card_fin] using IsCycle.length_le_card hc
  match n with
  | 0 => exact Fin.elim0 u
  | 1 | 2 => omega
  | 3 => exact pathGraph_three_no_cycle c hc
  | m + 4 =>
    have hn : 2 ≤ m + 4 := by omega
    have h0 := pathGraph_zero_in_cycle_support hn c hc
    exact notMem_support_of_degree_le_one
      (by rw [pathGraph_degree_zero hn]; exact le_rfl) c hc h0

lemma cycleSpectrum_bot (n : ℕ) : cycleSpectrum (⊥ : SimpleGraph (Fin n)) = ∅ := by
  ext ℓ
  simp only [mem_cycleSpectrum, Set.mem_setOf_eq, iff_false]
  intro h
  obtain ⟨u, p, hp, _⟩ := h
  exact (isAcyclic_bot (V := Fin n)) p hp

lemma cycleSpectrum_pathGraph (n : ℕ) :
    cycleSpectrum (pathGraph n) = ∅ := by
  ext ℓ
  simp only [mem_cycleSpectrum, Set.mem_setOf_eq, iff_false]
  intro h
  obtain ⟨u, p, hp, _⟩ := h
  exact (pathGraph_IsAcyclic n) p hp

lemma cycleSpectrum_addIsolatedVertex {m : ℕ} (G : SimpleGraph (Fin m)) :
    cycleSpectrum (addIsolatedVertex G) = cycleSpectrum G := by
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, p, hp, hlen⟩
    have hu : u.val < m := by
      by_contra hge
      have heq : u = newVertex m := Fin.ext (by simp [newVertex]; omega)
      subst heq
      exact addIsolatedVertex_notMem_cycle_support G p hp (Walk.start_mem_support p)
    have hold : ∀ w ∈ p.support, w.val < m := by
      intro w hw
      by_contra hge
      have heq : w = newVertex m := Fin.ext (by simp [newVertex]; omega)
      rw [heq] at hw
      exact addIsolatedVertex_notMem_support G hu p hw
    obtain ⟨u', v', p', heq, heqv, hmap⟩ := walk_oldVertex_eq_map G hu hu p hold
    have huv : u' = v' := embedOld_injective m (heq.symm.trans heqv)
    subst huv
    have hp' : p'.IsCycle :=
      (map_isCycle_iff_of_injective (f := embedOldHom G) (embedOld_injective m)).mp
        (by rw [← hmap]; exact hp)
    exact ⟨u', p', hp', by rw [← Walk.length_map (f := embedOldHom G), hmap, hlen]⟩
  · rintro ⟨u, p, hp, hlen⟩
    exact ⟨embedOld m u, p.map (embedOldHom G), map_isCycle_embedOld G p hp,
      by rw [← Walk.length_map (f := embedOldHom G) (p := p)]; exact hlen⟩

/-- Embed `Fin m` into the initial segment of `Fin (m + 2)`. -/
def embedMaxOld (m : ℕ) (v : Fin m) : Fin (m + 2) :=
  Fin.castAdd 2 v

lemma embedMaxOld_val (m : ℕ) (v : Fin m) : (embedMaxOld m v).val = v.val := rfl

lemma embedMaxOld_injective (m : ℕ) : Function.Injective (embedMaxOld m) :=
  Fin.castAdd_injective m 2

lemma addMaxCycle_embedOld_adj {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) (i j : Fin m) :
    (addMaxCycle G hm).Adj (embedMaxOld m i) (embedMaxOld m j) ↔ G.Adj i j := by
  simp [addMaxCycle, embedMaxOld, Fin.val_castAdd, Fin.castLT]

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

lemma addMaxCycle_adj_snd_old {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) {u w : Fin (m + 2)}
    (hu : u.val < m) (h : (addMaxCycle G hm).Adj u w) : w.val < m := by
  by_contra hge
  have hk : w.val = m ∨ w.val = m + 1 := by omega
  rcases hk with hwm | hwm
  · by_cases hi : u.val < m <;> by_cases hj : w.val < m <;> simp [addMaxCycle, hi, hj, hwm] at h <;> tauto
  · by_cases hi : u.val < m <;> by_cases hj : w.val < m <;> simp [addMaxCycle, hi, hj, hwm] at h <;> tauto

def unembedMaxVert {m : ℕ} (v : Fin (m + 2)) (hv : v.val < m) : Fin m := ⟨v.val, hv⟩

lemma embedMaxOld_unembedMaxVert {m : ℕ} {u : Fin (m + 2)} (hu : u.val < m) :
    embedMaxOld m (unembedMaxVert u hu) = u := Fin.ext (by simp [embedMaxOld, unembedMaxVert])

/-- `Fin.last (m - 1)` cast into `Fin m` (for `m ≥ 1`). -/
def finLastPred (m : ℕ) (_hm : 1 ≤ m) : Fin m :=
  (Fin.last (m - 1)).cast (by omega)

noncomputable def unembedMaxWalk {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) {u v : Fin (m + 2)}
    (hu : u.val < m) (hv : v.val < m) (p : (addMaxCycle G hm).Walk u v) :
    G.Walk (unembedMaxVert u hu) (unembedMaxVert v hv) :=
  show G.Walk (unembedMaxVert u hu) (unembedMaxVert v hv) from match p with
  | nil => Walk.cast (by cases p; rfl) Walk.nil
  | cons h q =>
    have hv' := addMaxCycle_adj_snd_old G hm hu h
    Walk.cons
      ((addMaxCycle_embedOld_adj G hm (unembedMaxVert u hu) (unembedMaxVert _ hv')).mp h)
      (unembedMaxWalk G hm hv' hv q)

lemma unembedMaxWalk_map {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) {u v : Fin (m + 2)}
    (hu : u.val < m) (hv : v.val < m) (p : (addMaxCycle G hm).Walk u v) :
    (unembedMaxWalk G hm hu hv p).map (embedMaxOldHom G hm) = p := by
  induction p with
  | nil => have huv : u = v := by cases p; rfl; simp [unembedMaxWalk, Walk.map_nil, embedMaxOldHom, embedMaxOld, embedMaxOld_unembedMaxVert, huv]
  | cons h q ih =>
    have hv' := addMaxCycle_adj_snd_old G hm hu h
    simp only [unembedMaxWalk, Walk.map_cons, ih, embedMaxOld_unembedMaxVert,
      addMaxCycle_embedOld_adj, embedMaxOldHom, embedMaxOld]

lemma walk_oldMax_eq_map {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (hu : u.val < m) (hv : v.val < m)
    (p : (addMaxCycle G hm).Walk u v) (_hold : ∀ w ∈ p.support, w.val < m) :
    ∃ (u' : Fin m) (v' : Fin m) (p' : G.Walk u' v'),
      u = embedMaxOld m u' ∧ v = embedMaxOld m v' ∧
        p = (p'.map (embedMaxOldHom G hm)) := by
  refine ⟨unembedMaxVert u hu, unembedMaxVert v hv, unembedMaxWalk G hm hu hv p, ?_, ?_, ?_⟩
  · exact embedMaxOld_unembedMaxVert hu
  · exact embedMaxOld_unembedMaxVert hv
  · rw [embedMaxOld_unembedMaxVert hu, embedMaxOld_unembedMaxVert hv]
    exact Eq.symm (unembedMaxWalk_map G hm hu hv p)

lemma addMaxCycle_adj_max_zero {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertex m) (⟨0, by omega⟩ : Fin (m + 2)) := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  simp [addMaxCycle, maxVertex]

lemma addMaxCycle_adj_max_succ {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertex m) (maxVertexSucc m) := by
  simp [addMaxCycle, maxVertex, maxVertexSucc]

lemma addMaxCycle_adj_succ_last {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).Adj (maxVertexSucc m) (embedMaxOld m (finLastPred m (by omega))) := by
  haveI : NeZero m := ⟨by omega⟩
  simp [addMaxCycle, maxVertexSucc, embedMaxOld, finLastPred, Fin.val_castAdd, Fin.val_cast]
  omega

lemma addMaxCycle_neighborFinset_maxVertex {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).neighborFinset (maxVertex m) =
      {(⟨0, by omega⟩ : Fin (m + 2)), maxVertexSucc m} := by
  haveI : NeZero (m + 2) := ⟨by omega⟩
  ext v
  simp [SimpleGraph.neighborFinset, SimpleGraph.mem_neighborSet, addMaxCycle, maxVertex,
    maxVertexSucc, Fin.ext_iff]
  constructor <;> intro h <;> simp_all (config := {decide := true}) <;> omega

lemma addMaxCycle_degree_maxVertex {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).degree (maxVertex m) = 2 := by
  classical
  rw [SimpleGraph.degree, addMaxCycle_neighborFinset_maxVertex G hm]
  simp

lemma addMaxCycle_neighborFinset_maxVertexSucc {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).neighborFinset (maxVertexSucc m) =
      {maxVertex m, embedMaxOld m (finLastPred m (by omega))} := by
  haveI : NeZero m := ⟨by omega⟩
  ext v
  simp [SimpleGraph.neighborFinset, SimpleGraph.mem_neighborSet, addMaxCycle, maxVertex,
    maxVertexSucc, embedMaxOld, finLastPred, Fin.ext_iff, Fin.val_castAdd, Fin.val_cast]
  constructor <;> intro h <;> simp_all (config := {decide := true}) <;> omega

lemma addMaxCycle_degree_maxVertexSucc {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m) :
    (addMaxCycle G hm).degree (maxVertexSucc m) = 2 := by
  classical
  rw [SimpleGraph.degree, addMaxCycle_neighborFinset_maxVertexSucc G hm]
  simp

lemma addMaxCycle_notMem_maxVertex_support {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u v) (hp : p.IsPath)
    (hlen : p.length ≠ m + 2) :
    maxVertex m ∉ p.support := by
  intro hmem
  haveI : NeZero (m + 2) := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  grind [addMaxCycle, maxVertex, IsPath.count_support_eq_one, addMaxCycle_degree_maxVertex G hm,
    Walk.length_cons]

lemma addMaxCycle_notMem_maxVertexSucc_support {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u v : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u v) (hp : p.IsPath)
    (hlen : p.length ≠ m + 2) :
    maxVertexSucc m ∉ p.support := by
  intro hmem
  haveI : NeZero (m + 2) := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  grind [addMaxCycle, maxVertexSucc, IsPath.count_support_eq_one,
    addMaxCycle_degree_maxVertexSucc G hm, Walk.length_cons]

lemma addMaxCycle_support_old_of_cycle_ne {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    {u : Fin (m + 2)} (p : (addMaxCycle G hm).Walk u u) (hp : p.IsCycle)
    (hlen : p.length ≠ m + 2) :
    ∀ w ∈ p.support, w.val < m := by
  intro w hw
  by_contra hw'
  push Not at hw'
  rcases w with ⟨k, hk⟩
  simp only [maxVertex, maxVertexSucc, Fin.ext_iff] at hw' ⊢
  have hk' : k = m ∨ k = m + 1 := by omega
  rcases hk' with rfl | rfl
  · exact addMaxCycle_notMem_maxVertex_support G hm p.tail hp.isPath_tail hlen hw
  · exact addMaxCycle_notMem_maxVertexSucc_support G hm p.tail hp.isPath_tail hlen hw

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
    (pathGraph (m + 1)).Walk (⟨0, by omega⟩ : Fin (m + 1)) (Fin.last m) :=
  match m with
  | 0 =>
    Walk.nil
  | m + 1 =>
    have hi : (⟨0, by omega⟩ : Fin (m + 2)).val + 1 < m + 2 := by omega
    Walk.cons (pathGraph_adj_succ hi)
      ((pathGraph_fwdWalk m).map (pathGraph_castAddHom (m + 1) 1))

lemma pathGraph_fwdWalk_length (m : ℕ) :
    (pathGraph_fwdWalk m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [pathGraph_fwdWalk, Walk.length_cons, Walk.length_map, ih, pathGraph_castAddHom]

lemma pathGraph_castAddHom_map_isPath {n k : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v)
    (hp : p.IsPath) :
    (p.map (pathGraph_castAddHom n)).IsPath := by
  rw [Walk.isPath_def, Walk.support_map]
  exact hp.support_nodup.map (Fin.castAdd_injective n k)

lemma pathGraph_fwdWalk_succ_start_not_mem (m : ℕ) :
    (⟨0, by omega⟩ : Fin (m + 2)) ∉
      ((pathGraph_fwdWalk m).map (pathGraph_castAddHom (m + 1) 1)).support := by
  intro hmem
  rw [Walk.support_map, List.mem_map] at hmem
  obtain ⟨x, hx, hx0⟩ := hmem
  have hxpos : 0 < x.val := by
    by_contra hle
    have hxval : x.val = 0 := by omega
    have hx0' : x = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hxval
    subst hx0'
    cases m with
    | zero => simp [pathGraph_fwdWalk, Walk.isPath_def] at hx
    | succ m' =>
      have hlen := pathGraph_fwdWalk_length (m' + 1)
      simp [pathGraph_fwdWalk, Walk.isPath_def] at hx
      omega
  have : 0 < (Fin.castAdd 1 x).val := by simp [Fin.val_castAdd, hxpos]
  simp [Fin.ext_iff] at hx0
  omega

lemma pathGraph_fwdWalk_isPath (m : ℕ) : (pathGraph_fwdWalk m).IsPath := by
  induction m with
  | zero => simp [pathGraph_fwdWalk, Walk.isPath_def]
  | succ m ih =>
    rw [pathGraph_fwdWalk, Walk.cons_isPath_iff]
    exact ⟨pathGraph_castAddHom_map_isPath _ ih, pathGraph_fwdWalk_succ_start_not_mem m⟩

lemma pathGraph_hamiltonianPath (m : ℕ) (hm : 3 ≤ m) :
    ∃ p : (pathGraph m).Walk (⟨0, by omega⟩ : Fin m) (finLastPred m (by omega)),
      p.IsPath ∧ p.length = m - 1 := by
  haveI : NeZero m := ⟨by omega⟩
  have hwd := pathGraph_fwdWalk (m - 1)
  have hend : (Fin.last (m - 1) : Fin m) = finLastPred m (by omega) := by apply Fin.ext; simp [finLastPred, Fin.last, Fin.val_cast]; omega
  exact ⟨hwd.copy (by rfl) hend, pathGraph_fwdWalk_isPath (m - 1), pathGraph_fwdWalk_length (m - 1)⟩

lemma addMaxCycle_maxWalk {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (⟨0, by omega⟩ : Fin m) (finLastPred m (by omega)),
      p.IsPath ∧ p.length = m - 1) :
    ∃ p : (addMaxCycle G hm).Walk (⟨0, by omega⟩ : Fin (m + 2)) (⟨0, by omega⟩ : Fin (m + 2)),
      p.IsCycle ∧ p.length = m + 2 := by
  obtain ⟨p0, hp0, hlen⟩ := hp
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (m + 2) := ⟨by omega⟩
  let p1 := p0.map (embedMaxOldHom G hm)
  have hadj1 := addMaxCycle_adj_max_zero G hm
  have hadj2 := addMaxCycle_adj_max_succ G hm
  have hadj3 := addMaxCycle_adj_succ_last G hm
  let G' := addMaxCycle G hm
  let tail := Walk.cons (G'.adj_symm hadj3) (Walk.cons (G'.adj_symm hadj2) (Walk.cons hadj1 Walk.nil))
  refine ⟨p1.append tail, ?_, by simp [Walk.length_append, Walk.length_cons, Walk.length_nil, hlen,
    Walk.length_map]⟩
  simp [Walk.isCycle_def, Walk.isPath_def, Walk.length_append, Walk.length_cons, Walk.length_nil,
    hlen, Walk.length_map, hp0.support_nodup]
  grind

lemma cycleSpectrum_addMaxCycle_pathGraph (m : ℕ) (hm : 3 ≤ m) :
    cycleSpectrum (addMaxCycle (pathGraph m) hm) = {m + 2} := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ :=
    addMaxCycle_maxWalk (pathGraph m) hm (pathGraph_hamiltonianPath m hm)
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, p, hp, hlen'⟩
    by_cases hcase : p.length = m + 2
    · exact hlen'.symm.trans hcase
    · exfalso
      by_cases hnew : ∃ w ∈ p.support, m ≤ w.val
      · rcases hnew with ⟨w, hw, _⟩
        have := addMaxCycle_support_old_of_cycle_ne (pathGraph m) hm p hp hcase w hw
        omega
      · push Not at hnew
        have hold : ∀ w ∈ p.support, w.val < m := hnew
        have hu : u.val < m := hold u (Walk.start_mem_support p)
        obtain ⟨u', v', p', heq, heqv, hmap⟩ := walk_oldMax_eq_map (pathGraph m) hm hu hu p hold
        have huv : u' = v' := embedMaxOld_injective m (heq.symm.trans heqv)
        subst huv
        have hp' : p'.IsCycle :=
          (map_isCycle_iff_of_injective (f := embedMaxOldHom (pathGraph m) hm)
            (embedMaxOld_injective m)).mp (by rw [← hmap]; exact hp)
        exact (pathGraph_IsAcyclic m) p' hp'
  · intro hℓ
    subst hℓ
    exact ⟨(⟨0, by omega⟩ : Fin (m + 2)), pmax, hpmax, hlen⟩

lemma cycleSpectrum_addMaxCycle {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (⟨0, by omega⟩ : Fin m) (finLastPred m (by omega)),
      p.IsPath ∧ p.length = m - 1) :
    cycleSpectrum (addMaxCycle G hm) = cycleSpectrum G ∪ {m + 2} := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ := addMaxCycle_maxWalk G hm hp
  ext ℓ
  simp only [cycleSpectrum, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, p, hp', hlen'⟩
    by_cases hℓ : ℓ = m + 2
    · exact Or.inr hℓ
    · have hold := addMaxCycle_support_old_of_cycle_ne G hm p hp'
        (by intro h; exact hℓ (hlen'.symm.trans h))
      have hu : u.val < m := hold u (Walk.start_mem_support p)
      obtain ⟨u', v', p', heq, heqv, hmap⟩ := walk_oldMax_eq_map G hm hu hu p hold
      have huv : u' = v' := embedMaxOld_injective m (heq.symm.trans heqv)
      subst huv
      have hp'' : p'.IsCycle :=
        (map_isCycle_iff_of_injective (f := embedMaxOldHom G hm) (embedMaxOld_injective m)).mp
          (by rw [← hmap]; exact hp')
      exact Or.inl ⟨u', p', hp'', by rw [← mapWalk_embedMaxOld G hm p', hmap, hlen']⟩
  · intro h
    rcases h with h | h
    · obtain ⟨u, p, hp', hlen'⟩ := h
      exact ⟨embedMaxOld m u, p.map (embedMaxOldHom G hm), map_isCycle_embedMaxOld G hm p hp',
        by rw [← mapWalk_embedMaxOld G hm p, hlen']⟩
    · subst h
      exact ⟨(⟨0, by omega⟩ : Fin (m + 2)), pmax, hpmax, hlen⟩

lemma cycleSpectrum_addMaxCycle_sup {m : ℕ} (G : SimpleGraph (Fin m)) (hm : 3 ≤ m)
    (hp : ∃ p : G.Walk (⟨0, by omega⟩ : Fin m) (finLastPred m (by omega)),
      p.IsPath ∧ p.length = m - 1) :
    cycleSpectrum G ∪ {m + 2} ⊆ cycleSpectrum (addMaxCycle G hm) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨pmax, hpmax, hlen⟩ := addMaxCycle_maxWalk G hm hp
  intro ℓ h
  simp only [Set.mem_union, Set.mem_singleton_iff, cycleSpectrum, Set.mem_setOf_eq] at h ⊢
  rcases h with h | h
  · obtain ⟨u, p, hp', hlen'⟩ := h
    refine ⟨embedMaxOld m u, p.map (embedMaxOldHom G hm), map_isCycle_embedMaxOld G hm p hp', ?_⟩
    rw [← mapWalk_embedMaxOld G hm p, hlen']
  · subst h
    exact ⟨(⟨0, by omega⟩ : Fin (m + 2)), pmax, hpmax, hlen⟩

end ErdosProblem84
