/-
  Part B (Phase 2) — the two alternating matchings of a cycle.

  The cone gadget of `ConeGadget.lean` consumes a cycle in *matching* form: two lists of pairs
  `M₁, M₂` with `pairEdges M₁ ∪ pairEdges M₂` the cycle.  A leftover cycle, on the other hand,
  arrives in *list* form (`IsCycleEdgeSet`, `cycleEdges l`).  This file builds the bridge:

  * `altPairs`, `altPairs₂` — the two alternating matchings of the vertex list `l`;
  * `cycleEdges_eq_altPairs` — the cycle is the union of their edge sets (any length);
  * `matchingPairs_altPairs`, `matchingPairs_altPairs₂` — for a nodup list of even length both
    are genuine matchings, as required by `MatchingPairs`;
  * `mem_altPairs`, `mem_altPairs₂` — their vertices are vertices of `l`, which is how the apex
    conditions of the cone gadget are checked.
-/
import Ax2.PartB.BKLO.CycleChunks
import Ax2.PartB.BKLO.ConeGadget

namespace Ax2.BKLO

open SimpleGraph Finset Ax2

variable {V : Type*} [DecidableEq V]

/-- The odd alternating matching of the vertex list `l`: the pairs
`(l₀,l₁), (l₂,l₃), …`. -/
def altPairs : List V → List (V × V)
  | a :: b :: t => (a, b) :: altPairs t
  | _ => []

/-- The even alternating matching of the vertex list `l`: the pairs
`(l₁,l₂), (l₃,l₄), …, (l_{k-1}, l₀)`, the last one closing the cycle. -/
def altPairs₂ : List V → List (V × V)
  | [] => []
  | a :: t => altPairs t ++ [(t.getLastD a, a)]

omit [DecidableEq V] in
@[simp] theorem altPairs_nil : altPairs ([] : List V) = [] := rfl

omit [DecidableEq V] in
@[simp] theorem altPairs_singleton (a : V) : altPairs [a] = [] := rfl

omit [DecidableEq V] in
@[simp] theorem altPairs_cons_cons (a b : V) (t : List V) :
    altPairs (a :: b :: t) = (a, b) :: altPairs t := rfl

@[simp] theorem pairEdges_nil : pairEdges ([] : List (V × V)) = ∅ := rfl

@[simp] theorem pairEdges_cons (p : V × V) (M : List (V × V)) :
    pairEdges (p :: M) = insert s(p.1, p.2) (pairEdges M) := by
  simp [pairEdges]

theorem pairEdges_append (M N : List (V × V)) :
    pairEdges (M ++ N) = pairEdges M ∪ pairEdges N := by
  induction M with
  | nil => simp
  | cons p M ih => simp [ih, Finset.insert_union]

omit [DecidableEq V] in
/-- The vertices of the odd alternating matching are vertices of the list. -/
theorem mem_altPairs {l : List V} : ∀ p ∈ altPairs l, p.1 ∈ l ∧ p.2 ∈ l := by
  induction l using altPairs.induct with
  | case1 a b t ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by simp, by simp⟩
      · obtain ⟨h1, h2⟩ := ih p hp
        exact ⟨by simp [h1], by simp [h2]⟩
  | case2 l h =>
      intro p hp
      rcases l with _ | ⟨a, t⟩
      · simp [altPairs] at hp
      rcases t with _ | ⟨b, t'⟩
      · simp [altPairs] at hp
      · exact absurd rfl (h a b t')

/-- **The cycle is the union of its two alternating matchings.** -/
theorem pathEdges_eq_altPairs (l : List V) :
    pathEdges l = pairEdges (altPairs l) ∪ pairEdges (altPairs l.tail) := by
  induction l with
  | nil => simp [pathEdges]
  | cons a t ih =>
      cases t with
      | nil => simp [pathEdges, walkEdges]
      | cons b t' =>
          simp only [pathEdges_cons, walkEdges_cons, List.tail_cons] at ih ⊢
          rw [show walkEdges b t' = pathEdges (b :: t') from rfl] at *
          rw [ih]
          simp only [altPairs_cons_cons, pairEdges_cons]
          ext e
          simp only [Finset.mem_insert, Finset.mem_union]
          tauto

/-- **The cycle along `l` is the union of the edges of its two alternating matchings.** -/
theorem cycleEdges_eq_altPairs (l : List V) :
    cycleEdges l = pairEdges (altPairs l) ∪ pairEdges (altPairs₂ l) := by
  cases l with
  | nil => simp [cycleEdges, altPairs₂]
  | cons a t =>
      have hpath : pathEdges (a :: t) = pairEdges (altPairs (a :: t)) ∪ pairEdges (altPairs t) := by
        simpa using pathEdges_eq_altPairs (a :: t)
      have hc : cycleEdges (a :: t)
          = insert s(t.getLastD a, a) (pathEdges (a :: t)) := by
        rw [show cycleEdges (a :: t)
            = insert s((a :: t).getLast (List.cons_ne_nil a t), a) (walkEdges a t) from rfl,
          List.getLast_eq_getLastD]
        rfl
      rw [hc, hpath, altPairs₂, pairEdges_append]
      ext e
      simp only [Finset.mem_insert, Finset.mem_union, pairEdges_cons, pairEdges_nil,
        Finset.notMem_empty, or_false]
      tauto

omit [DecidableEq V] in
/-- The vertices of the even alternating matching are vertices of the list. -/
theorem mem_altPairs₂ {l : List V} : ∀ p ∈ altPairs₂ l, p.1 ∈ l ∧ p.2 ∈ l := by
  cases l with
  | nil => simp [altPairs₂]
  | cons a t =>
      intro p hp
      rw [altPairs₂, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨h1, h2⟩ := mem_altPairs p hp
        exact ⟨by simp [h1], by simp [h2]⟩
      · rw [List.mem_singleton] at hp
        subst hp
        exact ⟨List.getLastD_mem_cons, by simp⟩

omit [DecidableEq V] in
/-- **The odd alternating matching of a nodup list is a matching.** -/
theorem matchingPairs_altPairs {l : List V} (hnd : l.Nodup) : MatchingPairs (altPairs l) := by
  induction l using altPairs.induct with
  | case1 a b t ih =>
      simp only [List.nodup_cons, List.mem_cons] at hnd
      obtain ⟨ha, hb, hnd'⟩ := hnd
      push_neg at ha
      obtain ⟨hab, hat⟩ := ha
      obtain ⟨h1, h2⟩ := ih hnd'
      refine ⟨?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hab
        · exact h1 p hp
      · refine List.pairwise_cons.mpr ⟨?_, h2⟩
        intro q hq
        obtain ⟨hq1, hq2⟩ := mem_altPairs q hq
        refine ⟨fun h => hat ?_, fun h => hat ?_, fun h => hb ?_, fun h => hb ?_⟩
        · rw [show a = q.1 from h]; exact hq1
        · rw [show a = q.2 from h]; exact hq2
        · rw [show b = q.1 from h]; exact hq1
        · rw [show b = q.2 from h]; exact hq2
  | case2 l h =>
      rcases l with _ | ⟨a, t⟩
      · exact ⟨by simp [altPairs], by simp [altPairs]⟩
      rcases t with _ | ⟨b, t'⟩
      · exact ⟨by simp [altPairs], by simp [altPairs]⟩
      · exact absurd rfl (h a b t')

omit [DecidableEq V] in
/-- On a nodup list of *odd* length the last vertex is left uncovered by the odd alternating
matching. -/
theorem getLastD_notMem_altPairs {l : List V} (hnd : l.Nodup) (hodd : Odd l.length) (d : V) :
    ∀ p ∈ altPairs l, p.1 ≠ l.getLastD d ∧ p.2 ≠ l.getLastD d := by
  induction l using altPairs.induct generalizing d with
  | case1 a b t ih =>
      simp only [List.nodup_cons, List.mem_cons] at hnd
      obtain ⟨ha, hb, hnd'⟩ := hnd
      push_neg at ha
      obtain ⟨hab, hat⟩ := ha
      have hlen : Odd t.length := by
        simp only [List.length_cons] at hodd
        rcases hodd with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have hne : t ≠ [] := by
        rintro rfl
        simp at hlen
      have hlast : (a :: b :: t).getLastD d = t.getLastD b := by
        rw [List.getLastD_cons, List.getLastD_cons]
      have hmem : t.getLastD b ∈ t := by
        cases t with
        | nil => exact absurd rfl hne
        | cons c t' =>
            rw [List.getLastD_cons]
            exact List.getLastD_mem_cons
      intro p hp
      rw [hlast]
      rcases List.mem_cons.mp hp with rfl | hp
      · refine ⟨fun h => hat ?_, fun h => hb ?_⟩
        · rw [show a = t.getLastD b from h]; exact hmem
        · rw [show b = t.getLastD b from h]; exact hmem
      · exact ih hnd' hlen b p hp
  | case2 l h =>
      intro p hp
      rcases l with _ | ⟨a, t⟩
      · simp [altPairs] at hp
      rcases t with _ | ⟨b, t'⟩
      · simp [altPairs] at hp
      · exact absurd rfl (h a b t')

omit [DecidableEq V] in
/-- **The even alternating matching of a nodup list of even length is a matching.** -/
theorem matchingPairs_altPairs₂ {l : List V} (hnd : l.Nodup) (heven : Even l.length) :
    MatchingPairs (altPairs₂ l) := by
  cases l with
  | nil => exact ⟨by simp [altPairs₂], by simp [altPairs₂]⟩
  | cons a t =>
      simp only [List.nodup_cons] at hnd
      obtain ⟨ha, hnd'⟩ := hnd
      have hodd : Odd t.length := by
        simp only [List.length_cons] at heven
        rcases heven with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have hne : t ≠ [] := by
        rintro rfl
        simp at hodd
      have hlast : t.getLastD a ∈ t := by
        cases t with
        | nil => exact absurd rfl hne
        | cons c t' =>
            rw [List.getLastD_cons]
            exact List.getLastD_mem_cons
      obtain ⟨h1, h2⟩ := matchingPairs_altPairs (l := t) hnd'
      have hfree := getLastD_notMem_altPairs (l := t) hnd' hodd a
      refine ⟨?_, ?_⟩
      · intro p hp
        rw [altPairs₂, List.mem_append] at hp
        rcases hp with hp | hp
        · exact h1 p hp
        · rw [List.mem_singleton] at hp
          subst hp
          exact fun h => ha (by rw [show t.getLastD a = a from h] at hlast; exact hlast)
      · rw [altPairs₂]
        refine List.pairwise_append.mpr ⟨h2, by simp, ?_⟩
        intro p hp q hq
        rw [List.mem_singleton] at hq
        subst hq
        obtain ⟨hp1, hp2⟩ := mem_altPairs p hp
        obtain ⟨hf1, hf2⟩ := hfree p hp
        refine ⟨hf1, fun h => ha ?_, hf2, fun h => ha ?_⟩
        · rw [show a = p.1 from h.symm]; exact hp1
        · rw [show a = p.2 from h.symm]; exact hp2

/-! ### The spokes of the two matchings -/

@[simp] theorem spokeEdges_nil (w : V) : spokeEdges w ([] : List (V × V)) = ∅ := rfl

@[simp] theorem spokeEdges_cons (w : V) (p : V × V) (M : List (V × V)) :
    spokeEdges w (p :: M) = insert s(w, p.1) (insert s(w, p.2) (spokeEdges w M)) := by
  simp [spokeEdges]

theorem spokeEdges_append (w : V) (M N : List (V × V)) :
    spokeEdges w (M ++ N) = spokeEdges w M ∪ spokeEdges w N := by
  induction M with
  | nil => simp
  | cons p M ih => simp [ih, Finset.insert_union]

/-- All spokes from `w` to the vertices of `l`. -/
def allSpokes (w : V) (l : List V) : Finset (Sym2 V) := (l.map (fun x => s(w, x))).toFinset

@[simp] theorem allSpokes_nil (w : V) : allSpokes w ([] : List V) = ∅ := rfl

@[simp] theorem allSpokes_cons (w a : V) (l : List V) :
    allSpokes w (a :: l) = insert s(w, a) (allSpokes w l) := by
  simp [allSpokes]

theorem allSpokes_of_perm {l l' : List V} (h : l.Perm l') (w : V) :
    allSpokes w l = allSpokes w l' := by
  ext e
  simp only [allSpokes, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, h.mem_iff.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, h.mem_iff.mpr hx, rfl⟩

/-- **On a list of even length the odd alternating matching covers every vertex**: its cone from
`w` uses exactly the spokes from `w` to `l`. -/
theorem spokeEdges_altPairs_even {l : List V} (h : Even l.length) (w : V) :
    spokeEdges w (altPairs l) = allSpokes w l := by
  induction l using altPairs.induct with
  | case1 a b t ih =>
      have ht : Even t.length := by
        simp only [List.length_cons] at h
        rcases h with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      rw [altPairs_cons_cons, spokeEdges_cons, ih ht]
      simp
  | case2 l hl =>
      rcases l with _ | ⟨a, t⟩
      · simp [altPairs]
      rcases t with _ | ⟨b, t'⟩
      · simp at h
      · exact absurd rfl (hl a b t')

/-- On a list of odd length the odd alternating matching leaves exactly the last vertex
uncovered. -/
theorem spokeEdges_altPairs_odd {l : List V} (h : Odd l.length) (w : V) :
    spokeEdges w (altPairs l) = allSpokes w l.dropLast := by
  induction l using altPairs.induct with
  | case1 a b t ih =>
      have ht : Odd t.length := by
        simp only [List.length_cons] at h
        rcases h with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have hne : t ≠ [] := by
        rintro rfl
        simp at ht
      rw [altPairs_cons_cons, spokeEdges_cons, ih ht]
      rw [show (a :: b :: t).dropLast = a :: b :: t.dropLast by
        rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b t),
          List.dropLast_cons_of_ne_nil hne]]
      simp
  | case2 l hl =>
      rcases l with _ | ⟨a, t⟩
      · simp at h
      rcases t with _ | ⟨b, t'⟩
      · simp [altPairs]
      · exact absurd rfl (hl a b t')

/-- **On a list of even length the even alternating matching also covers every vertex**: its cone
from `u` uses exactly the spokes from `u` to `l`.  Hence two even cycles on the same vertex set
span the same double cone — the hypothesis `hspokes` of
`localAbsorbable_evenCycle_of_coneReserve`. -/
theorem spokeEdges_altPairs₂_even {l : List V} (h : Even l.length) (u : V) :
    spokeEdges u (altPairs₂ l) = allSpokes u l := by
  cases l with
  | nil => simp [altPairs₂]
  | cons a t =>
      have ht : Odd t.length := by
        simp only [List.length_cons] at h
        rcases h with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have hne : t ≠ [] := by
        rintro rfl
        simp at ht
      rw [altPairs₂, spokeEdges_append, spokeEdges_altPairs_odd ht]
      have hgl : t.getLast hne = t.getLastD a := by
        cases t with
        | nil => exact absurd rfl hne
        | cons c t' =>
            rw [List.getLastD_cons]
            exact List.getLast_eq_getLastD _
      have hsplit : t.dropLast ++ [t.getLastD a] = t := by
        rw [← hgl]
        exact List.dropLast_append_getLast hne
      have hlast : allSpokes u t = insert s(u, t.getLastD a) (allSpokes u t.dropLast) := by
        have haux : allSpokes u (t.dropLast ++ [t.getLastD a])
            = insert s(u, t.getLastD a) (allSpokes u t.dropLast) := by
          ext e
          simp only [allSpokes, List.map_append, List.toFinset_append, List.mem_toFinset,
            List.mem_map, Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
            · exact Or.inr ⟨x, hx, rfl⟩
            · rw [List.mem_singleton] at hx
              exact Or.inl (by rw [hx])
          · rintro (rfl | ⟨x, hx, rfl⟩)
            · exact Or.inr ⟨t.getLastD a, by simp, rfl⟩
            · exact Or.inl ⟨x, hx, rfl⟩
        rwa [hsplit] at haux
      rw [allSpokes_cons, hlast]
      simp only [spokeEdges_cons, spokeEdges_nil]
      ext e
      simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
      tauto


/-- **Two even cycles on the same vertex set span the same double cone.**  This is exactly the
hypothesis `hspokes` of `localAbsorbable_evenCycle_of_coneReserve`: a reserved double cone over
the vertex set of a cycle serves every other even cycle on that same vertex set. -/
theorem spokeEdges_eq_of_perm {l l' : List V} (hperm : l.Perm l') (h : Even l.length) (w u : V) :
    spokeEdges w (altPairs l') ∪ spokeEdges u (altPairs₂ l')
      = spokeEdges w (altPairs l) ∪ spokeEdges u (altPairs₂ l) := by
  have h' : Even l'.length := by
    rw [← hperm.length_eq]
    exact h
  rw [spokeEdges_altPairs_even h' w, spokeEdges_altPairs₂_even h' u,
    spokeEdges_altPairs_even h w, spokeEdges_altPairs₂_even h u,
    allSpokes_of_perm hperm w, allSpokes_of_perm hperm u]

end Ax2.BKLO
