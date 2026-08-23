/-
# The greedy cover-down.

The second half of a vortex step of BKLO §10 covers the sparse leftover `L` of the nibble by
triangles whose apex lies in the next vortex set `W`, using only *reserved* edges (the edge set `R`
that the nibble was told to avoid, cf. `BKLO.nibbleReserving_of_inputs`).

This file proves that step as a purely combinatorial statement: if no edge of the leftover meets
`W` and every edge `uv` of the leftover has at least `deg_L(u) + deg_L(v)` reserved common
neighbours in `W`, then the leftover is covered by edge-disjoint triangles, each consisting of one
leftover edge and two reserved edges.  The degree bound is exactly what the greedy argument needs:
when the edge `uv` is processed, the apexes already used up are those consumed by the previously
processed leftover edges at `u` and at `v`.

Everything here is `sorry`-free.
-/
import BKLO.Vortex

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-- The reserved common neighbours of `u` and `v` inside `W`: the possible apexes of a triangle
covering the edge `uv` and using only reserved edges. -/
def apexes (R : Finset (Sym2 V)) (W : Finset V) (u v : V) : Finset V :=
  W.filter (fun w => s(u, w) ∈ R ∧ s(v, w) ∈ R)

theorem mem_apexes {R : Finset (Sym2 V)} {W : Finset V} {u v w : V} :
    w ∈ apexes R W u v ↔ w ∈ W ∧ s(u, w) ∈ R ∧ s(v, w) ∈ R := by
  simp [apexes]

theorem filter_erase (L : Finset (Sym2 V)) (e : Sym2 V) (p : Sym2 V → Prop) [DecidablePred p] :
    (L.erase e).filter p = (L.filter p).erase e := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_erase]
  tauto

theorem edeg_erase_of_mem {L : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ L) (v : V) (hv : v ∈ e) :
    edeg (L.erase e) v + 1 = edeg L v := by
  classical
  have h : (L.erase e).filter (fun f => v ∈ f) = (L.filter (fun f => v ∈ f)).erase e :=
    filter_erase _ _ _
  have hmem : e ∈ L.filter (fun f => v ∈ f) := Finset.mem_filter.2 ⟨he, hv⟩
  have hpos : 1 ≤ (L.filter (fun f => v ∈ f)).card := Finset.card_pos.2 ⟨e, hmem⟩
  rw [edeg, h, Finset.card_erase_of_mem hmem, edeg]
  omega

theorem edeg_erase_le (L : Finset (Sym2 V)) (e : Sym2 V) (v : V) :
    edeg (L.erase e) v ≤ edeg L v :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

/-- The three edges of a triangle on three distinct vertices. -/
theorem cliqueEdges_tripleV {x y w : V} (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) :
    cliqueEdges ({x, y, w} : Finset V) = {s(x, y), s(x, w), s(y, w)} := by
  classical
  have hyx : y ≠ x := hxy.symm
  have hwx : w ≠ x := hxw.symm
  have hwy : w ≠ y := hyw.symm
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_cliqueEdgesV, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton,
      Sym2.isDiag_iff_proj_eq, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hab⟩
      have ha := hmem a (Or.inl rfl)
      have hb := hmem b (Or.inr rfl)
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp_all
    · intro h
      have hmem : ∀ z : V, z = a ∨ z = b → z = x ∨ z = y ∨ z = w := by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rintro z (rfl | rfl) <;> tauto
      refine ⟨hmem, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp_all

/-- **The greedy cover-down.**  Suppose the leftover `L` is disjoint from the reserved set `R`, is
loopless, meets no vertex of the apex set `W`, and every edge `uv` of `L` has at least
`deg_L(u) + deg_L(v)` reserved common neighbours in `W`.  Then `L` is covered by a family of
edge-disjoint triangles, each consisting of one edge of `L` and two reserved edges. -/
theorem exists_coverDown_family (W : Finset V) :
    ∀ (n : ℕ) (L R : Finset (Sym2 V)), L.card ≤ n → Disjoint L R →
      (∀ u v : V, s(u, v) ∈ L → u ≠ v) →
      (∀ u v : V, s(u, v) ∈ L → u ∉ W ∧ v ∉ W) →
      (∀ u v : V, s(u, v) ∈ L → edeg L u + edeg L v ≤ (apexes R W u v).card) →
      ∃ P : Finset (Finset V), (∀ t ∈ P, t.card = 3) ∧ (∀ t ∈ P, cliqueEdges t ⊆ L ∪ R) ∧
        (∀ t ∈ P, ∀ t' ∈ P, t ≠ t' → Disjoint (cliqueEdges t) (cliqueEdges t')) ∧
        L ⊆ famEdges P := by
  classical
  intro n
  induction n with
  | zero =>
    intro L R hcard _ _ _ _
    have hL : L = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    exact ⟨∅, by simp, by simp, by simp, by simp [hL]⟩
  | succ n ih =>
    intro L R hcard hLR hnd hLW hcod
    rcases Finset.eq_empty_or_nonempty L with rfl | ⟨e, he⟩
    · exact ⟨∅, by simp, by simp, by simp, by simp⟩
    · induction e using Sym2.ind with
      | _ x y =>
        have hxy : x ≠ y := hnd x y he
        have hxW : x ∉ W := (hLW x y he).1
        have hyW : y ∉ W := (hLW x y he).2
        -- choose an apex
        have hpos : 0 < (apexes R W x y).card := by
          have h1 : 1 ≤ edeg L x :=
            Finset.card_pos.2 ⟨s(x, y), Finset.mem_filter.2 ⟨he, by simp⟩⟩
          have := hcod x y he
          omega
        obtain ⟨w, hw⟩ := Finset.card_pos.1 hpos
        obtain ⟨hwW, hxw, hyw⟩ := mem_apexes.1 hw
        have hxw' : x ≠ w := fun h => hxW (h ▸ hwW)
        have hyw' : y ≠ w := fun h => hyW (h ▸ hwW)
        set L' : Finset (Sym2 V) := L.erase s(x, y) with hL'
        set R' : Finset (Sym2 V) := (R.erase s(x, w)).erase s(y, w) with hR'
        have hL'sub : L' ⊆ L := Finset.erase_subset _ _
        have hR'sub : R' ⊆ R := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
        have hnd' : ∀ u v : V, s(u, v) ∈ L' → u ≠ v := fun u v h => hnd u v (hL'sub h)
        have hLW' : ∀ u v : V, s(u, v) ∈ L' → u ∉ W ∧ v ∉ W := fun u v h => hLW u v (hL'sub h)
        have hLR' : Disjoint L' R' :=
          Finset.disjoint_of_subset_left hL'sub (Finset.disjoint_of_subset_right hR'sub hLR)
        -- an apex is lost only if it is `w`
        have hapex : ∀ u v : V, u ∉ W → v ∉ W →
            (apexes R W u v).erase w ⊆ apexes R' W u v := by
          intro u v huW hvW z hz
          obtain ⟨hzw, hz'⟩ := Finset.mem_erase.1 hz
          obtain ⟨hzW, hzu, hzv⟩ := mem_apexes.1 hz'
          have key : ∀ a : V, a ∉ W → s(a, z) ∈ R → s(a, z) ∈ R' := by
            intro a haW haz
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, haz⟩⟩
            · intro h
              rw [Sym2.eq_iff] at h
              rcases h with ⟨-, rfl⟩ | ⟨rfl, -⟩
              exacts [hzw rfl, haW hwW]
            · intro h
              rw [Sym2.eq_iff] at h
              rcases h with ⟨-, rfl⟩ | ⟨rfl, -⟩
              exacts [hzw rfl, haW hwW]
          exact mem_apexes.2 ⟨hzW, key u huW hzu, key v hvW hzv⟩
        have hcod' : ∀ u v : V, s(u, v) ∈ L' → edeg L' u + edeg L' v ≤ (apexes R' W u v).card := by
          intro u v huv
          have huvL : s(u, v) ∈ L := hL'sub huv
          have huW := (hLW u v huvL).1
          have hvW := (hLW u v huvL).2
          have hcard1 : (apexes R W u v).card ≤ (apexes R' W u v).card + 1 := by
            have h1 : ((apexes R W u v).erase w).card ≤ (apexes R' W u v).card :=
              Finset.card_le_card (hapex u v huW hvW)
            have h2 : (apexes R W u v).card ≤ ((apexes R W u v).erase w).card + 1 := by
              by_cases hmem : w ∈ apexes R W u v
              · rw [Finset.card_erase_of_mem hmem]
                have : 1 ≤ (apexes R W u v).card := Finset.card_pos.2 ⟨w, hmem⟩
                omega
              · rw [Finset.erase_eq_of_notMem hmem]; omega
            omega
          have hbase := hcod u v huvL
          by_cases hu : u = x ∨ u = y
          · have hdu : edeg L' u + 1 = edeg L u := by
              refine edeg_erase_of_mem he u ?_
              rcases hu with rfl | rfl <;> simp
            have hdv : edeg L' v ≤ edeg L v := edeg_erase_le _ _ _
            omega
          · by_cases hv : v = x ∨ v = y
            · have hdv : edeg L' v + 1 = edeg L v := by
                refine edeg_erase_of_mem he v ?_
                rcases hv with rfl | rfl <;> simp
              have hdu : edeg L' u ≤ edeg L u := edeg_erase_le _ _ _
              omega
            · -- no shared endpoint: no apex is lost at all
              have hsub : apexes R W u v ⊆ apexes R' W u v := by
                intro z hz
                obtain ⟨hzW, hzu, hzv⟩ := mem_apexes.1 hz
                have key : ∀ a : V, ¬ (a = x ∨ a = y) → a ∉ W → s(a, z) ∈ R → s(a, z) ∈ R' := by
                  intro a ha haW haz
                  push_neg at ha
                  refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, haz⟩⟩
                  · intro h
                    rw [Sym2.eq_iff] at h
                    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
                    exacts [ha.2 rfl, haW hwW]
                  · intro h
                    rw [Sym2.eq_iff] at h
                    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
                    exacts [ha.1 rfl, haW hwW]
                exact mem_apexes.2 ⟨hzW, key u hu huW hzu, key v hv hvW hzv⟩
              have hdu : edeg L' u ≤ edeg L u := edeg_erase_le _ _ _
              have hdv : edeg L' v ≤ edeg L v := edeg_erase_le _ _ _
              have := Finset.card_le_card hsub
              omega
        have hcardL' : L'.card ≤ n := by
          have hpos' : 1 ≤ L.card := Finset.card_pos.2 ⟨_, he⟩
          have : L'.card + 1 = L.card := by
            rw [hL', Finset.card_erase_of_mem he]; omega
          omega
        obtain ⟨P, hP3, hPsub, hPdisj, hPcov⟩ := ih L' R' hcardL' hLR' hnd' hLW' hcod'
        -- add the triangle `{x, y, w}`
        have htri : cliqueEdges ({x, y, w} : Finset V) = {s(x, y), s(x, w), s(y, w)} :=
          cliqueEdges_tripleV hxy hxw' hyw'
        have hfresh : ∀ f ∈ cliqueEdges ({x, y, w} : Finset V), f ∉ L' ∪ R' := by
          intro f hf hmem
          rw [htri] at hf
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases Finset.mem_union.1 hmem with hL'' | hR''
          · rcases hf with rfl | rfl | rfl
            · exact (Finset.mem_erase.1 hL'').1 rfl
            · exact (hLW x w (hL'sub hL'')).2 hwW
            · exact (hLW y w (hL'sub hL'')).2 hwW
          · rcases hf with rfl | rfl | rfl
            · exact (Finset.disjoint_left.1 hLR he) (hR'sub hR'')
            · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hR'').2).1 rfl
            · exact (Finset.mem_erase.1 hR'').1 rfl
        have hcard3 : ({x, y, w} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hxy, hxw']),
            Finset.card_insert_of_notMem (by simp [hyw']), Finset.card_singleton]
        refine ⟨insert ({x, y, w} : Finset V) P, ?_, ?_, ?_, ?_⟩
        · intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht
          exacts [hcard3, hP3 t ht]
        · intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht
          · rw [htri]
            intro f hf
            simp only [Finset.mem_insert, Finset.mem_singleton] at hf
            rcases hf with rfl | rfl | rfl
            exacts [Finset.mem_union_left _ he, Finset.mem_union_right _ hxw,
              Finset.mem_union_right _ hyw]
          · exact (hPsub t ht).trans (Finset.union_subset_union hL'sub hR'sub)
        · have hcross : ∀ t ∈ P, Disjoint (cliqueEdges ({x, y, w} : Finset V)) (cliqueEdges t) := by
            intro t ht
            refine Finset.disjoint_left.2 fun f hf hf' => ?_
            exact hfresh f hf (hPsub t ht hf')
          intro t ht t' ht' hne
          rcases Finset.mem_insert.1 ht with rfl | ht
          · rcases Finset.mem_insert.1 ht' with h' | h'
            · exact absurd h'.symm hne
            · exact hcross t' h'
          · rcases Finset.mem_insert.1 ht' with rfl | h'
            · exact (hcross t ht).symm
            · exact hPdisj t ht t' h' hne
        · intro f hf
          by_cases hfe : f = s(x, y)
          · subst hfe
            refine Finset.mem_biUnion.2 ⟨{x, y, w}, Finset.mem_insert_self _ _, ?_⟩
            rw [htri]; simp
          · have : f ∈ L' := Finset.mem_erase.2 ⟨hfe, hf⟩
            obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.1 (hPcov this)
            exact Finset.mem_biUnion.2 ⟨t, Finset.mem_insert_of_mem ht, hft⟩

end BKLO
