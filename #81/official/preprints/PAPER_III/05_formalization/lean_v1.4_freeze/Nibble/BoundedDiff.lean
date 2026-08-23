/-
# Nibble — Module M5 (core) : locality of the round matching under a single-edge change

Standalone, Mathlib-only. Toward the bounded-difference input of the McDiarmid bridge (Layer M).

The bounded-difference property of `deg_residual(v)` under toggling one retention bit rests on a
purely combinatorial *locality* fact: adding one edge `e` to the retained set `R` changes the
round's matching only among `e` itself and the edges conflicting with `e`. Precisely:

* `roundMatching_insert_sdiff_subset` — new matched edges after adding `e` are just `{e}`.
* `roundMatching_erase_sdiff_subset` — edges that stop being matched all conflict with `e`.

Together these bound the symmetric difference of the matchings (hence of the covered set, hence
the change in `deg_residual(v)`) by a local quantity — the seed of the McDiarmid coefficient `c_e`.

Deterministic; holds for any `R`. Must be sorry-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.Basic
import Nibble.Round

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- **M5-core(1) — new matched edges after adding `e` are just `e`.** -/
theorem roundMatching_insert_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    roundMatching (insert e R) \ roundMatching R ⊆ {e} := by
  intro f hf
  rw [Finset.mem_sdiff] at hf
  obtain ⟨hf', hfnot⟩ := hf
  rw [roundMatching, Finset.mem_filter] at hf' hfnot
  push_neg at hfnot
  rw [Finset.mem_singleton]
  by_contra hfe
  obtain ⟨hfins, hiso⟩ := hf'
  have hfR : f ∈ R := (Finset.mem_insert.mp hfins).resolve_left hfe
  obtain ⟨g, hgR, hgf, hndis⟩ := hfnot hfR
  exact hndis (hiso g (Finset.mem_insert_of_mem hgR) hgf)

/-- **M5-core(2) — edges that stop being matched all conflict with `e`.** -/
theorem roundMatching_erase_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    roundMatching R \ roundMatching (insert e R) ⊆ R.filter (fun f => ¬ Disjoint e f) := by
  intro f hf
  rw [Finset.mem_sdiff] at hf
  obtain ⟨hf', hfnot⟩ := hf
  rw [roundMatching, Finset.mem_filter] at hf' hfnot
  obtain ⟨hfR, hiso⟩ := hf'
  push_neg at hfnot
  rw [Finset.mem_filter]
  refine ⟨hfR, ?_⟩
  obtain ⟨g, hgins, hgf, hndis⟩ := hfnot (Finset.mem_insert_of_mem hfR)
  rcases Finset.mem_insert.mp hgins with hge | hgR
  · subst hge
    rwa [disjoint_comm]
  · exact absurd (hiso g hgR hgf) hndis

/-- **M5-core(3) — newly covered vertices after adding `e` lie in `e`.** -/
theorem covered_insert_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered (insert e R) \ covered R ⊆ e := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxin, hxout⟩ := hx
  rw [covered, support, Finset.mem_biUnion] at hxin hxout
  push_neg at hxout
  obtain ⟨f, hfM, hxf⟩ := hxin
  have hfnotR : f ∉ roundMatching R := fun h => hxout f h (by simpa using hxf)
  have : f ∈ {e} := roundMatching_insert_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hfM, hfnotR⟩)
  rw [Finset.mem_singleton] at this
  subst this
  simpa using hxf

/-- **M5-core(4) — vertices that stop being covered lie in the support of the edges conflicting
with `e`.** -/
theorem covered_erase_sdiff_subset (R : Finset (Finset V)) (e : Finset V) :
    covered R \ covered (insert e R) ⊆ support (R.filter (fun f => ¬ Disjoint e f)) := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxin, hxout⟩ := hx
  rw [covered, support, Finset.mem_biUnion] at hxin hxout
  push_neg at hxout
  obtain ⟨f, hfM, hxf⟩ := hxin
  have hfnot : f ∉ roundMatching (insert e R) := fun h => hxout f h (by simpa using hxf)
  have hfc : f ∈ R.filter (fun f => ¬ Disjoint e f) :=
    roundMatching_erase_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hfM, hfnot⟩)
  rw [support, Finset.mem_biUnion]
  exact ⟨f, hfc, hxf⟩

/-- **M5-core(5) — residual degree changes only among `v`-edges meeting the local set.**
The `v`-edges whose residual-membership flips when `e` is toggled all meet
`D = e ∪ support(edges conflicting with e)`. Hence the change in `deg_residual(v)` is bounded by
the number of `v`-edges meeting the *local* set `D` — this is the McDiarmid coefficient `c_e`,
confirmed local (independent of `|H|`). -/
theorem residual_deg_change_local (H R : Finset (Finset V)) (e : Finset V) (v : V) :
    (((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R)))
          \ ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R)))))
        ∪ (((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R))))
          \ ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R))))
      ⊆ (H.filter (fun f => v ∈ f)).filter
          (fun f => ¬ Disjoint f (e ∪ support (R.filter (fun g => ¬ Disjoint e g)))) := by
  intro f hf
  rw [Finset.mem_union] at hf
  rw [Finset.mem_filter]
  rcases hf with hf | hf <;> rw [Finset.mem_sdiff] at hf
  · obtain ⟨hfa, hfb⟩ := hf
    rw [Finset.mem_filter] at hfa
    refine ⟨hfa.1, ?_⟩
    have hnd : ¬ Disjoint f (covered (insert e R)) := fun h =>
      hfb (Finset.mem_filter.mpr ⟨hfa.1, h⟩)
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨x, hxf, hxc⟩ := hnd
    have hxnotR : x ∉ covered R := fun h => (Finset.disjoint_left.mp hfa.2 hxf) h
    have hxe : x ∈ e := covered_insert_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hxc, hxnotR⟩)
    rw [Finset.not_disjoint_iff]
    exact ⟨x, hxf, Finset.mem_union_left _ hxe⟩
  · obtain ⟨hfb, hfa⟩ := hf
    rw [Finset.mem_filter] at hfb
    refine ⟨hfb.1, ?_⟩
    have hnd : ¬ Disjoint f (covered R) := fun h =>
      hfa (Finset.mem_filter.mpr ⟨hfb.1, h⟩)
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨x, hxf, hxc⟩ := hnd
    have hxnotR' : x ∉ covered (insert e R) := fun h => (Finset.disjoint_left.mp hfb.2 hxf) h
    have hxsup : x ∈ support (R.filter (fun g => ¬ Disjoint e g)) :=
      covered_erase_sdiff_subset R e (Finset.mem_sdiff.mpr ⟨hxc, hxnotR'⟩)
    rw [Finset.not_disjoint_iff]
    exact ⟨x, hxf, Finset.mem_union_right _ hxsup⟩

/-- **M5 — the McDiarmid coefficient `c_e` is explicitly local.** The number of `v`-edges whose
residual-membership changes when edge `e` is toggled is at most `∑_{x∈D} deg x`, where
`D = e ∪ support(edges conflicting with e)` — an explicit, local bound (no dependence on `|H|`).
This is the bounded-difference coefficient `c_e` of `deg_residual(v)` for McDiarmid. -/
theorem residual_deg_change_card_le (H R : Finset (Finset V)) (e : Finset V) (v : V) :
    ((((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R)))
          \ ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R)))))
        ∪ (((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered (insert e R))))
          \ ((H.filter (fun f => v ∈ f)).filter (fun f => Disjoint f (covered R))))).card
      ≤ ∑ x ∈ (e ∪ support (R.filter (fun g => ¬ Disjoint e g))), degree H x := by
  refine le_trans (Finset.card_le_card (residual_deg_change_local H R e v)) ?_
  refine le_trans (Finset.card_le_card ?_)
    (edges_meeting_le H (e ∪ support (R.filter (fun g => ¬ Disjoint e g))))
  intro f hf
  rw [Finset.mem_filter] at hf
  obtain ⟨hfH, hfnd⟩ := hf
  rw [Finset.mem_filter] at hfH
  rw [Finset.mem_filter]
  refine ⟨hfH.1, ?_⟩
  rwa [Finset.not_disjoint_iff_nonempty_inter] at hfnd

end Hypergraph
