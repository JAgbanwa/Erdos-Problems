/-
# Back-degeneracy of an edge set on `ℕ`.

To *place* an absorber built over `ℕ` inside a dense host graph one embeds its vertices one at a
time in increasing order, each new vertex landing in the common neighbourhood of the images of its
already-embedded neighbours.  The relevant parameter is therefore the **back-degree** in the natural
order of `ℕ`:

  `NatDegen d A` — every vertex of `A` has at most `d` neighbours smaller than itself.

This file develops the calculus of `backNbrs` / `NatDegen` used to instrument the absorber
recursion of `BKLO.AbsorberExists`:

* the two ways of splitting a union (`natDegen_union_split`, by height; `natDegen_union_supp`, by
  disjoint supports);
* the bound `NatDegen 2` for a single cycle and for a vertex-disjoint family of cycles;
* transport along the translation `v ↦ b + v`, which is how the explicit finite gadgets are placed
  on a fresh block of vertices.
-/
import BKLO.Cycles
import Mathlib.Tactic.Bound

open Finset

namespace BKLO

/-! ### Back-neighbours -/

/-- The `A`-neighbours of `v` that are smaller than `v`. -/
def backNbrs (A : Finset (Sym2 ℕ)) (v : ℕ) : Finset ℕ :=
  (supp A).filter (fun u => u < v ∧ s(u, v) ∈ A)

@[simp] theorem mem_backNbrs {A : Finset (Sym2 ℕ)} {v u : ℕ} :
    u ∈ backNbrs A v ↔ u < v ∧ s(u, v) ∈ A := by
  simp only [backNbrs, Finset.mem_filter, mem_supp]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨_, h2, by simp⟩, h1, h2⟩

/-- **Back-degeneracy.**  Every vertex of `A` has at most `d` neighbours smaller than itself. -/
def NatDegen (d : ℕ) (A : Finset (Sym2 ℕ)) : Prop := ∀ v : ℕ, (backNbrs A v).card ≤ d

theorem natDegen_empty (d : ℕ) : NatDegen d (∅ : Finset (Sym2 ℕ)) := by
  intro v
  simp [backNbrs, supp]

theorem NatDegen.mono {d d' : ℕ} {A : Finset (Sym2 ℕ)} (h : NatDegen d A) (hd : d ≤ d') :
    NatDegen d' A := fun v => le_trans (h v) hd

theorem backNbrs_eq_empty_of_notMem_supp {A : Finset (Sym2 ℕ)} {v : ℕ} (hv : v ∉ supp A) :
    backNbrs A v = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun u hu => ?_)
  rw [mem_backNbrs] at hu
  exact hv (mem_supp.2 ⟨_, hu.2, by simp⟩)

theorem backNbrs_union (A B : Finset (Sym2 ℕ)) (v : ℕ) :
    backNbrs (A ∪ B) v = backNbrs A v ∪ backNbrs B v := by
  ext u
  simp only [mem_backNbrs, Finset.mem_union]
  tauto

theorem card_backNbrs_union_le (A B : Finset (Sym2 ℕ)) (v : ℕ) :
    (backNbrs (A ∪ B) v).card ≤ (backNbrs A v).card + (backNbrs B v).card := by
  rw [backNbrs_union]
  exact Finset.card_union_le _ _

theorem backNbrs_eq_empty_of_touches {c : ℕ} {A : Finset (Sym2 ℕ)} (h : Touches c A) {v : ℕ}
    (hv : v < c) : backNbrs A v = ∅ := by
  refine Finset.eq_empty_of_forall_notMem (fun u hu => ?_)
  rw [mem_backNbrs] at hu
  obtain ⟨w, hw, hwc⟩ := h _ hu.2
  simp only [Sym2.mem_iff] at hw
  rcases hw with rfl | rfl <;> omega

theorem backNbrs_eq_empty_of_below {c : ℕ} {A : Finset (Sym2 ℕ)} (h : Below c A) {v : ℕ}
    (hv : c ≤ v) : backNbrs A v = ∅ :=
  backNbrs_eq_empty_of_notMem_supp (fun hmem => absurd (h v hmem) (by omega))

/-- Two edge sets whose back-neighbourhoods never both fire combine without loss. -/
theorem natDegen_union_of_alt {d : ℕ} {A B : Finset (Sym2 ℕ)} (hA : NatDegen d A)
    (hB : NatDegen d B) (h : ∀ v, backNbrs A v = ∅ ∨ backNbrs B v = ∅) : NatDegen d (A ∪ B) := by
  intro v
  rw [backNbrs_union]
  rcases h v with he | he <;> simp [he, hA v, hB v]

/-- **Splitting by height.**  `A` lives below `c` and every edge of `B` reaches above `c`. -/
theorem natDegen_union_split {d c : ℕ} {A B : Finset (Sym2 ℕ)} (hA : NatDegen d A)
    (hB : NatDegen d B) (hbA : Below c A) (htB : Touches c B) : NatDegen d (A ∪ B) := by
  refine natDegen_union_of_alt hA hB (fun v => ?_)
  rcases Nat.lt_or_ge v c with hv | hv
  · exact Or.inr (backNbrs_eq_empty_of_touches htB hv)
  · exact Or.inl (backNbrs_eq_empty_of_below hbA hv)

/-- **Splitting by support.** -/
theorem natDegen_union_supp {d : ℕ} {A B : Finset (Sym2 ℕ)} (hA : NatDegen d A)
    (hB : NatDegen d B) (hd : Disjoint (supp A) (supp B)) : NatDegen d (A ∪ B) := by
  refine natDegen_union_of_alt hA hB (fun v => ?_)
  by_cases hv : v ∈ supp A
  · exact Or.inr (backNbrs_eq_empty_of_notMem_supp (Finset.disjoint_left.1 hd hv))
  · exact Or.inl (backNbrs_eq_empty_of_notMem_supp hv)

theorem natDegen_of_forall_supp {d : ℕ} {A : Finset (Sym2 ℕ)}
    (h : ∀ v ∈ supp A, (backNbrs A v).card ≤ d) : NatDegen d A := by
  intro v
  by_cases hv : v ∈ supp A
  · exact h v hv
  · simp [backNbrs_eq_empty_of_notMem_supp hv]

/-! ### Comparison with the degree -/

theorem card_backNbrs_le_deg (A : Finset (Sym2 ℕ)) (v : ℕ) : (backNbrs A v).card ≤ deg A v := by
  refine Finset.card_le_card_of_injOn (fun u => s(u, v)) (fun u hu => ?_) (fun u hu u' hu' huu => ?_)
  · simp only [Finset.mem_coe, mem_backNbrs] at hu
    exact Finset.mem_filter.2 ⟨hu.2, by simp⟩
  · simp only [Finset.mem_coe, mem_backNbrs] at hu hu'
    simp only [Sym2.eq_iff] at huu
    rcases huu with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · omega

theorem natDegen_of_deg_le {d : ℕ} {A : Finset (Sym2 ℕ)} (h : ∀ v, deg A v ≤ d) : NatDegen d A :=
  fun v => le_trans (card_backNbrs_le_deg A v) (h v)

/-! ### Degrees along a path and a cycle -/

theorem deg_empty (v : ℕ) : deg (∅ : Finset (Sym2 ℕ)) v = 0 := by simp [deg]

theorem deg_le_of_notMem_supp {A : Finset (Sym2 ℕ)} {v : ℕ} (hv : v ∉ supp A) : deg A v = 0 := by
  rw [deg, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem (fun e he => ?_)
  rw [Finset.mem_filter] at he
  exact hv (mem_supp.2 ⟨e, he.1, he.2⟩)

theorem deg_insert_le (e : Sym2 ℕ) (E : Finset (Sym2 ℕ)) (v : ℕ) :
    deg (insert e E) v ≤ deg E v + (if v ∈ e then 1 else 0) := by
  by_cases hv : v ∈ e
  · simp only [hv, if_pos]
    rw [deg, deg, Finset.filter_insert, if_pos hv]
    exact le_trans (Finset.card_insert_le _ _) (by omega)
  · simp only [hv, if_neg, not_false_iff]
    rw [deg, deg, Finset.filter_insert, if_neg hv]
    omega

/-- Along a path with distinct vertices, every vertex has degree at most `2`, and the two
endpoints have degree at most `1`. -/
theorem deg_pathEdges_bounds : ∀ {l : List ℕ}, l.Nodup → ∀ v : ℕ,
    deg (pathEdges l) v ≤ 2 ∧ (l.head? = some v → deg (pathEdges l) v ≤ 1) ∧
      (l.getLast? = some v → deg (pathEdges l) v ≤ 1) := by
  intro l
  induction l with
  | nil => intro _ v; simp [deg_empty]
  | cons a t IH =>
    match t with
    | [] => intro _ v; simp [deg_empty]
    | b :: t' =>
      intro hnd v
      have hndt : (b :: t').Nodup := hnd.of_cons
      have hant : a ∉ (b :: t') := by
        simpa using (List.nodup_cons.1 hnd).1
      have hasupp : a ∉ supp (pathEdges (b :: t')) := fun hmem =>
        hant (List.mem_toFinset.1 (supp_pathEdges _ hmem))
      have hdega : deg (pathEdges (b :: t')) a = 0 := deg_le_of_notMem_supp hasupp
      have hkey := deg_insert_le s(a, b) (pathEdges (b :: t')) v
      rw [← pathEdges_cons₂] at hkey
      have hIH := IH hndt v
      refine ⟨?_, ?_, ?_⟩
      · by_cases hv : v ∈ s(a, b)
        · rw [if_pos hv] at hkey
          have hv' : v = a ∨ v = b := by simpa using hv
          rcases hv' with rfl | rfl
          · rw [hdega] at hkey; omega
          · have := (IH hndt v).2.1 (by simp); omega
        · rw [if_neg hv] at hkey
          omega
      · intro hhd
        have hva : v = a := by simpa using hhd.symm
        have hmem : v ∈ s(a, b) := by rw [hva]; simp
        rw [if_pos hmem, hva, hdega] at hkey
        rw [hva]
        omega
      · intro hlast
        have hlast' : (b :: t').getLast? = some v := by simpa using hlast
        have hvb : v ∈ (b :: t') := List.mem_of_getLast? hlast'
        have hva : v ≠ a := by rintro rfl; exact hant hvb
        cases t' with
        | nil =>
          have hvb2 : b = v := by simpa using hlast'
          rw [← hvb2]
          simp only [pathEdges_cons₂, pathEdges_singleton]
          rw [deg, Finset.filter_insert, if_pos (by simp : b ∈ s(a, b))]
          simp
        | cons c t'' =>
          have hlast'' : (c :: t'').getLast? = some v := by simpa using hlast'
          have hvb2 : v ≠ b := by
            rintro rfl
            exact (List.nodup_cons.1 hndt).1 (List.mem_of_getLast? hlast'')
          have h1 := (IH hndt v).2.2 hlast'
          have hvin : v ∉ s(a, b) := by
            simp only [Sym2.mem_iff]
            rintro (rfl | rfl)
            exacts [hva rfl, hvb2 rfl]
          rw [if_neg hvin] at hkey
          omega

theorem deg_cycEdges_le_two {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) (v : ℕ) :
    deg (cycEdges l) v ≤ 2 := by
  obtain ⟨a, z, ha, hz, -, -, heq, -⟩ := cycEdges_eq hnd h3
  rw [heq]
  have hkey := deg_insert_le s(z, a) (pathEdges l) v
  have hb := deg_pathEdges_bounds hnd v
  by_cases hv : v ∈ s(z, a)
  · rw [if_pos hv] at hkey
    have hv' : v = z ∨ v = a := by simpa using hv
    rcases hv' with rfl | rfl
    · have := hb.2.2 hz; omega
    · have := hb.2.1 ha; omega
  · rw [if_neg hv] at hkey
    omega

theorem natDegen_cycEdges {l : List ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length) :
    NatDegen 2 (cycEdges l) :=
  natDegen_of_deg_le (deg_cycEdges_le_two hnd h3)

/-! ### Vertex-disjoint families -/

theorem natDegen_cycFamEdges_vertDisj : ∀ {L : List (List ℕ)}, VertDisjFam L →
    NatDegen 2 (cycFamEdges L) := by
  intro L
  induction L with
  | nil => intro _; simpa using natDegen_empty 2
  | cons l L IH =>
    intro hvd
    have htail : VertDisjFam L :=
      ⟨fun x hx => hvd.nodup x (List.mem_cons_of_mem _ hx),
        fun x hx => hvd.three x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 hvd.pdisj).2⟩
    rw [cycFamEdges_cons]
    refine natDegen_union_supp (natDegen_cycEdges (hvd.nodup l (by simp)) (hvd.three l (by simp)))
      (IH htail) ?_
    rw [Finset.disjoint_left]
    intro v hv hv'
    have h1 : v ∈ l := List.mem_toFinset.1 (supp_cycEdges _ hv)
    have h2 := supp_cycFamEdges L hv'
    rw [List.mem_toFinset, List.mem_flatten] at h2
    obtain ⟨l', hl', hvl'⟩ := h2
    exact (List.pairwise_cons.1 hvd.pdisj).1 l' hl' v h1 hvl'

end BKLO
