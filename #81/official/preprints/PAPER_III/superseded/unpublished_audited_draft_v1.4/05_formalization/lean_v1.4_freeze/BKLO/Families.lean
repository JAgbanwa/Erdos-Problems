/-
# Families of cycles: relocation onto fresh vertices, and the reduction round.

Three cover steps make up one *round* of the absorber construction.  Starting from a family `L` of
edge-disjoint cycles living below `b`:

1. `subdivFam L b` — subdivide every cycle, giving each cycle a private block of fresh vertices.
   The original family covers the subdivided one (`subdiv_cyc`).
2. `freshFam L b` — the fresh copies, i.e. the blocks themselves.  Each fresh copy covers the
   corresponding subdivided cycle (`subdiv_cyc'`).  After this step the family is *vertex*-disjoint
   and lives entirely above `b`.
3. `reduceFam` — apply the halving/odd/four move to every cycle, shrinking every cycle of length
   `≥ 6` and flipping `4 ↔ 5`.

Because covers compose (`BKLO.Covers`), and because `3 ∣ |T| + |C|` for a cover, a family whose
total length is divisible by `3` is carried to a family with the same property.
-/
import BKLO.GadgetsBlk
import BKLO.HasAbs

open Finset

namespace BKLO

/-! ### Disjointness from supports -/

theorem disjoint_of_supp_disjoint {E₁ E₂ : Finset (Sym2 ℕ)} (h : ∀ v ∈ supp E₁, v ∉ supp E₂) :
    Disjoint E₁ E₂ := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  revert he₁ he₂
  induction e using Sym2.ind with
  | _ x y =>
    intro he₁ he₂
    exact h x (mem_supp.2 ⟨_, he₁, by simp⟩) (mem_supp.2 ⟨_, he₂, by simp⟩)

/-- The support of a cycle family is contained in the union of its cycles. -/
theorem supp_cycFamEdges_mem {L : List (List ℕ)} {v : ℕ} (hv : v ∈ supp (cycFamEdges L)) :
    ∃ l ∈ L, v ∈ l := by
  have := supp_cycFamEdges L hv
  rw [List.mem_toFinset, List.mem_flatten] at this
  exact this

/-! ### The generic family transformation -/

/-- Apply the cycle transformation `F` to every member of a family, giving the `i`-th cycle a
private block of `w`-many fresh vertices, laid end to end starting at `b`. -/
def famMap (F : List ℕ → ℕ → List ℕ) (w : List ℕ → ℕ) : List (List ℕ) → ℕ → List (List ℕ)
  | [], _ => []
  | l :: L, b => F l b :: famMap F w L (b + w l)

@[simp] theorem famMap_nil (F w) (b : ℕ) : famMap F w [] b = [] := rfl

@[simp] theorem famMap_cons (F w) (l : List ℕ) (L : List (List ℕ)) (b : ℕ) :
    famMap F w (l :: L) b = F l b :: famMap F w L (b + w l) := rfl

/-- Total width of the fresh blocks used by `famMap`. -/
def totalW (w : List ℕ → ℕ) (L : List (List ℕ)) : ℕ := (L.map w).sum

@[simp] theorem totalW_nil (w) : totalW w [] = 0 := rfl

@[simp] theorem totalW_cons (w) (l : List ℕ) (L : List (List ℕ)) :
    totalW w (l :: L) = w l + totalW w L := rfl

theorem famMap_length (F w) (L : List (List ℕ)) (b : ℕ) : (famMap F w L b).length = L.length := by
  induction L generalizing b <;> simp_all

theorem famMap_forall₂ {F w} {Q : List ℕ → List ℕ → Prop} {L : List (List ℕ)} {b : ℕ}
    (h : ∀ l ∈ L, ∀ b', b ≤ b' → Q l (F l b')) : List.Forall₂ Q L (famMap F w L b) := by
  revert h
  induction L generalizing b with
  | nil => intro _; simp
  | cons l L IH =>
    intro h
    rw [famMap_cons]
    refine List.Forall₂.cons (h l (by simp) b le_rfl) (IH ?_)
    intro l' hl' b' hb'
    exact h l' (List.mem_cons_of_mem _ hl') b' (le_trans (Nat.le_add_right b _) hb')

/-- Where the transformed cycles live. -/
theorem famMap_mem {F w} {L : List (List ℕ)} {b : ℕ}
    (hF : ∀ l ∈ L, ∀ b', b ≤ b' → ∀ v ∈ F l b', v ∈ l ∨ (b' ≤ v ∧ v < b' + w l)) :
    ∀ l' ∈ famMap F w L b, ∀ v ∈ l',
      v ∈ L.flatten ∨ (b ≤ v ∧ v < b + totalW w L) := by
  revert hF
  induction L generalizing b with
  | nil => intro _ l' hl'; simp at hl'
  | cons l L IH =>
    intro hF l' hl' v hv
    rw [famMap_cons, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · rcases hF l (by simp) b le_rfl v hv with h | h
      · exact Or.inl (by rw [List.flatten_cons]; exact List.mem_append_left _ h)
      · refine Or.inr ?_
        simp only [totalW_cons]
        omega
    · have hIH := IH (b := b + w l)
        (fun x hx b' hb' => hF x (List.mem_cons_of_mem _ hx) b'
          (le_trans (Nat.le_add_right _ _) hb')) l' hl' v hv
      rcases hIH with h | h
      · exact Or.inl (by rw [List.flatten_cons]; exact List.mem_append_right _ h)
      · refine Or.inr ?_
        simp only [totalW_cons]
        omega

/-- The special case of `famMap_mem` where the transformation only ever uses fresh vertices. -/
theorem famMap_mem_block {F w} {L : List (List ℕ)} {b : ℕ}
    (hF : ∀ l ∈ L, ∀ b', ∀ v ∈ F l b', b' ≤ v ∧ v < b' + w l) :
    ∀ l' ∈ famMap F w L b, ∀ v ∈ l', b ≤ v ∧ v < b + totalW w L := by
  revert hF
  induction L generalizing b with
  | nil => intro _ l' hl'; simp at hl'
  | cons l L IH =>
    intro hF l' hl' v hv
    rw [famMap_cons, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · have := hF l (by simp) b v hv
      simp only [totalW_cons]
      omega
    · have := IH (b := b + w l) (fun x hx b' => hF x (List.mem_cons_of_mem _ hx) b') l' hl' v hv
      simp only [totalW_cons]
      omega

theorem VertDisjFam.tail {l : List ℕ} {L : List (List ℕ)} (h : VertDisjFam (l :: L)) :
    VertDisjFam L :=
  ⟨fun x hx => h.nodup x (List.mem_cons_of_mem _ hx),
    fun x hx => h.three x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.1 h.pdisj).2⟩

/-- If the source family is vertex-disjoint, so is the transformed family. -/
theorem famMap_vertDisj {F w} {L : List (List ℕ)} {b : ℕ} (hvd : VertDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b)
    (hF : ∀ l ∈ L, ∀ b', b ≤ b' → (F l b').Nodup ∧ 3 ≤ (F l b').length ∧
        ∀ v ∈ F l b', v ∈ l ∨ (b' ≤ v ∧ v < b' + w l)) :
    VertDisjFam (famMap F w L b) := by
  revert hvd hb hF
  induction L generalizing b with
  | nil => intro _ _ _; exact ⟨by simp, by simp, by simp⟩
  | cons l L IH =>
    intro hvd hb hF
    have hbwl : ∀ l' ∈ L, ∀ v ∈ l', v < b + w l := fun l' hl' v hv =>
      lt_of_lt_of_le (hb l' (List.mem_cons_of_mem _ hl') v hv) (Nat.le_add_right _ _)
    have hFtail : ∀ l' ∈ L, ∀ b', b + w l ≤ b' → (F l' b').Nodup ∧ 3 ≤ (F l' b').length ∧
        ∀ v ∈ F l' b', v ∈ l' ∨ (b' ≤ v ∧ v < b' + w l') := fun l' hl' b' hb' =>
      hF l' (List.mem_cons_of_mem _ hl') b' (le_trans (Nat.le_add_right _ _) hb')
    have hIH := IH (b := b + w l) hvd.tail hbwl hFtail
    have hmem : ∀ l'' ∈ famMap F w L (b + w l), ∀ v ∈ l'',
        v ∈ L.flatten ∨ (b + w l ≤ v ∧ v < b + w l + totalW w L) := by
      refine famMap_mem (F := F) (w := w) (L := L) (b := b + w l) ?_
      intro l' hl' b' hb' v hv
      exact (hF l' (List.mem_cons_of_mem _ hl') b'
        (le_trans (Nat.le_add_right _ _) hb')).2.2 v hv
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [famMap_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (hF l (by simp) b le_rfl).1
      · exact hIH.nodup x hx
    · intro x hx
      rw [famMap_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (hF l (by simp) b le_rfl).2.1
      · exact hIH.three x hx
    · rw [famMap_cons]
      refine List.pairwise_cons.2 ⟨?_, hIH.pdisj⟩
      intro l'' hl'' v hv hv2
      have h1 := (hF l (by simp) b le_rfl).2.2 v hv
      have h2 := hmem l'' hl'' v hv2
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 h2
          exact (List.pairwise_cons.1 hvd.pdisj).1 l₀ hl₀ v h1 hvl₀
        · have := hb l (by simp) v h1
          omega
      · rcases h2 with h2 | h2
        · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 h2
          have := hb l₀ (List.mem_cons_of_mem _ hl₀) v hvl₀
          omega
        · omega

theorem famMap_touches {F w} {L : List (List ℕ)} {b : ℕ}
    (hT : ∀ l ∈ L, ∀ b', b ≤ b' → Touches b' (cycEdges (F l b'))) :
    Touches b (cycFamEdges (famMap F w L b)) := by
  revert hT
  induction L generalizing b with
  | nil => intro _; simpa using Touches.empty b
  | cons l L IH =>
    intro hT
    rw [famMap_cons, cycFamEdges_cons]
    refine Touches.union (hT l (by simp) b le_rfl) ?_
    refine Touches.mono_le (Nat.le_add_right b (w l)) (IH ?_)
    intro l' hl' b' hb'
    exact hT l' (List.mem_cons_of_mem _ hl') b' (le_trans (Nat.le_add_right b _) hb')

/-- **Back-degeneracy of a transformed family.**  Each transformed cycle stays inside its own
block, and everything built later reaches above that block, so the back-neighbourhoods never
overlap and the bound `2` for a single cycle survives. -/
theorem famMap_natDegen {F w} {L : List (List ℕ)} {b : ℕ}
    (hT : ∀ l ∈ L, ∀ b', b ≤ b' → Touches b' (cycEdges (F l b')))
    (hB : ∀ l ∈ L, ∀ b', b ≤ b' → Below (b' + w l) (cycEdges (F l b')))
    (hnd : ∀ l ∈ L, ∀ b', b ≤ b' → (F l b').Nodup ∧ 3 ≤ (F l b').length) :
    NatDegen 2 (cycFamEdges (famMap F w L b)) := by
  revert hT hB hnd
  induction L generalizing b with
  | nil => intro _ _ _; simpa using natDegen_empty 2
  | cons l L IH =>
    intro hT hB hnd
    have hstep : ∀ (P : List ℕ → ℕ → Prop),
        (∀ l' ∈ l :: L, ∀ b', b ≤ b' → P l' b') → ∀ l' ∈ L, ∀ b', b + w l ≤ b' → P l' b' :=
      fun P hP l' hl' b' hb' =>
        hP l' (List.mem_cons_of_mem _ hl') b' (le_trans (Nat.le_add_right _ _) hb')
    rw [famMap_cons, cycFamEdges_cons]
    have hrest : NatDegen 2 (cycFamEdges (famMap F w L (b + w l))) :=
      IH (hstep _ hT) (hstep _ hB) (hstep _ hnd)
    have htouch : Touches (b + w l) (cycFamEdges (famMap F w L (b + w l))) :=
      famMap_touches (hstep _ hT)
    obtain ⟨hnd1, hnd2⟩ := hnd l (by simp) b le_rfl
    exact natDegen_union_split (natDegen_cycEdges hnd1 hnd2) hrest (hB l (by simp) b le_rfl) htouch

/-- The transformed family lives inside the union of the source cycles and the fresh blocks. -/
theorem famMap_supp {F w} {L : List (List ℕ)} {b : ℕ}
    (hF : ∀ l ∈ L, ∀ b', b ≤ b' → ∀ v ∈ F l b', v ∈ l ∨ (b' ≤ v ∧ v < b' + w l)) :
    ∀ v ∈ supp (cycFamEdges (famMap F w L b)),
      v ∈ L.flatten ∨ (b ≤ v ∧ v < b + totalW w L) := by
  intro v hv
  obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
  exact famMap_mem hF l' hl' v hvl'

/-! ### Composing the covers of a family -/

/-- **Family cover, height regime.**  The covered family `L` lives below `b` and every transformed
cycle reaches above its own base while staying inside its own block. -/
theorem famMap_covers_gen {F w} {L : List (List ℕ)} {b : ℕ} (hed : EdgeDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b)
    (hT : ∀ l ∈ L, ∀ b', b ≤ b' → Touches b' (cycEdges (F l b')))
    (hB : ∀ l ∈ L, ∀ b', b ≤ b' → Below (b' + w l) (cycEdges (F l b')))
    (hC : ∀ l ∈ L, ∀ b', b ≤ b' → Covers (cycEdges (F l b')) (cycEdges l)) :
    Covers (cycFamEdges (famMap F w L b)) (cycFamEdges L) := by
  revert hed hb hT hB hC
  induction L generalizing b with
  | nil => intro _ _ _ _ _; exact ⟨by simp, by simpa using triDecomp_empty⟩
  | cons l L IH =>
    intro hed hb hT hB hC
    have hmemL : ∀ l' ∈ L, ∀ b', b + w l ≤ b' → True := fun _ _ _ _ => trivial
    have hbtail : ∀ l' ∈ L, ∀ v ∈ l', v < b + w l := fun l' hl' v hv =>
      lt_of_lt_of_le (hb l' (List.mem_cons_of_mem _ hl') v hv) (Nat.le_add_right _ _)
    have hle : b ≤ b + w l := Nat.le_add_right _ _
    have hIH := IH (b := b + w l) hed.tail hbtail
      (fun l' hl' b' hb' => hT l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
      (fun l' hl' b' hb' => hB l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
      (fun l' hl' b' hb' => hC l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
    rw [famMap_cons, cycFamEdges_cons, cycFamEdges_cons]
    refine Covers.union (hC l (by simp) b le_rfl) hIH ?_
    -- disjointness of the head part from the tail part
    have hBl : Below b (cycEdges l) := by
      intro v hv
      exact hb l (by simp) v (List.mem_toFinset.1 (supp_cycEdges l hv))
    have hBL : Below b (cycFamEdges L) := by
      intro v hv
      obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
      exact hb l' (List.mem_cons_of_mem _ hl') v hvl'
    have hTtail : Touches (b + w l) (cycFamEdges (famMap F w L (b + w l))) := by
      refine famMap_touches ?_
      intro l' hl' b' hb'
      exact hT l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb')
    have hd1 : Disjoint (cycEdges (F l b)) (cycFamEdges (famMap F w L (b + w l))) :=
      (disjoint_of_touches_below hTtail (hB l (by simp) b le_rfl)).symm
    have hd2 : Disjoint (cycEdges (F l b)) (cycFamEdges L) :=
      disjoint_of_touches_below (hT l (by simp) b le_rfl) hBL
    have hd3 : Disjoint (cycEdges l) (cycFamEdges (famMap F w L (b + w l))) :=
      (disjoint_of_touches_below (hTtail.mono_le hle) hBl).symm
    have hd4 : Disjoint (cycEdges l) (cycFamEdges L) := hed.head_disjoint
    exact Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_right.2 ⟨hd1, hd2⟩, Finset.disjoint_union_right.2 ⟨hd3, hd4⟩⟩

/-- **Family cover, two transformations.**  Both families are built on the same blocks. -/
theorem famMap_covers_gen2 {F F' w} {L : List (List ℕ)} {b : ℕ}
    (hT : ∀ l ∈ L, ∀ b', b ≤ b' →
      Touches b' (cycEdges (F l b')) ∧ Touches b' (cycEdges (F' l b')))
    (hB : ∀ l ∈ L, ∀ b', b ≤ b' →
      Below (b' + w l) (cycEdges (F l b')) ∧ Below (b' + w l) (cycEdges (F' l b')))
    (hC : ∀ l ∈ L, ∀ b', b ≤ b' → Covers (cycEdges (F l b')) (cycEdges (F' l b'))) :
    Covers (cycFamEdges (famMap F w L b)) (cycFamEdges (famMap F' w L b)) := by
  revert hT hB hC
  induction L generalizing b with
  | nil => intro _ _ _; exact ⟨by simp, by simpa using triDecomp_empty⟩
  | cons l L IH =>
    intro hT hB hC
    have hle : b ≤ b + w l := Nat.le_add_right _ _
    have hIH := IH (b := b + w l)
      (fun l' hl' b' hb' => hT l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
      (fun l' hl' b' hb' => hB l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
      (fun l' hl' b' hb' => hC l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
    rw [famMap_cons, famMap_cons, cycFamEdges_cons, cycFamEdges_cons]
    refine Covers.union (hC l (by simp) b le_rfl) hIH ?_
    have hTtail : Touches (b + w l) (cycFamEdges (famMap F w L (b + w l))) := by
      refine famMap_touches ?_
      intro l' hl' b' hb'
      exact (hT l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb')).1
    have hTtail' : Touches (b + w l) (cycFamEdges (famMap F' w L (b + w l))) := by
      refine famMap_touches ?_
      intro l' hl' b' hb'
      exact (hT l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb')).2
    have hBhead := (hB l (by simp) b le_rfl).1
    have hBhead' := (hB l (by simp) b le_rfl).2
    exact Finset.disjoint_union_left.2
      ⟨Finset.disjoint_union_right.2
        ⟨(disjoint_of_touches_below hTtail hBhead).symm,
         (disjoint_of_touches_below hTtail' hBhead).symm⟩,
       Finset.disjoint_union_right.2
        ⟨(disjoint_of_touches_below hTtail hBhead').symm,
         (disjoint_of_touches_below hTtail' hBhead').symm⟩⟩

/-- **Family cover, vertex-disjoint regime.**  Used for the reduction step, where the covering
cycles may consist of chords inside the cycle they cover. -/
theorem famMap_covers_vd {F w} {L : List (List ℕ)} {b : ℕ} (hvd : VertDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b)
    (hloc : ∀ l ∈ L, ∀ b', b ≤ b' → ∀ v ∈ F l b', v ∈ l ∨ (b' ≤ v ∧ v < b' + w l))
    (hC : ∀ l ∈ L, ∀ b', b ≤ b' → Covers (cycEdges (F l b')) (cycEdges l)) :
    Covers (cycFamEdges (famMap F w L b)) (cycFamEdges L) := by
  revert hvd hb hloc hC
  induction L generalizing b with
  | nil => intro _ _ _ _; exact ⟨by simp, by simpa using triDecomp_empty⟩
  | cons l L IH =>
    intro hvd hb hloc hC
    have hle : b ≤ b + w l := Nat.le_add_right _ _
    have hbtail : ∀ l' ∈ L, ∀ v ∈ l', v < b + w l := fun l' hl' v hv =>
      lt_of_lt_of_le (hb l' (List.mem_cons_of_mem _ hl') v hv) (Nat.le_add_right _ _)
    have hIH := IH (b := b + w l) hvd.tail hbtail
      (fun l' hl' b' hb' => hloc l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
      (fun l' hl' b' hb' => hC l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb'))
    rw [famMap_cons, cycFamEdges_cons, cycFamEdges_cons]
    refine Covers.union (hC l (by simp) b le_rfl) hIH ?_
    -- locate the two sides
    have hloc1 : ∀ v ∈ supp (cycEdges (F l b) ∪ cycEdges l), v ∈ l ∨ (b ≤ v ∧ v < b + w l) := by
      intro v hv
      rw [supp_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact hloc l (by simp) b le_rfl v (List.mem_toFinset.1 (supp_cycEdges _ hv))
      · exact Or.inl (List.mem_toFinset.1 (supp_cycEdges _ hv))
    have hloc2 : ∀ v ∈ supp (cycFamEdges (famMap F w L (b + w l)) ∪ cycFamEdges L),
        v ∈ L.flatten ∨ b + w l ≤ v := by
      intro v hv
      rw [supp_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · have := famMap_supp (F := F) (w := w) (L := L) (b := b + w l)
          (fun l' hl' b' hb' => hloc l' (List.mem_cons_of_mem _ hl') b' (le_trans hle hb')) v hv
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
        exact Or.inl (List.mem_flatten.2 ⟨l', hl', hvl'⟩)
    refine disjoint_of_supp_disjoint ?_
    intro v hv1 hv2
    have h1 := hloc1 v hv1
    have h2 := hloc2 v hv2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 h2
        exact (List.pairwise_cons.1 hvd.pdisj).1 l₀ hl₀ v h1 hvl₀
      · have := hb l (by simp) v h1
        omega
    · rcases h2 with h2 | h2
      · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 h2
        have := hb l₀ (List.mem_cons_of_mem _ hl₀) v hvl₀
        omega
      · omega

/-! ### Subdivision of a single cycle onto a fresh block -/

theorem cycEdges_interleave_eq {a m : List ℕ} (hlen : a.length = m.length) (ha : a ≠ []) :
    ∃ z ∈ a, cycEdges (interleave a m) = pathEdges (interleave (a ++ [z]) m) := by
  cases a with
  | nil => exact absurd rfl ha
  | cons a0 a' =>
    refine ⟨a0, by simp, ?_⟩
    obtain ⟨R, hR⟩ : ∃ R, interleave (a0 :: a') m = a0 :: R := by
      cases m with
      | nil => exact ⟨[], rfl⟩
      | cons x t => exact ⟨x :: interleave a' t, rfl⟩
    have h1 : interleave (a0 :: a') m ++ [a0] = interleave ((a0 :: a') ++ [a0]) m :=
      interleave_append_last hlen a0
    rw [← h1, hR, cycEdges_cons]
    rfl

theorem mem_snd_of_mem_cycEdges_interleave {a m : List ℕ} (hlen : a.length = m.length)
    (ha : a ≠ []) {e : Sym2 ℕ} (he : e ∈ cycEdges (interleave a m)) : ∃ v ∈ e, v ∈ m := by
  obtain ⟨z, _, hz⟩ := cycEdges_interleave_eq hlen ha
  rw [hz] at he
  exact mem_snd_of_mem_pathEdges_interleave _ _ e he

theorem mem_fst_of_mem_cycEdges_interleave {a m : List ℕ} (hlen : a.length = m.length)
    (ha : a ≠ []) {e : Sym2 ℕ} (he : e ∈ cycEdges (interleave a m)) : ∃ v ∈ e, v ∈ a := by
  obtain ⟨z, hzmem, hz⟩ := cycEdges_interleave_eq hlen ha
  rw [hz] at he
  obtain ⟨v, hv, hva⟩ := mem_fst_of_mem_pathEdges_interleave _ _ e he
  rcases List.mem_append.1 hva with h | h
  · exact ⟨v, hv, h⟩
  · have : v = z := by simpa using h
    exact ⟨v, hv, this ▸ hzmem⟩

/-- Everything the two relocation covers need about a single cycle. -/
theorem subdiv_ok {l : List ℕ} {b b' : ℕ} (hnd : l.Nodup) (h3 : 3 ≤ l.length)
    (hb : ∀ v ∈ l, v < b) (hbb : b ≤ b') :
    Covers (cycEdges (interleave l (blk b' l.length))) (cycEdges l) ∧
    Covers (cycEdges (blk b' l.length)) (cycEdges (interleave l (blk b' l.length))) ∧
    Touches b' (cycEdges (interleave l (blk b' l.length))) ∧
    Below (b' + l.length) (cycEdges (interleave l (blk b' l.length))) ∧
    Dips b (cycEdges (interleave l (blk b' l.length))) ∧
    AllAbove b' (cycEdges (blk b' l.length)) ∧
    Below (b' + l.length) (cycEdges (blk b' l.length)) := by
  have hlne : l ≠ [] := by rintro rfl; simp at h3
  have hlen : l.length = (blk b' l.length).length := by simp
  have hndapp : (l ++ blk b' l.length).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, blk_nodup _ _, ?_⟩
    intro x hx y hy
    have h1 := hb x hx
    have h2 := (mem_blk.1 hy).1
    omega
  have hcov1 := (subdiv_cyc hlen h3 hndapp).symm
  have hcov2 := subdiv_cyc' hlen h3 hndapp
  refine ⟨hcov1, hcov2, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨v, hv, hvm⟩ := mem_snd_of_mem_cycEdges_interleave hlen hlne he
    exact ⟨v, hv, (mem_blk.1 hvm).1⟩
  · intro v hv
    have := List.mem_toFinset.1 (supp_cycEdges _ hv)
    rcases mem_interleave this with h | h
    · have := hb v h; omega
    · exact (mem_blk.1 h).2
  · intro e he
    obtain ⟨v, hv, hvl⟩ := mem_fst_of_mem_cycEdges_interleave hlen hlne he
    exact ⟨v, hv, hb v hvl⟩
  · intro v hv
    exact (mem_blk.1 (List.mem_toFinset.1 (supp_cycEdges _ hv))).1
  · intro v hv
    exact (mem_blk.1 (List.mem_toFinset.1 (supp_cycEdges _ hv))).2

/-! ### Relocation -/

/-- Subdivide each cycle, using a private block of fresh vertices for the new vertices. -/
def subdivFam (L : List (List ℕ)) (b : ℕ) : List (List ℕ) :=
  famMap (fun l b' => interleave l (blk b' l.length)) List.length L b

/-- The fresh copies of the cycles: the blocks themselves. -/
def freshFam (L : List (List ℕ)) (b : ℕ) : List (List ℕ) :=
  famMap (fun l b' => blk b' l.length) List.length L b

/-- **Relocation, first half.**  The subdivision covers the family. -/
theorem covers_subdivFam {L : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b) :
    Covers (cycFamEdges (subdivFam L b)) (cycFamEdges L) := by
  refine famMap_covers_gen h hb ?_ ?_ ?_
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.2.1
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.2.2.1
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').1

/-- **Relocation, second half.**  The fresh copies cover the subdivision. -/
theorem covers_freshFam {L : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b) :
    Covers (cycFamEdges (freshFam L b)) (cycFamEdges (subdivFam L b)) := by
  refine famMap_covers_gen2 (w := List.length) ?_ ?_ ?_
  · intro l hl b' hb'
    obtain ⟨-, -, hT, -, -, hA, -⟩ := subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb'
    exact ⟨hA.touches, hT⟩
  · intro l hl b' hb'
    obtain ⟨-, -, -, hB, -, -, hB'⟩ := subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb'
    exact ⟨hB', hB⟩
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.1

/-- The subdivision of a family living below `b` lives below `b + totalLen G`. -/
theorem subdivFam_below {L : List (List ℕ)} {b : ℕ} (hb : ∀ l ∈ L, ∀ v ∈ l, v < b) :
    Below (b + totalLen L) (cycFamEdges (subdivFam L b)) := by
  intro v hv
  have hloc : ∀ l ∈ L, ∀ b', b ≤ b' → ∀ v ∈ interleave l (blk b' l.length),
      v ∈ l ∨ (b' ≤ v ∧ v < b' + l.length) := by
    intro l _ b' _ v hv'
    rcases mem_interleave hv' with hx | hx
    · exact Or.inl hx
    · exact Or.inr (mem_blk.1 hx)
  have := famMap_supp (F := fun l b' => interleave l (blk b' l.length)) (w := List.length)
    (L := L) (b := b) hloc v hv
  have hw : totalW List.length L = totalLen L := rfl
  rcases this with hx | hx
  · obtain ⟨l, hl, hvl⟩ := List.mem_flatten.1 hx
    have := hb l hl v hvl
    omega
  · omega

/-- **The subdivision is `2`-degenerate.**  Every subdivision vertex has exactly its two original
neighbours below it, and the blocks are laid out in increasing order. -/
theorem natDegen_subdivFam {L : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b) : NatDegen 2 (cycFamEdges (subdivFam L b)) := by
  refine famMap_natDegen ?_ ?_ ?_
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.2.1
  · intro l hl b' hb'
    exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.2.2.1
  · intro l hl b' hb'
    have hlen : l.length = (blk b' l.length).length := by simp
    have h3 := h.three l hl
    refine ⟨interleave_nodup ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨h.nodup l hl, blk_nodup _ _, ?_⟩
      intro x hx y hy
      have h1 := hb l hl x hx
      have h2 := (mem_blk.1 hy).1
      omega
    · rw [interleave_length hlen]
      omega

/-- Every edge of the subdivision has an endpoint below `b`. -/
theorem subdivFam_dips {L : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam L)
    (hb : ∀ l ∈ L, ∀ v ∈ l, v < b) : Dips b (cycFamEdges (subdivFam L b)) := by
  have key : ∀ (M : List (List ℕ)) (c : ℕ), (∀ l ∈ M, l.Nodup) → (∀ l ∈ M, 3 ≤ l.length) →
      (∀ l ∈ M, ∀ v ∈ l, v < b) → b ≤ c →
      Dips b (cycFamEdges (famMap (fun l b' => interleave l (blk b' l.length)) List.length M c)) := by
    intro M
    induction M with
    | nil => intro c _ _ _ _ e he; simp at he
    | cons l M IH =>
      intro c hnd h3 hbM hbc
      rw [famMap_cons, cycFamEdges_cons]
      intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact (subdiv_ok (hnd l (by simp)) (h3 l (by simp)) (hbM l (by simp)) hbc).2.2.2.2.1 e he
      · exact IH (c + l.length) (fun x hx => hnd x (List.mem_cons_of_mem _ hx))
          (fun x hx => h3 x (List.mem_cons_of_mem _ hx))
          (fun x hx => hbM x (List.mem_cons_of_mem _ hx)) (by omega) e he
  exact key L b h.nodup h.three hb le_rfl

theorem freshFam_vertDisj {L : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam L) :
    VertDisjFam (freshFam L b) := by
  have key : ∀ (M : List (List ℕ)) (c : ℕ), (∀ l ∈ M, 3 ≤ l.length) →
      VertDisjFam (famMap (fun l b' => blk b' l.length) List.length M c) := by
    intro M
    induction M with
    | nil => intro c _; exact ⟨by simp, by simp, by simp⟩
    | cons l M IH =>
      intro c h3
      have hIH := IH (c + l.length) (fun x hx => h3 x (List.mem_cons_of_mem _ hx))
      have hmem : ∀ l'' ∈ famMap (fun l b' => blk b' l.length) List.length M (c + l.length),
          ∀ v ∈ l'', c + l.length ≤ v := by
        intro l'' hl'' v hv
        exact (famMap_mem_block (F := fun l b' => blk b' l.length) (w := List.length) (L := M)
          (b := c + l.length) (fun x _ b' v hv => mem_blk.1 hv) l'' hl'' v hv).1
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [famMap_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact blk_nodup _ _
        · exact hIH.nodup x hx
      · intro x hx
        rw [famMap_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using h3 l (by simp)
        · exact hIH.three x hx
      · rw [famMap_cons]
        refine List.pairwise_cons.2 ⟨?_, hIH.pdisj⟩
        intro l'' hl'' v hv hv2
        have h1 := (mem_blk.1 hv).2
        have h2 := hmem l'' hl'' v hv2
        omega
  exact key L b h.three

theorem freshFam_mem {L : List (List ℕ)} {b : ℕ} :
    ∀ l' ∈ freshFam L b, ∀ v ∈ l', b ≤ v ∧ v < b + totalLen L := by
  intro l' hl' v hv
  have h := famMap_mem_block (F := fun l b' => blk b' l.length) (w := List.length) (L := L)
    (b := b) (fun x _ b' v hv => mem_blk.1 hv) l' hl' v hv
  have he : totalW List.length L = totalLen L := rfl
  refine ⟨h.1, ?_⟩
  omega

@[simp] theorem freshFam_nil (b : ℕ) : freshFam [] b = [] := rfl

theorem freshFam_cons (l : List ℕ) (L : List (List ℕ)) (b : ℕ) :
    freshFam (l :: L) b = blk b l.length :: freshFam L (b + l.length) := rfl

theorem freshFam_forall₂ (L : List (List ℕ)) (b : ℕ) :
    List.Forall₂ (fun l l' => l'.length = l.length) L (freshFam L b) := by
  refine famMap_forall₂ (b := b) ?_
  intro l _ b' _
  simp

/-! ### The relocation bridge

Everything the recursion does to a family `G` living below `b` starts by *relocating* `G` onto the
fresh block `[b, b + totalLen G)`, via the two covers `covers_subdivFam` and `covers_freshFam`.
The bridge below says: an absorber of the relocated family that uses no vertex below `b` yields an
absorber of `G` itself, satisfying the recursion's contract. -/

theorem mem_supp_cycFamEdges {L : List (List ℕ)} {l : List ℕ} (hl : l ∈ L) (h2 : 2 ≤ l.length)
    {v : ℕ} (hv : v ∈ l) : v ∈ supp (cycFamEdges L) := by
  induction L with
  | nil => simp at hl
  | cons l' L IH =>
    rw [cycFamEdges_cons, supp_union, Finset.mem_union]
    rcases List.mem_cons.1 hl with rfl | hl'
    · exact Or.inl (mem_supp_cycEdges h2 hv)
    · exact Or.inr (IH hl')

theorem allAbove_freshFam {G : List (List ℕ)} {b : ℕ} :
    AllAbove b (cycFamEdges (freshFam G b)) := by
  intro v hv
  obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
  exact (freshFam_mem l' hl' v hvl').1

theorem touches_subdivFam {G : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam G)
    (hb : ∀ l ∈ G, ∀ v ∈ l, v < b) : Touches b (cycFamEdges (subdivFam G b)) := by
  refine famMap_touches ?_
  intro l hl b' hb'
  exact (subdiv_ok (h.nodup l hl) (h.three l hl) (hb l hl) hb').2.2.1

theorem hasAbs_relocate {G : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam G)
    (hb : ∀ l ∈ G, ∀ v ∈ l, v < b)
    (hA : ∃ A, IsAbsorber A (cycFamEdges (freshFam G b)) ∧ AllAbove b A ∧
      NatDegen 9 (cycFamEdges (freshFam G b) ∪ A) ∧
      ∀ v, v < b + totalLen G → (backNbrs (cycFamEdges (freshFam G b) ∪ A) v).card ≤ 7) :
    HasAbs b (cycFamEdges G) := by
  obtain ⟨A, hAabs, hAab, hAdeg, hAdeg7⟩ := hA
  have hSC : Covers (cycFamEdges (subdivFam G b)) (cycFamEdges G) := covers_subdivFam h hb
  have hTS : Covers (cycFamEdges (freshFam G b)) (cycFamEdges (subdivFam G b)) :=
    covers_freshFam h hb
  have hAS : Disjoint A (cycFamEdges (subdivFam G b)) :=
    disjoint_of_allAbove_dips hAab (subdivFam_dips h hb)
  have habsS : IsAbsorber (cycFamEdges (freshFam G b) ∪ A) (cycFamEdges (subdivFam G b)) :=
    isAbsorber_of_covers hTS hAabs hAS
  have hAllT : AllAbove b (cycFamEdges (freshFam G b)) := allAbove_freshFam
  have hBC : Below b (cycFamEdges G) := by
    intro v hv
    obtain ⟨l, hl, hvl⟩ := supp_cycFamEdges_mem hv
    exact hb l hl v hvl
  have hTA : Touches b (cycFamEdges (freshFam G b) ∪ A) :=
    Touches.union hAllT.touches hAab.touches
  have habsC : IsAbsorber (cycFamEdges (subdivFam G b) ∪ (cycFamEdges (freshFam G b) ∪ A))
      (cycFamEdges G) :=
    isAbsorber_of_covers hSC habsS (disjoint_of_touches_below hTA hBC)
  refine ⟨_, habsC, Touches.union (touches_subdivFam h hb) hTA, ?_, ?_⟩
  swap
  · intro v
    refine le_trans (card_backNbrs_union_le _ _ v) ?_
    rcases Nat.lt_or_ge v (b + totalLen G) with hv | hv
    · have h1 := natDegen_subdivFam h hb v
      have h2 := hAdeg7 v hv
      omega
    · have h1 : backNbrs (cycFamEdges (subdivFam G b)) v = ∅ :=
        backNbrs_eq_empty_of_below (subdivFam_below hb) hv
      have h2 := hAdeg v
      rw [h1]
      simpa using h2
  intro v hv
  rw [supp_union, Finset.mem_union] at hv
  rcases hv with hv | hv
  · have hloc : ∀ l ∈ G, ∀ b', b ≤ b' → ∀ v ∈ interleave l (blk b' l.length),
        v ∈ l ∨ (b' ≤ v ∧ v < b' + l.length) := by
      intro l _ b' _ v hv'
      rcases mem_interleave hv' with hx | hx
      · exact Or.inl hx
      · exact Or.inr (mem_blk.1 hx)
    have := famMap_supp (F := fun l b' => interleave l (blk b' l.length)) (w := List.length)
      (L := G) (b := b) hloc v hv
    rcases this with hx | hx
    · obtain ⟨l, hl, hvl⟩ := List.mem_flatten.1 hx
      exact Or.inl (mem_supp_cycFamEdges hl (by have := h.three l hl; omega) hvl)
    · exact Or.inr hx.1
  · rw [supp_union, Finset.mem_union] at hv
    rcases hv with hv | hv
    · exact Or.inr (hAllT v hv)
    · exact Or.inr (hAab v hv)

/-! ### The reduction move -/

/-- One reduction move on a single cycle of length `≥ 4`, using at most two fresh vertices from
`b`: halve an even cycle, use the fresh vertex `b` for an odd cycle, and turn a `4`-cycle into a
`5`-cycle through `b` and `b+1`. -/
def reduceCyc : List ℕ → ℕ → List ℕ
  | [a, _, c, d], b => [a, c, b, d, b + 1]
  | l, b => if l.length % 2 = 0 then evensL l else evensL l ++ [b]

/-- **The reduction move.** -/
theorem reduceCyc_spec {l : List ℕ} {b : ℕ} (hnd : l.Nodup) (h4 : 4 ≤ l.length)
    (hb : ∀ v ∈ l, v < b) :
    (reduceCyc l b).Nodup ∧ 3 ≤ (reduceCyc l b).length ∧
      (∀ v ∈ reduceCyc l b, v ∈ l ∨ (b ≤ v ∧ v < b + 2)) ∧
      3 ∣ l.length + (reduceCyc l b).length ∧
      (l.length ≤ 5 → (reduceCyc l b).length ≤ 5) ∧
      (6 ≤ l.length → (reduceCyc l b).length < l.length) ∧
      Covers (cycEdges (reduceCyc l b)) (cycEdges l) := by
  match l, h4 with
  | a :: x :: c :: d :: rest, _ =>
    match rest with
    | [] =>
      -- the `4 → 5` move
      have ha := hb a (by simp)
      have hx := hb x (by simp)
      have hc := hb c (by simp)
      have hd := hb d (by simp)
      have hbn : b ∉ ([a, x, c, d] : List ℕ) := by
        intro hmem
        have := hb b hmem
        omega
      have hbn' : b + 1 ∉ ([a, x, c, d] : List ℕ) := by
        intro hmem
        have := hb (b + 1) hmem
        omega
      have hred : reduceCyc [a, x, c, d] b = [a, c, b, d, b + 1] := rfl
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at hnd
      obtain ⟨⟨hax, hac, had⟩, ⟨hxc, hxd⟩, hcd⟩ := hnd
      have hndl : ([a, x, c, d] : List ℕ).Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true]
        exact ⟨⟨hax, hac, had⟩, ⟨hxc, hxd⟩, hcd⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hred]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, and_true]
        refine ⟨⟨hac, ?_, had, ?_⟩, ⟨?_, hcd.1, ?_⟩, ⟨?_, ?_⟩, ?_, not_false⟩ <;> omega
      · rw [hred]; simp
      · rw [hred]
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inl (by simp)
        · exact Or.inr (by omega)
        · exact Or.inl (by simp)
        · exact Or.inr (by omega)
      · rw [hred]; simp
      · rw [hred]; simp
      · rw [hred]; simp
      · rw [hred]
        exact covers_four_expl hndl hbn hbn' (by omega)
    | e :: rest' =>
      set l : List ℕ := a :: x :: c :: d :: e :: rest' with hl
      have h5 : 5 ≤ l.length := by simp [hl]
      have hred : reduceCyc l b = if l.length % 2 = 0 then evensL l else evensL l ++ [b] := rfl
      have hevlen := evensL_length l
      by_cases hpar : l.length % 2 = 0
      · obtain ⟨k, hk⟩ : ∃ k, l.length = 2 * k := ⟨l.length / 2, by omega⟩
        have hk3 : 3 ≤ k := by omega
        have hlen' : (evensL l).length = k := by omega
        rw [hred, if_pos hpar]
        refine ⟨evensL_nodup hnd, by omega, ?_, by omega, by omega, by omega,
          covers_even hnd hk hk3⟩
        intro v hv
        exact Or.inl (evensL_subset hv)
      · obtain ⟨k, hk⟩ : ∃ k, l.length = 2 * k + 1 := ⟨l.length / 2, by omega⟩
        have hk2 : 2 ≤ k := by omega
        have hlen' : (evensL l).length = k + 1 := by omega
        have hbl : b ∉ l := by
          intro hmem
          have := hb b hmem
          omega
        rw [hred, if_neg hpar]
        have hndapp : (evensL l ++ [b]).Nodup := by
          rw [List.nodup_append]
          refine ⟨evensL_nodup hnd, by simp, ?_⟩
          intro p hp q hq
          have hq' : q = b := by simpa using hq
          subst hq'
          intro hpq
          exact hbl (hpq ▸ evensL_subset hp)
        refine ⟨hndapp, by simp; omega, ?_, ?_, ?_, ?_, covers_odd hnd hbl hk hk2⟩
        · intro v hv
          rcases List.mem_append.1 hv with h | h
          · exact Or.inl (evensL_subset h)
          · have : v = b := by simpa using h
            exact Or.inr (by omega)
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro hle
          simp only [List.length_append, List.length_singleton]
          omega
        · intro hge
          simp only [List.length_append, List.length_singleton]
          omega

/-- Apply the reduction move to every cycle of a family. -/
def reduceFam (L : List (List ℕ)) (b : ℕ) : List (List ℕ) := famMap reduceCyc (fun _ => 2) L b

/-! ### The terminal groups -/

/-- **The terminal case.**  A group of at most three cycles, each of length `4` or `5`, whose total
length is divisible by `3`, is `C₄ ⊎ C₅`, `3 · C₄` or `3 · C₅`; each is absorbed by an explicit
gadget placed on the relocated (hence fresh) copy of the group. -/
theorem terminal_group {G : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam G)
    (hb : ∀ l ∈ G, ∀ v ∈ l, v < b) (hlen : ∀ l ∈ G, l.length = 4 ∨ l.length = 5)
    (h3 : G.length ≤ 3) (hdvd : 3 ∣ totalLen G) : HasAbs b (cycFamEdges G) := by
  refine hasAbs_relocate h hb ?_
  rcases G with _ | ⟨l₁, _ | ⟨l₂, _ | ⟨l₃, _ | ⟨l₄, t⟩⟩⟩⟩
  · refine ⟨∅, by simpa using isAbsorber_empty, by simp [AllAbove], ?_, ?_⟩
    · simpa using natDegen_empty 9
    · intro v _
      simp [backNbrs]
  · exfalso
    have h1 := hlen l₁ (by simp)
    simp only [totalLen_cons, totalLen_nil] at hdvd
    omega
  · -- two cycles: `C₄ ⊎ C₅`
    have h1 := hlen l₁ (by simp)
    have h2 := hlen l₂ (by simp)
    simp only [totalLen_cons, totalLen_nil] at hdvd
    rw [freshFam_cons, freshFam_cons, freshFam_nil, cycFamEdges_cons, cycFamEdges_cons,
      cycFamEdges_nil, Finset.union_empty]
    rcases h1 with e1 | e1
    · rcases h2 with e2 | e2
      · exfalso; omega
      · rw [e1, e2]
        obtain ⟨A, hA, hsupp, hdeg⟩ := gadget_45_blk b
        exact ⟨A, hA, hsupp, hdeg.mono (by omega), fun v _ => hdeg v⟩
    rcases h2 with e2 | e2
    · rw [e1, e2]
      obtain ⟨A, hA, hsupp, hdeg⟩ := gadget_54_blk b
      exact ⟨A, hA, hsupp, hdeg.mono (by omega), fun v _ => hdeg v⟩
    · exfalso; omega
  · -- three cycles: `3 · C₄` or `3 · C₅`
    have h1 := hlen l₁ (by simp)
    have h2 := hlen l₂ (by simp)
    have h3' := hlen l₃ (by simp)
    simp only [totalLen_cons, totalLen_nil] at hdvd
    rw [freshFam_cons, freshFam_cons, freshFam_cons, freshFam_nil, cycFamEdges_cons,
      cycFamEdges_cons, cycFamEdges_cons, cycFamEdges_nil, Finset.union_empty]
    have hall : (l₁.length = 4 ∧ l₂.length = 4 ∧ l₃.length = 4) ∨
        (l₁.length = 5 ∧ l₂.length = 5 ∧ l₃.length = 5) := by
      rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rcases h3' with e3 | e3 <;> omega
    rcases hall with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · rw [e1, e2, e3, show b + 4 + 4 = b + 8 from by omega]
      obtain ⟨A, hA, hsupp, hdeg⟩ := gadget_444_blk b
      exact ⟨A, hA, hsupp, hdeg.mono (by omega), fun v _ => hdeg v⟩
    · rw [e1, e2, e3, show b + 5 + 5 = b + 10 from by omega]
      obtain ⟨A, hA, hsupp, hdeg⟩ := gadget_555_blk b
      exact ⟨A, hA, hsupp, hdeg.mono (by omega), fun v _ => hdeg v⟩
  · exfalso; simp at h3; omega

/-! ### One reduction round -/

theorem forall₂_mem_right {R : List ℕ → List ℕ → Prop} {L M : List (List ℕ)}
    (h : List.Forall₂ R L M) : ∀ y ∈ M, ∃ x ∈ L, R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | @cons a b l₁ l₂ hr _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact ⟨a, by simp, hr⟩
    · obtain ⟨x, hx, hr'⟩ := ih y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hr'⟩

theorem forall₂_comp {P Q R : List ℕ → List ℕ → Prop} {A B C : List (List ℕ)}
    (h1 : List.Forall₂ P A B) (h2 : List.Forall₂ Q B C)
    (hR : ∀ x y z, P x y → Q y z → R x z) : List.Forall₂ R A C := by
  revert C
  induction h1 with
  | nil => intro C h2; cases h2; exact List.Forall₂.nil
  | @cons a b l₁ l₂ hp _ ih =>
    intro C h2
    cases h2 with
    | cons hq ht2 => exact List.Forall₂.cons (hR _ _ _ hp hq) (ih ht2)

/-- **One round.**  A group of cycles of length `≥ 4` living below `b` is relocated onto fresh
vertices and then reduced: every cycle of length `≥ 6` gets strictly shorter, `4` and `5` swap, and
an absorber of the new family (living below `b'`) yields one of the old. -/
theorem round_reduce {G : List (List ℕ)} {b : ℕ} (h : EdgeDisjFam G)
    (hb : ∀ l ∈ G, ∀ v ∈ l, v < b) (h4 : ∀ l ∈ G, 4 ≤ l.length) :
    ∃ (G' : List (List ℕ)) (b' : ℕ), b ≤ b' ∧ VertDisjFam G' ∧
      (∀ l ∈ G', ∀ v ∈ l, b ≤ v ∧ v < b') ∧
      List.Forall₂ (fun l l' => 3 ∣ l.length + l'.length ∧
        (l.length ≤ 5 → l'.length ≤ 5) ∧ (6 ≤ l.length → l'.length < l.length)) G G' ∧
      (HasAbs b' (cycFamEdges G') → HasAbs b (cycFamEdges G)) := by
  have hFvd : VertDisjFam (freshFam G b) := freshFam_vertDisj h
  have hFmem : ∀ l ∈ freshFam G b, ∀ v ∈ l, b ≤ v ∧ v < b + totalLen G :=
    fun l hl v hv => freshFam_mem l hl v hv
  have hFb : ∀ l ∈ freshFam G b, ∀ v ∈ l, v < b + totalLen G :=
    fun l hl v hv => (hFmem l hl v hv).2
  have hFlen : List.Forall₂ (fun l l' => l'.length = l.length) G (freshFam G b) :=
    freshFam_forall₂ G b
  have hF4 : ∀ l' ∈ freshFam G b, 4 ≤ l'.length := by
    intro l' hl'
    obtain ⟨x, hx, hr⟩ := forall₂_mem_right hFlen l' hl'
    rw [hr]
    exact h4 x hx
  have hspec : ∀ l ∈ freshFam G b, ∀ b', b + totalLen G ≤ b' →
      (reduceCyc l b').Nodup ∧ 3 ≤ (reduceCyc l b').length ∧
      (∀ v ∈ reduceCyc l b', v ∈ l ∨ (b' ≤ v ∧ v < b' + 2)) ∧
      3 ∣ l.length + (reduceCyc l b').length ∧
      (l.length ≤ 5 → (reduceCyc l b').length ≤ 5) ∧
      (6 ≤ l.length → (reduceCyc l b').length < l.length) ∧
      Covers (cycEdges (reduceCyc l b')) (cycEdges l) := by
    intro l hl b' hb'
    exact reduceCyc_spec (hFvd.nodup l hl) (hF4 l hl)
      (fun v hv => lt_of_lt_of_le (hFb l hl v hv) hb')
  have hRvd : VertDisjFam (reduceFam (freshFam G b) (b + totalLen G)) := by
    refine famMap_vertDisj hFvd hFb ?_
    intro l hl b' hb'
    exact ⟨(hspec l hl b' hb').1, (hspec l hl b' hb').2.1, (hspec l hl b' hb').2.2.1⟩
  have hRebelow : Below (b + totalLen G + totalW (fun _ => 2) (freshFam G b))
      (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G))) := by
    intro v hv
    obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
    have hmem := famMap_mem (F := reduceCyc) (w := fun _ => 2) (L := freshFam G b)
      (b := b + totalLen G) (fun l hl b' hb' => (hspec l hl b' hb').2.2.1) l' hl' v hvl'
    have hz : 0 ≤ totalW (fun _ => 2) (freshFam G b) := Nat.zero_le _
    rcases hmem with hx | hx
    · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 hx
      have := (hFmem l₀ hl₀ v hvl₀).2
      omega
    · omega
  refine ⟨reduceFam (freshFam G b) (b + totalLen G),
    b + totalLen G + totalW (fun _ => 2) (freshFam G b), by omega, hRvd, ?_, ?_, ?_⟩
  · intro l' hl' v hv
    have hmem := famMap_mem (F := reduceCyc) (w := fun _ => 2) (L := freshFam G b)
      (b := b + totalLen G) (fun l hl b' hb' => (hspec l hl b' hb').2.2.1) l' hl' v hv
    rcases hmem with hx | hx
    · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 hx
      have := hFmem l₀ hl₀ v hvl₀
      omega
    · omega
  · have hQ : List.Forall₂ (fun l l' => 3 ∣ l.length + l'.length ∧
        (l.length ≤ 5 → l'.length ≤ 5) ∧ (6 ≤ l.length → l'.length < l.length))
        (freshFam G b) (reduceFam (freshFam G b) (b + totalLen G)) := by
      refine famMap_forall₂ (b := b + totalLen G) ?_
      intro l hl b' hb'
      exact ⟨(hspec l hl b' hb').2.2.2.1, (hspec l hl b' hb').2.2.2.2.1,
        (hspec l hl b' hb').2.2.2.2.2.1⟩
    refine forall₂_comp hFlen hQ ?_
    intro x y z hxy hyz
    rw [hxy] at hyz
    exact hyz
  · rintro ⟨A, hAabs, hAt, hAs, hAn⟩
    have hG'above : ∀ v ∈ supp (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G))),
        b ≤ v := by
      intro v hv
      obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
      have hmem := famMap_mem (F := reduceCyc) (w := fun _ => 2) (L := freshFam G b)
        (b := b + totalLen G) (fun l hl b' hb' => (hspec l hl b' hb').2.2.1) l' hl' v hvl'
      rcases hmem with hx | hx
      · obtain ⟨l₀, hl₀, hvl₀⟩ := List.mem_flatten.1 hx
        exact (hFmem l₀ hl₀ v hvl₀).1
      · omega
    have hcov : Covers (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G)))
        (cycFamEdges (freshFam G b)) := by
      refine famMap_covers_vd hFvd hFb (fun l hl b' hb' => (hspec l hl b' hb').2.2.1) ?_
      intro l hl b' hb'
      exact (hspec l hl b' hb').2.2.2.2.2.2
    have hFbelow : Below (b + totalLen G + totalW (fun _ => 2) (freshFam G b))
        (cycFamEdges (freshFam G b)) := by
      intro v hv
      obtain ⟨l', hl', hvl'⟩ := supp_cycFamEdges_mem hv
      have := (hFmem l' hl' v hvl').2
      omega
    have habs : IsAbsorber (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G)) ∪ A)
        (cycFamEdges (freshFam G b)) :=
      isAbsorber_of_covers hcov hAabs (disjoint_of_touches_below hAt hFbelow)
    have hbound : ∀ v, (backNbrs (cycFamEdges (freshFam G b) ∪
        (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G)) ∪ A)) v).card ≤
        (backNbrs (cycFamEdges (freshFam G b)) v).card +
        ((backNbrs (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G))) v).card +
          (backNbrs A v).card) := by
      intro v
      exact le_trans (card_backNbrs_union_le _ _ v)
        (Nat.add_le_add_left (card_backNbrs_union_le _ _ v) _)
    have hFe2 : NatDegen 2 (cycFamEdges (freshFam G b)) :=
      natDegen_cycFamEdges_vertDisj hFvd
    have hRe2 : NatDegen 2 (cycFamEdges (reduceFam (freshFam G b) (b + totalLen G))) :=
      natDegen_cycFamEdges_vertDisj hRvd
    refine hasAbs_relocate h hb ⟨_, habs, ?_, ?_, ?_⟩
    · intro v hv
      rw [supp_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact hG'above v hv
      · rcases hAs v hv with hx | hx
        · exact hG'above v hx
        · omega
    · intro v
      have hb1 := hbound v
      have h1 := hFe2 v
      have h2 := hRe2 v
      rcases Nat.lt_or_ge v (b + totalLen G + totalW (fun _ => 2) (freshFam G b)) with hv | hv
      · have h3 : (backNbrs A v).card = 0 := by
          rw [backNbrs_eq_empty_of_touches hAt hv]; simp
        omega
      · have h1' : (backNbrs (cycFamEdges (freshFam G b)) v).card = 0 := by
          rw [backNbrs_eq_empty_of_below hFbelow hv]; simp
        have h2' : (backNbrs (cycFamEdges
            (reduceFam (freshFam G b) (b + totalLen G))) v).card = 0 := by
          rw [backNbrs_eq_empty_of_below hRebelow hv]; simp
        have h3 := hAn v
        omega
    · intro v hv
      have hb1 := hbound v
      have h1 := hFe2 v
      have h2 := hRe2 v
      have hz : 0 ≤ totalW (fun _ => 2) (freshFam G b) := Nat.zero_le _
      have h3 : (backNbrs A v).card = 0 := by
        rw [backNbrs_eq_empty_of_touches hAt (by omega)]; simp
      omega

end BKLO
