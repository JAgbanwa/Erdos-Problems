/-
# Even graphs are `F₂`-sums of triangles

For the parity arguments of BKLO §9 the relevant algebraic fact is that the parity functional
`E ↦ (d_E(x, W) mod 2)` is additive over symmetric differences of edge sets, and that **every**
loopless even-degree graph on a vertex set `S` is a symmetric difference of triangles with vertices
in `S` (`BKLO.even_graph_triSum`).  Together these reduce the construction of a parity graph to the
task of realising the parity vector of a *single* triangle on `S`.

Everything here is `sorry`-free.
-/
import BKLO.ParityTools
import Mathlib.Algebra.Field.ZMod

open Finset

namespace BKLO

variable {V : Type*} [DecidableEq V]

/-! ### Parity is additive over symmetric differences -/

theorem card_symmDiff_zmod (s t : Finset V) :
    ((symmDiff s t).card : ZMod 2) = (s.card : ZMod 2) + (t.card : ZMod 2) := by
  classical
  have hsd : symmDiff s t = (s \ t) ∪ (t \ s) := rfl
  have hdisj : Disjoint (s \ t) (t \ s) :=
    Finset.disjoint_left.2 fun a ha ha' => (Finset.mem_sdiff.1 ha).2 (Finset.mem_sdiff.1 ha').1
  have h1 : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
    rw [hsd, Finset.card_union_of_disjoint hdisj]
  have h2 : (s \ t).card + (s ∩ t).card = s.card := Finset.card_sdiff_add_card_inter s t
  have h3 : (t \ s).card + (t ∩ s).card = t.card := Finset.card_sdiff_add_card_inter t s
  have h4 : t ∩ s = s ∩ t := Finset.inter_comm t s
  rw [h4] at h3
  have h5 : (s.card : ZMod 2) + (t.card : ZMod 2)
      = ((s \ t).card : ZMod 2) + ((t \ s).card : ZMod 2)
        + 2 * ((s ∩ t).card : ZMod 2) := by
    rw [← h2, ← h3]
    push_cast
    ring
  have h6 : (2 : ZMod 2) = 0 := by decide +kernel
  rw [h1]
  push_cast
  rw [h5, h6]
  ring

theorem nbhdIn_symmDiff (A B : Finset (Sym2 V)) (x : V) (W : Finset V) :
    nbhdIn (symmDiff A B) x W = symmDiff (nbhdIn A x W) (nbhdIn B x W) := by
  ext y
  simp only [mem_nbhdIn, Finset.mem_symmDiff]
  tauto

/-- The parity of `d_E(x, W)` is additive over symmetric differences of edge sets. -/
theorem degTo_symmDiff_zmod (A B : Finset (Sym2 V)) (x : V) (W : Finset V) :
    ((degTo (symmDiff A B) x W : ℕ) : ZMod 2)
      = ((degTo A x W : ℕ) : ZMod 2) + ((degTo B x W : ℕ) : ZMod 2) := by
  rw [degTo, nbhdIn_symmDiff, card_symmDiff_zmod]
  rfl

theorem edeg_symmDiff_zmod (A B : Finset (Sym2 V)) (v : V) :
    ((edeg (symmDiff A B) v : ℕ) : ZMod 2)
      = ((edeg A v : ℕ) : ZMod 2) + ((edeg B v : ℕ) : ZMod 2) := by
  classical
  have hfil : (symmDiff A B).filter (fun e => v ∈ e)
      = symmDiff (A.filter (fun e => v ∈ e)) (B.filter (fun e => v ∈ e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  rw [edeg, hfil, card_symmDiff_zmod]
  rfl

/-- `Even n` in terms of the cast to `ZMod 2`. -/
theorem even_iff_natCast_zmod {n : ℕ} : Even n ↔ ((n : ZMod 2) = 0) := by
  rw [ZMod.natCast_eq_zero_iff, Nat.even_iff]
  omega

theorem evenDegrees_symmDiff {A B : Finset (Sym2 V)} (hA : EvenDegrees A) (hB : EvenDegrees B) :
    EvenDegrees (symmDiff A B) := by
  intro v
  have h := edeg_symmDiff_zmod A B v
  rw [even_iff_natCast_zmod.1 (hA v), even_iff_natCast_zmod.1 (hB v), add_zero] at h
  exact even_iff_natCast_zmod.2 h

/-! ### The three edges of a triangle -/

theorem cliqueEdges_triple' {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cliqueEdges ({a, b, c} : Finset V) = ({s(a, b), s(b, c), s(a, c)} : Finset (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_cliqueEdgesV, Sym2.mem_iff, Sym2.isDiag_iff_proj_eq, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨h, hne⟩
      rcases h x (Or.inl rfl) with rfl | rfl | rfl <;>
        rcases h y (Or.inr rfl) with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        refine ⟨?_, ?_⟩ <;> simp_all <;> tauto

/-! ### Sums of triangles -/

/-- The `F₂`-sum (iterated symmetric difference) of the edge sets of a list of triangles. -/
def triSum : List (Finset V) → Finset (Sym2 V)
  | [] => ∅
  | T :: L => symmDiff (cliqueEdges T) (triSum L)

@[simp] theorem triSum_nil : triSum ([] : List (Finset V)) = ∅ := rfl

@[simp] theorem triSum_cons (T : Finset V) (L : List (Finset V)) :
    triSum (T :: L) = symmDiff (cliqueEdges T) (triSum L) := rfl

/-- **Every loopless even graph on `S` is an `F₂`-sum of triangles with vertices in `S`.** -/
theorem even_graph_triSum {S : Finset V} :
    ∀ (n : ℕ) (E : Finset (Sym2 V)), E.card ≤ n → E ⊆ cliqueEdges S → EvenDegrees E →
      ∃ L : List (Finset V), (∀ T ∈ L, T.card = 3 ∧ T ⊆ S) ∧ E = triSum L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hcard hES hev
    rcases Finset.eq_empty_or_nonempty E with rfl | ⟨e₀, he₀⟩
    · exact ⟨[], by simp, by simp⟩
    · -- pick an edge `s(a,b)` of `E`
      obtain ⟨a, b, rfl⟩ : ∃ a b, e₀ = s(a, b) := Sym2.ind (fun p q => ⟨p, q, rfl⟩) e₀
      obtain ⟨hmem₀, hnd₀⟩ := mem_cliqueEdgesV.1 (hES he₀)
      have hab : a ≠ b := by
        intro hc; exact hnd₀ (by simp [hc])
      have haS : a ∈ S := hmem₀ a (by simp)
      have hbS : b ∈ S := hmem₀ b (by simp)
      -- `b` has a second edge
      have hb2 : 2 ≤ edeg E b := by
        have h1 : 1 ≤ edeg E b := by
          have : s(a, b) ∈ E.filter (fun e => b ∈ e) := Finset.mem_filter.2 ⟨he₀, by simp⟩
          exact Finset.card_pos.2 ⟨_, this⟩
        rcases hev b with ⟨c, hc⟩
        omega
      obtain ⟨e₁, he₁, hne₁⟩ : ∃ e₁ ∈ E.filter (fun e => b ∈ e), e₁ ≠ s(a, b) := by
        by_contra hcon
        push_neg at hcon
        have hsub : E.filter (fun e => b ∈ e) ⊆ {s(a, b)} := by
          intro e he; simpa using hcon e he
        have := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at this
        rw [edeg] at hb2
        omega
      obtain ⟨he₁E, hbe₁⟩ := Finset.mem_filter.1 he₁
      obtain ⟨hmem₁, hnd₁⟩ := mem_cliqueEdgesV.1 (hES he₁E)
      obtain ⟨c, hcdef⟩ : ∃ c, e₁ = s(b, c) := Sym2.mem_iff_exists.1 hbe₁
      subst hcdef
      have hbc : b ≠ c := by
        intro hc; exact hnd₁ (by simp [hc])
      have hcS : c ∈ S := hmem₁ c (by simp)
      have hac : a ≠ c := by
        intro hc
        apply hne₁
        rw [hc, Sym2.eq_swap]
      -- the triangle to peel off
      set T : Finset V := {a, b, c} with hTdef
      have hTcard : T.card = 3 := by
        rw [hTdef, Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      have hTS : T ⊆ S := by
        rw [hTdef]
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        exacts [haS, hbS, hcS]
      have hCT : cliqueEdges T = ({s(a, b), s(b, c), s(a, c)} : Finset (Sym2 V)) :=
        cliqueEdges_triple' hab hac hbc
      set E' : Finset (Sym2 V) := symmDiff E (cliqueEdges T) with hE'def
      -- `E'` is smaller
      have hsub' : E' ⊆ ((E.erase s(a, b)).erase s(b, c)) ∪ {s(a, c)} := by
        intro x hx
        rw [hE'def, Finset.mem_symmDiff] at hx
        rcases hx with ⟨hxE, hxC⟩ | ⟨hxC, hxE⟩
        · refine Finset.mem_union_left _ ?_
          rw [hCT] at hxC
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
          push_neg at hxC
          exact Finset.mem_erase.2 ⟨hxC.2.1, Finset.mem_erase.2 ⟨hxC.1, hxE⟩⟩
        · rw [hCT] at hxC
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
          rcases hxC with rfl | rfl | rfl
          · exact absurd he₀ hxE
          · exact absurd he₁E hxE
          · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hne : s(a, b) ≠ s(b, c) := by
        simp only [ne_eq, Sym2.eq_iff]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hab h1
        · exact hac h1
      have hcardlt : E'.card < E.card := by
        have h1 : ((E.erase s(a, b)).erase s(b, c)).card = E.card - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne.symm, he₁E⟩),
            Finset.card_erase_of_mem he₀]
          omega
        have h2 : E'.card ≤ ((E.erase s(a, b)).erase s(b, c)).card + 1 :=
          le_trans (Finset.card_le_card hsub')
            (le_trans (Finset.card_union_le _ _) (by simp))
        have h3 : 2 ≤ E.card := by
          have : ({s(a, b), s(b, c)} : Finset (Sym2 V)).card ≤ E.card := by
            refine Finset.card_le_card ?_
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            exacts [he₀, he₁E]
          rwa [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton] at this
        omega
      -- `E'` is again even and lives on `S`
      have hCTeven : EvenDegrees (cliqueEdges T) := by
        intro v
        rw [edeg_cliqueEdges hTcard v]
        split
        · exact even_two
        · exact ⟨0, rfl⟩
      have hE'even : EvenDegrees E' := evenDegrees_symmDiff hev hCTeven
      have hE'S : E' ⊆ cliqueEdges S := by
        intro x hx
        rw [hE'def, Finset.mem_symmDiff] at hx
        rcases hx with ⟨hxE, -⟩ | ⟨hxC, -⟩
        · exact hES hxE
        · exact cliqueEdges_mono hTS hxC
      obtain ⟨L, hL, hLeq⟩ := ih (n - 1) (by omega) E' (by omega) hE'S hE'even
      refine ⟨T :: L, ?_, ?_⟩
      · intro T' hT'
        rcases List.mem_cons.1 hT' with rfl | hT'
        · exact ⟨hTcard, hTS⟩
        · exact hL T' hT'
      · rw [triSum_cons, ← hLeq, hE'def, symmDiff_comm E (cliqueEdges T),
          symmDiff_symmDiff_cancel_left]

end BKLO
