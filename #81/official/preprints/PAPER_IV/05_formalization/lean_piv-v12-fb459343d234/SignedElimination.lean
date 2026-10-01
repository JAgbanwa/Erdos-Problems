import SignedDualModel
import RootStepBudget
import DualBudgetArithmetic

/-! Exact resource accounting for elimination outside a prescribed clique.
Signed weights need not be nonnegative: every real edge is counted once.
-/
namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding PaperIV.RootedSimplicialDefect
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def edgesWithin (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => e.toFinset ⊆ U)

theorem mk_mem_edgesWithin {U : Finset V} {a b : V} :
    s(a,b) ∈ edgesWithin G U ↔ G.Adj a b ∧ a ∈ U ∧ b ∈ U := by
  simp [edgesWithin,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff]

theorem edgesWithin_univ : edgesWithin G univ = G.edgeFinset := by
  simp [edgesWithin]

theorem edgesWithin_clique {R : Finset V} (hR : G.IsClique (R : Set V)) :
    edgesWithin G R = pairs R := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_edgesWithin,mk_mem_pairs]
    exact ⟨fun h => ⟨h.2.1,h.2.2,h.1.ne⟩,
      fun h => ⟨hR h.1 h.2.1 h.2.2,h.1,h.2.1⟩⟩

theorem sum_edgesWithin_erase (z : Sym2 V → ℚ) {U : Finset V} {v : V}
    (hv : v ∈ U) :
    ∑ e ∈ edgesWithin G U, z e =
      (∑ e ∈ edgesWithin G (U.erase v), z e) +
      ∑ u ∈ neighborsIn G U v, z s(v,u) := by
  classical
  have hinj : Function.Injective (fun u : V => s(v,u)) := by
    intro a b hab
    rcases Sym2.eq_iff.mp hab with ⟨_,h⟩ | ⟨h1,h2⟩
    · exact h
    · exact h2.trans h1
  have hset : edgesWithin G U = edgesWithin G (U.erase v) ∪
      (neighborsIn G U v).image (fun u => s(v,u)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_union,mk_mem_edgesWithin,mk_mem_edgesWithin]
      constructor
      · rintro ⟨hab,ha,hb⟩
        by_cases hav : a = v
        · subst a
          exact Or.inr (mem_image.mpr ⟨b,mem_filter.mpr ⟨hb,hab⟩,rfl⟩)
        by_cases hbv : b = v
        · subst b
          exact Or.inr (mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,hab.symm⟩,Sym2.eq_swap⟩)
        exact Or.inl ⟨hab,mem_erase.mpr ⟨hav,ha⟩,mem_erase.mpr ⟨hbv,hb⟩⟩
      · rintro (⟨hab,ha,hb⟩ | he)
        · exact ⟨hab,mem_of_mem_erase ha,mem_of_mem_erase hb⟩
        obtain ⟨u,hu,he⟩ := mem_image.mp he
        have hu' : u ∈ U ∧ G.Adj v u := mem_filter.mp hu
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hu'.2,hv,hu'.1⟩
        · exact ⟨hu'.2.symm,hu'.1,hv⟩
  have hdis : Disjoint (edgesWithin G (U.erase v))
      ((neighborsIn G U v).image (fun u => s(v,u))) := by
    apply disjoint_left.mpr
    intro e he hi
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
    exact (mem_erase.mp (mk_mem_edgesWithin G |>.mp he).2.1).1 rfl
  rw [hset,sum_union hdis,sum_image]
  exact fun _ _ _ _ h => hinj h

/-- Every row is bounded by the maximum clique-star plus its capped exceptions. -/
theorem exists_bounded_signed_row {s : ℕ} (hG : RootedDefectAt G s)
    (z : Sym2 V → ℚ) (hz : ∀ e, z e ≤ 1) (α : ℚ)
    (hmax : ∀ v (P : Finset V), G.IsClique (P : Set V) →
      (∀ u ∈ P, G.Adj v u) → (∑ u ∈ P, z s(v,u)) ≤ α)
    {U R : Finset V} (hRU : R ⊆ U) (hR : G.IsClique (R : Set V))
    (hne : (U \ R).Nonempty) :
    ∃ v ∈ U \ R, (∑ u ∈ neighborsIn G U v, z s(v,u)) ≤
      α + (min s ((U \ R).card-1) : ℕ) := by
  classical
  obtain ⟨v,hv,P,hP,hPc,hcap⟩ := exists_root_step_with_capped_budget G hG hRU hR hne
  have hp := hmax v P hPc (fun u hu => (mem_filter.mp (hP hu)).2)
  have hrest : (∑ u ∈ neighborsIn G U v \ P, z s(v,u)) ≤
      ((neighborsIn G U v \ P).card : ℚ) := by
    calc
      _ ≤ ∑ _u ∈ neighborsIn G U v \ P, (1 : ℚ) := sum_le_sum (fun u _ => hz _)
      _ = _ := by simp
  have hsplit := sum_sdiff hP (f := fun u => z s(v,u))
  have hc : ((neighborsIn G U v \ P).card : ℚ) ≤
      (min s ((U \ R).card-1) : ℕ) := by exact_mod_cast hcap
  exact ⟨v,hv,by linarith⟩

/-- Global signed sum with the exact exception charge, no favorable root
or nonnegative-edge assumption hidden in the induction. -/
theorem signed_elimination_bound {s : ℕ} (hG : RootedDefectAt G s)
    (z : Sym2 V → ℚ) (hz : ∀ e, z e ≤ 1) (α : ℚ)
    (hmax : ∀ v (P : Finset V), G.IsClique (P : Set V) →
      (∀ u ∈ P, G.Adj v u) → (∑ u ∈ P, z s(v,u)) ≤ α)
    (R : Finset V) (hR : G.IsClique (R : Set V)) :
    ∀ U : Finset V, R ⊆ U →
      (∑ e ∈ edgesWithin G U, z e) ≤
        ((U.card-R.card : ℕ) : ℚ)*α +
        (∑ j ∈ range (U.card-R.card), ((min s j : ℕ) : ℚ)) +
        ∑ e ∈ pairs R, z e := by
  classical
  intro U
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro hRU
    by_cases heq : U = R
    · subst U
      simp [edgesWithin_clique G hR]
    have hne : (U \ R).Nonempty := by
      rw [sdiff_nonempty]
      intro hUR
      exact heq (Subset.antisymm hUR hRU)
    obtain ⟨v,hv,hrow⟩ := exists_bounded_signed_row G hG z hz α hmax hRU hR hne
    have hvU : v ∈ U := (mem_sdiff.mp hv).1
    have hvR : v ∉ R := (mem_sdiff.mp hv).2
    have hRe : R ⊆ U.erase v := by
      intro u hu
      exact mem_erase.mpr ⟨fun he => hvR (he ▸ hu),hRU hu⟩
    have hrec := ih (U.erase v) (erase_ssubset hvU) hRe
    have hcard := card_le_card hRe
    have hq : U.card-R.card = (U.erase v).card-R.card+1 := by
      have hpos : 0 < U.card := card_pos.mpr ⟨v,hvU⟩
      rw [card_erase_of_mem hvU] at hcard ⊢
      omega
    have hq' : (U \ R).card-1 = (U.erase v).card-R.card := by
      rw [card_sdiff_of_subset hRU,hq]
      omega
    rw [sum_edgesWithin_erase G z hvU,hq,sum_range_succ]
    rw [hq'] at hrow
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.signed_elimination_bound
