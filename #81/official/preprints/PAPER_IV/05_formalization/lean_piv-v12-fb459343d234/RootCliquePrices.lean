import SignedElimination
import PaperIV.SplitUniformIncidence

namespace PaperIV.SublinearResearch
open Finset PaperIV.FarRounding
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem sum_pairs_erase (z : Sym2 V → ℚ) {C : Finset V} {v : V} (hv : v ∈ C) :
    ∑ e ∈ pairs C, z e = (∑ e ∈ pairs (C.erase v), z e) +
      ∑ u ∈ C.erase v, z s(v,u) := by
  classical
  have hc : (⊤ : SimpleGraph V).IsClique (C : Set V) := by
    intro a ha b hb hab
    exact hab
  have hce : (⊤ : SimpleGraph V).IsClique (C.erase v : Set V) := by
    intro a ha b hb hab
    exact hab
  have hn : PaperIV.RootedSimplicialDefect.neighborsIn (⊤ : SimpleGraph V) C v =
      C.erase v := by
    ext u
    simp [PaperIV.RootedSimplicialDefect.neighborsIn,SimpleGraph.top_adj,
      mem_erase,ne_comm,and_comm]
  have h := sum_edgesWithin_erase (⊤ : SimpleGraph V) z hv
  rwa [edgesWithin_clique _ hc,edgesWithin_clique _ hce,hn] at h

/-- Pair inequalities against a host, summed without orienting an edge twice. -/
theorem sum_pairs_triangle_bound (z : Sym2 V → ℚ) (a : V → ℚ)
    (C : Finset V)
    (h : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → z s(u,v) ≤ 1-a u-a v) :
    (∑ e ∈ pairs C, z e) ≤ (C.card.choose 2 : ℚ) -
      ((C.card : ℚ)-1)*(∑ u ∈ C, a u) := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [pairs]
  | @insert v C hv ih =>
    have hC : ∀ u ∈ C, ∀ w ∈ C, u ≠ w → z s(u,w) ≤ 1-a u-a w :=
      fun u hu w hw hne => h u (mem_insert_of_mem hu) w (mem_insert_of_mem hw) hne
    have hrow : (∑ u ∈ C, z s(v,u)) ≤ (C.card : ℚ)*(1-a v) - ∑ u ∈ C, a u := by
      calc
        _ ≤ ∑ u ∈ C, (1-a v-a u) := sum_le_sum (fun u hu =>
          h v (mem_insert_self _ _) u (mem_insert_of_mem hu) (fun he => hv (he ▸ hu)))
        _ = _ := by rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    have hi := ih hC
    rw [sum_pairs_erase z (mem_insert_self v C),erase_insert hv,
      card_insert_of_notMem hv,sum_insert hv]
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_one] at hi ⊢
    nlinarith

theorem signed_triangle (y : DualCover G ℚ) {v u w : V}
    (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w) :
    signedPrice y s(u,w) ≤ 1-signedPrice y s(v,u)-signedPrice y s(v,w) := by
  classical
  have hcl : G.IsClique (({v,u,w} : Finset V) : Set V) := by
    intro a ha b hb hab
    simp only [mem_coe,mem_insert,mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact (hab rfl).elim | exact hvu | exact hvw | exact huw |
      exact hvu.symm | exact hvw.symm | exact huw.symm
  have hcard : ({v,u,w} : Finset V).card = 3 := by
    simp [hvu.ne,hvw.ne,huw.ne]
  have hi : ({v,u,w} : Finset V) ∈ items G := mem_items.mpr ⟨hcl,Or.inl hcard⟩
  have hs := signed_item_sum_le_one y _ hi
  rw [sum_pairs_erase (signedPrice y) (mem_insert_self v {u,w})] at hs
  have hvnot : v ∉ ({u,w} : Finset V) := by simp [hvu.ne,hvw.ne]
  rw [erase_insert hvnot] at hs
  have hp : pairs ({u,w} : Finset V) = {s(u,w)} := by
    have hnd : ¬ (s(u,w) : Sym2 V).IsDiag := by simpa using huw.ne
    simpa only [Sym2.toFinset_mk_eq] using (pairs_toFinset hnd)
  rw [hp] at hs
  simp [huw.ne] at hs
  linarith

theorem signed_root_triangle_bound (y : DualCover G ℚ) {v : V} {C : Finset V}
    (hC : G.IsClique (C : Set V)) (hv : ∀ u ∈ C, G.Adj v u) :
    (∑ e ∈ pairs C, signedPrice y e) ≤ (C.card.choose 2 : ℚ) -
      ((C.card : ℚ)-1)*(∑ u ∈ C, signedPrice y s(v,u)) := by
  exact sum_pairs_triangle_bound _ _ C (fun u hu w hw hne =>
    signed_triangle y (hv u hu) (hv w hw) (hC hu hw hne))

/-- Uniform K4 incidence gives an upper bound on signed mass inside any clique.
No sign condition on the weights is needed in this exact double count. -/
theorem signed_root_K4_bound (y : DualCover G ℚ) {C : Finset V}
    (hC : G.IsClique (C : Set V)) (hc : 4 ≤ C.card) :
    (∑ e ∈ pairs C, signedPrice y e) ≤ (C.card.choose 2 : ℚ)/6 := by
  classical
  let F := C.powersetCard 4
  have hinc : ∀ e ∈ pairs C, (F.filter (fun K => e ∈ pairs K)).card =
      (C.card-2).choose 2 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hm := mk_mem_pairs.mp he
      have hi := SplitUniformIncidence.incidence_famK4core_inner hm.1 hm.2.1 hm.2.2
      simpa [F,SplitUniformIncidence.incidence,SplitUniformIncidence.famK4core,
        mk_mem_pairs,hm.2.2] using hi
  have hsum : (∑ K ∈ F, ∑ e ∈ pairs K, signedPrice y e) =
      (((C.card-2).choose 2 : ℕ) : ℚ)*(∑ e ∈ pairs C, signedPrice y e) := by
    calc
      _ = ∑ K ∈ F, ∑ e ∈ pairs C, if e ∈ pairs K then signedPrice y e else 0 := by
        apply sum_congr rfl
        intro K hK
        have hKC := (mem_powersetCard.mp hK).1
        rw [← sum_filter]
        congr 1
        ext e
        simp only [mem_filter]
        exact ⟨fun he => ⟨by
          induction e using Sym2.ind with
          | _ u v =>
            rw [mk_mem_pairs] at he ⊢
            exact ⟨hKC he.1,hKC he.2.1,he.2.2⟩,he⟩,fun he => he.2⟩
      _ = ∑ e ∈ pairs C, ∑ K ∈ F, if e ∈ pairs K then signedPrice y e else 0 := sum_comm
      _ = ∑ e ∈ pairs C, (((C.card-2).choose 2 : ℕ) : ℚ)*signedPrice y e := by
        apply sum_congr rfl
        intro e he
        rw [← sum_filter,sum_const,nsmul_eq_mul,hinc e he]
      _ = _ := (mul_sum ..).symm
  have hupper : (∑ K ∈ F, ∑ e ∈ pairs K, signedPrice y e) ≤ (C.card.choose 4 : ℚ) := by
    calc
      _ ≤ ∑ _K ∈ F, (1 : ℚ) := by
        apply sum_le_sum
        intro K hK
        have hm := mem_powersetCard.mp hK
        exact signed_item_sum_le_one y K (mem_items.mpr
          ⟨fun u hu v hv hne => hC (hm.1 hu) (hm.1 hv) hne,Or.inr hm.2⟩)
      _ = _ := by simp [F]
  have hid : (6 : ℚ)*(C.card.choose 4 : ℚ) =
      (((C.card-2).choose 2 : ℕ) : ℚ)*(C.card.choose 2 : ℚ) := by
    exact_mod_cast SplitUniformIncidence.six_mul_choose_four C.card
  have hpos : (0 : ℚ) < ((C.card-2).choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ C.card-2 by omega)
  rw [hsum] at hupper
  nlinarith

end PaperIV.SublinearResearch
#print axioms PaperIV.SublinearResearch.signed_root_triangle_bound
#print axioms PaperIV.SublinearResearch.signed_root_K4_bound
