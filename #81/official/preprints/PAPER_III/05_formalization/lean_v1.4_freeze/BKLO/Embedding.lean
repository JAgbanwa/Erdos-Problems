/-
# BKLO Section 5 — the embedding lemma.

The engine uses one technical tool from §5: a bounded-degeneracy gadget embeds into a host graph
whose small sets have large common neighbourhoods, avoiding a prescribed bounded set of vertices
and extending a prescribed placement of its "roots".  This is what transports the abstract
absorbers of `BKLO.AbsorberExists` (which live on `ℕ`, using fresh vertices) into the dense host
graph `G`.

The proof is the greedy embedding: process the vertices in increasing order; a vertex with at most
`d` already-embedded neighbours must land in the common neighbourhood of their images, which is
large by hypothesis.  Everything here is proved.

The quantitative input is `card_commonNbrs_ge`: in a graph with minimum degree `δ`, any set of `s`
vertices has at least `n - s(n - δ)` common neighbours.  For `δ ≥ (9/10 + ε)n` and `s ≤ 9` this is
at least `(1/10)n`, which is why back-degeneracy `≤ 9` is the relevant bound for the triangle
threshold.
-/
import BKLO.Degeneracy
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common neighbourhood of a finite set `S` of vertices. -/
def commonNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter (fun w => ∀ s ∈ S, G.Adj s w)

/-- **Common neighbourhoods in a graph of large minimum degree.**
`n ≤ |N(S)| + |S| * (n - δ(G))`. -/
theorem card_commonNbrs_ge (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Fintype.card V ≤ (commonNbrs G S).card + S.card * (Fintype.card V - G.minDegree) := by
  classical
  have hcover : (Finset.univ \ commonNbrs G S)
      ⊆ S.biUnion (fun s => Finset.univ \ G.neighborFinset s) := by
    intro w hw
    have hw' : ¬ (∀ s ∈ S, G.Adj s w) := by
      have := (Finset.mem_sdiff.1 hw).2
      simpa [commonNbrs] using this
    push_neg at hw'
    obtain ⟨s, hs, hns⟩ := hw'
    exact Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by
      simpa [SimpleGraph.mem_neighborFinset] using hns⟩⟩
  have hcard : (Finset.univ \ commonNbrs G S).card
      ≤ S.card * (Fintype.card V - G.minDegree) := by
    refine le_trans (Finset.card_le_card hcover) (le_trans Finset.card_biUnion_le ?_)
    refine le_trans (Finset.sum_le_card_nsmul _ _ (Fintype.card V - G.minDegree) ?_) ?_
    · intro s _
      have h1 : (Finset.univ \ G.neighborFinset s).card = Fintype.card V - G.degree s :=
        Finset.card_univ_diff _
      rw [h1]
      exact Nat.sub_le_sub_left (G.minDegree_le_degree s) _
    · simp [smul_eq_mul]
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (commonNbrs G S))
  rw [Finset.card_univ] at hsum
  omega

/-! ### The greedy embedding -/

/-- The greedy embedding, run up to level `k`. -/
private theorem embed_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F : Finset V)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hroom : ∀ S : Finset V, S.card ≤ d → F.card + (supp A).card < (commonNbrs G S).card) :
    ∀ k : ℕ, ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → v < k → f v ∉ F) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, u < k → v < k → f u = f v → u = v) ∧
      (∀ e ∈ A, (∀ v ∈ e, v < k) → Sym2.map f e ∈ G.edgeFinset) := by
  classical
  intro k
  induction k with
  | zero =>
    exact ⟨f₀, fun v _ => rfl, fun v _ _ h => absurd h (by omega),
      fun u _ v _ h => absurd h (by omega), fun e he hlt => by
        induction e using Sym2.ind with
        | _ x y => exact absurd (hlt x (by simp)) (by omega)⟩
  | succ k ih =>
    obtain ⟨f, hfb, hfF, hfinj, hfe⟩ := ih
    by_cases hk : k ∈ supp A ∧ b ≤ k
    · -- the interesting case: place the vertex `k`
      obtain ⟨hkA, hkb⟩ := hk
      set S : Finset V := (backNbrs A k).image f with hS
      have hScard : S.card ≤ d := le_trans Finset.card_image_le (hdeg k)
      set Bad : Finset V := F ∪ ((supp A).filter (fun v => v < k)).image f with hBad
      have hBadcard : Bad.card < (commonNbrs G S).card := by
        refine lt_of_le_of_lt (le_trans (Finset.card_union_le _ _) ?_) (hroom S hScard)
        exact Nat.add_le_add_left (le_trans Finset.card_image_le (Finset.card_filter_le _ _)) _
      obtain ⟨w, hw, hwBad⟩ : ∃ w ∈ commonNbrs G S, w ∉ Bad := by
        by_contra hcon
        push_neg at hcon
        exact absurd (Finset.card_le_card (fun x hx => hcon x hx)) (by omega)
      refine ⟨Function.update f k w, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rw [Function.update_of_ne (show v ≠ k by omega)]
        exact hfb v hv
      · intro v hvA hvb hvk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
        · rw [Function.update_of_ne (show v ≠ k by omega)]; exact hfF v hvA hvb h
        · rw [Function.update_self]
          exact fun hc => hwBad (Finset.mem_union_left _ hc)
      · intro u huA v hvA huk hvk heq
        by_cases hu : u = k <;> by_cases hv : v = k
        · rw [hu, hv]
        · subst hu
          rw [Function.update_self, Function.update_of_ne hv] at heq
          refine absurd ?_ hwBad
          rw [heq]
          exact Finset.mem_union_right _
            (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hvA, by omega⟩))
        · subst hv
          rw [Function.update_self, Function.update_of_ne hu] at heq
          refine absurd ?_ hwBad
          rw [← heq]
          exact Finset.mem_union_right _
            (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨huA, by omega⟩))
        · rw [Function.update_of_ne hu, Function.update_of_ne hv] at heq
          exact hfinj u huA v hvA (by omega) (by omega) heq
      · intro e heA hlt
        induction e using Sym2.ind with
        | _ x y =>
          have hxy : x ≠ y := fun h => hloop _ heA (by simp [h])
          have hxA : x ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          have hyA : y ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          have hx : x < k + 1 := hlt x (by simp)
          have hy : y < k + 1 := hlt y (by simp)
          by_cases hxk : x = k
          · subst hxk
            have hyk : y < x := by omega
            have hyb : y ∈ backNbrs A x :=
              Finset.mem_filter.2 ⟨hyA, hyk, by rw [Sym2.eq_swap]; exact heA⟩
            have hadj : G.Adj (f y) w := by
              simp only [commonNbrs, Finset.mem_filter] at hw
              exact hw.2 (f y) (Finset.mem_image_of_mem f hyb)
            simp only [Sym2.map_pair_eq, Function.update_self,
              Function.update_of_ne (show y ≠ x by omega), SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet]
            exact hadj.symm
          · by_cases hyk : y = k
            · subst hyk
              have hxk' : x < y := by omega
              have hxb : x ∈ backNbrs A y := Finset.mem_filter.2 ⟨hxA, hxk', heA⟩
              have hadj : G.Adj (f x) w := by
                simp only [commonNbrs, Finset.mem_filter] at hw
                exact hw.2 (f x) (Finset.mem_image_of_mem f hxb)
              simp only [Sym2.map_pair_eq, Function.update_self,
                Function.update_of_ne (show x ≠ y by omega), SimpleGraph.mem_edgeFinset,
                SimpleGraph.mem_edgeSet]
              exact hadj
            · have hprev := hfe _ heA (by
                intro v hv
                simp only [Sym2.mem_iff] at hv
                rcases hv with rfl | rfl <;> omega)
              simpa only [Sym2.map_pair_eq, Function.update_of_ne hxk,
                Function.update_of_ne hyk] using hprev
    · by_cases hkA : k ∈ supp A
      · -- `k` is a root: it was already placed by `f₀`
        have hkb : k < b := by by_contra h; exact hk ⟨hkA, by omega⟩
        refine ⟨f, hfb, ?_, ?_, ?_⟩
        · intro v hvA hvb hvk; exact absurd hvb (by omega)
        · intro u huA v hvA huk hvk heq
          have hub : u < b := by omega
          have hvb : v < b := by omega
          rw [hfb u hub, hfb v hvb] at heq
          exact hinj₀ u huA v hvA hub hvb heq
        · intro e heA hlt
          obtain ⟨x, hx, hxb⟩ := htouch e heA
          exact absurd (hlt x hx) (by omega)
      · -- `k` is not a vertex of `A` at all
        have hlt' : ∀ v ∈ supp A, v < k + 1 → v < k := by
          intro v hvA hvk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
          · exact h
          · exact absurd hvA hkA
        refine ⟨f, hfb, ?_, ?_, ?_⟩
        · intro v hvA hvb hvk
          exact hfF v hvA hvb (hlt' v hvA hvk)
        · intro u huA v hvA huk hvk heq
          exact hfinj u huA v hvA (hlt' u huA huk) (hlt' v hvA hvk) heq
        · intro e heA hlt
          refine hfe e heA fun v hv => ?_
          exact hlt' v (mem_supp.2 ⟨_, heA, hv⟩) (hlt v hv)

/-- **Lemma 5.2 (embedding), operational form.**  Let `A` be a loopless edge set on `ℕ` whose
vertices below `b` (the *roots*) span no edge (`Touches b A`) and in which every vertex has at most
`d` smaller neighbours.  Let `f₀` place the roots of `A` injectively in `V`, and let `F` be a set of
forbidden vertices.  If every set of at most `d` vertices of `G` has more than `|F| + |V(A)|` common
neighbours, then `A` embeds into `G` extending `f₀`, injectively, with all new vertices outside
`F`. -/
theorem exists_embedding (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F : Finset V)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hroom : ∀ S : Finset V, S.card ≤ d → F.card + (supp A).card < (commonNbrs G S).card) :
    ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → f v ∉ F) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, f u = f v → u = v) ∧
      (∀ e ∈ A, Sym2.map f e ∈ G.edgeFinset) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ supp A, v < N :=
    ⟨(supp A).sup id + 1, fun v hv => Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)⟩
  obtain ⟨f, hfb, hfF, hfinj, hfe⟩ := embed_aux G hdeg hloop htouch f₀ F hinj₀ hroom N
  refine ⟨f, hfb, fun v hv hvb => hfF v hv hvb (hN v hv), fun u hu v hv =>
    hfinj u hu v hv (hN u hu) (hN v hv), fun e he => ?_⟩
  refine hfe e he fun v hv => hN v (mem_supp.2 ⟨_, he, hv⟩)

end BKLO
