/-
# The embedding lemma with a conflict relation

`BKLO.exists_embedding` (BKLO §5) embeds a `d`-degenerate gadget into a host graph whose small sets
have large common neighbourhoods, avoiding a prescribed forbidden set.  For the §11 cells route one
needs more: the reservation must be spread *at the scale of a single bottom cell* of the vortex, so
the new vertices have to be routed to pairwise "non-conflicting" places — in the application, to
distinct bottom cells which moreover carry no reserved edge to each other yet.

This file proves the variant `BKLO.exists_embedding_conf`.  Instead of prescribing a target set for
each new vertex (which cannot work: a single cell need not contain a common neighbour of nine given
vertices) it takes an abstract reflexive symmetric *conflict relation* `conf` and asks only that

* for every set `Bad` of at most `Kb` already-used vertices and every set `Q` of at most `d`
  vertices there is a common neighbour of `Q`, outside the forbidden set `F`, in conflict with no
  element of `Bad`.

The embedding then places every new vertex outside `F`, in conflict with no other placed vertex and
with no vertex of the prescribed set `Z` of previously used vertices.  Reflexivity of `conf` makes
the embedding automatically injective on the new vertices.
-/
import BKLO.Embedding

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The greedy conflict-avoiding embedding, run up to level `k`. -/
private theorem embedConf_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b Kb : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F Z : Finset V)
    (conf : V → V → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hbud : Z.card + (supp A).card ≤ Kb)
    (hroom : ∀ Bad : Finset V, Bad.card ≤ Kb → ∀ Q : Finset V, Q.card ≤ d →
      ∃ y ∈ commonNbrs G Q, y ∉ F ∧ ∀ z ∈ Bad, ¬ conf y z) :
    ∀ k : ℕ, ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → v < k → f v ∉ F) ∧
      (∀ v ∈ supp A, b ≤ v → v < k → ∀ z ∈ Z, ¬ conf (f v) z) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, b ≤ u → u < k → v < k → u ≠ v → ¬ conf (f u) (f v)) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, u < k → v < k → f u = f v → u = v) ∧
      (∀ e ∈ A, (∀ v ∈ e, v < k) → Sym2.map f e ∈ G.edgeFinset) := by
  classical
  intro k
  induction k with
  | zero =>
    exact ⟨f₀, fun v _ => rfl, fun v _ _ h => absurd h (by omega),
      fun v _ _ h => absurd h (by omega),
      fun u _ v _ _ h => absurd h (by omega),
      fun u _ v _ h => absurd h (by omega), fun e he hlt => by
        induction e using Sym2.ind with
        | _ x y => exact absurd (hlt x (by simp)) (by omega)⟩
  | succ k ih =>
    obtain ⟨f, hfb, hfF, hfZ, hfconf, hfinj, hfe⟩ := ih
    by_cases hk : k ∈ supp A ∧ b ≤ k
    · obtain ⟨hkA, hkb⟩ := hk
      set Bad : Finset V := Z ∪ ((supp A).filter (fun v => v < k)).image f with hBad
      have hBadcard : Bad.card ≤ Kb := by
        refine le_trans (Finset.card_union_le _ _) (le_trans (Nat.add_le_add_left ?_ _) hbud)
        exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
      have hBadmem : ∀ v ∈ supp A, v < k → f v ∈ Bad := by
        intro v hv hvk
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hv, hvk⟩))
      set Q : Finset V := (backNbrs A k).image f with hQ
      have hQcard : Q.card ≤ d := le_trans Finset.card_image_le (hdeg k)
      obtain ⟨w, hwQ, hwF, hwBad⟩ := hroom Bad hBadcard Q hQcard
      have hwne : ∀ v ∈ supp A, v < k → w ≠ f v := by
        intro v hv hvk heq
        exact hwBad (f v) (hBadmem v hv hvk) (heq ▸ hrefl w)
      refine ⟨Function.update f k w, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rw [Function.update_of_ne (show v ≠ k by omega)]
        exact hfb v hv
      · intro v hvA hvb hvk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
        · rw [Function.update_of_ne (show v ≠ k by omega)]; exact hfF v hvA hvb h
        · rw [Function.update_self]; exact hwF
      · intro v hvA hvb hvk z hz
        rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
        · rw [Function.update_of_ne (show v ≠ k by omega)]; exact hfZ v hvA hvb h z hz
        · rw [Function.update_self]; exact hwBad z (Finset.mem_union_left _ hz)
      · intro u huA v hvA hub huk hvk hne
        by_cases hu : u = k <;> by_cases hv : v = k
        · exact absurd (hu.trans hv.symm) hne
        · subst hu
          rw [Function.update_self, Function.update_of_ne hv]
          exact hwBad (f v) (hBadmem v hvA (by omega))
        · subst hv
          rw [Function.update_self, Function.update_of_ne hu]
          exact fun hc => hwBad (f u) (hBadmem u huA (by omega)) (hsymm _ _ hc)
        · rw [Function.update_of_ne hu, Function.update_of_ne hv]
          exact hfconf u huA v hvA hub (by omega) (by omega) hne
      · intro u huA v hvA huk hvk heq
        by_cases hu : u = k <;> by_cases hv : v = k
        · rw [hu, hv]
        · subst hu
          rw [Function.update_self, Function.update_of_ne hv] at heq
          exact absurd heq (hwne v hvA (by omega))
        · subst hv
          rw [Function.update_self, Function.update_of_ne hu] at heq
          exact absurd heq.symm (hwne u huA (by omega))
        · rw [Function.update_of_ne hu, Function.update_of_ne hv] at heq
          exact hfinj u huA v hvA (by omega) (by omega) heq
      · intro e heA hlt
        induction e using Sym2.ind with
        | _ x y =>
          have hxA : x ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          have hyA : y ∈ supp A := mem_supp.2 ⟨_, heA, by simp⟩
          have hx : x < k + 1 := hlt x (by simp)
          have hy : y < k + 1 := hlt y (by simp)
          by_cases hxk : x = k
          · subst hxk
            have hxy : y ≠ x := fun h => hloop _ heA (by simp [h])
            have hyk : y < x := by omega
            have hyb : y ∈ backNbrs A x :=
              Finset.mem_filter.2 ⟨hyA, hyk, by rw [Sym2.eq_swap]; exact heA⟩
            have hadj : G.Adj (f y) w := by
              simp only [commonNbrs, Finset.mem_filter] at hwQ
              exact hwQ.2 (f y) (Finset.mem_image_of_mem f hyb)
            simp only [Sym2.map_pair_eq, Function.update_self,
              Function.update_of_ne hxy, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hadj.symm
          · by_cases hyk : y = k
            · subst hyk
              have hxy : x ≠ y := fun h => hloop _ heA (by simp [h])
              have hxk' : x < y := by omega
              have hxb : x ∈ backNbrs A y := Finset.mem_filter.2 ⟨hxA, hxk', heA⟩
              have hadj : G.Adj (f x) w := by
                simp only [commonNbrs, Finset.mem_filter] at hwQ
                exact hwQ.2 (f x) (Finset.mem_image_of_mem f hxb)
              simp only [Sym2.map_pair_eq, Function.update_self,
                Function.update_of_ne hxy, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              exact hadj
            · have hprev := hfe _ heA (by
                intro v hv
                simp only [Sym2.mem_iff] at hv
                rcases hv with rfl | rfl <;> omega)
              simpa only [Sym2.map_pair_eq, Function.update_of_ne hxk,
                Function.update_of_ne hyk] using hprev
    · by_cases hkA : k ∈ supp A
      · have hkb : k < b := by by_contra h; exact hk ⟨hkA, by omega⟩
        refine ⟨f, hfb, ?_, ?_, ?_, ?_, ?_⟩
        · intro v hvA hvb hvk; exact absurd hvb (by omega)
        · intro v hvA hvb hvk; exact absurd hvb (by omega)
        · intro u huA v hvA hub huk hvk hne
          exact absurd hub (by omega)
        · intro u huA v hvA huk hvk heq
          have hub : u < b := by omega
          have hvb : v < b := by omega
          rw [hfb u hub, hfb v hvb] at heq
          exact hinj₀ u huA v hvA hub hvb heq
        · intro e heA hlt
          obtain ⟨x, hx, hxb⟩ := htouch e heA
          exact absurd (hlt x hx) (by omega)
      · have hlt' : ∀ v ∈ supp A, v < k + 1 → v < k := by
          intro v hvA hvk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
          · exact h
          · exact absurd hvA hkA
        refine ⟨f, hfb, ?_, ?_, ?_, ?_, ?_⟩
        · intro v hvA hvb hvk; exact hfF v hvA hvb (hlt' v hvA hvk)
        · intro v hvA hvb hvk; exact hfZ v hvA hvb (hlt' v hvA hvk)
        · intro u huA v hvA hub huk hvk hne
          exact hfconf u huA v hvA hub (hlt' u huA huk) (hlt' v hvA hvk) hne
        · intro u huA v hvA huk hvk heq
          exact hfinj u huA v hvA (hlt' u huA huk) (hlt' v hvA hvk) heq
        · intro e heA hlt
          refine hfe e heA fun v hv => ?_
          exact hlt' v (mem_supp.2 ⟨_, heA, hv⟩) (hlt v hv)

/-- **Lemma 5.2 (embedding) with a conflict relation.**  As `BKLO.exists_embedding`, but every new
vertex of `A` is placed outside the forbidden set `F`, in conflict neither with the prescribed set
`Z` nor with any other placed vertex.  Only the "room" hypothesis is needed: any at most `d`
vertices have a common neighbour outside `F` avoiding the conflicts of any at most `Kb` vertices. -/
theorem exists_embedding_conf (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b Kb : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F Z : Finset V)
    (conf : V → V → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hbud : Z.card + (supp A).card ≤ Kb)
    (hroom : ∀ Bad : Finset V, Bad.card ≤ Kb → ∀ Q : Finset V, Q.card ≤ d →
      ∃ y ∈ commonNbrs G Q, y ∉ F ∧ ∀ z ∈ Bad, ¬ conf y z) :
    ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → f v ∉ F) ∧
      (∀ v ∈ supp A, b ≤ v → ∀ z ∈ Z, ¬ conf (f v) z) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, b ≤ u → u ≠ v → ¬ conf (f u) (f v)) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, f u = f v → u = v) ∧
      (∀ e ∈ A, Sym2.map f e ∈ G.edgeFinset) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ supp A, v < N :=
    ⟨(supp A).sup id + 1, fun v hv => Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)⟩
  obtain ⟨f, hfb, hfF, hfZ, hfconf, hfinj, hfe⟩ :=
    embedConf_aux G hdeg hloop htouch f₀ F Z conf hrefl hsymm hinj₀ hbud hroom N
  refine ⟨f, hfb, fun v hv hvb => hfF v hv hvb (hN v hv),
    fun v hv hvb => hfZ v hv hvb (hN v hv),
    fun u hu v hv hub hne => hfconf u hu v hv hub (hN u hu) (hN v hv) hne,
    fun u hu v hv => hfinj u hu v hv (hN u hu) (hN v hv), fun e he => ?_⟩
  exact hfe e he fun v hv => hN v (mem_supp.2 ⟨_, he, hv⟩)

end BKLO
