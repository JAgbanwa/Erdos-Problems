/-
# The embedding lemma with prescribed targets

`BKLO.exists_embedding` (BKLO §5) embeds a `d`-degenerate gadget into a host graph whose small
sets have large common neighbourhoods, avoiding a prescribed forbidden set.  For the §11 cells
route one needs more: the *location* of the new vertices must be controlled, because the
reservation has to be spread at the scale of a single bottom cell of the vortex.

This file proves the variant `BKLO.exists_embedding_target`, in which every new vertex `v` is
given its own candidate set `Y v`, the candidate sets of distinct new vertices are disjoint, and
the greedy step only needs *one* candidate in the common neighbourhood of the (at most `d`)
already-embedded neighbours.  Applied with `Y v` a set of vertices inside a bottom cell of the
vortex, this places at most one new vertex per cell.
-/
import BKLO.Embedding

open Finset

namespace BKLO

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The greedy embedding into prescribed targets, run up to level `k`. -/
private theorem embedTarget_aux (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F : Finset V) (Y : ℕ → Finset V)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hf₀F : ∀ v ∈ supp A, v < b → f₀ v ∈ F)
    (hYF : ∀ v ∈ supp A, b ≤ v → Disjoint (Y v) F)
    (hYdisj : ∀ u ∈ supp A, ∀ v ∈ supp A, b ≤ u → b ≤ v → u ≠ v → Disjoint (Y u) (Y v))
    (hroom : ∀ v ∈ supp A, b ≤ v → ∀ S : Finset V, S.card ≤ d →
      (commonNbrs G S ∩ Y v).Nonempty) :
    ∀ k : ℕ, ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → v < k → f v ∈ Y v) ∧
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
    obtain ⟨f, hfb, hfY, hfinj, hfe⟩ := ih
    by_cases hk : k ∈ supp A ∧ b ≤ k
    · -- the interesting case: place the vertex `k`
      obtain ⟨hkA, hkb⟩ := hk
      set S : Finset V := (backNbrs A k).image f with hS
      have hScard : S.card ≤ d := le_trans Finset.card_image_le (hdeg k)
      obtain ⟨w, hw⟩ := hroom k hkA hkb S hScard
      obtain ⟨hwS, hwY⟩ := Finset.mem_inter.1 hw
      have hwF : w ∉ F := fun hc => (Finset.disjoint_left.1 (hYF k hkA hkb)) hwY hc
      refine ⟨Function.update f k w, ?_, ?_, ?_, ?_⟩
      · intro v hv
        rw [Function.update_of_ne (show v ≠ k by omega)]
        exact hfb v hv
      · intro v hvA hvb hvk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hvk with h | rfl
        · rw [Function.update_of_ne (show v ≠ k by omega)]; exact hfY v hvA hvb h
        · rw [Function.update_self]; exact hwY
      · intro u huA v hvA huk hvk heq
        by_cases hu : u = k <;> by_cases hv : v = k
        · rw [hu, hv]
        · -- `u = k`, `v < k`
          subst hu
          rw [Function.update_self, Function.update_of_ne hv] at heq
          exfalso
          by_cases hvb : v < b
          · rw [hfb v hvb] at heq
            exact hwF (by rw [heq]; exact hf₀F v hvA hvb)
          · have hvb' : b ≤ v := by omega
            have hvY : f v ∈ Y v := hfY v hvA hvb' (by omega)
            exact (Finset.disjoint_left.1 (hYdisj u huA v hvA hkb hvb' (by omega)))
              (heq ▸ hwY) hvY
        · -- `v = k`, `u < k`
          subst hv
          rw [Function.update_self, Function.update_of_ne hu] at heq
          exfalso
          by_cases hub : u < b
          · rw [hfb u hub] at heq
            exact hwF (by rw [← heq]; exact hf₀F u huA hub)
          · have hub' : b ≤ u := by omega
            have huY : f u ∈ Y u := hfY u huA hub' (by omega)
            exact (Finset.disjoint_left.1 (hYdisj v hvA u huA hkb hub' (by omega)))
              (by rw [heq]; exact hwY) huY
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
              simp only [commonNbrs, Finset.mem_filter] at hwS
              exact hwS.2 (f y) (Finset.mem_image_of_mem f hyb)
            simp only [Sym2.map_pair_eq, Function.update_self,
              Function.update_of_ne (show y ≠ x by omega), SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet]
            exact hadj.symm
          · by_cases hyk : y = k
            · subst hyk
              have hxk' : x < y := by omega
              have hxb : x ∈ backNbrs A y := Finset.mem_filter.2 ⟨hxA, hxk', heA⟩
              have hadj : G.Adj (f x) w := by
                simp only [commonNbrs, Finset.mem_filter] at hwS
                exact hwS.2 (f x) (Finset.mem_image_of_mem f hxb)
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
          exact hfY v hvA hvb (hlt' v hvA hvk)
        · intro u huA v hvA huk hvk heq
          exact hfinj u huA v hvA (hlt' u huA huk) (hlt' v hvA hvk) heq
        · intro e heA hlt
          refine hfe e heA fun v hv => ?_
          exact hlt' v (mem_supp.2 ⟨_, heA, hv⟩) (hlt v hv)

/-- **Lemma 5.2 (embedding) with prescribed targets.**  As `BKLO.exists_embedding`, but each new
vertex `v` of `A` is placed inside its own candidate set `Y v`.  The candidate sets of distinct new
vertices are disjoint and avoid the forbidden set `F` (which contains the images of the roots), and
each of them must meet the common neighbourhood of any `d` vertices of `G`. -/
theorem exists_embedding_target (G : SimpleGraph V) [DecidableRel G.Adj]
    {d b : ℕ} {A : Finset (Sym2 ℕ)} (hdeg : NatDegen d A) (hloop : ∀ e ∈ A, ¬ e.IsDiag)
    (htouch : Touches b A) (f₀ : ℕ → V) (F : Finset V) (Y : ℕ → Finset V)
    (hinj₀ : ∀ u ∈ supp A, ∀ v ∈ supp A, u < b → v < b → f₀ u = f₀ v → u = v)
    (hf₀F : ∀ v ∈ supp A, v < b → f₀ v ∈ F)
    (hYF : ∀ v ∈ supp A, b ≤ v → Disjoint (Y v) F)
    (hYdisj : ∀ u ∈ supp A, ∀ v ∈ supp A, b ≤ u → b ≤ v → u ≠ v → Disjoint (Y u) (Y v))
    (hroom : ∀ v ∈ supp A, b ≤ v → ∀ S : Finset V, S.card ≤ d →
      (commonNbrs G S ∩ Y v).Nonempty) :
    ∃ f : ℕ → V,
      (∀ v, v < b → f v = f₀ v) ∧
      (∀ v ∈ supp A, b ≤ v → f v ∈ Y v) ∧
      (∀ u ∈ supp A, ∀ v ∈ supp A, f u = f v → u = v) ∧
      (∀ e ∈ A, Sym2.map f e ∈ G.edgeFinset) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ supp A, v < N :=
    ⟨(supp A).sup id + 1, fun v hv => Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)⟩
  obtain ⟨f, hfb, hfY, hfinj, hfe⟩ :=
    embedTarget_aux G hdeg hloop htouch f₀ F Y hinj₀ hf₀F hYF hYdisj hroom N
  refine ⟨f, hfb, fun v hv hvb => hfY v hv hvb (hN v hv), fun u hu v hv =>
    hfinj u hu v hv (hN u hu) (hN v hv), fun e he => ?_⟩
  exact hfe e he fun v hv => hN v (mem_supp.2 ⟨_, he, hv⟩)

end BKLO
