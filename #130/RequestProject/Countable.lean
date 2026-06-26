import RequestProject.Defs
/-!
# Local countability and countable colourability (Section 2)
* `IntDistGraph.neighborSet_countable` — Lemma 2.1: every vertex has countable degree.
* `IntDistGraph.component_countable` — Lemma 2.2: every connected component is countable.
* `IntDistGraph.colorable_aleph0` — Theorem 1.2: `Γ(A)` admits a proper colouring with
  colours in `ℕ`, i.e. `χ(Γ(A)) ≤ ℵ₀`.
-/
open scoped BigOperators
open EuclideanGeometry
namespace IntDistGraph
variable {A : Set Plane}
/-
For a fixed center `P` and radius `m`, the set of points of `A` at distance exactly `m`
from `P` is finite: otherwise four of them would be concyclic.
-/
lemma circle_fiber_finite (hA4 : NoFourConcyclic A) (P : Plane) (m : ℝ) :
    {Q : A | dist (Q : Plane) P = m}.Finite := by
  contrapose! hA4;
  simp +decide [ NoFourConcyclic ];
  obtain ⟨ s, hs ⟩ := hA4.exists_subset_card_eq 4;
  refine' ⟨ s.image Subtype.val, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  · rw [ Finset.card_image_of_injective _ Subtype.coe_injective, hs.2 ];
  · exact ⟨ P, m, by aesop ⟩
/-
**Lemma 2.1 (Countable degree).** Every vertex of `Γ(A)` has countably many neighbours.
-/
lemma neighborSet_countable (hA4 : NoFourConcyclic A) (P : A) :
    ((IntDistGraph A).neighborSet P).Countable := by
  refine' Set.Countable.mono _ ( Set.countable_iUnion fun n : ℕ => Set.Finite.countable <| circle_fiber_finite hA4 P ( n : ℝ ) );
  intro Q hQ;
  simp +zetaDelta at *;
  exact hQ.2.imp fun n hn => by rw [ dist_comm, hn ] ;
/-- The BFS levels around a vertex `v`: `reachSet v 0 = {v}` and `reachSet v (n+1)` adds all
neighbours of points reached so far. -/
def reachSet (v : A) : ℕ → Set A
  | 0 => {v}
  | (n + 1) => reachSet v n ∪ ⋃ x ∈ reachSet v n, (IntDistGraph A).neighborSet x
lemma reachSet_countable (hA4 : NoFourConcyclic A) (v : A) (n : ℕ) :
    (reachSet v n).Countable := by
  induction' n with n ih;
  · exact Set.countable_singleton _;
  · exact Set.Countable.union ih ( Set.Countable.biUnion ih fun x hx => IntDistGraph.neighborSet_countable hA4 x )
/-
The set of vertices reachable from `v` is the union of all BFS levels.
-/
lemma reachable_iff_mem_iUnion (v w : A) :
    (IntDistGraph A).Reachable v w ↔ w ∈ ⋃ n, reachSet v n := by
  constructor <;> intro h;
  · -- By definition of reachability, there exists a walk from $v$ to $w$.
    obtain ⟨p, hp⟩ : ∃ p : (IntDistGraph A).Walk v w, True := by
      exact ⟨ h.some, trivial ⟩;
    have h_walk : ∀ {u w : A}, (IntDistGraph A).Walk u w → u ∈ ⋃ n, reachSet v n → w ∈ ⋃ n, reachSet v n := by
      intros u w p hu
      induction' p with u w p ih;
      · exact hu;
      · obtain ⟨ n, hn ⟩ := Set.mem_iUnion.mp hu;
        exact ‹p ∈ ⋃ n, reachSet v n → ih ∈ ⋃ n, reachSet v n› ( Set.mem_iUnion.mpr ⟨ n + 1, by exact Set.mem_union_right _ <| Set.mem_iUnion₂.mpr ⟨ w, hn, by tauto ⟩ ⟩ );
    exact h_walk p ( Set.mem_iUnion.mpr ⟨ 0, by simp +decide [ reachSet ] ⟩ );
  · simp +zetaDelta at *;
    obtain ⟨ n, hn ⟩ := h;
    induction' n with n ih generalizing w <;> simp_all +decide [ reachSet ];
    rcases hn with ( hn | ⟨ i, hi, hn, hw ⟩ ) <;> [ exact ih _ _ hn; exact SimpleGraph.Reachable.trans ( ih _ _ hn ) ( SimpleGraph.Adj.reachable hw ) ]
/-
**Lemma 2.2 (Countable components).** Every connected component of `Γ(A)` is countable.
-/
theorem component_countable (hA4 : NoFourConcyclic A) (v : A) :
    {w : A | (IntDistGraph A).Reachable v w}.Countable := by
  rw [ show { w | ( IntDistGraph A ).Reachable v w } = ⋃ n, reachSet v n from ?_ ];
  · exact Set.countable_iUnion fun n => IntDistGraph.reachSet_countable hA4 v n;
  · ext w; exact reachable_iff_mem_iUnion v w;
/-
**Theorem 1.2 (Countable upper bound for the chromatic number).**
`Γ(A)` admits a proper colouring with colours in `ℕ`; equivalently `χ(Γ(A)) ≤ ℵ₀`.
-/
theorem colorable_aleph0 (hA4 : NoFourConcyclic A) :
    Nonempty ((IntDistGraph A).Coloring ℕ) := by
  -- By definition of $component_countable$, there exists a coloring function $f$ such that $f(w) \neq f(w')$ for any adjacent vertices $w$ and $w'$.
  have h_colorable : ∀ (C : (IntDistGraph A).ConnectedComponent), ∃ f : C.supp → ℕ, Function.Injective f := by
    intro C;
    obtain ⟨r, hr⟩ : ∃ r : A, (IntDistGraph A).connectedComponentMk r = C := by
      exact C.exists_rep;
    have h_countable : Set.Countable (C.supp : Set A) := by
      convert component_countable hA4 r using 1;
      grind +suggestions;
    grind +suggestions;
  choose f hf using h_colorable;
  refine' ⟨ fun w => f ( ( IntDistGraph A ).connectedComponentMk w ) ⟨ w, _ ⟩, _ ⟩;
  all_goals norm_num [ Function.Injective ];
  grind +suggestions
end IntDistGraph
