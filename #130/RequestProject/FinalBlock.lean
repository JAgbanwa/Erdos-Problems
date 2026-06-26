import RequestProject.Defs
import RequestProject.Countable
set_option maxHeartbeats 4000000
/-!
# The finite-block criterion (Section 4)
This file formalises Theorem 1.4, the equivalence between
* (a) the existence of an infinite general-position set `A` with `χ(Γ(A)) = ℵ₀` (equivalently,
  `Γ(A)` is not `n`-colourable for any finite `n`), and
* (b) the existence, for every `k`, of a finite general-position set whose integer-distance graph
  has chromatic number at least `k` (i.e. finite integer-distance graphs of unbounded chromatic
  number).
The **forward** direction (a) ⇒ (b) is proved using the De Bruijn–Erdős compactness theorem
(`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`).
The **converse** (b) ⇒ (a) rests on the generic-separation Lemma 4.2 (`generic_separation`),
an additional finite-realisation/Baire-category input which is stated faithfully here; its proof
and the disjoint-block construction it powers are recorded as `sorry` (the deep analytic content
that the paper isolates as a separate problem).
-/
open scoped BigOperators
open EuclideanGeometry
namespace IntDistGraph
/-
**Lemma 4.1 / De Bruijn–Erdős, applied form.** If the integer-distance graph of `A` is not
`n`-colourable, then some finite subset `B ⊆ A` already has a non-`n`-colourable integer-distance
graph.
-/
lemma exists_finite_subset_not_colorable {A : Set Plane} {n : ℕ}
    (h : ¬ (IntDistGraph A).Colorable n) :
    ∃ B : Finset Plane, ↑B ⊆ A ∧ ¬ (IntDistGraph (↑B : Set Plane)).Colorable n := by
  contrapose! h with h_contra; simp_all +decide [ SimpleGraph.Colorable ] ;
  have h_subgraph_colorable : ∀ (G' : (IntDistGraph A).Subgraph), G'.verts.Finite → Nonempty (G'.coe.Coloring (Fin n)) := by
    intro G' hG'_finite
    obtain ⟨B, hB⟩ : ∃ B : Finset Plane, (B : Set Plane) = Subtype.val '' G'.verts := by
      exact ⟨ hG'_finite.toFinset.image Subtype.val, by aesop ⟩;
    have hB_subset : (B : Set Plane) ⊆ A := by
      exact hB.symm ▸ Set.image_subset_iff.mpr fun x hx => x.2
    obtain ⟨c, hc⟩ : ∃ c : (IntDistGraph B).Coloring (Fin n), True := by
      exact ⟨ h_contra B hB_subset |> Classical.choice, trivial ⟩
    have hB_adj : ∀ (a b : ↥G'.verts), G'.coe.Adj a b → (IntDistGraph B).Adj ⟨a.val, by
      aesop⟩ ⟨b.val, by
      aesop⟩ := by
      intros a b hab
      generalize_proofs at *;
      have := G'.adj_sub hab; simp_all +decide [ IntDistGraph ] ;
    generalize_proofs at *;
    refine' ⟨ ⟨ fun x => c ⟨ x.val, by
      exact hB.symm.subset <| Set.mem_image_of_mem _ x.2 ⟩, _ ⟩ ⟩
    generalize_proofs at *;
    exact fun { a b } hab => c.valid ( hB_adj a b hab );
  apply Classical.byContradiction
  intro h_not_colorable;
  convert SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom ( G := IntDistGraph A ) ( F := ⊤ ) ?_;
  any_goals exact Fin n;
  · aesop;
  · infer_instance;
  · exact fun G' hG' => Classical.choice ( h_subgraph_colorable G' hG' )
/-
**Theorem 1.4, forward direction (a) ⇒ (b).** If `Γ(A)` is not `n`-colourable for any finite
`n`, then for every `k` there is a finite general-position subset of `A` whose integer-distance
graph has chromatic number at least `k`.
-/
theorem finite_block_forward {A : Set Plane}
    (hA3 : NoThreeCollinear A) (hA4 : NoFourConcyclic A)
    (hχ : ∀ n : ℕ, ¬ (IntDistGraph A).Colorable n) :
    ∀ k : ℕ, ∃ B : Finset Plane, NoThreeCollinear (↑B : Set Plane) ∧
      NoFourConcyclic (↑B : Set Plane) ∧ (k : ℕ∞) ≤ (IntDistGraph (↑B : Set Plane)).chromaticNumber := by
  intro k
  obtain ⟨B, hB⟩ : ∃ B : Finset Plane, ((↑B : Set Plane) ⊆ A ∧ ¬(IntDistGraph (↑B : Set Plane)).Colorable k) := exists_finite_subset_not_colorable (hχ k);
  refine' ⟨ B, _, _, _ ⟩;
  · intro s hs hs' hs''; exact hA3 s ( hs.trans hB.1 ) hs' hs'';
  · exact fun s hs hs' hs'' => hA4 s ( hs.trans hB.1 ) hs' hs'';
  · refine' le_csInf _ _ <;> norm_num;
    · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
    · exact fun n hn => le_of_not_gt fun h => hB.2 <| hn.mono h.le
/-- **Lemma 4.2 (Generic separation of one finite block).** Given finite general-position sets
`F` and `B` and any radius `R`, there is a rigid motion `T` (an isometry of the plane) placing a
copy of `B` far from the origin, keeping the union in general position, and creating no integer
distances between `F` and the moved copy of `B`. The internal distances inside `B` are preserved
because `T` is an isometry.
This is the additional finite-realisation input isolated by the paper; its (Baire-category) proof
is left as `sorry`. -/
lemma generic_separation (F B : Finset Plane)
    (hF3 : NoThreeCollinear (↑F : Set Plane)) (hF4 : NoFourConcyclic (↑F : Set Plane))
    (hB3 : NoThreeCollinear (↑B : Set Plane)) (hB4 : NoFourConcyclic (↑B : Set Plane))
    (R : ℝ) :
    ∃ T : Plane ≃ᵢ Plane,
      (∀ x ∈ B, R < ‖T x‖) ∧
      NoThreeCollinear (↑F ∪ T '' ↑B : Set Plane) ∧
      NoFourConcyclic (↑F ∪ T '' ↑B : Set Plane) ∧
      (∀ P ∈ F, ∀ Q ∈ B, ¬ IsIntDist P (T Q)) := by
  sorry
/-- **Theorem 1.4, converse direction (b) ⇒ (a).** If for every `k` there is a finite
general-position set whose integer-distance graph has chromatic number at least `k`, then there is
an infinite general-position set `A` whose integer-distance graph is not `n`-colourable for any
finite `n` (so `χ(Γ(A)) = ℵ₀`).
This is obtained by the disjoint-block construction powered by `generic_separation`; its full
formalisation is recorded as `sorry`. -/
theorem finite_block_converse
    (hb : ∀ k : ℕ, ∃ B : Finset Plane, NoThreeCollinear (↑B : Set Plane) ∧
      NoFourConcyclic (↑B : Set Plane) ∧ (k : ℕ∞) ≤ (IntDistGraph (↑B : Set Plane)).chromaticNumber) :
    ∃ A : Set Plane, A.Infinite ∧ NoThreeCollinear A ∧ NoFourConcyclic A ∧
      ∀ n : ℕ, ¬ (IntDistGraph A).Colorable n := by
  sorry
/-- **Theorem 1.4 (Finite-block criterion for infinite chromatic number).** For general-position
sets, the existence of an infinite example with `χ = ℵ₀` is equivalent to the existence of finite
examples of unbounded chromatic number. -/
theorem finite_block_criterion :
    (∃ A : Set Plane, A.Infinite ∧ NoThreeCollinear A ∧ NoFourConcyclic A ∧
        ∀ n : ℕ, ¬ (IntDistGraph A).Colorable n)
    ↔
    (∀ k : ℕ, ∃ B : Finset Plane, NoThreeCollinear (↑B : Set Plane) ∧
        NoFourConcyclic (↑B : Set Plane) ∧
        (k : ℕ∞) ≤ (IntDistGraph (↑B : Set Plane)).chromaticNumber) := by
  constructor
  · rintro ⟨A, _, hA3, hA4, hχ⟩
    exact finite_block_forward hA3 hA4 hχ
  · intro hb
    obtain ⟨A, _, hA3, hA4, hχ⟩ := finite_block_converse hb
    exact ⟨A, ‹_›, hA3, hA4, hχ⟩
end IntDistGraph
