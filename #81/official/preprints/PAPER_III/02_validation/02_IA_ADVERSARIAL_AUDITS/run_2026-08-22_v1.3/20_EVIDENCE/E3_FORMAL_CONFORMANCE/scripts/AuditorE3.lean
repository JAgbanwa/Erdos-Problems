/-
INDEPENDENT AUDITOR QUERY -- Paper III v1.3, gate E3.

The request demands that the four canonical bridges be *independently validated, not just
compiled*, and compared "with an auditor-constructed bridge or direct unfolding proof".

So this file does not cite them. It restates the manuscript forms from the manuscript text,
proves them with the auditor's own arguments, and only then checks that the target's lemmas
say the same thing. Where the auditor's proof and the target's lemma coincide, the target's
lemma is confirmed semantically; where the auditor can prove a statement WITHOUT the
target's lemma, that is recorded too.

Manuscript statements used (PAPER_III_preprint_draft_v1.3.md):
  Thm 1.1   exists C, for all split G on n vertices: |E(G)| - 2 nu3(G) <= n^2/6 + C n
  Sec 2.2   a fractional triangle packing is a nonnegative weighting of triangles with
            total weight <= 1 through every edge; its maximum is nu3*(G). The dual is a
            fractional cover; LP duality gives equality of the two optima.
  Thm 2.1   nu3*(G) - nu3(G) = o(|V|^2) uniformly  (Haxell-Rodl/Yuster at H = K3)
  Thm 2.3   for every eps>0, every large triangle-divisible H with delta(H) >= (0.9+eps)|V|
            has a triangle decomposition
-/
import PaperIII.Theorem_1_1_Final
import PaperIII.PublicAPI
import PaperIII.CanonicalTrianglePacking

namespace AuditorE3

open Finset SimpleGraph

/-! ## 1. The manuscript forms, written by the auditor from the manuscript text. -/

/-- Manuscript Theorem 2.1 at `H = K3`, packing side, in eps/threshold normalization. -/
def ManuscriptAX1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      n₀ ≤ Fintype.card V →
      PaperIII.nu3Star G - (PaperIII.nu3 G : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- Manuscript Theorem 2.3, with the threshold written as `9/10` rather than `0.9`. -/
def ManuscriptAX2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      3 ∣ H.edgeFinset.card →
      (∀ v : V, Even (H.degree v)) →
      n₀ ≤ Fintype.card V →
      ((9 / 10 + ε) * (Fintype.card V : ℝ) ≤ (H.minDegree : ℝ)) →
      PaperIII.HasTriangleDecomposition H

/-! ## 2. The auditor's own bridge, proved without citing the target's four lemmas.

`no_clique_contains_nonedge` and `fracPacking_iff` are the auditor's own proofs, written for
the Paper III v1.2 residual audit and reused here deliberately: reusing the AUDITOR's
independent construction is what makes the comparison independent. -/

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A pair that is not an edge lies in no 3-clique. -/
theorem auditor_no_clique_contains_nonedge {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (t : Finset V) (ht : G.IsNClique 3 t) : ¬ ({u, v} : Finset V) ⊆ t := by
  intro hsub
  exact hnadj (ht.1 (hsub (by simp)) (hsub (by simp)) huv)

/-- **Auditor bridge.** The two fractional-packing predicates define the same feasible set.
The Nibble side imposes a capacity on EVERY two-element vertex set, including non-edges;
the extra constraints are vacuous. -/
theorem auditor_fracPacking_iff (w : Finset V → ℝ) :
    Nibble.YusterE.IsTriangleFracPacking G w ↔ PaperIII.IsFracPacking G w := by
  constructor
  · rintro ⟨h0, hsupp, hcap⟩
    refine ⟨h0, hsupp, ?_⟩
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have huv : u ≠ v := hadj.ne
      have hcard : ({u, v} : Finset V).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]
      have h := hcap {u, v} hcard
      have hfilter :
          (G.cliqueFinset 3).filter (fun t => ∀ x ∈ (s(u, v) : Sym2 V), x ∈ t)
            = (G.cliqueFinset 3).filter (fun t => ({u, v} : Finset V) ⊆ t) := by
        apply Finset.filter_congr
        intro t _
        simp [Finset.insert_subset_iff]
      rw [hfilter]
      exact h
  · rintro ⟨h0, hsupp, hcap⟩
    refine ⟨h0, hsupp, ?_⟩
    intro e hcard
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
    by_cases hadj : G.Adj u v
    · have he : (s(u, v) : Sym2 V) ∈ G.edgeFinset := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      have h := hcap _ he
      have hfilter :
          (G.cliqueFinset 3).filter (fun t => ({u, v} : Finset V) ⊆ t)
            = (G.cliqueFinset 3).filter (fun t => ∀ x ∈ (s(u, v) : Sym2 V), x ∈ t) := by
        apply Finset.filter_congr
        intro t _
        simp [Finset.insert_subset_iff]
      rw [hfilter]
      exact h
    · have hempty :
          (G.cliqueFinset 3).filter (fun t => ({u, v} : Finset V) ⊆ t) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
        exact auditor_no_clique_contains_nonedge G huv hadj t ht.1 ht.2
      rw [hempty, Finset.sum_empty]
      norm_num

/-- **Auditor bridge, optimum level**, from the auditor's predicate bridge. -/
theorem auditor_nu3Star_eq : Nibble.YusterE.nu3star G = PaperIII.nu3Star G := by
  rw [Nibble.YusterE.nu3star_eq_triangleFrac_sSup, PaperIII.nu3Star]
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (auditor_fracPacking_iff G w).mp hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (auditor_fracPacking_iff G w).mpr hw, rfl⟩

/-! ## 3. The target's four lemmas say what the auditor proves.

Each `example` below asserts the target's lemma statement and discharges it with the
AUDITOR's construction, so agreement is a theorem rather than a comparison of prose. -/

example (w : Finset V → ℝ) :
    PaperIII.IsFracPacking G w ↔ Nibble.YusterE.IsTriangleFracPacking G w :=
  (auditor_fracPacking_iff G w).symm

example : PaperIII.nu3Star G = Nibble.YusterE.nu3star G :=
  (auditor_nu3Star_eq G).symm

/-- The target's `tau3Star_eq_nu3Star`, reproved by the auditor: weak duality is proved in
the target, and the reverse direction goes through the auditor's optimum bridge plus the
target's finite LP strong duality instantiation. -/
theorem auditor_tau3Star_eq_nu3Star : PaperIII.tau3Star G = PaperIII.nu3Star G := by
  refine le_antisymm ?_ (PaperIII.nu3Star_le_tau3Star G)
  have htau : Nibble.AX1.tau3Star G = PaperIII.tau3Star G := rfl
  rw [← htau, ← auditor_nu3Star_eq G]
  exact Nibble.AX1.tau3Star_le_nu3star G

example : PaperIII.tau3Star G = PaperIII.nu3Star G := auditor_tau3Star_eq_nu3Star G

/-! ## 4. AX1 conformance, both directions, by the auditor. -/

theorem auditor_AX1_iff_manuscript : PaperIII.AX1Assumption ↔ ManuscriptAX1 := by
  constructor
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, ?_⟩
    intro W fW dW H dH hn
    letI : Fintype W := fW
    letI : DecidableEq W := dW
    letI : DecidableRel H.Adj := dH
    have hh := hn₀ W fW dW H dH hn
    rwa [auditor_tau3Star_eq_nu3Star H] at hh
  · intro h ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, ?_⟩
    intro W fW dW H dH hn
    letI : Fintype W := fW
    letI : DecidableEq W := dW
    letI : DecidableRel H.Adj := dH
    have hh := hn₀ W fW dW H dH hn
    rwa [← auditor_tau3Star_eq_nu3Star H] at hh

/-- Manuscript Theorem 2.1 at `H = K3` holds unconditionally in the development. -/
theorem auditor_manuscriptAX1_holds : ManuscriptAX1 :=
  (auditor_AX1_iff_manuscript).mp PaperIII.AX1_holds

/-! ## 5. AX2 conformance, and the decomposition predicate. -/

theorem auditor_AX2_implies_manuscript : PaperIII.AX2Assumption → ManuscriptAX2 := by
  intro h ε hε
  obtain ⟨n₀, hn₀⟩ := h ε hε
  refine ⟨n₀, ?_⟩
  intro W fW dW H dH hdvd hdeg hn hδ
  letI : Fintype W := fW
  letI : DecidableEq W := dW
  letI : DecidableRel H.Adj := dH
  refine hn₀ W fW dW H dH ?_ hdeg hn ?_
  · obtain ⟨k, hk⟩ := hdvd
    simp [hk, Nat.mul_mod_right]
  · rw [show (0.9 : ℝ) = 9 / 10 by norm_num]
    exact hδ

theorem auditor_manuscriptAX2_holds : ManuscriptAX2 :=
  auditor_AX2_implies_manuscript PaperIII.AX2_holds

/-- `HasTriangleDecomposition` is an exact edge decomposition into 3-cliques. -/
theorem auditor_decomposition_unfolds (H : SimpleGraph V) [DecidableRel H.Adj] :
    PaperIII.HasTriangleDecomposition H ↔
      ∃ T : Finset (Finset V),
        (∀ t ∈ T, H.IsNClique 3 t) ∧
        ∀ e ∈ H.edgeFinset, ∃! t, t ∈ T ∧ ∀ v ∈ e, v ∈ t :=
  Iff.rfl

/-! ## 6. The claim map: manuscript Theorem 1.1 through the formal chain. -/

#check @PaperIII.Theorem_1_1
#check @PaperIII.Corollary_1_2
#check @PaperIII.Theorem_1_1_of_AX1_AX2
#check @PaperIII.AX1_holds
#check @PaperIII.AX2_holds
#check @PaperIII.global_bound_from_eventual_high_degree
#check @PaperIII.eventual_bound_of_high_degree_of_AX1_AX2
#check @PaperIII.AX1Assumption
#check @PaperIII.AX2Assumption

#print axioms AuditorE3.auditor_fracPacking_iff
#print axioms AuditorE3.auditor_nu3Star_eq
#print axioms AuditorE3.auditor_tau3Star_eq_nu3Star
#print axioms AuditorE3.auditor_AX1_iff_manuscript
#print axioms AuditorE3.auditor_manuscriptAX1_holds
#print axioms AuditorE3.auditor_AX2_implies_manuscript
#print axioms AuditorE3.auditor_manuscriptAX2_holds
#print axioms AuditorE3.auditor_decomposition_unfolds

end AuditorE3
