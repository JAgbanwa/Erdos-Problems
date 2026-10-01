import PaperIV.RC01RootwiseReference
import PaperIV.RC01CanonicalFiberProfile
import PaperIV.RootedK3Counting
import PaperIV.RootedK4Counting

/-!
# RC01: literal K3 rooted-moment adapter

This module identifies the indexed root used by `RootedK3Counting` with the
coordinate-free root position used by `RC01CleanFiber`.  It is the first of
the two graph adapters needed to feed the existing moment estimates into the
exact root-dependent cleanup centre.
-/

namespace PaperIV.RC01RootedMomentAdapter

open Finset
open PaperIV.PatternCounting
open PaperIV.RC01Candidates
open PaperIV.RC01CleanFiber
open PaperIV.RC01RegularVolume
open PaperIV.RC01CanonicalFiberProfile
open PaperIV.RC01RootwiseReference
open PaperIV.PartitionBridge
open PaperIV.RegularityFormat
open PaperIV.RootedCountingBridge
open PaperIV.RootedK3Degree

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

noncomputable def rootPair3 (V : Fin 3 → Finset α) :
    Finset (Option (Finset α)) :=
  {some (V 0), some (V 1)}

theorem classOfPart_eq {δ : ℚ} (R : EqualRegularity G δ)
    {Q : Finset α} (hQ : Q ∈ R.parts) :
    univ.filter (fun v => partOf R v = some Q) = Q := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact mem_of_partOf_eq_some R
  · exact partOf_eq_some R hQ

theorem crossPair_rootPair3_eq_rootEdges3 {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (h01 : V 0 ≠ V 1) :
    crossPair G (partOf R) (rootPair3 V) = rootEdges3 G V := by
  rw [rootPair3, crossPair_pair_eq_interedges_image]
  · rw [classOfPart_eq R (hV 0), classOfPart_eq R (hV 1)]
    rfl
  · simpa using h01

theorem rootEdge_piece_K3_eq {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {φ : Fin 3 → α}
    (hφ : φ ∈ transversal G V patK3) :
    rootEdge (partOf R) (rootPair3 V) (piece φ) = rootEdge3 φ := by
  have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)
  have hφmem : ∀ i, φ i ∈ V i := (mem_transversal.1 hφ).1
  have hK : piece φ ∈ profileFiber G (partOf R) (regularPattern V) := by
    rw [← candidates_K3_eq_profileFiber R V hV hVinj]
    exact mem_candidates.2 ⟨φ, hφ, rfl⟩
  have hpair : rootEdge3 φ ∈ MixedRounding.pairs (piece φ) := by
    rw [rootEdge3, MixedRounding.mk_mem_pairs]
    exact ⟨apply_mem_piece φ 0, apply_mem_piece φ 1,
      (injective_of_mem_piFinset hdisj hφmem).ne (by decide)⟩
  have hroot := rootEdge_eq_of_mem_pairs hK hpair
  have hparts : PaperIV.PatternTransfer.partsOf (partOf R) (rootEdge3 φ)
      = rootPair3 V := by
    rw [rootEdge3, rootPair3]
    exact partsOf_eq_pair R (hV 0) (hV 1) (hφmem 0) (hφmem 1)
  rwa [hparts] at hroot

theorem physicalRootFiber3_eq_image {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) (e : Sym2 α) :
    fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) (rootPair3 V)) e
      = (fiber (transversal G V patK3) rootEdge3 e).image piece := by
  ext K
  constructor
  · intro hK
    rw [fiber, Finset.mem_filter] at hK
    have hKcand : K ∈ candidates G V patK3 := by
      rw [candidates_K3_eq_profileFiber R V hV hVinj]
      exact hK.1
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hKcand
    rw [Finset.mem_image]
    refine ⟨φ, ?_, rfl⟩
    rw [fiber, Finset.mem_filter]
    exact ⟨hφ, (rootEdge_piece_K3_eq R V hV hVinj hφ).symm.trans hK.2⟩
  · intro hK
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hK
    rw [fiber, Finset.mem_filter] at hφ ⊢
    constructor
    · rw [← candidates_K3_eq_profileFiber R V hV hVinj]
      exact mem_candidates.2 ⟨φ, hφ.1, rfl⟩
    · rw [rootEdge_piece_K3_eq R V hV hVinj hφ.1]
      exact hφ.2

theorem physicalRootFiber3_card_eq {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) (e : Sym2 α) :
    (fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) (rootPair3 V)) e).card
      = (fiber (transversal G V patK3) rootEdge3 e).card := by
  rw [physicalRootFiber3_eq_image R V hV hVinj]
  apply Finset.card_image_of_injOn
  intro φ hφ ψ hψ heq
  apply piece_injOn (G := G) (V := V)
    (fun i j hij => R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)) patK3
  · exact (Finset.mem_filter.1 hφ).1
  · exact (Finset.mem_filter.1 hψ).1
  · exact heq

/-- The indexed K3 second moment, transported literally to the physical
profile fibre at the coordinate root `{V 0, V 1}`. -/
theorem second_moment_physical_root3 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    ∑ e ∈ crossPair G (partOf R) (rootPair3 V),
        (rootCount G (partOf R) (regularPattern V) (rootPair3 V) e
          - rootProd3 G V * (t : ℚ)) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
  have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)
  rw [crossPair_rootPair3_eq_rootEdges3 R V hV (hVinj.ne (by decide))]
  have hmoment := second_moment_rooted3 (G := G) hδ hcard hdisj hdisc
  calc
    ∑ e ∈ rootEdges3 G V,
        (rootCount G (partOf R) (regularPattern V) (rootPair3 V) e
          - rootProd3 G V * (t : ℚ)) ^ 2
        = ∑ e ∈ rootEdges3 G V,
            (((fiber (transversal G V patK3) rootEdge3 e).card : ℚ)
              - rootProd3 G V * (t : ℚ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro e he
            rw [rootCount, physicalRootFiber3_card_eq R V hV hVinj]
    _ ≤ 11 * δ * (t : ℚ) ^ 4 := hmoment

/-- Recentring the transported K3 moment at the exact physical root mean. -/
theorem second_moment_exact_root3 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty) :
    ∑ e ∈ crossPair G (partOf R) (rootPair3 V),
        (rootCount G (partOf R) (regularPattern V) (rootPair3 V) e
          - rootwiseReference (G := G) (partOf R) (regularPattern V) (rootPair3 V)) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
  have hpqcard : (rootPair3 V).card = 2 := by
    simp [rootPair3, hVinj.ne (show (0 : Fin 3) ≠ 1 by decide)]
  have hpqsub : rootPair3 V ⊆ regularPattern V := by
    intro p hp
    simp only [rootPair3, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [regularPattern]
  exact second_moment_rootwiseReference_le (G := G) hpqcard hpqsub hne
    (rootProd3 G V * (t : ℚ)) (11 * δ * (t : ℚ) ^ 4)
    (second_moment_physical_root3 hδ R V hV hVinj hcard hdisc)

/-! ## The K4 coordinate root -/

noncomputable def rootPair4 (V : Fin 4 → Finset α) :
    Finset (Option (Finset α)) :=
  {some (V 0), some (V 1)}

theorem crossPair_rootPair4_eq_rootEdges {δ : ℚ}
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (h01 : V 0 ≠ V 1) :
    crossPair G (partOf R) (rootPair4 V) =
      PaperIV.RootedK4Degree.rootEdges G V := by
  rw [rootPair4, crossPair_pair_eq_interedges_image]
  · rw [classOfPart_eq R (hV 0), classOfPart_eq R (hV 1)]
    rfl
  · simpa using h01

theorem rootEdge_piece_K4_eq {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {φ : Fin 4 → α}
    (hφ : φ ∈ transversal G V patK4) :
    rootEdge (partOf R) (rootPair4 V) (piece φ) =
      PaperIV.RootedK4Degree.rootEdge φ := by
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)
  have hφmem : ∀ i, φ i ∈ V i := (mem_transversal.1 hφ).1
  have hK : piece φ ∈ profileFiber G (partOf R) (regularPattern V) := by
    rw [← candidates_K4_eq_profileFiber R V hV hVinj]
    exact mem_candidates.2 ⟨φ, hφ, rfl⟩
  have hpair : PaperIV.RootedK4Degree.rootEdge φ ∈
      MixedRounding.pairs (piece φ) := by
    rw [PaperIV.RootedK4Degree.rootEdge, MixedRounding.mk_mem_pairs]
    exact ⟨apply_mem_piece φ 0, apply_mem_piece φ 1,
      (injective_of_mem_piFinset hdisj hφmem).ne (by decide)⟩
  have hroot := rootEdge_eq_of_mem_pairs hK hpair
  have hparts : PaperIV.PatternTransfer.partsOf (partOf R)
      (PaperIV.RootedK4Degree.rootEdge φ) = rootPair4 V := by
    rw [PaperIV.RootedK4Degree.rootEdge, rootPair4]
    exact partsOf_eq_pair R (hV 0) (hV 1) (hφmem 0) (hφmem 1)
  rwa [hparts] at hroot

theorem physicalRootFiber4_eq_image {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) (e : Sym2 α) :
    fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) (rootPair4 V)) e
      = (fiber (transversal G V patK4)
          PaperIV.RootedK4Degree.rootEdge e).image piece := by
  ext K
  constructor
  · intro hK
    rw [fiber, Finset.mem_filter] at hK
    have hKcand : K ∈ candidates G V patK4 := by
      rw [candidates_K4_eq_profileFiber R V hV hVinj]
      exact hK.1
    obtain ⟨φ, hφ, rfl⟩ := mem_candidates.1 hKcand
    rw [Finset.mem_image]
    refine ⟨φ, ?_, rfl⟩
    rw [fiber, Finset.mem_filter]
    exact ⟨hφ, (rootEdge_piece_K4_eq R V hV hVinj hφ).symm.trans hK.2⟩
  · intro hK
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hK
    rw [fiber, Finset.mem_filter] at hφ ⊢
    constructor
    · rw [← candidates_K4_eq_profileFiber R V hV hVinj]
      exact mem_candidates.2 ⟨φ, hφ.1, rfl⟩
    · rw [rootEdge_piece_K4_eq R V hV hVinj hφ.1]
      exact hφ.2

theorem physicalRootFiber4_card_eq {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) (e : Sym2 α) :
    (fiber (profileFiber G (partOf R) (regularPattern V))
        (rootEdge (partOf R) (rootPair4 V)) e).card
      = (fiber (transversal G V patK4)
          PaperIV.RootedK4Degree.rootEdge e).card := by
  rw [physicalRootFiber4_eq_image R V hV hVinj]
  apply Finset.card_image_of_injOn
  intro φ hφ ψ hψ heq
  apply piece_injOn (G := G) (V := V)
    (fun i j hij => R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)) patK4
  · exact (Finset.mem_filter.1 hφ).1
  · exact (Finset.mem_filter.1 hψ).1
  · exact heq

theorem second_moment_physical_root4 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j)) :
    ∑ e ∈ crossPair G (partOf R) (rootPair4 V),
        (rootCount G (partOf R) (regularPattern V) (rootPair4 V) e
          - PaperIV.RootedK4Degree.rootProd G V * (t : ℚ) ^ 2) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
  have hdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (V i) (V j) := by
    intro i j hij
    exact R.pairwise_disjoint _ (hV i) _ (hV j) (hVinj.ne hij)
  rw [crossPair_rootPair4_eq_rootEdges R V hV (hVinj.ne (by decide))]
  have hmoment := PaperIV.RootedK4Degree.second_moment_rooted
    (G := G) hδ hcard hdisj hdisc
  calc
    ∑ e ∈ PaperIV.RootedK4Degree.rootEdges G V,
        (rootCount G (partOf R) (regularPattern V) (rootPair4 V) e
          - PaperIV.RootedK4Degree.rootProd G V * (t : ℚ) ^ 2) ^ 2
        = ∑ e ∈ PaperIV.RootedK4Degree.rootEdges G V,
            (((fiber (transversal G V patK4)
                PaperIV.RootedK4Degree.rootEdge e).card : ℚ)
              - PaperIV.RootedK4Degree.rootProd G V * (t : ℚ) ^ 2) ^ 2 := by
            apply Finset.sum_congr rfl
            intro e he
            rw [rootCount, physicalRootFiber4_card_eq R V hV hVinj]
    _ ≤ 23 * δ * (t : ℚ) ^ 6 := hmoment

theorem second_moment_exact_root4 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty) :
    ∑ e ∈ crossPair G (partOf R) (rootPair4 V),
        (rootCount G (partOf R) (regularPattern V) (rootPair4 V) e
          - rootwiseReference (G := G) (partOf R) (regularPattern V) (rootPair4 V)) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
  have hpqcard : (rootPair4 V).card = 2 := by
    simp [rootPair4, hVinj.ne (show (0 : Fin 4) ≠ 1 by decide)]
  have hpqsub : rootPair4 V ⊆ regularPattern V := by
    intro p hp
    simp only [rootPair4, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [regularPattern]
  exact second_moment_rootwiseReference_le (G := G) hpqcard hpqsub hne
    (PaperIV.RootedK4Degree.rootProd G V * (t : ℚ) ^ 2)
    (23 * δ * (t : ℚ) ^ 6)
    (second_moment_physical_root4 hδ R V hV hVinj hcard hdisc)

/-! ## Arbitrary physical root positions -/

theorem regularPattern_comp_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Finset α) (σ : Equiv.Perm ι) :
    regularPattern (V ∘ σ) = regularPattern V := by
  ext p
  simp only [regularPattern, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

theorem exists_perm3_of_ne {i j : Fin 3} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
  revert hij
  revert i j
  decide

theorem exists_perm4_of_ne {i j : Fin 4} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  revert hij
  revert i j
  decide

theorem exists_perm3_rootPair_eq (V : Fin 3 → Finset α)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    ∃ σ : Equiv.Perm (Fin 3), rootPair3 (V ∘ σ) = pq := by
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.1 hpqcard
  have hp : p ∈ regularPattern V := hpqsub (by rw [hpqeq]; simp)
  have hq : q ∈ regularPattern V := hpqsub (by rw [hpqeq]; simp)
  rw [regularPattern] at hp hq
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
  have hij : i ≠ j := by
    intro h
    apply hpq
    rw [h]
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm3_of_ne hij
  refine ⟨σ, ?_⟩
  rw [rootPair3, Function.comp_apply, Function.comp_apply, hσ0, hσ1]
  exact hpqeq.symm

theorem exists_perm4_rootPair_eq (V : Fin 4 → Finset α)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    ∃ σ : Equiv.Perm (Fin 4), rootPair4 (V ∘ σ) = pq := by
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.1 hpqcard
  have hp : p ∈ regularPattern V := hpqsub (by rw [hpqeq]; simp)
  have hq : q ∈ regularPattern V := hpqsub (by rw [hpqeq]; simp)
  rw [regularPattern] at hp hq
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
  have hij : i ≠ j := by
    intro h
    apply hpq
    rw [h]
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm4_of_ne hij
  refine ⟨σ, ?_⟩
  rw [rootPair4, Function.comp_apply, Function.comp_apply, hσ0, hσ1]
  exact hpqeq.symm

theorem second_moment_exact_any_root3 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    ∑ e ∈ crossPair G (partOf R) pq,
        (rootCount G (partOf R) (regularPattern V) pq e
          - rootwiseReference (G := G) (partOf R) (regularPattern V) pq) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
  obtain ⟨σ, hroot⟩ := exists_perm3_rootPair_eq V hpqcard hpqsub
  have hreg := regularPattern_comp_perm V σ
  have h := second_moment_exact_root3 hδ R (V ∘ σ)
    (fun i => hV (σ i)) (hVinj.comp σ.injective)
    (fun i => hcard (σ i))
    (fun i j hij => hdisc (σ i) (σ j) (σ.injective.ne hij))
    (by simpa [hreg] using hne)
  rwa [hreg, hroot] at h

theorem second_moment_exact_any_root4 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    ∑ e ∈ crossPair G (partOf R) pq,
        (rootCount G (partOf R) (regularPattern V) pq e
          - rootwiseReference (G := G) (partOf R) (regularPattern V) pq) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
  obtain ⟨σ, hroot⟩ := exists_perm4_rootPair_eq V hpqcard hpqsub
  have hreg := regularPattern_comp_perm V σ
  have h := second_moment_exact_root4 hδ R (V ∘ σ)
    (fun i => hV (σ i)) (hVinj.comp σ.injective)
    (fun i => hcard (σ i))
    (fun i j hij => hdisc (σ i) (σ j) (σ.injective.ne hij))
    (by simpa [hreg] using hne)
  rwa [hreg, hroot] at h

theorem badRoots_mul_sq_le_any_root3 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 3 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 3, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty)
    {u : ℚ} (hu : 0 < u) {pq : Finset (Option (Finset α))}
    (hpq : pq ∈ (regularPattern V).powersetCard 2) :
    ((badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq).card : ℚ) *
        (u * rootwiseReference (G := G) (partOf R) (regularPattern V) pq) ^ 2
      ≤ 11 * δ * (t : ℚ) ^ 4 := by
  rw [Finset.mem_powersetCard] at hpq
  exact PaperIV.RC01DeviationCleanup.card_deviationBad_mul_le
    (crossPair G (partOf R) pq)
    (rootCount G (partOf R) (regularPattern V) pq)
    (rootwiseReference (G := G) (partOf R) (regularPattern V) pq)
    u (11 * δ * (t : ℚ) ^ 4) hu
    (rootwiseReference_pos_of_profileFiber_nonempty_active
      (G := G) hpq.2 hpq.1 hne)
    (second_moment_exact_any_root3 hδ R V hV hVinj hcard hdisc hne hpq.2 hpq.1)

theorem badRoots_mul_sq_le_any_root4 {δ : ℚ} (hδ : 0 ≤ δ)
    (R : EqualRegularity G δ) (V : Fin 4 → Finset α)
    (hV : ∀ i, V i ∈ R.parts) (hVinj : Function.Injective V) {t : ℕ}
    (hcard : ∀ i, (V i).card = t)
    (hdisc : ∀ i j : Fin 4, i ≠ j →
      PaperIV.OneStepEstimate.DiscrepAt G δ
        (G.edgeDensity (V i) (V j)) (V i) (V j))
    (hne : (profileFiber G (partOf R) (regularPattern V)).Nonempty)
    {u : ℚ} (hu : 0 < u) {pq : Finset (Option (Finset α))}
    (hpq : pq ∈ (regularPattern V).powersetCard 2) :
    ((badRoots G (partOf R)
        (rootwiseReference (G := G) (partOf R)) u (regularPattern V) pq).card : ℚ) *
        (u * rootwiseReference (G := G) (partOf R) (regularPattern V) pq) ^ 2
      ≤ 23 * δ * (t : ℚ) ^ 6 := by
  rw [Finset.mem_powersetCard] at hpq
  exact PaperIV.RC01DeviationCleanup.card_deviationBad_mul_le
    (crossPair G (partOf R) pq)
    (rootCount G (partOf R) (regularPattern V) pq)
    (rootwiseReference (G := G) (partOf R) (regularPattern V) pq)
    u (23 * δ * (t : ℚ) ^ 6) hu
    (rootwiseReference_pos_of_profileFiber_nonempty_active
      (G := G) hpq.2 hpq.1 hne)
    (second_moment_exact_any_root4 hδ R V hV hVinj hcard hdisc hne hpq.2 hpq.1)

theorem pairScale_le_sq_any_root3 {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {t : ℕ} (ht : 1 ≤ t)
    (hcard : ∀ i, (V i).card = t)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    pairScale (G := G) (partOf R) pq ≤ (t : ℚ) ^ 2 := by
  obtain ⟨σ, hroot⟩ := exists_perm3_rootPair_eq V hpqcard hpqsub
  rw [← hroot, pairScale, max_le_iff]
  constructor
  · norm_num
    exact_mod_cast ht
  · rw [crossPair_rootPair3_eq_rootEdges3 R (V ∘ σ)
      (fun i => hV (σ i)) ((hVinj.comp σ.injective).ne (by decide))]
    have hdisj : Disjoint ((V ∘ σ) 0) ((V ∘ σ) 1) :=
      R.pairwise_disjoint _ (hV (σ 0)) _ (hV (σ 1))
        ((hVinj.comp σ.injective).ne (by decide))
    have hnat : (rootEdges3 G (V ∘ σ)).card ≤ t ^ 2 := by
      calc
        (rootEdges3 G (V ∘ σ)).card
            = (G.interedges ((V ∘ σ) 0) ((V ∘ σ) 1)).card :=
                card_rootEdges3 hdisj
        _ ≤ ((V ∘ σ) 0).card * ((V ∘ σ) 1).card :=
              G.card_interedges_le_mul _ _
        _ = t ^ 2 := by
              simp [Function.comp_apply, hcard, pow_two]
    exact_mod_cast hnat

theorem pairScale_le_sq_any_root4 {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {t : ℕ} (ht : 1 ≤ t)
    (hcard : ∀ i, (V i).card = t)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) :
    pairScale (G := G) (partOf R) pq ≤ (t : ℚ) ^ 2 := by
  obtain ⟨σ, hroot⟩ := exists_perm4_rootPair_eq V hpqcard hpqsub
  rw [← hroot, pairScale, max_le_iff]
  constructor
  · norm_num
    exact_mod_cast ht
  · rw [crossPair_rootPair4_eq_rootEdges R (V ∘ σ)
      (fun i => hV (σ i)) ((hVinj.comp σ.injective).ne (by decide))]
    have hdisj : Disjoint ((V ∘ σ) 0) ((V ∘ σ) 1) :=
      R.pairwise_disjoint _ (hV (σ 0)) _ (hV (σ 1))
        ((hVinj.comp σ.injective).ne (by decide))
    have hnat : (PaperIV.RootedK4Degree.rootEdges G (V ∘ σ)).card ≤ t ^ 2 := by
      calc
        (PaperIV.RootedK4Degree.rootEdges G (V ∘ σ)).card
            = (G.interedges ((V ∘ σ) 0) ((V ∘ σ) 1)).card :=
                PaperIV.RootedK4Degree.card_rootEdges hdisj
        _ ≤ ((V ∘ σ) 0).card * ((V ∘ σ) 1).card :=
              G.card_interedges_le_mul _ _
        _ = t ^ 2 := by
              simp [Function.comp_apply, hcard, pow_two]
    exact_mod_cast hnat

/-! ## Literal upper bounds for a rooted fibre

Fixing a physical root fixes two coordinates.  Hence a rooted triangle fibre
injects into its third part, while a rooted `K4` fibre injects into the product
of its two remaining parts.  These are the type-specific scales used by the
cleanup ledger (`t` and `t²`, respectively). -/

theorem indexed_rootFiber3_card_le {V : Fin 3 → Finset α}
    (hdisj : Disjoint (V 0) (V 1)) (e : Sym2 α) :
    (fiber (transversal G V patK3) rootEdge3 e).card ≤ (V 2).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun φ => φ 2) ?_ ?_
  · intro φ hφ
    exact (mem_transversal.1 (Finset.mem_filter.1 hφ).1).1 2
  · intro φ hφ ψ hψ h2
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ hψ
    have hmφ := (mem_transversal.1 hφ.1).1
    have hmψ := (mem_transversal.1 hψ.1).1
    have hroot : rootEdge3 φ = rootEdge3 ψ := hφ.2.trans hψ.2.symm
    have h01 : φ 0 = ψ 0 ∧ φ 1 = ψ 1 := by
      rw [rootEdge3, rootEdge3, Sym2.eq_iff] at hroot
      rcases hroot with hroot | hroot
      · exact hroot
      · exact absurd (hroot.1 ▸ hmφ 0)
          (Finset.disjoint_right.1 hdisj (hmψ 1))
    funext i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2

theorem indexed_rootFiber4_card_le {V : Fin 4 → Finset α}
    (hdisj : Disjoint (V 0) (V 1)) (e : Sym2 α) :
    (fiber (transversal G V patK4) PaperIV.RootedK4Degree.rootEdge e).card
      ≤ (V 2 ×ˢ V 3).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun φ => (φ 2, φ 3)) ?_ ?_
  · intro φ hφ
    have hm := (mem_transversal.1 (Finset.mem_filter.1 hφ).1).1
    exact Finset.mem_product.2 ⟨hm 2, hm 3⟩
  · intro φ hφ ψ hψ h23
    rw [Finset.mem_coe, fiber, Finset.mem_filter] at hφ hψ
    have hmφ := (mem_transversal.1 hφ.1).1
    have hmψ := (mem_transversal.1 hψ.1).1
    have hroot : PaperIV.RootedK4Degree.rootEdge φ =
        PaperIV.RootedK4Degree.rootEdge ψ := hφ.2.trans hψ.2.symm
    obtain ⟨h0, h1⟩ := PaperIV.RootedK4Degree.eq_of_rootEdge_eq
      hdisj hmφ hmψ hroot
    have h2 : φ 2 = ψ 2 := congrArg Prod.fst h23
    have h3 : φ 3 = ψ 3 := congrArg Prod.snd h23
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem physical_rootFiber3_card_le_any_root {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 3 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {t : ℕ} (hcard : ∀ i, (V i).card = t)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) (e : Sym2 α) :
    (fiber (profileFiber G (partOf R) (regularPattern V))
      (rootEdge (partOf R) pq) e).card ≤ t := by
  obtain ⟨σ, hroot⟩ := exists_perm3_rootPair_eq V hpqcard hpqsub
  have hdisj : Disjoint ((V ∘ σ) 0) ((V ∘ σ) 1) :=
    R.pairwise_disjoint _ (hV (σ 0)) _ (hV (σ 1))
      ((hVinj.comp σ.injective).ne (by decide))
  rw [← hroot, ← regularPattern_comp_perm V σ,
    physicalRootFiber3_card_eq R (V ∘ σ) (fun i => hV (σ i))
      (hVinj.comp σ.injective)]
  exact (indexed_rootFiber3_card_le (G := G) hdisj e).trans_eq
    (by simp [Function.comp_apply, hcard])

theorem physical_rootFiber4_card_le_any_root {δ : ℚ} (R : EqualRegularity G δ)
    (V : Fin 4 → Finset α) (hV : ∀ i, V i ∈ R.parts)
    (hVinj : Function.Injective V) {t : ℕ} (hcard : ∀ i, (V i).card = t)
    {pq : Finset (Option (Finset α))}
    (hpqcard : pq.card = 2) (hpqsub : pq ⊆ regularPattern V) (e : Sym2 α) :
    (fiber (profileFiber G (partOf R) (regularPattern V))
      (rootEdge (partOf R) pq) e).card ≤ t ^ 2 := by
  obtain ⟨σ, hroot⟩ := exists_perm4_rootPair_eq V hpqcard hpqsub
  have hdisj : Disjoint ((V ∘ σ) 0) ((V ∘ σ) 1) :=
    R.pairwise_disjoint _ (hV (σ 0)) _ (hV (σ 1))
      ((hVinj.comp σ.injective).ne (by decide))
  rw [← hroot, ← regularPattern_comp_perm V σ,
    physicalRootFiber4_card_eq R (V ∘ σ) (fun i => hV (σ i))
      (hVinj.comp σ.injective)]
  calc
    (fiber (transversal G (V ∘ ⇑σ) patK4)
      PaperIV.RootedK4Degree.rootEdge e).card
        ≤ (((V ∘ σ) 2) ×ˢ ((V ∘ σ) 3)).card :=
          indexed_rootFiber4_card_le hdisj e
    _ = t ^ 2 := by simp [Function.comp_apply, hcard, pow_two]

end PaperIV.RC01RootedMomentAdapter
