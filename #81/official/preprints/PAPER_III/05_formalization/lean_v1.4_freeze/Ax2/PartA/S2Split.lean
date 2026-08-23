/-
  Part A — S2 decomposition (Minkowski–Weyl closedness of the triangle cone).

  S2 (`triCone_isClosed`) splits as:
  * S2b `isClosed_nonnegConeSpan` — a *simplicial* cone (nonnegative span of a linearly
    independent family) is closed.                                            [PROVED here]
  * S2a — Carathéodory for cones: every point of a finitely generated cone lies in the
    nonnegative span of a linearly independent subfamily.                     [to farm]
  * S2c — assembly: the cone is the finite union of simplicial cones, hence closed.

  S2b is the geometric heart and is fully proved: the linear map `c ↦ ∑ cᵢ • gᵢ` on a
  linearly independent family is injective with finite-dimensional domain, hence a closed
  embedding (`LinearMap.isClosedEmbedding_of_injective`), so it maps the (closed) nonnegative
  orthant onto a closed set.
-/
import Ax2.PartA.FarkasSplit

namespace Ax2

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **S2b — a simplicial cone is closed.** The nonnegative span of a linearly independent
finite family `g` is a closed subset. -/
theorem isClosed_nonnegConeSpan {ι : Type*} [Fintype ι] (g : ι → (Sym2 V → ℝ))
    (hg : LinearIndependent ℝ g) :
    IsClosed { f : Sym2 V → ℝ | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ f = ∑ i, c i • g i } := by
  classical
  -- the linear combination map
  let L : (ι → ℝ) →ₗ[ℝ] (Sym2 V → ℝ) :=
    { toFun := fun c => ∑ i, c i • g i
      map_add' := by
        intro x y
        show ∑ i, (x + y) i • g i = (∑ i, x i • g i) + ∑ i, y i • g i
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        show ∑ i, (r • x) i • g i = r • ∑ i, x i • g i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext i
    exact Fintype.linearIndependent_iff.mp hg c hc i
  have hemb := L.isClosedEmbedding_of_injective hker
  have horthant : IsClosed { c : ι → ℝ | ∀ i, 0 ≤ c i } := by
    have he : { c : ι → ℝ | ∀ i, 0 ≤ c i } = Set.univ.pi (fun _ => Set.Ici (0 : ℝ)) := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ici]
    rw [he]; exact isClosed_set_pi (fun i _ => isClosed_Ici)
  have himg : { f : Sym2 V → ℝ | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ f = ∑ i, c i • g i }
      = L '' { c : ι → ℝ | ∀ i, 0 ≤ c i } := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  rw [himg]
  exact hemb.isClosedMap _ horthant

/-- The `Finset`-indexed simplicial cone (nonneg combinations over a finite subset `s'`) is
closed when the subfamily is linearly independent — bridge from `isClosed_nonnegConeSpan`. -/
theorem isClosed_nonnegConeSpanFinset {ι : Type*} [DecidableEq ι] (g : ι → (Sym2 V → ℝ))
    (s' : Finset ι) (hli : LinearIndependent ℝ (fun i : s' => g i.1)) :
    IsClosed { f : Sym2 V → ℝ | ∃ c : ι → ℝ, (∀ i ∈ s', 0 ≤ c i) ∧ f = ∑ i ∈ s', c i • g i } := by
  classical
  have hcl := isClosed_nonnegConeSpan (fun i : s' => g i.1) hli
  convert hcl using 1
  ext f
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i.1, fun i => hc i.1 i.2, ?_⟩
    exact (Finset.sum_attach s' (fun i => c i • g i)).symm
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun t => if h : t ∈ s' then c ⟨t, h⟩ else 0, fun i hi => by simp [hi, hc], ?_⟩
    rw [← Finset.sum_attach s' (fun t => (if h : t ∈ s' then c ⟨t, h⟩ else 0) • g t)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.2, dif_pos]

-- NOTE: `triCone_isClosed` (S2) is proved directly in `Ax2.PartA.FarkasSplit` by sequential
-- closedness. The S2b lemmas above (`isClosed_nonnegConeSpan`, `isClosed_nonnegConeSpanFinset`)
-- are kept as reusable, axiom-clean building blocks (the Carathéodory-based alternative route).

end Ax2
