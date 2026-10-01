module

public import RequestProject.AS.Counting
public import RequestProject.AS.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Lemma 3.5 of Alon–Shapira

> For every `l` and `γ` there exists `δ = δ_{3.5}(l, γ)` such that every (large enough) vertex set
> `U` of a graph contains disjoint sets `W₁, …, W_l` with `|Wᵢ| ≥ δ |U|`, all pairs `γ`-regular,
> and either all pairs of density at least `1/2`, or all pairs of density less than `1/2`.

We prove it by applying Lemma 3.8 (`AFKS.corollary_4_2`, whose output has *all* pairs regular)
to the subgraph induced on `U` with at least `4^l` parts, and then Ramsey's theorem to the
colouring of the pairs of parts according to whether their density is at least `1/2`.
-/

@[expose] public section

open Finset Fintype AFKS

open scoped Classical

universe u

namespace AlonShapira

section Transfer

variable {V W : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (e : W ↪ V)

theorem dens_comap (A B : Finset W) : dens (G.comap e) A B = dens G (A.map e) (B.map e) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [AFKS.dens]
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [AFKS.dens]
  have h1 := card_mul_card_mul_dens (G.comap e) hA hB
  have h2 := card_mul_card_mul_dens G (hA.map (f := e)) (hB.map (f := e))
  rw [Finset.card_map, Finset.card_map, Finset.sum_map] at h2
  simp only [Finset.sum_map] at h2
  have h3 : ∑ a ∈ A, ∑ b ∈ B, ind (G.comap e) a b = ∑ a ∈ A, ∑ b ∈ B, ind G (e a) (e b) := by
    unfold ind; simp [SimpleGraph.comap_adj]
  have hpos : (0 : ℝ) < #A * #B := by
    have := hA.card_pos; have := hB.card_pos; positivity
  have := h1.trans (h3.trans h2.symm)
  exact mul_left_cancel₀ hpos.ne' this

theorem IsRegularPair.map {γ : ℝ} {A B : Finset W} (h : IsRegularPair (G.comap e) γ A B) :
    IsRegularPair G γ (A.map e) (B.map e) := by
  intro A'' hA'' B'' hB'' hAc hBc
  obtain ⟨A', hA', rfl⟩ := Finset.subset_map_iff.1 hA''
  obtain ⟨B', hB', rfl⟩ := Finset.subset_map_iff.1 hB''
  rw [Finset.card_map, Finset.card_map] at hAc hBc
  have := h A' hA' B' hB' hAc hBc
  rwa [dens_comap, dens_comap] at this

end Transfer

/-- **Lemma 3.5 of Alon–Shapira.** For every `l` and `γ > 0` there are `0 < α ≤ 1/2` and `M` such
that every vertex set `U` with `|U| ≥ M` of a graph `G` contains pairwise disjoint sets
`W₁, …, W_l ⊆ U` with `|Wᵢ| ≥ α |U|`, all pairs `γ`-regular, and either all pairs of density
`≥ 1/2` (`c = true`) or all pairs of density `< 1/2` (`c = false`). -/
theorem lemma_3_5 (l : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ α > (0 : ℝ), α ≤ 1 / 2 ∧ ∃ M : ℕ, ∀ {V : Type u} (G : SimpleGraph V) [DecidableRel G.Adj]
      (U : Finset V), M ≤ #U → ∃ W : Fin l → Finset V,
        (∀ a, W a ⊆ U) ∧ (∀ a, α * #U ≤ #(W a)) ∧ (∀ a b, a ≠ b → Disjoint (W a) (W b)) ∧
        (∀ a b, a ≠ b → IsRegularPair G γ (W a) (W b)) ∧
        ∃ c : Bool, ∀ a b, a ≠ b → (1 / 2 ≤ dens G (W a) (W b) ↔ c = true) := by
  set E : ℕ → ℝ := fun _ => min γ (1 / 2) with hE
  obtain ⟨S, hS⟩ := corollary_4_2.{u} (4 ^ l) E (fun _ => by positivity)
    (fun _ => lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  refine ⟨1 / ((S : ℝ) + 2), by positivity, ?_, S, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [(S.cast_nonneg : (0 : ℝ) ≤ S)]
  intro V G _ U hU
  set e : U ↪ V := Function.Embedding.subtype _
  have hcard : S ≤ Fintype.card U := by rwa [Fintype.card_coe]
  obtain ⟨k, Vp, Up, hVdisj, -, -, hk, -, hUV, hUsize, -, hreg, -⟩ := hS (G.comap e) hcard
  let H : SimpleGraph (Fin k) :=
    { Adj := fun i j => i ≠ j ∧ 1 / 2 ≤ dens (G.comap e) (Up i) (Up j)
      symm := fun i j h => ⟨h.1.symm, by
        rw [AFKS.dens, SimpleGraph.edgeDensity_comm]; exact h.2⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  obtain ⟨c, g, hg⟩ := ramsey_fin l k hk H
  refine ⟨fun a => (Up (g a)).map e, fun a => ?_, fun a => ?_, fun a b hab => ?_,
    fun a b hab => ?_, c, fun a b hab => ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
    exact y.2
  · rw [Finset.card_map]
    have h1 := hUsize (g a)
    rw [Fintype.card_coe] at h1
    calc 1 / ((S : ℝ) + 2) * #U ≤ 1 / ((S : ℝ) + 2) * (S * #(Up (g a))) := by gcongr
      _ ≤ #(Up (g a)) := by
        rw [← mul_assoc]
        refine mul_le_of_le_one_left (by positivity) ?_
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  · rw [Finset.disjoint_map]
    exact (hVdisj _ _ (g.injective.ne hab)).mono (hUV _) (hUV _)
  · refine IsRegularPair.map G e ?_
    exact IsRegularPair.mono _ (min_le_left _ _) (hreg _ _ (g.injective.ne hab))
  · rw [← dens_comap]
    have := hg a b hab
    simp only [H] at this
    rw [← this]
    exact ⟨fun h => ⟨g.injective.ne hab, h⟩, fun h => h.2⟩

end AlonShapira
