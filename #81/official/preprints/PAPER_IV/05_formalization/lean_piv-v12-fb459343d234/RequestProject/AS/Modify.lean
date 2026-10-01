module

public import RequestProject.AS.EditDist
public import RequestProject.AFKS.MeanSquare
import Mathlib.Tactic.Bound

/-!
# The modified graph `G̃` of the proof of Lemma 4.2 and its edit distance to `G`

Given a partition of `Fin n` into clusters (`cl v` is the cluster of `v`), a vertex colouring
`c` and a symmetric edge colouring `col` of the clusters, `modGraph` makes every cluster a clique
(if `c i = true`) or an independent set (if `c i = false`), makes the pair of clusters `(i, j)`
complete if `col i j = 1`, empty if `col i j = 0`, and leaves it unchanged if `col i j = 2`.

`two_mul_editDist_modGraph_le` bounds the number of edits.
-/

@[expose] public section

open Finset AFKS

open scoped Classical

namespace AlonShapira

variable {n k : ℕ}

/-- The modified graph `G̃`. -/
def modGraph (G : SimpleGraph (Fin n)) (cl : Fin n → Fin k) (c : Fin k → Bool)
    (col : Fin k → Fin k → Fin 3) (hcol : ∀ i j, col i j = col j i) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (if cl u = cl v then c (cl u) = true else
    (col (cl u) (cl v) = 1 ∨ (col (cl u) (cl v) = 2 ∧ G.Adj u v)))
  symm := fun u v h => ⟨h.1.symm, by
    obtain ⟨-, h⟩ := h
    by_cases e : cl u = cl v
    · rw [if_pos e] at h; rw [if_pos e.symm, ← e]; exact h
    · rw [if_neg e] at h; rw [if_neg (Ne.symm e), hcol]; exact h.imp id fun h' => ⟨h'.1, h'.2.symm⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- **Edit distance of `G̃` (Claim 5.4 of Alon–Shapira), abstract form.** If every cluster has at
most `L` vertices, and for every pair of distinct clusters `(i, j)` which is not `bad`, the colour
`0` is only used when `d(Vᵢ, Vⱼ) ≤ θ` and the colour `1` only when `d(Vᵢ, Vⱼ) ≥ 1 - θ`, then
`2 · editDist(G, G̃) ≤ L n + #(bad ordered pairs) L² + θ n²`. -/
theorem two_mul_editDist_modGraph_le (G : SimpleGraph (Fin n)) (cl : Fin n → Fin k)
    (Vp : Fin k → Finset (Fin n)) (hVp : ∀ i u, u ∈ Vp i ↔ cl u = i) (c : Fin k → Bool)
    (col : Fin k → Fin k → Fin 3) (hcs : ∀ i j, col i j = col j i) (bad : Fin k → Fin k → Prop)
    {L θ : ℝ} (hL : ∀ i, (#(Vp i) : ℝ) ≤ L) (hθ : 0 ≤ θ)
    (hcol : ∀ i j, i ≠ j → ¬ bad i j →
      (col i j = 0 → dens G (Vp i) (Vp j) ≤ θ) ∧ (col i j = 1 → 1 - θ ≤ dens G (Vp i) (Vp j))) :
    2 * (editDist G (modGraph G cl c col hcs) : ℝ) ≤
      L * n + (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) * L ^ 2 + θ * (n : ℝ) ^ 2 := by
  set G' := modGraph G cl c col hcs
  have hsplit : ∀ g : Fin n → ℝ, ∑ u, g u = ∑ i, ∑ u ∈ Vp i, g u := by
    intro g
    rw [← Finset.sum_fiberwise univ cl g]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext u; simp [hVp]
  have hn : ∑ i, (#(Vp i) : ℝ) = n := by
    have := hsplit fun _ => 1
    simpa using this.symm
  have hL0 : ∀ i, 0 ≤ L := fun i => le_trans (by positivity) (hL i)
  set bound : Fin k → Fin k → ℝ := fun i j =>
    (if i = j then L * #(Vp i) else 0) + (if i ≠ j ∧ bad i j then L ^ 2 else 0) +
      θ * #(Vp i) * #(Vp j) with hbound
  have hblock : ∀ i j, ∑ u ∈ Vp i, ∑ v ∈ Vp j, disagree G G' u v ≤ bound i j := by
    intro i j
    have hdis01 : ∀ u v, 0 ≤ disagree G G' u v ∧ disagree G G' u v ≤ 1 := fun u v => by
      unfold disagree; split_ifs <;> norm_num
    have htriv : ∑ u ∈ Vp i, ∑ v ∈ Vp j, disagree G G' u v ≤ #(Vp i) * #(Vp j) := by
      calc ∑ u ∈ Vp i, ∑ v ∈ Vp j, disagree G G' u v ≤ ∑ u ∈ Vp i, ∑ v ∈ Vp j, (1 : ℝ) :=
            Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (hdis01 u v).2
        _ = #(Vp i) * #(Vp j) := by simp
    have hA : 0 ≤ (if i = j then L * #(Vp i) else 0) := by
      split_ifs
      · exact mul_nonneg (hL0 i) (Nat.cast_nonneg _)
      · exact le_rfl
    have hB : 0 ≤ (if i ≠ j ∧ bad i j then L ^ 2 else 0) := by split_ifs <;> positivity
    have hC : 0 ≤ θ * #(Vp i) * #(Vp j) := by positivity
    by_cases hij : i = j
    · subst hij
      have : (#(Vp i) : ℝ) * #(Vp i) ≤ L * #(Vp i) := by gcongr; exact hL i
      have e : bound i i = L * #(Vp i) + θ * #(Vp i) * #(Vp i) := by simp [hbound]
      rw [e]
      linarith
    by_cases hb : bad i j
    · have : (#(Vp i) : ℝ) * #(Vp j) ≤ L ^ 2 := by
        rw [sq]; exact mul_le_mul (hL i) (hL j) (by positivity) (hL0 i)
      simp only [hbound, if_neg hij, if_pos (And.intro hij hb)]
      linarith
    -- a good pair: compare with `θ |Vᵢ| |Vⱼ|`
    have hcl : ∀ u ∈ Vp i, ∀ v ∈ Vp j, cl u = i ∧ cl v = j := fun u hu v hv =>
      ⟨(hVp i u).1 hu, (hVp j v).1 hv⟩
    have key : ∑ u ∈ Vp i, ∑ v ∈ Vp j, disagree G G' u v ≤ θ * #(Vp i) * #(Vp j) := by
      rcases (Vp i).eq_empty_or_nonempty with hi | hi
      · simp [hi]
      rcases (Vp j).eq_empty_or_nonempty with hj | hj
      · simp [hj]
      have hG' : ∀ u ∈ Vp i, ∀ v ∈ Vp j, (G'.Adj u v ↔ u ≠ v ∧ (col i j = 1 ∨
          (col i j = 2 ∧ G.Adj u v))) := by
        intro u hu v hv
        obtain ⟨h1, h2⟩ := hcl u hu v hv
        show (u ≠ v ∧ _) ↔ _
        rw [if_neg (by rw [h1, h2]; exact hij), h1, h2]
      have hne : ∀ u ∈ Vp i, ∀ v ∈ Vp j, u ≠ v := by
        intro u hu v hv h
        subst h
        exact hij (((hcl u hu u hv).1).symm.trans (hcl u hu u hv).2)
      have hd := card_mul_card_mul_dens G hi hj
      obtain ⟨h0, h1⟩ := hcol i j hij hb
      have hc3 : col i j = 0 ∨ col i j = 1 ∨ col i j = 2 := by
        rcases col i j with ⟨_ | _ | _ | m, hm⟩
        · left; rfl
        · right; left; rfl
        · right; right; rfl
        · omega
      rcases hc3 with hc | hc | hc
      · -- `G̃` is empty on the pair
        have : ∀ u ∈ Vp i, ∀ v ∈ Vp j, disagree G G' u v = ind G u v := by
          intro u hu v hv
          have := hG' u hu v hv
          rw [hc] at this
          unfold disagree ind
          by_cases hG : G.Adj u v
          · rw [if_neg (by simp [this, hG]), if_pos hG]
          · rw [if_pos (by simp [this, hG]), if_neg hG]
        rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => this u hu v hv,
          ← hd]
        have := h0 hc
        have : (0 : ℝ) ≤ #(Vp i) * #(Vp j) := by positivity
        nlinarith
      · -- `G̃` is complete on the pair
        have : ∀ u ∈ Vp i, ∀ v ∈ Vp j, disagree G G' u v = 1 - ind G u v := by
          intro u hu v hv
          have := hG' u hu v hv
          rw [hc] at this
          have hnuv := hne u hu v hv
          unfold disagree ind
          by_cases hG : G.Adj u v
          · rw [if_pos (by simp [this, hG, hnuv]), if_pos hG]; ring
          · rw [if_neg (by simp [this, hG, hnuv]), if_neg hG]; ring
        rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => this u hu v hv]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [← hd]
        have := h1 hc
        have : (0 : ℝ) ≤ #(Vp i) * #(Vp j) := by positivity
        nlinarith
      · -- `G̃` agrees with `G` on the pair
        have : ∀ u ∈ Vp i, ∀ v ∈ Vp j, disagree G G' u v = 0 := by
          intro u hu v hv
          have := hG' u hu v hv
          rw [hc] at this
          have hnuv := hne u hu v hv
          unfold disagree
          rw [if_pos (by simp [this, hnuv])]
        rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => this u hu v hv]
        simp only [Finset.sum_const_zero]
        positivity
    simp only [hbound]
    linarith
  rw [two_mul_editDist, hsplit]
  calc ∑ i, ∑ u ∈ Vp i, ∑ v, disagree G G' u v
      = ∑ i, ∑ j, ∑ u ∈ Vp i, ∑ v ∈ Vp j, disagree G G' u v := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun u _ => hsplit (fun v => disagree G G' u v)]
        exact Finset.sum_comm
    _ ≤ ∑ i, ∑ j, bound i j := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hblock i j
    _ = L * n + (#{p : Fin k × Fin k | p.1 ≠ p.2 ∧ bad p.1 p.2} : ℝ) * L ^ 2 +
          θ * (n : ℝ) ^ 2 := by
        simp only [hbound, Finset.sum_add_distrib]
        congr 1
        congr 1
        · simp [Finset.sum_ite_eq, ← Finset.mul_sum, hn]
        · rw [← Finset.sum_product', Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
          refine Finset.sum_congr (by simp) fun p _ => ?_
          split_ifs <;> simp
        · simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hn]
          ring

end AlonShapira
