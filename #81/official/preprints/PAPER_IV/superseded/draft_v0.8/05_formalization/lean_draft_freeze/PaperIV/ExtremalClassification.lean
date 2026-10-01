import PaperIV.IntegralStability
import PaperIV.CliquePartitionTransport
import PaperIV.SplitCompleteRigidity
import PaperIV.SplitCompleteSharpValue
import PaperIV.Erdos81Unconditional

/-!
# BP-02 — clasificación de los extremizadores

Para `n` suficientemente grande y `G` cordal de orden `n`:

```text
cp(G) = M(n)   ⟺   c₄(G) = M(n)   ⟺   G es completo-split con núcleo de tamaño
      r        si n = 3r
      r o r+1  si n = 3r+1
      r+1      si n = 3r+2
```

## Reparto del trabajo

* La parte **aritmética** ya estaba hecha: `SplitCompleteRigidity.optimal_cores` clasifica
  los `k` con `baseline n k = targetSize n`, y `(n+1)/3` vale `r`, `r`, `r+1` en los tres
  casos (`optimalCore_iff_cases` lo comprueba literalmente).  Aquí no se rehace.
* La parte **estructural** —que todo extremal *sea* un completo-split— es BP-01 con `δ = 0`:
  la cuenta `m/20 + A/2 ≤ 0` fuerza `m = A = 0`, luego `d_E(G, S_R) = 0` y, por la identidad
  de edición, `G` **es** `S_R`.
* El **valor** del completo-split lo da `SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities`,
  que es simultáneamente cota inferior contra particiones *no restringidas* y partición
  óptima de orden `≤ 4`.  Por eso las dos nociones `cp` y `c₄` coinciden en los extremales
  y el ciclo de implicaciones se cierra.

## Lectura de los enunciados

`cp(G) = M(n)` se escribe como «`M(n)` es cota inferior de todos los tamaños **y** se
alcanza» (`CliqueCoverEq`), y `c₄(G) = M(n)` igual pero restringido a particiones de orden
a lo sumo cuatro (`CliqueCover4Eq`).  Ninguna de las dos postula un minimizador: la
existencia es parte de la definición y se demuestra en cada dirección.

Las dos hipótesis del teorema son `N ≤ n` (umbral fijado antes que `n`) y la cordalidad de
`G`.  No hay ninguna otra: en particular no se supone que `G` sea un split, que es
precisamente lo que se concluye.
-/

namespace PaperIV.ExtremalClassification

open PaperIV.FarRounding
open PaperIV.SplitUniformIncidence
open PaperIV.SplitCompleteRigidity
open PaperIV.CliquePartitionTransport

/-! ## 1. Vocabulario -/

/-- Los tamaños de núcleo óptimos: `(n+1)/3` siempre, y uno más cuando `n ≡ 1 (mod 3)`. -/
def OptimalCore (n k : ℕ) : Prop :=
  k = (n + 1) / 3 ∨ (n % 3 = 1 ∧ k = (n + 1) / 3 + 1)

/-- La traducción literal del enunciado del contrato: `r`, `r`/`r+1`, `r+1`. -/
theorem optimalCore_iff_cases (r k : ℕ) :
    (OptimalCore (3 * r) k ↔ k = r) ∧
    (OptimalCore (3 * r + 1) k ↔ (k = r ∨ k = r + 1)) ∧
    (OptimalCore (3 * r + 2) k ↔ k = r + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;>
    simp only [OptimalCore] at * <;> omega

/-- `G` es el completo-split de núcleo `R`, con `R` de tamaño óptimo. -/
def IsOptimalCompleteSplit {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ R : Finset (Fin n), G = splitGraph R (Finset.univ \ R) ∧ OptimalCore n R.card

/-- `cp(G) = t`: `t` acota inferiormente el tamaño de toda partición en cliques y se
alcanza. -/
def CliqueCoverEq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  (∀ Q : CliquePartition G, t ≤ Q.size) ∧ (∃ Q : CliquePartition G, Q.size = t)

/-- `c₄(G) = t`: lo mismo, restringido a particiones de orden a lo sumo cuatro. -/
def CliqueCover4Eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  (∀ Q : CliquePartition G, Q.OrderAtMost 4 → t ≤ Q.size) ∧
    (∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = t)

/-! ## 2. El valor exacto de un completo-split -/

/-- **El completo-split vale `baseline n k`, contra particiones no restringidas.**  El
óptimo se alcanza con piezas de orden a lo sumo cuatro, así que `cp` y `c₄` coinciden en
esta familia. -/
theorem split_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {R : Finset (Fin n)} (hG : G = splitGraph R (Finset.univ \ R))
    (hk2 : 2 ≤ R.card) (hk : R.card ≤ (Finset.univ \ R).card) :
    (∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = baseline n R.card) ∧
      (∀ Q : CliquePartition G, baseline n R.card ≤ Q.size) := by
  classical
  have hd : Disjoint R (Finset.univ \ R) := Finset.disjoint_sdiff
  obtain ⟨Q₀, hQ₀4, hQ₀size, hQ₀min⟩ :=
    PaperIV.SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities hd hk2 hk
  have hcard : (Finset.univ \ R).card = n - R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R)]
    simp
  have hbase : R.card * (Finset.univ \ R).card - (R.card).choose 2 = baseline n R.card := by
    rw [hcard, baseline]
  have hadj : ∀ x y, (splitGraph R (Finset.univ \ R)).Adj x y ↔ G.Adj x y := by
    intro x y; rw [hG]
  have hadj' : ∀ x y, G.Adj x y ↔ (splitGraph R (Finset.univ \ R)).Adj x y := by
    intro x y; rw [hG]
  refine ⟨⟨transport hadj Q₀, transport_orderAtMost hadj Q₀ hQ₀4, ?_⟩, ?_⟩
  · rw [transport_size, hQ₀size, hbase]
  · intro Q
    have := hQ₀min (transport hadj' Q)
    rw [transport_size, hQ₀size, hbase] at this
    exact this

/-! ## 3. La aritmética, tal como está demostrada -/

/-- `baseline n k = targetSize n` exactamente en los núcleos óptimos.  Es
`SplitCompleteRigidity.optimal_cores` reescrito con el vocabulario del contrato. -/
theorem baseline_eq_target_iff_optimalCore {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    baseline n k = PaperIV.targetSize n ↔ OptimalCore n k := by
  obtain ⟨hne, heq⟩ := optimal_cores n hn
  by_cases h3 : n % 3 = 1
  · rw [heq h3 k hk]
    simp only [OptimalCore, h3]
    tauto
  · rw [hne h3 k hk]
    simp only [OptimalCore]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h h3

/-! ## 4. La clasificación -/

/-- **BP-02.**  Para `n` grande, un grafo cordal alcanza el máximo `M(n)` —con particiones
arbitrarias o con particiones de orden a lo sumo cuatro, indistintamente— si y sólo si es un
completo-split de núcleo óptimo.

Hipótesis: el umbral `N ≤ n`, fijado antes que `n`, y la cordalidad de `G`. -/
theorem chordal_extremal_classification :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        (CliqueCoverEq G (PaperIV.targetSize n) ↔
            CliqueCover4Eq G (PaperIV.targetSize n)) ∧
          (CliqueCover4Eq G (PaperIV.targetSize n) ↔ IsOptimalCompleteSplit G) := by
  classical
  obtain ⟨Nstab, hstab⟩ := PaperIV.IntegralStability.chordal_linear_stability
  obtain ⟨Nerd, herd⟩ := PaperIV.Erdos81Unconditional.erdos81_cliquePartition
  refine ⟨max (max Nstab Nerd) 9, ?_⟩
  intro n hn G _ hG
  have hn9 : 9 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnstab : Nstab ≤ n :=
    le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnerd : Nerd ≤ n :=
    le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  -- (1) extremal para orden ≤ 4  ⟹  completo-split de núcleo óptimo
  have step1 : CliqueCover4Eq G (PaperIV.targetSize n) → IsOptimalCompleteSplit G := by
    rintro ⟨hlow, Qext, hQext4, hQextsize⟩
    obtain ⟨R, hRclique, hR2, hRout, hacct, hedit⟩ :=
      hstab n hnstab G hG 0 le_rfl
        (mul_nonneg PaperIV.IntegralStability.gamma_pos.le (sq_nonneg _))
        (fun Q hQ4 => by
          have := hlow Q hQ4
          have : ((PaperIV.targetSize n : ℕ) : ℚ) ≤ ((Q.size : ℕ) : ℚ) := by exact_mod_cast this
          linarith)
    have hzero : PaperIV.EditMetric.editDist G.edgeFinset
        (PaperIV.GraphFamilyDistance.graphEdgeSupport
          (splitGraph R (Finset.univ \ R))) = 0 := by
      have hnn : (0 : ℚ) ≤ (PaperIV.EditMetric.editDist G.edgeFinset
        (PaperIV.GraphFamilyDistance.graphEdgeSupport
          (splitGraph R (Finset.univ \ R))) : ℚ) := by positivity
      have : ((PaperIV.EditMetric.editDist G.edgeFinset
        (PaperIV.GraphFamilyDistance.graphEdgeSupport
          (splitGraph R (Finset.univ \ R))) : ℕ) : ℚ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
    have hGsplit : G = splitGraph R (Finset.univ \ R) :=
      PaperIV.SplitEditIdentity.eq_splitGraph_of_editDist_eq_zero G hzero
    obtain ⟨⟨Qs, hQs4, hQssize⟩, hQlow⟩ := split_value G hGsplit hR2 hRout
    have hRn : R.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ R)
      simpa using this
    have h1 : PaperIV.targetSize n ≤ baseline n R.card := by
      have := hlow Qs hQs4
      omega
    have h2 : baseline n R.card ≤ PaperIV.targetSize n := by
      have := hQlow Qext
      omega
    exact ⟨R, hGsplit,
      (baseline_eq_target_iff_optimalCore (by omega) hRn).mp (le_antisymm h2 h1)⟩
  -- (2) completo-split de núcleo óptimo  ⟹  extremal sin restricción de orden
  have step2 : IsOptimalCompleteSplit G → CliqueCoverEq G (PaperIV.targetSize n) := by
    rintro ⟨R, hGsplit, hopt⟩
    have hRn : R.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ R)
      simpa using this
    have hcard : (Finset.univ \ R).card = n - R.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ R)]
      simp
    have hk2 : 2 ≤ R.card := by
      rcases hopt with h | ⟨-, h⟩ <;> omega
    have hk : R.card ≤ (Finset.univ \ R).card := by
      rw [hcard]
      rcases hopt with h | ⟨-, h⟩ <;> omega
    obtain ⟨⟨Qs, -, hQssize⟩, hQlow⟩ := split_value G hGsplit hk2 hk
    have hbase : baseline n R.card = PaperIV.targetSize n :=
      (baseline_eq_target_iff_optimalCore (by omega) hRn).mpr hopt
    refine ⟨fun Q => ?_, ⟨Qs, by rw [hQssize, hbase]⟩⟩
    have := hQlow Q
    omega
  -- (3) extremal sin restricción  ⟹  extremal para orden ≤ 4
  have step3 : CliqueCoverEq G (PaperIV.targetSize n) →
      CliqueCover4Eq G (PaperIV.targetSize n) := by
    rintro ⟨hlow, -⟩
    obtain ⟨Q, hQ4, hQsize⟩ := herd n hnerd G hG
    exact ⟨fun Q' _ => hlow Q', ⟨Q, hQ4, le_antisymm hQsize (hlow Q)⟩⟩
  exact ⟨⟨step3, fun h => step2 (step1 h)⟩,
    ⟨step1, fun h => step3 (step2 h)⟩⟩

end PaperIV.ExtremalClassification
