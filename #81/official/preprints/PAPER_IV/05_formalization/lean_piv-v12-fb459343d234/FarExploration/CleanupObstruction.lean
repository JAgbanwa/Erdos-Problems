import FarExploration.CleanupLP

/-!
# La obstrucción: el LP de la limpieza es **infactible** en el régimen que importa

Este módulo construye, para cada `n`, un sistema de items explícito sobre los recursos reales
del problema —los pares `Sym2 (Fin n)`— que satisface **todas** las hipótesis del enunciado de
limpieza escritas en el LP (rangos `3`, capacidades `1`, masa de rango `3` cuadrática) y para el
cual **no existe** ninguna solución con codegrado `≤ gam` y pérdida de valor `≤ xi·n²` en cuanto
`49·xi < 2(1-gam)`.

## La familia

Seis estratos de `⌊n/6⌋` vértices cada uno, `vtx p i = 6i + p`.  Para cada par de índices
`(i,j)` un item con **tres** recursos:

```
block i j = { s(vtx 0 i, vtx 1 j), s(vtx 2 i, vtx 3 j), s(vtx 4 i, vtx 5 j) }
```

Cada recurso pertenece a lo sumo a un item (el estrato dice de qué arista se trata, y los dos
índices dicen a qué item), luego los `⌊n/6⌋²` items son disjuntos dos a dos y el peso `1` en
todos ellos es admisible: valor `2⌊n/6⌋²`, masa `⌊n/6⌋²`.

## La rigidez

Como cada par de recursos de un mismo item no está en ningún otro item, la restricción de
codegrado dice literalmente `y(block i j) ≤ gam`.  Luego **toda** solución admisible tiene valor
`≤ 2·gam·⌊n/6⌋²`, y la pérdida es al menos `2(1-gam)⌊n/6⌋² ≥ 2(1-gam)n²/49`.

Es decir: sobre la escala cuadrática, la cota de escalado de `CleanupLP.abstractCleanupAt_of_scale`
es **exacta**; la dualidad lineal no da nada mejor que multiplicar por `gam`.

## Lo que esto decide

`CleanupBridge.codegreeCleanupAt_of_abstract` demuestra que la versión abstracta implica la
concreta.  Por tanto un argumento que no use que los soportes son **cliques de un grafo**
demostraría también la abstracta, que aquí se refuta.  La hipótesis de masa triangular no
salva la situación: la familia de arriba tiene masa `⌊n/6⌋² ≥ n²/49`, cuadrática.  Lo único que
la excluye es que sus items no son triángulos ni `K₄`.
-/

namespace FarExploration.CleanupObstruction

open Finset FarExploration.CleanupLP

/-! ## 1. Los vértices estratificados -/

/-- El vértice de estrato `p ∈ {0,…,5}` e índice `i < ⌊n/6⌋`. -/
def vtx {n : ℕ} (p : Fin 6) (i : Fin (n / 6)) : Fin n :=
  ⟨6 * i.val + p.val, by have h1 := i.isLt; have h2 := p.isLt; omega⟩

@[simp] lemma vtx_val {n : ℕ} (p : Fin 6) (i : Fin (n / 6)) :
    (vtx p i).val = 6 * i.val + p.val := rfl

/-! ## 2. Los items -/

/-- El item de índices `(i,j)`: tres recursos, uno por cada par de estratos consecutivos. -/
def block {n : ℕ} (i j : Fin (n / 6)) : Finset (Sym2 (Fin n)) :=
  {s(vtx 0 i, vtx 1 j), s(vtx 2 i, vtx 3 j), s(vtx 4 i, vtx 5 j)}

lemma mem_block {n : ℕ} {i j : Fin (n / 6)} {r : Sym2 (Fin n)} :
    r ∈ block i j ↔
      r = s(vtx 0 i, vtx 1 j) ∨ r = s(vtx 2 i, vtx 3 j) ∨ r = s(vtx 4 i, vtx 5 j) := by
  simp [block]

/-- **Cada recurso identifica su item.**  Si un recurso pertenece a dos items, los índices
coinciden. -/
lemma block_index_unique {n : ℕ} {i j i' j' : Fin (n / 6)} {r : Sym2 (Fin n)}
    (hr : r ∈ block i j) (hr' : r ∈ block i' j') : i = i' ∧ j = j' := by
  rw [mem_block] at hr hr'
  have hgoal : i.val = i'.val ∧ j.val = j'.val := by
    rcases hr with rfl | rfl | rfl <;> rcases hr' with h | h | h <;>
      · rw [Sym2.eq_iff] at h
        simp only [Fin.ext_iff, vtx_val] at h
        omega
  exact ⟨Fin.ext hgoal.1, Fin.ext hgoal.2⟩

/-- Los tres recursos de un item son distintos: el item tiene rango `3`. -/
lemma card_block {n : ℕ} (i j : Fin (n / 6)) : (block i j).card = 3 := by
  have h01 : (s(vtx 0 i, vtx 1 j) : Sym2 (Fin n)) ≠ s(vtx 2 i, vtx 3 j) := by
    intro h
    rw [Sym2.eq_iff] at h
    simp only [Fin.ext_iff, vtx_val] at h
    omega
  have h02 : (s(vtx 0 i, vtx 1 j) : Sym2 (Fin n)) ≠ s(vtx 4 i, vtx 5 j) := by
    intro h
    rw [Sym2.eq_iff] at h
    simp only [Fin.ext_iff, vtx_val] at h
    omega
  have h12 : (s(vtx 2 i, vtx 3 j) : Sym2 (Fin n)) ≠ s(vtx 4 i, vtx 5 j) := by
    intro h
    rw [Sym2.eq_iff] at h
    simp only [Fin.ext_iff, vtx_val] at h
    omega
  rw [block, Finset.card_insert_of_notMem (by simp [h01, h02]),
    Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]

lemma block_injective {n : ℕ} {i j i' j' : Fin (n / 6)} (h : block i j = block i' j') :
    (i, j) = (i', j') := by
  have hmem : (s(vtx 0 i, vtx 1 j) : Sym2 (Fin n)) ∈ block i' j' := by
    rw [← h, mem_block]; exact Or.inl rfl
  obtain ⟨hi, hj⟩ := block_index_unique (mem_block.2 (Or.inl rfl)) hmem
  simp [hi, hj]

/-- **El sistema de items de la obstrucción.** -/
def obstructionSystem (n : ℕ) : ItemSystem (Sym2 (Fin n)) where
  supports := (Finset.univ : Finset (Fin (n / 6) × Fin (n / 6))).image fun ij => block ij.1 ij.2
  rank_mem := by
    intro S hS
    obtain ⟨ij, -, rfl⟩ := Finset.mem_image.1 hS
    exact Or.inl (card_block ij.1 ij.2)

lemma mem_obstructionSystem {n : ℕ} {S : Finset (Sym2 (Fin n))} :
    S ∈ (obstructionSystem n).supports ↔ ∃ i j : Fin (n / 6), block i j = S := by
  simp [obstructionSystem, Finset.mem_image, Prod.exists]

lemma card_supports (n : ℕ) :
    (obstructionSystem n).supports.card = (n / 6) * (n / 6) := by
  classical
  rw [obstructionSystem]
  rw [Finset.card_image_of_injective _ (fun ij kl h => block_injective h)]
  simp [Finset.card_univ]

/-! ## 3. El empaquetamiento rígido -/

/-- Todos los items tienen rango `3`. -/
lemma obstruction_three (n : ℕ) :
    ∀ S ∈ (obstructionSystem n).supports, S.card = 3 := by
  intro S hS
  obtain ⟨i, j, rfl⟩ := mem_obstructionSystem.1 hS
  exact card_block i j

/-- **La familia es rígida**: cada recurso pertenece a lo sumo a un item. -/
lemma obstruction_rigid (n : ℕ) : (obstructionSystem n).Rigid := by
  intro S hS T hT r hrS hrT
  obtain ⟨i, j, rfl⟩ := mem_obstructionSystem.1 hS
  obtain ⟨i', j', rfl⟩ := mem_obstructionSystem.1 hT
  obtain ⟨hi, hj⟩ := block_index_unique hrS hrT
  rw [hi, hj]

/-- Peso `1` sobre cada item de la familia: admisible porque los items son disjuntos. -/
def rigidPacking (n : ℕ) : Frac (obstructionSystem n) :=
  (obstructionSystem n).rigidFrac (obstruction_rigid n)

lemma rigidPacking_value (n : ℕ) :
    (rigidPacking n).value = 2 * ((n / 6 : ℕ) : ℚ) ^ 2 := by
  rw [rigidPacking, ItemSystem.rigidFrac_value _ _ (obstruction_three n), card_supports]
  push_cast
  ring

lemma rigidPacking_mass (n : ℕ) :
    (rigidPacking n).mass = ((n / 6 : ℕ) : ℚ) ^ 2 := by
  rw [rigidPacking, ItemSystem.rigidFrac_mass _ _ (obstruction_three n), card_supports]
  push_cast
  ring

/-! ## 4. La rigidez: toda solución con codegrado `≤ gam` tiene valor `≤ 2·gam·⌊n/6⌋²` -/

/-- **La cota de valor para soluciones dispersas.**  Es la rigidez general de `CleanupLP`
aplicada a esta familia. -/
lemma value_le_of_codeg {n : ℕ} (gam : ℝ) (y : Frac (obstructionSystem n))
    (hcod : ∀ r s : Sym2 (Fin n), r ≠ s → ((y.codeg r s : ℚ) : ℝ) ≤ gam) :
    ((y.value : ℚ) : ℝ) ≤ 2 * gam * ((n / 6 : ℕ) : ℝ) ^ 2 := by
  have h := Frac.value_le_of_rigid_three (obstruction_rigid n) (obstruction_three n) y gam hcod
  rw [card_supports] at h
  push_cast at h
  calc ((y.value : ℚ) : ℝ) ≤ 2 * gam * (((n / 6 : ℕ) : ℝ) * ((n / 6 : ℕ) : ℝ)) := h
    _ = 2 * gam * ((n / 6 : ℕ) : ℝ) ^ 2 := by ring

/-! ## 5. El teorema de imposibilidad -/

/-- Aritmética del truncamiento: para `n ≥ 30`, `n² ≤ 49·⌊n/6⌋²`. -/
lemma sq_le_of_div_six {n : ℕ} (hn : 30 ≤ n) :
    (n : ℝ) ^ 2 ≤ 49 * ((n / 6 : ℕ) : ℝ) ^ 2 := by
  have hle : n ≤ 7 * (n / 6) := by omega
  have hleR : (n : ℝ) ≤ 7 * ((n / 6 : ℕ) : ℝ) := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ ((n / 6 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **Teorema de imposibilidad.**  La versión LP del enunciado de limpieza es **falsa** en todo
el régimen `49·xi < 2(1-gam)`, con `m ≤ 1/49` y cualquier `Cst`: la familia rígida de arriba
satisface la hipótesis de masa y ninguna solución admisible conserva el valor. -/
theorem not_abstractCleanupAt (gam Cst : ℝ) (m xi : ℚ)
    (hxi0 : 0 ≤ xi) (hm : (m : ℝ) ≤ 1 / 49) (hgap : 49 * (xi : ℝ) < 2 * (1 - gam)) :
    ¬ AbstractCleanupAt gam Cst m xi := by
  classical
  rintro ⟨N, hN⟩
  obtain ⟨n, hnN, hn30⟩ : ∃ n : ℕ, N ≤ n ∧ 30 ≤ n :=
    ⟨max N 30, le_max_left _ _, le_max_right _ _⟩
  have hKpos : (0 : ℝ) < ((n / 6 : ℕ) : ℝ) := by
    have h : 0 < n / 6 := by omega
    exact_mod_cast h
  have hsq : (n : ℝ) ^ 2 ≤ 49 * ((n / 6 : ℕ) : ℝ) ^ 2 := sq_le_of_div_six hn30
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hmass : (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ (((rigidPacking n).mass : ℚ) : ℝ) := by
    rw [rigidPacking_mass]
    have h1 : (m : ℝ) * (n : ℝ) ^ 2 ≤ (1 / 49) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hm hn2
    push_cast
    linarith
  obtain ⟨y, hcod, -, hloss⟩ := hN n hnN (obstructionSystem n) (rigidPacking n) hmass
  have hyval : ((y.value : ℚ) : ℝ) ≤ 2 * gam * ((n / 6 : ℕ) : ℝ) ^ 2 :=
    value_le_of_codeg gam y hcod
  have hxval : (((rigidPacking n).value : ℚ) : ℝ) = 2 * ((n / 6 : ℕ) : ℝ) ^ 2 := by
    rw [rigidPacking_value]; push_cast; ring
  have hxi0R : (0 : ℝ) ≤ (xi : ℝ) := by exact_mod_cast hxi0
  have hlossR : (((rigidPacking n).value : ℚ) : ℝ) - ((y.value : ℚ) : ℝ)
      ≤ (xi : ℝ) * (n : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).2 hloss
    push_cast at h
    linarith
  have hchain : (xi : ℝ) * (n : ℝ) ^ 2 ≤ 49 * (xi : ℝ) * ((n / 6 : ℕ) : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq hxi0R
    linarith
  have hstrict : 0 < (2 * (1 - gam) - 49 * (xi : ℝ)) * ((n / 6 : ℕ) : ℝ) ^ 2 :=
    mul_pos (by linarith) (by positivity)
  nlinarith [hlossR, hchain, hstrict, hxval, hyval]

end FarExploration.CleanupObstruction
