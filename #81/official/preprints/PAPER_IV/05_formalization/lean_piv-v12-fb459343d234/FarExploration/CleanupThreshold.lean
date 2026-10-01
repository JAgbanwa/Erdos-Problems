import FarExploration.CleanupBridge

/-!
# Una obstrucción **realizable como grafo**: el umbral de la limpieza no es uniforme

La obstrucción de `FarExploration.CleanupObstruction` es abstracta a propósito: sus items no son
cliques.  Aquí se hace lo mismo con una familia **de grafos de verdad**, el grafo de bloques

```
triGraph n : i ~ j  ↔  i ≠ j ∧ i/3 = j/3
```

—una unión disjunta de `⌊n/3⌋` triángulos—.  Sus items son exactamente triángulos disjuntos dos a
dos, luego el sistema de items es rígido y todo empaquetamiento con codegrado `≤ gam` pierde al
menos `2(1-gam)⌊n/3⌋` de valor.

El precio de ser realizable es la escala: los bloques son `Θ(n)`, no `Θ(n²)`, y por eso esta
familia **no** refuta `CodegreeCleanupAt` —la pérdida es lineal, no cuadrática—.  Lo que sí da es
una **cota inferior del umbral**: mientras `xi·n² < 2(1-gam)⌊n/3⌋` y la hipótesis de masa se
cumpla, ese `n` queda por debajo de cualquier umbral válido.  Con los parámetros de la aplicación
(`m = eps/30`, `xi = eps/4`) eso significa `N > n` para todo `n ≥ 9` con `eps·n ≤ 1`: el umbral
crece al menos como `1/eps`.

Es la versión concreta de la misma lección: los items disjuntos son la configuración que hace
grandes los precios duales; a escala cuadrática esa configuración deja de ser realizable como
grafo, y ahí es donde entra el conteo (regularidad), no la dualidad.
-/

namespace FarExploration.CleanupThreshold

open Finset MixedRounding FarExploration.CleanupLP FarExploration.CleanupBridge

/-! ## 1. El grafo de bloques -/

/-- **El grafo de bloques**: unión disjunta de triángulos `{3q, 3q+1, 3q+2}`. -/
def triGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (a : ℕ) / 3 = (b : ℕ) / 3
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (triGraph n).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (a : ℕ) / 3 = (b : ℕ) / 3))

/-- Un conjunto de tres naturales tiene a lo sumo tres elementos. -/
private lemma card_triple_le (a b c : ℕ) : ({a, b, c} : Finset ℕ).card ≤ 3 := by
  classical
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h : ({b, c} : Finset ℕ).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  omega

/-- La fibra del cociente: los vértices `v` con `v/3 = q`. -/
private def fiber (n q : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n => (v : ℕ) / 3 = q)

private lemma card_fiber_le (n q : ℕ) : (fiber n q).card ≤ 3 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn (fun v => (v : ℕ))
    (t := ({3 * q, 3 * q + 1, 3 * q + 2} : Finset ℕ)) ?_ ?_) (card_triple_le _ _ _)
  · intro v hv
    have hv3 : (v : ℕ) / 3 = q := by simpa [fiber] using hv
    have hcases : (v : ℕ) = 3 * q ∨ (v : ℕ) = 3 * q + 1 ∨ (v : ℕ) = 3 * q + 2 := by omega
    rcases hcases with h | h | h <;> simp [h]
  · intro u _ v _ h
    exact Fin.ext h

private lemma item_subset_fiber {n : ℕ} {K : Finset (Fin n)} (hK : IsItem (triGraph n) K)
    {a : Fin n} (ha : a ∈ K) : K ⊆ fiber n ((a : ℕ) / 3) := by
  intro v hv
  rw [fiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ v, ?_⟩
  by_cases h : v = a
  · rw [h]
  · exact (hK.1 v hv a ha h).2

/-- **Todo item del grafo de bloques es un triángulo.**  Los vértices de un item son mutuamente
adyacentes, luego comparten el cociente `v/3`, y sólo hay tres vértices con cada cociente. -/
lemma item_card_eq_three {n : ℕ} {K : Finset (Fin n)} (hK : IsItem (triGraph n) K) :
    K.card = 3 := by
  classical
  have hle : K.card ≤ 3 := by
    rcases K.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · exact le_trans (Finset.card_le_card (item_subset_fiber hK ha)) (card_fiber_le n _)
  rcases hK.2 with h3 | h4 <;> omega

/-- **Dos items que comparten un vértice coinciden.** -/
lemma item_unique_of_mem {n : ℕ} {K L : Finset (Fin n)} (hK : IsItem (triGraph n) K)
    (hL : IsItem (triGraph n) L) {a : Fin n} (haK : a ∈ K) (haL : a ∈ L) : K = L := by
  classical
  have hKT : K = fiber n ((a : ℕ) / 3) :=
    Finset.eq_of_subset_of_card_le (item_subset_fiber hK haK)
      (by rw [item_card_eq_three hK]; exact card_fiber_le n _)
  have hLT : L = fiber n ((a : ℕ) / 3) :=
    Finset.eq_of_subset_of_card_le (item_subset_fiber hL haL)
      (by rw [item_card_eq_three hL]; exact card_fiber_le n _)
  rw [hKT, hLT]

/-! ## 2. El sistema de items es rígido -/

lemma graphSystem_three (n : ℕ) :
    ∀ S ∈ (graphSystem (triGraph n)).supports, S.card = 3 := by
  intro S hS
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  have e32 : Nat.choose 3 2 = 3 := by decide
  rw [card_pairs, item_card_eq_three hK, e32]

lemma graphSystem_rigid (n : ℕ) : (graphSystem (triGraph n)).Rigid := by
  classical
  intro S hS T hT e heS heT
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  obtain ⟨L, hL, rfl⟩ := mem_supports.1 hT
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_pairs] at heS heT
    rw [item_unique_of_mem hK hL heS.1 heT.1]

/-! ## 3. Hay al menos `⌊n/3⌋` items -/

/-- El vértice de índice `i` del bloque `q`. -/
def bvtx {n : ℕ} (q : Fin (n / 3)) (i : Fin 3) : Fin n :=
  ⟨3 * q.val + i.val, by have h1 := q.isLt; have h2 := i.isLt; omega⟩

/-- El bloque `q`, como conjunto de vértices. -/
def bset {n : ℕ} (q : Fin (n / 3)) : Finset (Fin n) := {bvtx q 0, bvtx q 1, bvtx q 2}

lemma bvtx_val {n : ℕ} (q : Fin (n / 3)) (i : Fin 3) : (bvtx q i).val = 3 * q.val + i.val := rfl

lemma bset_isItem {n : ℕ} (q : Fin (n / 3)) : IsItem (triGraph n) (bset q) := by
  classical
  constructor
  · intro a ha b hb hab
    simp only [bset, Finset.mem_insert, Finset.mem_singleton] at ha hb
    refine ⟨hab, ?_⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp only [bvtx_val] <;> omega
  · left
    have h01 : (bvtx q 0 : Fin n) ≠ bvtx q 1 := by
      intro h; have := congrArg Fin.val h; simp only [bvtx_val] at this; omega
    have h02 : (bvtx q 0 : Fin n) ≠ bvtx q 2 := by
      intro h; have := congrArg Fin.val h; simp only [bvtx_val] at this; omega
    have h12 : (bvtx q 1 : Fin n) ≠ bvtx q 2 := by
      intro h; have := congrArg Fin.val h; simp only [bvtx_val] at this; omega
    rw [bset, Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]

lemma bset_injective {n : ℕ} {q q' : Fin (n / 3)} (h : bset q = bset q') : q = q' := by
  classical
  have hmem : (bvtx q 0 : Fin n) ∈ bset q' := by
    rw [← h]
    simp [bset]
  simp only [bset, Finset.mem_insert, Finset.mem_singleton] at hmem
  refine Fin.ext ?_
  rcases hmem with h0 | h0 | h0 <;>
    · have := congrArg Fin.val h0
      simp only [bvtx_val] at this
      omega

lemma card_supports_ge (n : ℕ) : n / 3 ≤ (graphSystem (triGraph n)).supports.card := by
  classical
  have hsub : (Finset.univ : Finset (Fin (n / 3))).image (fun q => pairs (bset q))
      ⊆ (graphSystem (triGraph n)).supports := by
    intro S hS
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hS
    exact Finset.mem_image.2 ⟨bset q, mem_items.2 (bset_isItem q), rfl⟩
  have hinj : Function.Injective (fun q : Fin (n / 3) => pairs (bset q)) := by
    intro q q' h
    exact bset_injective (pairs_injOn_items (bset_isItem q) (bset_isItem q') h)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

/-! ## 4. El empaquetamiento rígido del grafo de bloques -/

/-- Peso `1` sobre cada triángulo del grafo de bloques. -/
def blockPacking (n : ℕ) : FracPacking (triGraph n) :=
  toPacking ((graphSystem (triGraph n)).rigidFrac (graphSystem_rigid n))

lemma blockPacking_value (n : ℕ) :
    (blockPacking n).value = 2 * ((graphSystem (triGraph n)).supports.card : ℚ) := by
  rw [blockPacking, toPacking_value,
    ItemSystem.rigidFrac_value _ _ (graphSystem_three n)]

lemma blockPacking_mass (n : ℕ) :
    PaperIV.JointTwoQuotaPhysical.triangleMass (blockPacking n)
      = ((graphSystem (triGraph n)).supports.card : ℝ) := by
  rw [blockPacking, toPacking_mass, ItemSystem.rigidFrac_mass _ _ (graphSystem_three n)]
  push_cast
  ring

/-- **La rigidez, en el grafo.**  Todo empaquetamiento fraccional con codegrado ponderado `≤ gam`
tiene valor `≤ 2·gam·(número de bloques)`. -/
lemma value_le_of_codeg (n : ℕ) (gam : ℝ) (y : FracPacking (triGraph n))
    (hcod : ∀ e f : Sym2 (Fin n), e ≠ f →
      ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports (triGraph n)).filter
        (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) :
    ((y.value : ℚ) : ℝ) ≤ 2 * gam * ((graphSystem (triGraph n)).supports.card : ℝ) := by
  have hcod' : ∀ e f : Sym2 (Fin n), e ≠ f → (((ofPacking y).codeg e f : ℚ) : ℝ) ≤ gam := by
    intro e f hef
    rw [← ofPacking_codeg]
    exact hcod e f hef
  have h := Frac.value_le_of_rigid_three (graphSystem_rigid n) (graphSystem_three n)
    (ofPacking y) gam hcod'
  rwa [ofPacking_value] at h

/-! ## 5. La cota inferior del umbral -/

/-- El cuerpo de `CodegreeCleanupAt` **con el umbral explícito**: es literalmente el enunciado de
`FarExploration.CodegreeCleanup.CodegreeCleanupAt` sin el cuantificador existencial sobre `N`. -/
def CleanupAtWith (gam Cst : ℝ) (m xi : ℚ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : FracPacking G),
      (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ PaperIV.JointTwoQuotaPhysical.triangleMass x →
      ∃ y : FracPacking G,
        (∀ e f : Sym2 (Fin n), e ≠ f →
          ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
              (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) ∧
        Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y ∧
        x.value - y.value ≤ xi * (n : ℚ) ^ 2

/-- `CodegreeCleanupAt` es exactamente «existe un umbral que funciona». -/
theorem codegreeCleanupAt_iff_exists_threshold (gam Cst : ℝ) (m xi : ℚ) :
    FarExploration.CodegreeCleanup.CodegreeCleanupAt gam Cst m xi
      ↔ ∃ N : ℕ, CleanupAtWith gam Cst m xi N := Iff.rfl

/-- **Cota inferior del umbral.**  Si `N` es un umbral válido para la limpieza, entonces todo `n`
en el que la familia de bloques cumpla la hipótesis de masa y fuerce una pérdida mayor que la
admitida queda **por debajo** de `N`.  No hay, pues, umbral uniforme. -/
theorem threshold_gt (gam Cst : ℝ) (m xi : ℚ) (hgam : gam ≤ 1) (N n : ℕ)
    (hN : CleanupAtWith gam Cst m xi N)
    (hmass : (m : ℝ) * (n : ℝ) ^ 2 - 1 ≤ ((n / 3 : ℕ) : ℝ))
    (hloss : (xi : ℝ) * (n : ℝ) ^ 2 < 2 * (1 - gam) * ((n / 3 : ℕ) : ℝ)) :
    n < N := by
  classical
  by_contra hcon
  push_neg at hcon
  set B : ℝ := ((graphSystem (triGraph n)).supports.card : ℝ) with hB
  have hBge : ((n / 3 : ℕ) : ℝ) ≤ B := by
    rw [hB]
    exact_mod_cast card_supports_ge n
  have hmass' : (m : ℝ) * (n : ℝ) ^ 2 - 1
      ≤ PaperIV.JointTwoQuotaPhysical.triangleMass (blockPacking n) := by
    rw [blockPacking_mass]
    linarith
  obtain ⟨y, hcod, -, hlossy⟩ := hN n hcon (triGraph n) (blockPacking n) hmass'
  have hyval : ((y.value : ℚ) : ℝ) ≤ 2 * gam * B := value_le_of_codeg n gam y hcod
  have hxval : (((blockPacking n).value : ℚ) : ℝ) = 2 * B := by
    rw [blockPacking_value]
    push_cast
    ring
  have hlossR : (((blockPacking n).value : ℚ) : ℝ) - ((y.value : ℚ) : ℝ)
      ≤ (xi : ℝ) * (n : ℝ) ^ 2 := by
    have hq := (Rat.cast_le (K := ℝ)).2 hlossy
    push_cast at hq
    linarith
  have hscale : 2 * (1 - gam) * ((n / 3 : ℕ) : ℝ) ≤ 2 * (1 - gam) * B :=
    mul_le_mul_of_nonneg_left hBge (by linarith)
  linarith

/-- **En los parámetros de la aplicación.**  Con `m = eps/30`, `xi = eps/4` y `gam ≤ 1/2`, todo
umbral válido supera a cualquier `n ≥ 9` con `eps·n ≤ 1`: el umbral de la limpieza crece al menos
como `1/eps`. -/
theorem application_threshold_gt (eps : ℚ) (gam Cst : ℝ) (N n : ℕ)
    (hgam : gam ≤ 1 / 2) (hN : CleanupAtWith gam Cst (eps / 30) (eps / 4) N)
    (hn9 : 9 ≤ n) (hepsn : (eps : ℝ) * (n : ℝ) ≤ 1) :
    n < N := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn9R : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
  have hblocks : ((n : ℝ) - 2) / 3 ≤ ((n / 3 : ℕ) : ℝ) := by
    have h3 : n ≤ 3 * (n / 3) + 2 := by omega
    have : (n : ℝ) ≤ 3 * ((n / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast h3
    linarith
  have hsq : (eps : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hepsn hn0
    nlinarith
  refine threshold_gt gam Cst (eps / 30) (eps / 4) (by linarith) N n hN ?_ ?_
  · have hm : ((eps / 30 : ℚ) : ℝ) * (n : ℝ) ^ 2 = (eps : ℝ) * (n : ℝ) ^ 2 / 30 := by
      push_cast; ring
    rw [hm]
    linarith
  · have hx : ((eps / 4 : ℚ) : ℝ) * (n : ℝ) ^ 2 = (eps : ℝ) * (n : ℝ) ^ 2 / 4 := by
      push_cast; ring
    rw [hx]
    have h1 : (1 : ℝ) ≤ 2 * (1 - gam) := by linarith
    have h2 : (0 : ℝ) ≤ ((n : ℝ) - 2) / 3 := by linarith
    have hlow : 1 * (((n : ℝ) - 2) / 3) ≤ 2 * (1 - gam) * ((n / 3 : ℕ) : ℝ) := by
      calc 1 * (((n : ℝ) - 2) / 3) ≤ 2 * (1 - gam) * (((n : ℝ) - 2) / 3) := by nlinarith
        _ ≤ 2 * (1 - gam) * ((n / 3 : ℕ) : ℝ) := by nlinarith
    linarith

end FarExploration.CleanupThreshold
