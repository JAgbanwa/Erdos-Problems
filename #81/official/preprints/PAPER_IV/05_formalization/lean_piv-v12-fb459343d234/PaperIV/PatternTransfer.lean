import PaperIV.PatternCoin

/-!
# La transferencia de capacidad al grafo reducido, **demostrada**

`PaperIV.PatternCoin` construye la moneda pesada indexada por patrón y deja su legalidad
apoyada en la hipótesis

```
(†)   ∑_{H ∈ serving e} ψ′(H)  ≤  d(e),
```

la capacidad transferida al grafo reducido.  El encargo pedía que, si esa transferencia era el
cuello de botella, se dijera.  **No lo es**, y este módulo lo demuestra: (†) es un lema de
conteo que sale de `FracPacking.capacity` y de nada más.

## El enunciado

Dada una partición cualquiera de los vértices, `part : V → P` —no hace falta que sea regular,
ni equitativa, ni nada—:

* el **patrón** de un item `K` es el perfil de partes que ocupa, `K.image part`;
* el peso transferido de un patrón `H` es `ψ′(H) = ∑_{K : perfil H} x.weight K` (`psiT`);
* un patrón **sirve** al par `e` si contiene las dos partes de `e` (`servingT`), y sólo se
  colorean los pares que cruzan dos partes distintas;
* la **densidad** del par es el número de aristas de `G` entre esas dos partes (`densT`), que es
  `d(i,j)·t²` sin normalizar; la probabilidad `ψ′(H)/densT` es la de Yuster, porque el factor
  `t²` se cancela arriba y abajo.

Entonces `transfer_capacity` demuestra (†) **incondicionalmente**.

## Por qué sale del conteo y no de la regularidad

Un item cuyo perfil de partes contiene `{i,j}` tiene al menos un vértice en `V_i` y otro en
`V_j`, luego **al menos una de sus aristas cruza el par `(i,j)`** (`exists_cross_edge`).
Agrupando los items por esa arista, su masa total no pasa de la suma de las cargas del LP
sobre las aristas del par, y cada carga es `≤ 1` por `FracPacking.capacity`; en total, el
número de aristas del par.

La regularidad **no** aparece aquí.  Donde sí vive es en el lema de conteo que garantiza que un
patrón de peso `≥ η` tiene muchas copias reales en `G` —es decir, en la hipótesis `hserved`/
`hmeet` del calendario `PatternSchedule.exists_large_layer_K4`, no en su legalidad—.  Véase
`docs/CAPACITY_TRANSFER_BOTTLENECK.md`.

## Consecuencia

`transferCoins` es una moneda pesada por patrón **concreta y sin hipótesis**: existe para todo
grafo, todo empaquetamiento fraccional y toda partición.
-/

namespace PaperIV.PatternTransfer

open Finset
open MixedRounding
open PaperIV.EighthMoment
open PaperIV.OwnerCoins
open PaperIV.WeightedCoin
open PaperIV.PatternCoin

variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Patrones, pesos transferidos y densidades -/

/-- Las partes en las que viven los extremos de un par. -/
def partsOf (part : V → P) (e : Sym2 V) : Finset P :=
  Sym2.lift ⟨fun a b => ({part a, part b} : Finset P), fun a b => Finset.pair_comm (part a) (part b)⟩ e

omit [Fintype V] [DecidableEq V] [Fintype P] in
@[simp] theorem partsOf_mk (part : V → P) (a b : V) :
    partsOf part s(a, b) = {part a, part b} := rfl

/-- **El peso transferido al grafo reducido.**  `ψ′(H)` es la masa fraccional de los items
cuyo perfil de partes es exactamente `H`. -/
noncomputable def psiT (x : FracPacking G) (part : V → P) (H : Finset P) : ℚ :=
  ∑ K ∈ items G, (if K.image part = H then x.weight K else 0)

omit [Fintype P] in
theorem psiT_nonneg (x : FracPacking G) (part : V → P) (H : Finset P) :
    0 ≤ psiT x part H := by
  refine Finset.sum_nonneg fun K _ => ?_
  split
  · exact x.weight_nonneg K
  · exact le_rfl

/-- **Los patrones que sirven a un par**: los que contienen sus dos partes.  Un par que no
cruza dos partes distintas no se colorea —es el «uncolored» de la prueba publicada—. -/
def servingT (part : V → P) (e : Sym2 V) : Finset (Finset P) :=
  if (partsOf part e).card = 2 then univ.filter (fun H => partsOf part e ⊆ H) else ∅

/-- Las aristas de `G` que viven en el mismo par de partes que `e`. -/
def crossEdges (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → P) (e : Sym2 V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun f => partsOf part f = partsOf part e)

/-- **La densidad del par**, sin normalizar: el número de aristas de `G` que lo cruzan.  El
`max 1` sólo evita el cero en los pares vacíos; no cambia nada donde hay masa. -/
noncomputable def densT (G : SimpleGraph V) [DecidableRel G.Adj] (part : V → P) (e : Sym2 V) :
    ℚ := max 1 ((crossEdges G part e).card : ℚ)

omit [DecidableEq V] [Fintype P] in
theorem densT_pos (part : V → P) (e : Sym2 V) : 0 < densT G part e :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-! ## 2. Un item con el perfil adecuado cruza el par -/

omit [Fintype P] in
/-- **El lema de conteo que lo hace todo.**  Si el perfil de partes de un item contiene las dos
partes del par `e`, el item tiene al menos una arista en ese par. -/
theorem exists_cross_edge {part : V → P} {e : Sym2 V} {K : Finset V}
    (hK : K ∈ items G) (hcard : (partsOf part e).card = 2)
    (hsub : partsOf part e ⊆ K.image part) :
    ∃ f ∈ crossEdges G part e, f ∈ pairs K := by
  obtain ⟨i, j, hij, hEq⟩ := Finset.card_eq_two.1 hcard
  have hi : i ∈ K.image part := hsub (by rw [hEq]; simp)
  have hj : j ∈ K.image part := hsub (by rw [hEq]; simp)
  obtain ⟨a, haK, hai⟩ := Finset.mem_image.1 hi
  obtain ⟨b, hbK, hbj⟩ := Finset.mem_image.1 hj
  have hab : a ≠ b := fun h => hij (by rw [← hai, ← hbj, h])
  have hpair : s(a, b) ∈ pairs K := mk_mem_pairs.2 ⟨haK, hbK, hab⟩
  refine ⟨s(a, b), ?_, hpair⟩
  rw [crossEdges, Finset.mem_filter]
  exact ⟨pairs_subset_edgeFinset (mem_items.1 hK) hpair, by rw [partsOf_mk, hai, hbj, hEq]⟩

/-! ## 3. La transferencia -/

/-- La masa que sirve al par, reagrupada por item. -/
theorem sum_psiT_serving (x : FracPacking G) (part : V → P) {e : Sym2 V}
    (hcard : (partsOf part e).card = 2) :
    ∑ H ∈ servingT part e, psiT x part H
      = ∑ K ∈ items G, (if partsOf part e ⊆ K.image part then x.weight K else 0) := by
  classical
  rw [servingT, if_pos hcard]
  simp only [psiT]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_ite_eq (univ.filter (fun H => partsOf part e ⊆ H)) (K.image part)
    (fun _ => x.weight K)]
  by_cases hmem : partsOf part e ⊆ K.image part
  · simp [hmem]
  · simp [hmem]

/-- **La transferencia de capacidad al grafo reducido.**

Es (†), y sale de `FracPacking.capacity` por conteo: la masa de los items que sirven al par no
pasa del número de aristas del par.  **Sin hipótesis de regularidad, ni de densidad, ni sobre
la partición.** -/
theorem transfer_capacity (x : FracPacking G) (part : V → P) (e : Sym2 V) :
    ∑ H ∈ servingT part e, psiT x part H ≤ densT G part e := by
  classical
  by_cases hcard : (partsOf part e).card = 2
  · rw [sum_psiT_serving x part hcard]
    -- la masa de cada item que sirve al par se carga en una arista del par
    have hstep : ∑ K ∈ items G, (if partsOf part e ⊆ K.image part then x.weight K else 0)
        ≤ ∑ f ∈ crossEdges G part e, load x f := by
      have hswap : ∑ f ∈ crossEdges G part e, load x f
          = ∑ K ∈ items G, ∑ f ∈ crossEdges G part e,
              (if f ∈ pairs K then x.weight K else 0) := by
        simp only [load]
        exact Finset.sum_comm
      rw [hswap]
      refine Finset.sum_le_sum fun K hK => ?_
      by_cases hsub : partsOf part e ⊆ K.image part
      · rw [if_pos hsub]
        obtain ⟨f₀, hf₀cross, hf₀pairs⟩ := exists_cross_edge hK hcard hsub
        have hterm : ∀ f ∈ crossEdges G part e,
            0 ≤ (if f ∈ pairs K then x.weight K else 0) := by
          intro f _
          split
          · exact x.weight_nonneg K
          · exact le_rfl
        have h := Finset.single_le_sum hterm hf₀cross
        rwa [if_pos hf₀pairs] at h
      · rw [if_neg hsub]
        refine Finset.sum_nonneg fun f _ => ?_
        split
        · exact x.weight_nonneg K
        · exact le_rfl
    -- y cada carga es `≤ 1`
    have hload : ∑ f ∈ crossEdges G part e, load x f
        ≤ ((crossEdges G part e).card : ℚ) := by
      calc ∑ f ∈ crossEdges G part e, load x f
          ≤ ∑ _f ∈ crossEdges G part e, (1 : ℚ) :=
            Finset.sum_le_sum fun f _ => load_le_one x f
        _ = ((crossEdges G part e).card : ℚ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact le_trans (le_trans hstep hload) (le_max_right _ _)
  · rw [servingT, if_neg hcard, Finset.sum_empty]
    exact (densT_pos part e).le

/-- A single served pattern cannot carry more mass than the whole physical
pair that serves it.  This is the dimensionally correct pointwise replacement
for the generally false normalization `psiT x part H ≤ 1`. -/
theorem psiT_le_densT_of_mem_serving (x : FracPacking G) (part : V → P)
    {H : Finset P} {e : Sym2 V} (hH : H ∈ servingT part e) :
    psiT x part H ≤ densT G part e := by
  have hsingle : psiT x part H ≤ ∑ J ∈ servingT part e, psiT x part J := by
    exact Finset.single_le_sum (fun J _ => psiT_nonneg x part J) hH
  exact hsingle.trans (transfer_capacity x part e)

/-! ## 4. La moneda pesada por patrón, ya sin hipótesis -/

/-- **La moneda pesada por patrón, concreta.**  Para todo grafo, todo empaquetamiento
fraccional y toda partición de los vértices: la legalidad ya no es una hipótesis, la da
`transfer_capacity`. -/
noncomputable def transferCoins (x : FracPacking G) (part : V → P) :
    FinProb (Sym2 V → Option (Finset P)) :=
  patternCoins (psi := psiT x part) (dens := densT G part) (serving := servingT part)
    (psiT_nonneg x part) (densT_pos part) (transfer_capacity x part)

end PaperIV.PatternTransfer
