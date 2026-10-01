import FarExploration.CleanupDense

/-!
# El medio, en el caso regular sin `K₄`: la limpieza sale con pérdida cero

Entre el extremo denso (`FarExploration.CleanupDense`, donde la limpieza es gratis) y el extremo
rígido (`FarExploration.CleanupRigidVerdict`, donde el umbral se dispara) hay una clase de grafos
en la que el argumento de dispersión funciona tal cual, y este módulo la aísla con hipótesis
explícitas:

* `G` **no tiene `K₄`** —todos sus items son triángulos—, y
* `G` es **triangularmente regular**: cada arista está exactamente en `q` triángulos.

En esa clase el reparto uniforme `w = 1/q` sobre todos los triángulos es admisible (la carga de
cada arista es exactamente `1`), su codegrado vale `1/q` —dos aristas distintas están en un único
triángulo común—, su masa triangular es `|E|/3` y su valor es `2|E|/3`, que es **el máximo
posible** de cualquier empaquetamiento fraccional de un grafo sin `K₄`.  Es decir: la limpieza se
consigue con **pérdida cero**.

Ejemplo no vacuo de la clase: el grafo tripartito completo `K_{t,t,t}`, sin `K₄`, con cada arista
en exactamente `t` triángulos y masa triangular `Θ(n²)`.

## Régimen, dicho con precisión

El resultado necesita `q ≥ 1/gam`: la regularidad triangular tiene que ser grande comparada con
el umbral de codegrado.  Eso lo cumplen los grafos localmente densos (`q = Θ(n)`), y no lo cumple
la familia rígida (`q = 1`), que es justo donde la cota inferior del umbral muerde.  El caso
general —ni regular, ni sin `K₄`— sigue abierto.

La última sección relaja la regularidad exacta a una horquilla `q ≤ t(e) ≤ Q`
(`nearRegular_cleanup`): la pérdida de valor pasa a estar acotada por `(2/3)·(1 - q/Q)·|E|`, que
se anula cuando `q = Q`.  Ojo con el régimen: como `|E| ≤ n²/2`, para que esa pérdida quepa en
`xi·n²` hace falta `1 - q/Q ≤ 3·xi`, es decir una horquilla **muy** estrecha; la versión casi
regular generaliza el enunciado pero no relaja de forma apreciable la hipótesis en la aplicación.
-/

namespace FarExploration.CleanupTriangleRegular

open Finset MixedRounding

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-! ## 1. La cota de valor con una ganancia por arista arbitraria -/

/-- Si cada item gana a lo sumo `c` por arista que ocupa, el valor no pasa de `c·|E|`. -/
lemma value_le_gain_bound (c : ℚ) (hc0 : 0 ≤ c)
    (hc : ∀ K ∈ items G, gainF ℚ K ≤ c * (((pairs K).card : ℕ) : ℚ)) (x : FracPacking G) :
    x.value ≤ c * (G.edgeFinset.card : ℚ) := by
  classical
  have hsum1 : x.value ≤ c * ∑ K ∈ items G, (((pairs K).card : ℕ) : ℚ) * x.weight K := by
    rw [FracPacking.value, Finset.mul_sum]
    refine Finset.sum_le_sum fun K hK => ?_
    have hw := x.weight_nonneg K
    have := hc K hK
    nlinarith [this, hw]
  have hcount : ∀ K ∈ items G, (((pairs K).card : ℕ) : ℚ)
      = ∑ e ∈ G.edgeFinset, (if e ∈ pairs K then (1 : ℚ) else 0) := by
    intro K hK
    rw [Finset.sum_ite_mem]
    have hsub : G.edgeFinset ∩ pairs K = pairs K :=
      Finset.inter_eq_right.2 (pairs_subset_edgeFinset (mem_items.1 hK))
    rw [hsub, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hdouble : ∑ K ∈ items G, (((pairs K).card : ℕ) : ℚ) * x.weight K
      = ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0) := by
    rw [Finset.sum_congr rfl (fun K hK => by rw [hcount K hK, Finset.sum_mul]), Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun K _ => ?_
    by_cases h : e ∈ pairs K <;> simp [h]
  have hload : ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
      ≤ (G.edgeFinset.card : ℚ) := by
    calc ∑ e ∈ G.edgeFinset, ∑ K ∈ items G, (if e ∈ pairs K then x.weight K else 0)
        ≤ ∑ _e ∈ G.edgeFinset, (1 : ℚ) := Finset.sum_le_sum fun e he => x.capacity e he
      _ = (G.edgeFinset.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hdouble] at hsum1
  nlinarith [hsum1, hload, hc0]

/-- **En un grafo sin `K₄` el valor no pasa de `(2/3)·|E|`.** -/
lemma value_le_two_thirds_edges (hk4 : ∀ K ∈ items G, K.card = 3) (x : FracPacking G) :
    x.value ≤ (2 / 3 : ℚ) * (G.edgeFinset.card : ℚ) := by
  refine value_le_gain_bound (2 / 3) (by norm_num) (fun K hK => ?_) x
  have e32 : Nat.choose 3 2 = 3 := by decide
  rw [card_pairs, hk4 K hK, e32, gainF, hk4 K hK, e32]
  norm_num

/-! ## 2. Doble conteo de items y aristas -/

/-- **Doble conteo arista–triángulo**: `3·(número de triángulos)` es la suma, sobre las aristas,
del número de triángulos que contienen a cada arista. -/
lemma three_mul_card_items_eq_sum (hk4 : ∀ K ∈ items G, K.card = 3) :
    3 * (items G).card
      = ∑ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card := by
  classical
  have hcount : ∀ K ∈ items G, (pairs K).card
      = ∑ e ∈ G.edgeFinset, (if e ∈ pairs K then 1 else 0) := by
    intro K hK
    rw [Finset.sum_ite_mem]
    have hsub : G.edgeFinset ∩ pairs K = pairs K :=
      Finset.inter_eq_right.2 (pairs_subset_edgeFinset (mem_items.1 hK))
    rw [hsub, Finset.sum_const, smul_eq_mul, mul_one]
  have hleft : ∑ K ∈ items G, (pairs K).card = 3 * (items G).card := by
    have e32 : Nat.choose 3 2 = 3 := by decide
    have h3 : ∀ K ∈ items G, (pairs K).card = 3 := by
      intro K hK
      rw [card_pairs, hk4 K hK, e32]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hleft, Finset.sum_congr rfl hcount, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => (Finset.card_filter _ _).symm

/-- **`3·(número de triángulos) = q·|E|`** en un grafo sin `K₄` con regularidad triangular `q`. -/
lemma three_mul_card_items (q : ℕ) (hk4 : ∀ K ∈ items G, K.card = 3)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card = q) :
    3 * (items G).card = q * G.edgeFinset.card := by
  rw [three_mul_card_items_eq_sum hk4, Finset.sum_congr rfl hreg, Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- Con regularidad triangular **mínima** `q`, el número de triángulos es al menos `q·|E|/3`. -/
lemma three_mul_card_items_ge (q : ℕ) (hk4 : ∀ K ∈ items G, K.card = 3)
    (hlo : ∀ e ∈ G.edgeFinset, q ≤ ((items G).filter (fun K => e ∈ pairs K)).card) :
    q * G.edgeFinset.card ≤ 3 * (items G).card := by
  rw [three_mul_card_items_eq_sum hk4]
  calc q * G.edgeFinset.card = ∑ _e ∈ G.edgeFinset, q := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum hlo

/-! ## 3. El empaquetamiento uniforme sobre los triángulos -/

/-- **El reparto uniforme sobre todos los triángulos**, peso `1/q` en cada uno. -/
def uniformTrianglePacking (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ) (hq : 0 < q)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q) :
    FracPacking G where
  weight := fun K => if K ∈ items G then (1 : ℚ) / (q : ℚ) else 0
  weight_nonneg := by
    intro K
    have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    by_cases hK : K ∈ items G <;> simp [hK, le_of_lt, hq0.le, div_nonneg]
  capacity := by
    intro e he
    classical
    have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    have hrw : ∑ K ∈ items G,
        (if e ∈ pairs K then (if K ∈ items G then (1 : ℚ) / (q : ℚ) else 0) else 0)
        = (((items G).filter (fun K => e ∈ pairs K)).card : ℚ) * (1 / (q : ℚ)) := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_congr rfl (fun K hK => if_pos (Finset.mem_filter.1 hK).1),
        Finset.sum_const, nsmul_eq_mul]
    rw [hrw]
    have hcard : ((((items G).filter (fun K => e ∈ pairs K)).card : ℕ) : ℚ) ≤ (q : ℚ) := by
      exact_mod_cast hreg e he
    rw [mul_one_div, div_le_one hq0]
    exact hcard

@[simp] lemma uniformTrianglePacking_weight (q : ℕ) (hq : 0 < q)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q)
    (K : Finset (Fin n)) :
    (uniformTrianglePacking G q hq hreg).weight K
      = if K ∈ items G then (1 : ℚ) / (q : ℚ) else 0 := rfl

/-! ## 4. Las tres propiedades -/

lemma uniform_codeg_le (q : ℕ) (hq : 0 < q)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q)
    (hk4 : ∀ K ∈ items G, K.card = 3) (e f : Sym2 (Fin n)) (hef : e ≠ f) :
    ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter (fun S => e ∈ S ∧ f ∈ S),
        inducedWeight (uniformTrianglePacking G q hq hreg) S
      ≤ ((1 : ℝ) / (q : ℝ)) := by
  classical
  rw [FarExploration.CleanupDense.codeg_eq_sum_items]
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  -- a lo sumo un triángulo contiene dos aristas distintas
  have hle_one : ((items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun K hK L hL => ?_
    rw [Finset.mem_filter] at hK hL
    have hsub : ∀ M : Finset (Fin n), M ∈ items G → e ∈ pairs M → f ∈ pairs M →
        e.toFinset ∪ f.toFinset ⊆ M := by
      intro M hM heM hfM
      have hde : ¬ e.IsDiag := (mem_pairs.1 heM).2
      have hdf : ¬ f.IsDiag := (mem_pairs.1 hfM).2
      rw [Finset.union_subset_iff]
      exact ⟨(FarExploration.CleanupDense.pairs_iff_toFinset_subset hde).1 heM,
        (FarExploration.CleanupDense.pairs_iff_toFinset_subset hdf).1 hfM⟩
    have hde : ¬ e.IsDiag := (mem_pairs.1 hK.2.1).2
    have hdf : ¬ f.IsDiag := (mem_pairs.1 hK.2.2).2
    have h3 : 3 ≤ (e.toFinset ∪ f.toFinset).card :=
      FarExploration.CleanupDense.three_le_card_union hde hdf hef
    have hKeq : e.toFinset ∪ f.toFinset = K :=
      Finset.eq_of_subset_of_card_le (hsub K hK.1 hK.2.1 hK.2.2)
        (by rw [hk4 K hK.1]; exact h3)
    have hLeq : e.toFinset ∪ f.toFinset = L :=
      Finset.eq_of_subset_of_card_le (hsub L hL.1 hL.2.1 hL.2.2)
        (by rw [hk4 L hL.1]; exact h3)
    rw [← hKeq, ← hLeq]
  have hQ : ∑ K ∈ (items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K),
      (uniformTrianglePacking G q hq hreg).weight K ≤ 1 / (q : ℚ) := by
    have hterm : ∀ K ∈ (items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K),
        (uniformTrianglePacking G q hq hreg).weight K = 1 / (q : ℚ) := by
      intro K hK
      rw [uniformTrianglePacking_weight, if_pos (Finset.mem_filter.1 hK).1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((((items G).filter (fun K => e ∈ pairs K ∧ f ∈ pairs K)).card : ℕ) : ℚ)
        ≤ 1 := by exact_mod_cast hle_one
    have hpos : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    nlinarith [hcard, hpos]
  have hcast := (Rat.cast_le (K := ℝ)).2 hQ
  push_cast at hcast ⊢
  linarith [hcast]

lemma uniform_mass (q : ℕ) (hq : 0 < q)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q)
    (hk4 : ∀ K ∈ items G, K.card = 3) :
    PaperIV.JointTwoQuotaPhysical.triangleMass (uniformTrianglePacking G q hq hreg)
      = (((items G).card : ℝ)) / (q : ℝ) := by
  classical
  rw [PaperIV.JointTwoQuotaPhysical.triangleMass, Finset.filter_true_of_mem hk4]
  have hterm : ∀ K ∈ items G,
      (((uniformTrianglePacking G q hq hreg).weight K : ℚ) : ℝ) = (1 : ℝ) / (q : ℝ) := by
    intro K hK
    rw [uniformTrianglePacking_weight, if_pos hK]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

lemma uniform_value (q : ℕ) (hq : 0 < q)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q)
    (hk4 : ∀ K ∈ items G, K.card = 3) :
    (uniformTrianglePacking G q hq hreg).value = 2 * ((items G).card : ℚ) / (q : ℚ) := by
  classical
  rw [FracPacking.value]
  have hterm : ∀ K ∈ items G,
      gainF ℚ K * (uniformTrianglePacking G q hq hreg).weight K = 2 * (1 / (q : ℚ)) := by
    intro K hK
    have e32 : Nat.choose 3 2 = 3 := by decide
    rw [uniformTrianglePacking_weight, if_pos hK, gainF, hk4 K hK, e32]
    norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## 5. La limpieza en la clase regular sin `K₄` -/

/-- **La limpieza, con pérdida cero, en los grafos sin `K₄` triangularmente regulares.**

Hipótesis, todas visibles: `G` no tiene `K₄` (`hk4`), cada arista está exactamente en `q`
triángulos (`hreg`), la regularidad supera el umbral de codegrado (`hgam : 1/q ≤ gam`) y hay
bastantes aristas para la constante de masa (`hCst : Cst ≤ |E|/3`).

La conclusión es más fuerte que la de `CodegreeCleanupAt`: el empaquetamiento limpio tiene valor
**al menos** el de `x`, luego la pérdida es cero. -/
theorem triangleRegular_cleanup (q : ℕ) (hq : 0 < q)
    (hk4 : ∀ K ∈ items G, K.card = 3)
    (hreg : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card = q)
    (gam Cst : ℝ) (hgam : (1 : ℝ) / (q : ℝ) ≤ gam)
    (hCst : Cst ≤ (G.edgeFinset.card : ℝ) / 3)
    (x : FracPacking G) :
    ∃ y : FracPacking G,
      (∀ e f : Sym2 (Fin n), e ≠ f →
        ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
            (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) ∧
      Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y ∧
      x.value ≤ y.value := by
  classical
  have hreg' : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ q :=
    fun e he => le_of_eq (hreg e he)
  have hq0Q : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdc : 3 * (items G).card = q * G.edgeFinset.card := three_mul_card_items q hk4 hreg
  have hdcQ : 3 * ((items G).card : ℚ) = (q : ℚ) * (G.edgeFinset.card : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) hdc
  have hdcR : 3 * ((items G).card : ℝ) = (q : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hdc
  refine ⟨uniformTrianglePacking G q hq hreg', ?_, ?_, ?_⟩
  · intro e f hef
    exact le_trans (uniform_codeg_le q hq hreg' hk4 e f hef) hgam
  · rw [uniform_mass q hq hreg' hk4]
    have : ((items G).card : ℝ) / (q : ℝ) = (G.edgeFinset.card : ℝ) / 3 := by
      field_simp
      linarith [hdcR]
    rw [this]
    exact hCst
  · rw [uniform_value q hq hreg' hk4]
    have hx := value_le_two_thirds_edges hk4 x
    have : 2 * ((items G).card : ℚ) / (q : ℚ) = (2 / 3 : ℚ) * (G.edgeFinset.card : ℚ) := by
      field_simp
      linarith [hdcQ]
    rw [this]
    exact hx

/-! ## 6. Casi regular: la limpieza con pérdida controlada por la razón `q/Q`

Relajando la regularidad exacta a una horquilla `q ≤ t(e) ≤ Q`, el mismo reparto uniforme (ahora
con peso `1/Q`) sigue siendo admisible y la pérdida de valor queda acotada por
`(2/3)·(1 - q/Q)·|E|`.  Con `q = Q` se recupera la pérdida cero. -/

/-- **La limpieza en grafos sin `K₄` casi triangularmente regulares.**

Hipótesis, todas visibles: `G` no tiene `K₄` (`hk4`), cada arista está en entre `q` y `Q`
triángulos (`hlo`, `hhi`), `1/Q ≤ gam` y `Cst ≤ q·|E|/(3Q)`.  La pérdida de valor está acotada
por `(2/3)·(1 - q/Q)·|E|`. -/
theorem nearRegular_cleanup (q Q : ℕ) (hQ : 0 < Q)
    (hk4 : ∀ K ∈ items G, K.card = 3)
    (hlo : ∀ e ∈ G.edgeFinset, q ≤ ((items G).filter (fun K => e ∈ pairs K)).card)
    (hhi : ∀ e ∈ G.edgeFinset, ((items G).filter (fun K => e ∈ pairs K)).card ≤ Q)
    (gam Cst : ℝ) (hgam : (1 : ℝ) / (Q : ℝ) ≤ gam)
    (hCst : Cst ≤ (q : ℝ) * (G.edgeFinset.card : ℝ) / (3 * (Q : ℝ)))
    (x : FracPacking G) :
    ∃ y : FracPacking G,
      (∀ e f : Sym2 (Fin n), e ≠ f →
        ∑ S ∈ (PaperIV.JointTypedNibbleGate.jointSupports G).filter
            (fun S => e ∈ S ∧ f ∈ S), inducedWeight y S ≤ gam) ∧
      Cst ≤ PaperIV.JointTwoQuotaPhysical.triangleMass y ∧
      x.value - y.value
        ≤ (2 / 3 : ℚ) * (1 - (q : ℚ) / (Q : ℚ)) * (G.edgeFinset.card : ℚ) := by
  classical
  have hQ0Q : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
  have hQ0R : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hdc : q * G.edgeFinset.card ≤ 3 * (items G).card := three_mul_card_items_ge q hk4 hlo
  have hdcQ : (q : ℚ) * (G.edgeFinset.card : ℚ) ≤ 3 * ((items G).card : ℚ) := by
    exact_mod_cast hdc
  have hdcR : (q : ℝ) * (G.edgeFinset.card : ℝ) ≤ 3 * ((items G).card : ℝ) := by
    exact_mod_cast hdc
  refine ⟨uniformTrianglePacking G Q hQ hhi, ?_, ?_, ?_⟩
  · intro e f hef
    exact le_trans (uniform_codeg_le Q hQ hhi hk4 e f hef) hgam
  · rw [uniform_mass Q hQ hhi hk4]
    refine le_trans hCst ?_
    rw [div_le_div_iff₀ (by positivity) hQ0R]
    nlinarith [hdcR]
  · rw [uniform_value Q hQ hhi hk4]
    have hx := value_le_two_thirds_edges hk4 x
    have hy : (2 / 3 : ℚ) * ((q : ℚ) / (Q : ℚ)) * (G.edgeFinset.card : ℚ)
        ≤ 2 * ((items G).card : ℚ) / (Q : ℚ) := by
      have hrw : (2 / 3 : ℚ) * ((q : ℚ) / (Q : ℚ)) * (G.edgeFinset.card : ℚ)
          = ((2 / 3 : ℚ) * (q : ℚ) * (G.edgeFinset.card : ℚ)) / (Q : ℚ) := by ring
      rw [hrw, div_le_div_iff₀ hQ0Q hQ0Q]
      nlinarith [hdcQ, hQ0Q]
    have hexp : (2 / 3 : ℚ) * (1 - (q : ℚ) / (Q : ℚ)) * (G.edgeFinset.card : ℚ)
        = (2 / 3 : ℚ) * (G.edgeFinset.card : ℚ)
          - (2 / 3 : ℚ) * ((q : ℚ) / (Q : ℚ)) * (G.edgeFinset.card : ℚ) := by ring
    rw [hexp]
    linarith [hx, hy]

end FarExploration.CleanupTriangleRegular
