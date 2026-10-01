import PaperIV.PatternCounting

/-!
# El octavo momento en un espacio finito (RC01 §13.1)

Bloque «Conteos» del contrato de RC01, primera mitad.

## Enunciado

Sean `X₁,…,X_m` mutuamente independientes, de media cero y con `|X_j| ≤ 1`.  Entonces

```
E (∑_j X_j)⁸  ≤  C₈ · m⁴,
```

y por Markov, para `z > 0`,

```
Pr( |∑_j X_j| ≥ z )  ≤  C₈ · m⁴ / z⁸.
```

No se supone distribución idéntica ni se necesita ninguna desigualdad exponencial de
concentración.  Es lo que consume §16.3 (concentración de los grados).

## Cómo

Se expande la octava potencia como suma sobre **funciones** `p : Fin 8 → Fin m`
(`Finset.sum_pow'`).  Un monomio en el que algún índice aparece **exactamente una vez** tiene
esperanza nula: al reagrupar (`Finset.prod_comp`) el factor de ese índice es `E[X_j] = 0`.  Los
que sobreviven tienen todas las fibras de tamaño `≠ 1`, luego **a lo sumo cuatro valores
distintos**, y cada uno de ellos se factoriza como `ι ∘ q` con `ι : Fin 4 → Fin m` y
`q : Fin 8 → Fin 4`.  Hay a lo sumo `m⁴ · 4⁸` de ésos, y cada esperanza está acotada por `1`.

Sale `C₈ = 4⁸ = 65536`, algo mejor que el `4⁹` que anuncia la fuente; se registran las dos.

## Independencia: la hipótesis exacta que se usa

Sólo se usa que **los momentos mixtos se factorizan**:
`E[∏_j X_j^{k_j}] = ∏_j E[X_j^{k_j}]` para todo multi-índice `k`.  Es consecuencia de la
independencia mutua, y es lo único que la prueba necesita.
-/

namespace PaperIV.EighthMoment

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## 1. Espacio de probabilidad finito y esperanza -/

/-- Un espacio de probabilidad finito con pesos racionales. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  /-- los pesos -/
  w : Ω → ℚ
  w_nonneg : ∀ ω, 0 ≤ w ω
  w_total : ∑ ω, w ω = 1

namespace FinProb

variable (P : FinProb Ω)

/-- La esperanza. -/
def expect (X : Ω → ℚ) : ℚ := ∑ ω, P.w ω * X ω

/-- La probabilidad de un suceso. -/
def prob (s : Finset Ω) : ℚ := ∑ ω ∈ s, P.w ω

theorem expect_const (c : ℚ) : P.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, P.w_total, one_mul]

theorem expect_mono {X Y : Ω → ℚ} (h : ∀ ω, X ω ≤ Y ω) : P.expect X ≤ P.expect Y :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.w_nonneg ω))

/-- Una cota uniforme sobre la variable acota su esperanza. -/
theorem abs_expect_le {X : Ω → ℚ} {c : ℚ} (h : ∀ ω, |X ω| ≤ c) : |P.expect X| ≤ c := by
  calc |P.expect X| ≤ ∑ ω, |P.w ω * X ω| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, P.w ω * |X ω| := by
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [abs_mul, abs_of_nonneg (P.w_nonneg ω)]
    _ ≤ ∑ ω, P.w ω * c :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.w_nonneg ω))
    _ = c := by rw [← Finset.sum_mul, P.w_total, one_mul]

theorem expect_sum {κ : Type*} (s : Finset κ) (f : κ → Ω → ℚ) :
    P.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, P.expect (f i) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem prob_nonneg (s : Finset Ω) : 0 ≤ P.prob s :=
  Finset.sum_nonneg (fun ω _ => P.w_nonneg ω)

/-- **Markov.**  Para una variable no negativa, `Pr(X ≥ z) ≤ E[X]/z`. -/
theorem markov {X : Ω → ℚ} (hX : ∀ ω, 0 ≤ X ω) {z : ℚ} (hz : 0 < z) :
    P.prob (univ.filter (fun ω => z ≤ X ω)) ≤ P.expect X / z := by
  classical
  rw [le_div_iff₀ hz]
  have hstep : P.prob (univ.filter (fun ω => z ≤ X ω)) * z
      = ∑ ω ∈ univ.filter (fun ω => z ≤ X ω), P.w ω * z := by
    unfold prob
    rw [Finset.sum_mul]
  rw [hstep]
  have h1 : ∑ ω ∈ univ.filter (fun ω => z ≤ X ω), P.w ω * z
      ≤ ∑ ω ∈ univ.filter (fun ω => z ≤ X ω), P.w ω * X ω := by
    refine Finset.sum_le_sum (fun ω hω => ?_)
    rw [Finset.mem_filter] at hω
    exact mul_le_mul_of_nonneg_left hω.2 (P.w_nonneg ω)
  refine le_trans h1 ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro ω _ _
  exact mul_nonneg (P.w_nonneg ω) (hX ω)

end FinProb

/-! ## 2. Expansión, reagrupación y anulación -/

/-- **La expansión.**  La potencia `n`-ésima de una suma es la suma sobre las funciones
`p : Fin n → Fin m` de los monomios correspondientes. -/
theorem expect_pow_eq_sum (P : FinProb Ω) {m : ℕ} (X : Fin m → Ω → ℚ) (n : ℕ) :
    P.expect (fun ω => (∑ j, X j ω) ^ n)
      = ∑ p ∈ Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin m))),
          P.expect (fun ω => ∏ i, X (p i) ω) := by
  classical
  have hexp : (fun ω => (∑ j, X j ω) ^ n)
      = fun ω => ∑ p ∈ Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin m))),
          ∏ i, X (p i) ω := by
    funext ω
    exact Finset.sum_pow' univ (fun j => X j ω) n
  rw [hexp]
  exact P.expect_sum _ _

/-- **Reagrupación.**  Un monomio es el producto de las potencias dadas por los tamaños de las
fibras. -/
theorem prod_eq_prod_pow_count {m n : ℕ} (p : Fin n → Fin m) (Y : Fin m → ℚ) :
    ∏ i, Y (p i) = ∏ j, (Y j) ^ ((univ.filter (fun i => p i = j)).card) := by
  classical
  rw [Finset.prod_comp]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro j _ hj
  have hzero : (univ.filter (fun i => p i = j)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ h
    exact hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, h⟩)
  rw [hzero, pow_zero]

/-- **Anulación.**  Si algún índice aparece exactamente una vez, el monomio tiene esperanza
nula: al factorizar, su factor es `E[X_j] = 0`. -/
theorem expect_prod_eq_zero (P : FinProb Ω) {m n : ℕ} (X : Fin m → Ω → ℚ)
    (hfac : ∀ k : Fin m → ℕ,
      P.expect (fun ω => ∏ j, (X j ω) ^ (k j)) = ∏ j, P.expect (fun ω => (X j ω) ^ (k j)))
    (hzero : ∀ j, P.expect (X j) = 0)
    (p : Fin n → Fin m) {j₀ : Fin m}
    (hj₀ : (univ.filter (fun i => p i = j₀)).card = 1) :
    P.expect (fun ω => ∏ i, X (p i) ω) = 0 := by
  classical
  have hre : (fun ω => ∏ i, X (p i) ω)
      = fun ω => ∏ j, (X j ω) ^ ((univ.filter (fun i => p i = j)).card) :=
    funext (fun ω => prod_eq_prod_pow_count p (fun j => X j ω))
  rw [hre, hfac]
  refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
  have hfun : (fun ω => (X j₀ ω) ^ ((univ.filter (fun i => p i = j₀)).card)) = X j₀ := by
    rw [hj₀]
    funext ω
    rw [pow_one]
  rw [hfun]
  exact hzero j₀

/-- Cada monomio tiene esperanza acotada por `1`. -/
theorem abs_expect_prod_le_one (P : FinProb Ω) {m n : ℕ} (X : Fin m → Ω → ℚ)
    (hb : ∀ j ω, |X j ω| ≤ 1) (p : Fin n → Fin m) :
    |P.expect (fun ω => ∏ i, X (p i) ω)| ≤ 1 := by
  refine P.abs_expect_le ?_
  intro ω
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hb _ ω)


/-! ## 3. Contar los monomios que sobreviven -/

/-- Las funciones cuyas fibras no tienen tamaño `1`: exactamente los monomios que la
anulación de §2 **no** mata. -/
def good (m n : ℕ) : Finset (Fin n → Fin m) :=
  (univ : Finset (Fin n → Fin m)).filter
    (fun p => ∀ j : Fin m, (univ.filter (fun i => p i = j)).card ≠ 1)

/-- Si ninguna fibra tiene tamaño `1`, todas tienen tamaño `≥ 2`, luego hay a lo sumo `n/2`
valores distintos. -/
theorem two_mul_card_image_le {m n : ℕ} {p : Fin n → Fin m} (hp : p ∈ good m n) :
    2 * (univ.image p).card ≤ n := by
  classical
  rw [good, Finset.mem_filter] at hp
  have hcount : (univ : Finset (Fin n)).card
      = ∑ j ∈ univ.image p, (univ.filter (fun i => p i = j)).card :=
    Finset.card_eq_sum_card_image p univ
  have hge : ∀ j ∈ univ.image p, 2 ≤ (univ.filter (fun i => p i = j)).card := by
    intro j hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hj
    have h1 : 1 ≤ (univ.filter (fun i => p i = j)).card := by
      refine Finset.card_pos.2 ⟨i, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi⟩
    have h2 := hp.2 j
    omega
  have hle : 2 * (univ.image p).card
      ≤ ∑ j ∈ univ.image p, (univ.filter (fun i => p i = j)).card := by
    calc 2 * (univ.image p).card = ∑ _j ∈ univ.image p, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hge
  rw [← hcount] at hle
  simpa using hle

/-- **Factorización.**  Un monomio superviviente de grado `8` toma a lo sumo cuatro valores,
luego se escribe como `ι ∘ q` con `ι : Fin 4 → Fin m` y `q : Fin 8 → Fin 4`. -/
theorem exists_factor {m : ℕ} {p : Fin 8 → Fin m} (hp : p ∈ good m 8) :
    ∃ (ι : Fin 4 → Fin m) (q : Fin 8 → Fin 4), (fun i => ι (q i)) = p := by
  classical
  have hmem : ∀ i : Fin 8, p i ∈ univ.image p :=
    fun i => Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have hc4 : (univ.image p).card ≤ 4 := by
    have := two_mul_card_image_le hp
    omega
  refine ⟨fun k => if h : (k : ℕ) < (univ.image p).card
      then (((univ.image p).equivFin.symm ⟨(k : ℕ), h⟩ : {x // x ∈ univ.image p}) : Fin m)
      else p 0,
    fun i => ⟨(((univ.image p).equivFin ⟨p i, hmem i⟩ : Fin (univ.image p).card) : ℕ),
      lt_of_lt_of_le ((univ.image p).equivFin ⟨p i, hmem i⟩).isLt hc4⟩, ?_⟩
  funext i
  dsimp only
  have h : (((univ.image p).equivFin ⟨p i, hmem i⟩ : Fin (univ.image p).card) : ℕ)
      < (univ.image p).card := ((univ.image p).equivFin ⟨p i, hmem i⟩).isLt
  rw [dif_pos h]
  have hfin : (⟨(((univ.image p).equivFin ⟨p i, hmem i⟩ : Fin (univ.image p).card) : ℕ), h⟩ :
        Fin (univ.image p).card)
      = (univ.image p).equivFin ⟨p i, hmem i⟩ := rfl
  rw [hfin, Equiv.symm_apply_apply]

/-- **La cuenta.**  A lo sumo `m⁴ · 4⁸` monomios de grado `8` sobreviven. -/
theorem card_good_le (m : ℕ) : (good m 8).card ≤ m ^ 4 * 4 ^ 8 := by
  classical
  have hsub : good m 8 ⊆ Finset.image
      (fun x : (Fin 4 → Fin m) × (Fin 8 → Fin 4) => fun i => x.1 (x.2 i)) univ := by
    intro p hp
    obtain ⟨ι, q, hq⟩ := exists_factor hp
    exact Finset.mem_image.2 ⟨(ι, q), Finset.mem_univ _, hq⟩
  calc (good m 8).card
      ≤ (Finset.image
          (fun x : (Fin 4 → Fin m) × (Fin 8 → Fin 4) => fun i => x.1 (x.2 i)) univ).card :=
        Finset.card_le_card hsub
    _ ≤ (univ : Finset ((Fin 4 → Fin m) × (Fin 8 → Fin 4))).card := Finset.card_image_le
    _ = m ^ 4 * 4 ^ 8 := by
        rw [Finset.card_univ]
        simp [Fintype.card_prod, Fintype.card_fun]


/-! ## 4. El octavo momento, y su cola por Markov -/

theorem FinProb.prob_mono (P : FinProb Ω) {s t : Finset Ω} (h : s ⊆ t) :
    P.prob s ≤ P.prob t :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun ω _ _ => P.w_nonneg ω)

set_option maxHeartbeats 1000000 in
/-- **El octavo momento (RC01 §13.1, ec. (13.1)).**  Para variables de media cero, acotadas por
`1`, y cuyos momentos mixtos se factorizan,

```
E (∑_j X_j)⁸  ≤  4⁸ · m⁴.
```

La constante `4⁸ = 65536` mejora el `4⁹` que anuncia la fuente; ver `eighth_moment_source`. -/
theorem eighth_moment (P : FinProb Ω) {m : ℕ} (X : Fin m → Ω → ℚ)
    (hfac : ∀ k : Fin m → ℕ,
      P.expect (fun ω => ∏ j, (X j ω) ^ (k j)) = ∏ j, P.expect (fun ω => (X j ω) ^ (k j)))
    (hzero : ∀ j, P.expect (X j) = 0)
    (hb : ∀ j ω, |X j ω| ≤ 1) :
    P.expect (fun ω => (∑ j, X j ω) ^ 8) ≤ 4 ^ 8 * (m : ℚ) ^ 4 := by
  classical
  -- expandir
  have hexp := expect_pow_eq_sum P X 8
  rw [Fintype.piFinset_univ] at hexp
  -- los monomios con un índice aislado se anulan
  have hzeroTerm : ∀ p ∈ (univ : Finset (Fin 8 → Fin m)).filter
      (fun p => ¬ ∀ j : Fin m, (univ.filter (fun i => p i = j)).card ≠ 1),
      P.expect (fun ω => ∏ i, X (p i) ω) = 0 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h2 := hp.2
    push_neg at h2
    obtain ⟨j₀, hj₀⟩ := h2
    exact expect_prod_eq_zero P X hfac hzero p hj₀
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin 8 → Fin m))
    (fun p => ∀ j : Fin m, (univ.filter (fun i => p i = j)).card ≠ 1)
    (fun p => P.expect (fun ω => ∏ i, X (p i) ω))
  rw [Finset.sum_eq_zero hzeroTerm, add_zero] at hsplit
  have hEq : P.expect (fun ω => (∑ j, X j ω) ^ 8)
      = ∑ p ∈ good m 8, P.expect (fun ω => ∏ i, X (p i) ω) := by
    rw [hexp, ← hsplit, good]
  -- cada monomio superviviente aporta a lo sumo `1`
  have habs : |∑ p ∈ good m 8, P.expect (fun ω => ∏ i, X (p i) ω)|
      ≤ ((good m 8).card : ℚ) := by
    calc |∑ p ∈ good m 8, P.expect (fun ω => ∏ i, X (p i) ω)|
        ≤ ∑ p ∈ good m 8, |P.expect (fun ω => ∏ i, X (p i) ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ good m 8, (1 : ℚ) :=
          Finset.sum_le_sum (fun p _ => abs_expect_prod_le_one P X hb p)
      _ = ((good m 8).card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((good m 8).card : ℚ) ≤ (m : ℚ) ^ 4 * 4 ^ 8 := by
    exact_mod_cast card_good_le m
  have hle := (abs_le.1 habs).2
  rw [← hEq] at hle
  calc P.expect (fun ω => (∑ j, X j ω) ^ 8) ≤ ((good m 8).card : ℚ) := hle
    _ ≤ (m : ℚ) ^ 4 * 4 ^ 8 := hcard
    _ = 4 ^ 8 * (m : ℚ) ^ 4 := by ring

/-- La misma cota con la constante que anuncia la fuente, `C₈ = 4⁹ = 262144`. -/
theorem eighth_moment_source (P : FinProb Ω) {m : ℕ} (X : Fin m → Ω → ℚ)
    (hfac : ∀ k : Fin m → ℕ,
      P.expect (fun ω => ∏ j, (X j ω) ^ (k j)) = ∏ j, P.expect (fun ω => (X j ω) ^ (k j)))
    (hzero : ∀ j, P.expect (X j) = 0)
    (hb : ∀ j ω, |X j ω| ≤ 1) :
    P.expect (fun ω => (∑ j, X j ω) ^ 8) ≤ 4 ^ 9 * (m : ℚ) ^ 4 := by
  have h := eighth_moment P X hfac hzero hb
  have hm : (0 : ℚ) ≤ (m : ℚ) ^ 4 := by positivity
  nlinarith [h, hm]

set_option maxHeartbeats 1000000 in
/-- **La cola (RC01 §13.1, ec. (13.2)).**  Por Markov aplicado a la octava potencia,

```
Pr( |∑_j X_j| ≥ z )  ≤  4⁸ · m⁴ / z⁸.
```

Sin desigualdad exponencial de concentración y sin distribución idéntica. -/
theorem tail_bound (P : FinProb Ω) {m : ℕ} (X : Fin m → Ω → ℚ)
    (hfac : ∀ k : Fin m → ℕ,
      P.expect (fun ω => ∏ j, (X j ω) ^ (k j)) = ∏ j, P.expect (fun ω => (X j ω) ^ (k j)))
    (hzero : ∀ j, P.expect (X j) = 0)
    (hb : ∀ j ω, |X j ω| ≤ 1)
    {z : ℚ} (hz : 0 < z) :
    P.prob (univ.filter (fun ω => z ≤ |∑ j, X j ω|))
      ≤ 4 ^ 8 * (m : ℚ) ^ 4 / z ^ 8 := by
  classical
  have hz8 : (0 : ℚ) < z ^ 8 := by positivity
  -- el suceso está contenido en el de la octava potencia
  have hsub : (univ.filter (fun ω => z ≤ |∑ j, X j ω|))
      ⊆ (univ.filter (fun ω => z ^ 8 ≤ (∑ j, X j ω) ^ 8)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ ω, ?_⟩
    have hpow : z ^ 8 ≤ |∑ j, X j ω| ^ 8 :=
      pow_le_pow_left₀ (le_of_lt hz) hω.2 8
    have heven : |∑ j, X j ω| ^ 8 = (∑ j, X j ω) ^ 8 := by
      rw [pow_abs, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (∑ j, X j ω) ^ 8)]
    rwa [heven] at hpow
  have hmk := P.markov (X := fun ω => (∑ j, X j ω) ^ 8)
    (fun ω => by positivity) hz8
  have hmom := eighth_moment P X hfac hzero hb
  calc P.prob (univ.filter (fun ω => z ≤ |∑ j, X j ω|))
      ≤ P.prob (univ.filter (fun ω => z ^ 8 ≤ (∑ j, X j ω) ^ 8)) := P.prob_mono hsub
    _ ≤ P.expect (fun ω => (∑ j, X j ω) ^ 8) / z ^ 8 := hmk
    _ ≤ 4 ^ 8 * (m : ℚ) ^ 4 / z ^ 8 := by
        rw [div_le_div_iff_of_pos_right hz8]
        exact hmom

end PaperIV.EighthMoment
