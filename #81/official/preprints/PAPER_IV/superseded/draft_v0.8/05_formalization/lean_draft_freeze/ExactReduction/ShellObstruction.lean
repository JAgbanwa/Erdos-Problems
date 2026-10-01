import PaperIV.FarRounding
import ExactReduction.Arithmetic

/-!
# La obstrucción exacta de la cáscara `S ⊔ R` (por qué falla la reducción por una bolsa)

Una **reducción por bolsa hoja** quiere borrar los vértices privados `R` de una bolsa
`B = S ⊔ R` del árbol de cliques (con `S` el separador), pagando sólo el presupuesto
`M(n) − M(n−r)` y aplicando la hipótesis de inducción a `G − R`.  Las piezas admisibles
son las que **no consumen aristas internas de `S`**, porque esas pertenecen a la partición
del resto; equivalentemente, cada pieza contiene a lo sumo un vértice de `S`.

Este módulo define exactamente esa noción (`ShellCover`) y demuestra la cota inferior

```text
|S| · |R| ≤ (número de piezas) + C(|R|, 2)                (shellCover_card_ge)
```

La demostración es un conteo por pieza: si una pieza `K` contiene un vértice de `S` y
`q = |K ∩ R|` vértices privados, cubre exactamente `q` aristas cruzadas y consume
`C(q,2)` aristas internas de `R`, y siempre `q ≤ 1 + C(q,2)`.  Sumando sobre las piezas
(disjuntas en aristas) y usando que sólo hay `C(|R|,2)` aristas internas disponibles se
obtiene la cota.  **No** se supone ninguna restricción de tamaño de las piezas: la cota
vale también contra particiones sin cota de orden, no sólo contra `c₄`.

Combinada con `ExactReduction.leafShell_budget_lt` esto convierte en teorema la evidencia
finita obtenida por búsqueda: la reducción de *una sola* bolsa es imposible en cuanto
`|R| ≤ |S|` (salvo el caso trivial `|R| = |S| = 1`).  El caso concreto `(s,r) = (3,2)`
aparece como `shell_three_two_exceeds_budget`.
-/

namespace ExactReduction.ShellObstruction

open PaperIV PaperIV.FarRounding Finset

variable {V : Type*} [DecidableEq V]

/-! ## 1. Los pares cruzados -/

/-- Los pares con un extremo en `S` y el otro en `R`. -/
def crossPairs (S R : Finset V) : Finset (Sym2 V) :=
  (S ×ˢ R).image fun p => s(p.1, p.2)

theorem mem_crossPairs {S R : Finset V} {e : Sym2 V} :
    e ∈ crossPairs S R ↔ ∃ a ∈ S, ∃ b ∈ R, e = s(a, b) := by
  simp only [crossPairs, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem card_crossPairs {S R : Finset V} (hd : Disjoint S R) :
    (crossPairs S R).card = S.card * R.card := by
  rw [crossPairs, Finset.card_image_of_injOn, Finset.card_product]
  intro p hp q hq hpq
  simp only [Finset.mem_coe, Finset.mem_product] at hp hq
  have h := Sym2.eq_iff.1 hpq
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exact absurd hp.1 (fun hmem => (Finset.disjoint_left.1 hd hmem) (h1 ▸ hq.2))

theorem card_crossPairs_le (S R : Finset V) :
    (crossPairs S R).card ≤ S.card * R.card := by
  rw [crossPairs, ← Finset.card_product S R]
  exact Finset.card_image_le

/-! ## 2. Intersecciones de soportes de aristas -/

theorem pairs_inter (A B : Finset V) : pairs A ∩ pairs B = pairs (A ∩ B) := by
  ext e
  simp only [Finset.mem_inter, mem_pairs, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hA, hd⟩, ⟨hB, -⟩⟩
    exact ⟨fun a ha => ⟨hA a ha, hB a ha⟩, hd⟩
  · rintro ⟨hAB, hd⟩
    exact ⟨⟨fun a ha => (hAB a ha).1, hd⟩, ⟨fun a ha => (hAB a ha).2, hd⟩⟩

/-- La desigualdad puntual que gobierna la cáscara: una pieza con `q` vértices privados
cubre a lo sumo `q` aristas cruzadas, y `q ≤ 1 + C(q,2)`. -/
theorem le_one_add_choose_two (q : ℕ) : q ≤ 1 + q.choose 2 := by
  rcases Nat.lt_or_ge q 2 with h | h
  · interval_cases q <;> simp
  · have h2 := ExactReduction.two_mul_choose_two q
    have : 2 * (q - 1) ≤ q * (q - 1) := Nat.mul_le_mul_right _ h
    omega

/-! ## 3. Cubrimientos de cáscara -/

/-- Un **cubrimiento de la cáscara** `S ⊔ R`: una familia de piezas disjuntas en aristas,
cada una con a lo sumo un vértice del separador `S` (luego ninguna consume aristas internas
de `S`), que cubre todas las aristas cruzadas y todas las internas de `R`. -/
structure ShellCover (S R : Finset V) where
  /-- Las piezas del cubrimiento. -/
  pieces : Finset (Finset V)
  /-- Ninguna pieza toca dos vértices del separador. -/
  meet_sep : ∀ K ∈ pieces, (K ∩ S).card ≤ 1
  /-- Las piezas son disjuntas en aristas. -/
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  /-- Se cubre todo `E(B) \ E(S)`. -/
  covers : crossPairs S R ∪ pairs R ⊆ pieces.biUnion pairs

variable {S R : Finset V}

private theorem biUnion_inter_eq (C : ShellCover S R) {T : Finset (Sym2 V)}
    (hT : T ⊆ C.pieces.biUnion pairs) :
    T = C.pieces.biUnion fun K => T ∩ pairs K := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · intro he
    obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hT he)
    exact ⟨K, hK, he, heK⟩
  · rintro ⟨K, -, he, -⟩
    exact he

private theorem card_eq_sum (C : ShellCover S R) {T : Finset (Sym2 V)}
    (hT : T ⊆ C.pieces.biUnion pairs) :
    T.card = ∑ K ∈ C.pieces, (T ∩ pairs K).card := by
  conv_lhs => rw [biUnion_inter_eq C hT]
  refine Finset.card_biUnion ?_
  intro K hK L hL hKL
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))

private theorem sum_inter_le (C : ShellCover S R) (T : Finset (Sym2 V)) :
    ∑ K ∈ C.pieces, (T ∩ pairs K).card ≤ T.card := by
  classical
  have hdisj : ∀ K ∈ C.pieces, ∀ L ∈ C.pieces, K ≠ L →
      Disjoint (T ∩ pairs K) (T ∩ pairs L) := fun K hK L hL hKL =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))
  have hcard : (C.pieces.biUnion fun K => T ∩ pairs K).card
      = ∑ K ∈ C.pieces, (T ∩ pairs K).card := Finset.card_biUnion hdisj
  rw [← hcard]
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨K, -, heK⟩ := Finset.mem_biUnion.1 he
  exact (Finset.mem_inter.1 heK).1

/-- Cota por pieza: aristas cruzadas cubiertas `≤ 1 +` aristas internas de `R` consumidas. -/
theorem piece_bound (K : Finset V) (hK : (K ∩ S).card ≤ 1) :
    (crossPairs S R ∩ pairs K).card ≤ 1 + (pairs R ∩ pairs K).card := by
  have hsub : crossPairs S R ∩ pairs K ⊆ crossPairs (K ∩ S) (K ∩ R) := by
    intro e he
    obtain ⟨hcross, hpairs⟩ := Finset.mem_inter.1 he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hcross
    obtain ⟨haK, hbK, -⟩ := mk_mem_pairs.1 hpairs
    exact mem_crossPairs.2 ⟨a, Finset.mem_inter.2 ⟨haK, ha⟩, b, Finset.mem_inter.2 ⟨hbK, hb⟩, rfl⟩
  have h1 : (crossPairs S R ∩ pairs K).card ≤ (K ∩ S).card * (K ∩ R).card :=
    le_trans (Finset.card_le_card hsub) (card_crossPairs_le _ _)
  have h2 : (K ∩ S).card * (K ∩ R).card ≤ (K ∩ R).card := by
    calc (K ∩ S).card * (K ∩ R).card ≤ 1 * (K ∩ R).card :=
          Nat.mul_le_mul_right _ hK
      _ = (K ∩ R).card := one_mul _
  have h3 : (pairs R ∩ pairs K).card = (K ∩ R).card.choose 2 := by
    rw [pairs_inter, card_pairs, Finset.inter_comm]
  have h4 : (K ∩ R).card ≤ 1 + (K ∩ R).card.choose 2 := le_one_add_choose_two _
  omega

/-- **Cota inferior de coste de la cáscara.**  Todo cubrimiento de `E(S ⊔ R) \ E(S)` por
piezas disjuntas en aristas, cada una con a lo sumo un vértice del separador, usa al menos
`|S|·|R| − C(|R|,2)` piezas. -/
theorem shellCover_card_ge (hd : Disjoint S R) (C : ShellCover S R) :
    S.card * R.card ≤ C.pieces.card + R.card.choose 2 := by
  have hcross : crossPairs S R ⊆ C.pieces.biUnion pairs := fun e he =>
    C.covers (Finset.mem_union_left _ he)
  have hsum : (crossPairs S R).card
      = ∑ K ∈ C.pieces, (crossPairs S R ∩ pairs K).card := card_eq_sum C hcross
  have hstep : ∑ K ∈ C.pieces, (crossPairs S R ∩ pairs K).card
      ≤ ∑ K ∈ C.pieces, (1 + (pairs R ∩ pairs K).card) :=
    Finset.sum_le_sum fun K hK => piece_bound K (C.meet_sep K hK)
  have hsplit : ∑ K ∈ C.pieces, (1 + (pairs R ∩ pairs K).card)
      = C.pieces.card + ∑ K ∈ C.pieces, (pairs R ∩ pairs K).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hinner : ∑ K ∈ C.pieces, (pairs R ∩ pairs K).card ≤ R.card.choose 2 := by
    have := sum_inter_le C (pairs R)
    rwa [card_pairs] at this
  rw [card_crossPairs hd] at hsum
  omega

/-! ## 4. La noción no es vacía: el cubrimiento trivial por `K₂` -/

theorem not_isDiag_of_mem_shell (hd : Disjoint S R) {e : Sym2 V}
    (he : e ∈ crossPairs S R ∪ pairs R) : ¬ e.IsDiag := by
  rcases Finset.mem_union.1 he with hc | hi
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hc
    have hab : a ≠ b := fun h => (Finset.disjoint_left.1 hd ha) (h ▸ hb)
    simpa [Sym2.isDiag_iff_proj_eq] using hab
  · exact (mem_pairs.1 hi).2

theorem inter_sep_card_le_one (hd : Disjoint S R) {e : Sym2 V}
    (he : e ∈ crossPairs S R ∪ pairs R) : (e.toFinset ∩ S).card ≤ 1 := by
  rcases Finset.mem_union.1 he with hc | hi
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hc
    have hbS : b ∉ S := fun h => (Finset.disjoint_left.1 hd h) hb
    have hsub : (Sym2.toFinset s(a, b)) ∩ S ⊆ {a} := by
      intro x hx
      obtain ⟨hxe, hxS⟩ := Finset.mem_inter.1 hx
      have : x = a ∨ x = b := by simpa using hxe
      rcases this with rfl | rfl
      · simp
      · exact absurd hxS hbS
    exact le_trans (Finset.card_le_card hsub) (by simp)
  · have hsub : (Sym2.toFinset e) ∩ S = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 ?_
      intro x hx
      obtain ⟨hxe, hxS⟩ := Finset.mem_inter.1 hx
      have hxR : x ∈ R := (mem_pairs.1 hi).1 x (by simpa using hxe)
      exact (Finset.disjoint_left.1 hd hxS) hxR
    simp [hsub]

/-- El cubrimiento trivial: una pieza `K₂` por cada arista de la cáscara.  Demuestra que
`ShellCover` no es una noción vacía; su coste es `|S|·|R| + C(|R|,2)`, es decir, exactamente
`C(|R|,2)` piezas por encima de la cota inferior `shellCover_card_ge`. -/
def trivialShellCover (hd : Disjoint S R) : ShellCover S R where
  pieces := (crossPairs S R ∪ pairs R).image Sym2.toFinset
  meet_sep := by
    intro K hK
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    exact inter_sep_card_le_one hd he
  edgeDisjoint := by
    intro K hK L hL hKL
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hL
    rw [pairs_toFinset (not_isDiag_of_mem_shell hd he),
      pairs_toFinset (not_isDiag_of_mem_shell hd hf)]
    simp only [Finset.disjoint_singleton]
    exact fun h => hKL (by rw [h])
  covers := by
    intro e he
    refine Finset.mem_biUnion.2 ⟨e.toFinset, Finset.mem_image_of_mem _ he, ?_⟩
    rw [pairs_toFinset (not_isDiag_of_mem_shell hd he)]
    exact Finset.mem_singleton_self e

theorem card_trivialShellCover (hd : Disjoint S R) :
    (trivialShellCover hd).pieces.card = S.card * R.card + R.card.choose 2 := by
  have hinj : Set.InjOn Sym2.toFinset ((crossPairs S R ∪ pairs R : Finset (Sym2 V)) : Set (Sym2 V)) := by
    intro e he f hf hef
    have hne : ¬ e.IsDiag := not_isDiag_of_mem_shell hd (by simpa using he)
    have hnf : ¬ f.IsDiag := not_isDiag_of_mem_shell hd (by simpa using hf)
    have h1 : pairs e.toFinset = ({e} : Finset (Sym2 V)) := pairs_toFinset hne
    have h2 : pairs f.toFinset = ({f} : Finset (Sym2 V)) := pairs_toFinset hnf
    rw [hef, h2] at h1
    simpa [eq_comm] using (Finset.singleton_injective h1)
  have hdisj : Disjoint (crossPairs S R) (pairs R) := by
    refine Finset.disjoint_left.2 ?_
    intro e he hf
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 he
    have haR : a ∈ R := (mem_pairs.1 hf).1 a (by simp)
    exact (Finset.disjoint_left.1 hd ha) haR
  show ((crossPairs S R ∪ pairs R).image Sym2.toFinset).card = _
  rw [Finset.card_image_of_injOn hinj, Finset.card_union_of_disjoint hdisj,
    card_crossPairs hd, card_pairs]

/-! ## 5. Consecuencia: la reducción por una sola bolsa hoja no cabe en el presupuesto -/

/-- **La reducción por una bolsa hoja es imposible cuando `|R| ≤ |S|`.**  Para cualquier
cubrimiento admisible de la cáscara, el coste supera estrictamente el presupuesto
`M(|S|+|R|) − M(|S|)` que la inducción tendría disponible. -/
theorem leafShell_reduction_fails (hd : Disjoint S R) (C : ShellCover S R)
    (hr : 1 ≤ R.card) (hrs : R.card ≤ S.card) (hnt : 2 ≤ R.card ∨ 2 ≤ S.card) :
    PaperIV.targetSize (S.card + R.card) < PaperIV.targetSize S.card + C.pieces.card := by
  have hlow := shellCover_card_ge hd C
  have hbudget := ExactReduction.leafShell_budget_lt (s := S.card) (r := R.card) hr hrs hnt
  omega

/-! ## 6. Con crédito de separador la obstrucción de conteo desaparece

La reducción por una bolsa aislada prohíbe consumir `E(S)`.  Si en cambio se permite que
las piezas de la bolsa alojen aristas del separador —que es lo que hace la partición óptima
del completo-split, con triángulos `{x,y,z}`, `x,y ∈ S`, `z ∈ R`— el conteo cambia y ya no
produce ninguna contradicción.  Esto localiza el fallo de la reducción local: no está en
las bolsas, sino en la contabilidad de las aristas del separador. -/

/-- Cáscara **con crédito de separador**: las piezas pueden usar aristas internas de `S`,
pero tienen a lo sumo cuatro vértices (el modelo físico `c₄`). -/
structure ShellCoverCredit (S R : Finset V) where
  /-- Las piezas del cubrimiento. -/
  pieces : Finset (Finset V)
  /-- Modelo físico: piezas de orden a lo sumo cuatro. -/
  card_le_four : ∀ K ∈ pieces, K.card ≤ 4
  /-- Las piezas son disjuntas en aristas. -/
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  /-- Se cubre todo `E(B) \ E(S)`. -/
  covers : crossPairs S R ∪ pairs R ⊆ pieces.biUnion pairs

private theorem card_eq_sum' (C : ShellCoverCredit S R) {T : Finset (Sym2 V)}
    (hT : T ⊆ C.pieces.biUnion pairs) :
    T.card = ∑ K ∈ C.pieces, (T ∩ pairs K).card := by
  have hb : T = C.pieces.biUnion fun K => T ∩ pairs K := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro he
      obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.1 (hT he)
      exact ⟨K, hK, he, heK⟩
    · rintro ⟨K, -, he, -⟩
      exact he
  conv_lhs => rw [hb]
  refine Finset.card_biUnion ?_
  intro K hK L hL hKL
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))

private theorem sum_inter_le' (C : ShellCoverCredit S R) (T : Finset (Sym2 V)) :
    ∑ K ∈ C.pieces, (T ∩ pairs K).card ≤ T.card := by
  have hdisj : ∀ K ∈ C.pieces, ∀ L ∈ C.pieces, K ≠ L →
      Disjoint (T ∩ pairs K) (T ∩ pairs L) := fun K hK L hL hKL =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (C.edgeDisjoint K hK L hL hKL))
  rw [← Finset.card_biUnion hdisj]
  refine Finset.card_le_card ?_
  intro e he
  obtain ⟨K, -, heK⟩ := Finset.mem_biUnion.1 he
  exact (Finset.mem_inter.1 heK).1

/-- La desigualdad puntual con crédito: `2jq ≤ 2 + 3·C(j,2) + 3·C(q,2)` si `j + q ≤ 4`. -/
theorem two_mul_le_credit {j q : ℕ} (h : j + q ≤ 4) :
    2 * (j * q) ≤ 2 + 3 * j.choose 2 + 3 * q.choose 2 := by
  have hj : j ≤ 4 := by omega
  have hq : q ≤ 4 := by omega
  interval_cases j <;> interval_cases q <;> simp_all [Nat.choose]

/-- Cota por pieza en el modelo con crédito de separador. -/
theorem piece_bound_credit (hd : Disjoint S R) (K : Finset V) (hK : K.card ≤ 4) :
    2 * (crossPairs S R ∩ pairs K).card
      ≤ 2 + 3 * (pairs S ∩ pairs K).card + 3 * (pairs R ∩ pairs K).card := by
  have hsub : crossPairs S R ∩ pairs K ⊆ crossPairs (K ∩ S) (K ∩ R) := by
    intro e he
    obtain ⟨hcross, hpairs⟩ := Finset.mem_inter.1 he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_crossPairs.1 hcross
    obtain ⟨haK, hbK, -⟩ := mk_mem_pairs.1 hpairs
    exact mem_crossPairs.2 ⟨a, Finset.mem_inter.2 ⟨haK, ha⟩, b, Finset.mem_inter.2 ⟨hbK, hb⟩, rfl⟩
  have h1 : (crossPairs S R ∩ pairs K).card ≤ (K ∩ S).card * (K ∩ R).card :=
    le_trans (Finset.card_le_card hsub) (card_crossPairs_le _ _)
  have hdisjKK : Disjoint (K ∩ S) (K ∩ R) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd)
  have hsum : (K ∩ S).card + (K ∩ R).card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint hdisjKK]
    exact le_trans (Finset.card_le_card (by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx <;> exact (Finset.mem_inter.1 hx).1)) hK
  have hS : (pairs S ∩ pairs K).card = (K ∩ S).card.choose 2 := by
    rw [pairs_inter, card_pairs, Finset.inter_comm]
  have hR : (pairs R ∩ pairs K).card = (K ∩ R).card.choose 2 := by
    rw [pairs_inter, card_pairs, Finset.inter_comm]
  have hkey := two_mul_le_credit hsum
  omega

/-- **Cota inferior con crédito de separador.**  Permitir que las piezas de la bolsa alojen
aristas internas de `S` rebaja la cota a `s·r − (3/2)(C(s,2) + C(r,2))`, que —a diferencia
de `shellCover_card_ge`— nunca supera el presupuesto `M(s+r) − M(s)`
(`credit_bound_within_budget`). -/
theorem shellCoverCredit_card_ge (hd : Disjoint S R) (C : ShellCoverCredit S R) :
    2 * (S.card * R.card)
      ≤ 2 * C.pieces.card + 3 * S.card.choose 2 + 3 * R.card.choose 2 := by
  have hcross : crossPairs S R ⊆ C.pieces.biUnion pairs := fun e he =>
    C.covers (Finset.mem_union_left _ he)
  have hsum : (crossPairs S R).card
      = ∑ K ∈ C.pieces, (crossPairs S R ∩ pairs K).card := card_eq_sum' C hcross
  have hstep : ∑ K ∈ C.pieces, 2 * (crossPairs S R ∩ pairs K).card
      ≤ ∑ K ∈ C.pieces, (2 + 3 * (pairs S ∩ pairs K).card + 3 * (pairs R ∩ pairs K).card) :=
    Finset.sum_le_sum fun K hK => piece_bound_credit hd K (C.card_le_four K hK)
  have hl : ∑ K ∈ C.pieces, 2 * (crossPairs S R ∩ pairs K).card
      = 2 * ∑ K ∈ C.pieces, (crossPairs S R ∩ pairs K).card := by
    rw [Finset.mul_sum]
  have hr : ∑ K ∈ C.pieces, (2 + 3 * (pairs S ∩ pairs K).card + 3 * (pairs R ∩ pairs K).card)
      = 2 * C.pieces.card + 3 * (∑ K ∈ C.pieces, (pairs S ∩ pairs K).card)
        + 3 * (∑ K ∈ C.pieces, (pairs R ∩ pairs K).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, Nat.mul_comm C.pieces.card 2]
  have hS : ∑ K ∈ C.pieces, (pairs S ∩ pairs K).card ≤ S.card.choose 2 := by
    have := sum_inter_le' C (pairs S); rwa [card_pairs] at this
  have hR : ∑ K ∈ C.pieces, (pairs R ∩ pairs K).card ≤ R.card.choose 2 := by
    have := sum_inter_le' C (pairs R); rwa [card_pairs] at this
  rw [card_crossPairs hd] at hsum
  omega

/-- Con crédito de separador el conteo **nunca** contradice el presupuesto: para todos
`s, r` se tiene `2sr + 2M(s) ≤ 2M(s+r) + 3(C(s,2) + C(r,2))`. -/
theorem credit_bound_within_budget (s r : ℕ) :
    2 * (s * r) + 2 * PaperIV.targetSize s
      ≤ 2 * PaperIV.targetSize (s + r) + 3 * (s.choose 2 + r.choose 2) := by
  rcases Nat.lt_or_ge (s + r) 3 with hsmall | hbig
  · have hs2 : s ≤ 2 := by omega
    have hr2 : r ≤ 2 := by omega
    interval_cases s <;> interval_cases r <;>
      simp_all [PaperIV.targetSize, Nat.choose]
  · have h1 : (s + r) * (s + r + 1) ≤ 6 * PaperIV.targetSize (s + r) + 2 :=
      ExactReduction.le_six_mul_targetSize_add_two _
    have h2 : 6 * PaperIV.targetSize s ≤ s * (s + 1) := ExactReduction.six_mul_targetSize_le _
    have h3 : 2 * s.choose 2 = s * (s - 1) := ExactReduction.two_mul_choose_two s
    have h4 : 2 * r.choose 2 = r * (r - 1) := ExactReduction.two_mul_choose_two r
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [Nat.zero_mul, Nat.zero_add] at *
      have h5 : 6 * PaperIV.targetSize r ≤ r * (r + 1) := ExactReduction.six_mul_targetSize_le r
      have h6 : r * (r + 1) ≤ 6 * PaperIV.targetSize r + 2 :=
        ExactReduction.le_six_mul_targetSize_add_two r
      simp only [PaperIV.targetSize] at *
      omega
    · rcases Nat.eq_zero_or_pos r with rfl | hrp
      · simp
      · obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at h3 h4
        nlinarith [h1, h2, h3, h4, hbig]

/-- El caso concreto `(|S|, |R|) = (3,2)` dentro de un grafo de orden `6`: el presupuesto
de la inducción es `M(6) − M(4) = 4`, pero toda cáscara admisible cuesta al menos `5`. -/
theorem shell_three_two_exceeds_budget (hd : Disjoint S R) (C : ShellCover S R)
    (hS : S.card = 3) (hR : R.card = 2) :
    5 ≤ C.pieces.card ∧ PaperIV.targetSize 6 < PaperIV.targetSize 4 + C.pieces.card := by
  have hlow := shellCover_card_ge hd C
  rw [hS, hR] at hlow
  norm_num [Nat.choose] at hlow
  refine ⟨by omega, ?_⟩
  have h6 : PaperIV.targetSize 6 = 7 := by norm_num [PaperIV.targetSize]
  have h4 : PaperIV.targetSize 4 = 3 := by norm_num [PaperIV.targetSize]
  omega

end ExactReduction.ShellObstruction
