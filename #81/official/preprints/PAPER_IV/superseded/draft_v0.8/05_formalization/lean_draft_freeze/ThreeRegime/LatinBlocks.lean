import ThreeRegime.OwnerPacking

/-!
# El esqueleto de Bose–Skolem: tres filas y un cuasigrupo conmutativo

Sobre el conjunto de vértices `Pt Q = (Q × ZMod 3) ⊕ Unit` —tres copias de `Q` más un punto
extra `star`— se construye la familia clásica de bloques:

* `rowBlock x y i = {(x,i), (y,i), (x∘y, i+1)}` para `x ≠ y`;
* `colBlock x = {(x,0), (x,1), (x,2)}` (o su `K₄` con `star`) para los puntos con `x∘x = x`;
* `starBlock x i = {star, (x,i), (x∘x, i+1)}` para los puntos con `x∘x ≠ x`.

El marco `Frame` recoge exactamente las propiedades algebraicas que hacen falta: `∘` es
conmutativo y cancelativo (un cuasigrupo conmutativo), el «cuadrado» `s x = x∘x` es idempotente
como función, es inyectivo sobre los puntos no fijos, y `tw` invierte `s` sobre ellos.

Con `Q = ZMod M` y `M` impar se obtiene la construcción de Bose (todos los puntos son fijos);
con `M` par, la de Skolem (la mitad de los puntos son fijos y la otra mitad se empareja con
`star`).
-/

namespace ThreeRegime.Latin

open Finset PaperIV PaperIV.FarRounding

/-! ## 0. Aritmética de `ZMod 3` -/

theorem zmod3_ne_succ (i : ZMod 3) : i ≠ i + 1 := by revert i; decide +kernel

theorem zmod3_tri (i j : ZMod 3) : i = j ∨ j = i + 1 ∨ i = j + 1 := by
  revert i j; decide +kernel

theorem zmod3_not_both {i j : ZMod 3} (h1 : j = i + 1) (h2 : i = j + 1) : False := by
  revert h1 h2; revert i j; decide +kernel

theorem zmod3_mem (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide +kernel

theorem zmod3_sub_add (i : ZMod 3) : i - 1 + 1 = i := by ring

/-! ## 1. El marco algebraico -/

/-- Datos algebraicos de la construcción: un cuasigrupo conmutativo con un cuadrado
idempotente.  `k4` decide si las columnas de puntos fijos se agrandan a `K₄` usando el punto
extra. -/
structure Frame (Q : Type*) where
  /-- La operación del cuasigrupo. -/
  op : Q → Q → Q
  /-- La solución de `op x · = c`. -/
  solve : Q → Q → Q
  /-- El compañero no fijo de un punto fijo. -/
  tw : Q → Q
  /-- ¿Se agrandan las columnas a `K₄`? -/
  k4 : Bool
  op_comm : ∀ x y, op x y = op y x
  op_solve : ∀ x c, op x (solve x c) = c
  solve_op : ∀ x y, solve x (op x y) = y
  s_idem : ∀ x, op (op x x) (op x x) = op x x
  s_inj : ∀ x y, op x x ≠ x → op y y ≠ y → op x x = op y y → x = y
  tw_spec : ∀ y, op y y ≠ y → tw (op y y) = y
  k4_fixed : k4 = true → ∀ x, op x x = x

namespace Frame

variable {Q : Type*} (F : Frame Q)

/-- El cuadrado `s x = x ∘ x`. -/
def s (x : Q) : Q := F.op x x

theorem op_inj {x y z : Q} (h : F.op x y = F.op x z) : y = z := by
  rw [← F.solve_op x y, h, F.solve_op]

theorem op_eq_s_iff {x y : Q} : F.op x y = F.s x ↔ y = x :=
  ⟨fun h => F.op_inj h, fun h => by rw [h, s]⟩

theorem solve_ne_self {x y : Q} (hy : y ≠ F.s x) : F.solve x y ≠ x := by
  intro h
  exact hy (by rw [← F.op_solve x y, h, s])

theorem s_s (x : Q) : F.s (F.s x) = F.s x := F.s_idem x

theorem tw_of_s {y : Q} (hy : F.s y ≠ y) : F.tw (F.s y) = y := F.tw_spec y hy

theorem k4_false_of_nonfixed {y : Q} (hy : F.s y ≠ y) : F.k4 = false := by
  cases hk : F.k4 with
  | false => rfl
  | true => exact absurd (F.k4_fixed hk y) hy

end Frame

/-! ## 2. Vértices y bloques -/

/-- El conjunto de vértices: tres copias de `Q` más un punto extra. -/
abbrev Pt (Q : Type*) := (Q × ZMod 3) ⊕ Unit

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (F : Frame Q)

/-- El vértice `(x, i)`. -/
abbrev pt (x : Q) (i : ZMod 3) : Pt Q := Sum.inl (x, i)

/-- El punto extra. -/
abbrev star : Pt Q := Sum.inr ()

theorem pt_inj {x y : Q} {i j : ZMod 3} (h : (pt x i : Pt Q) = pt y j) : x = y ∧ i = j := by
  simpa [Prod.ext_iff] using h

@[simp] theorem pt_eq_pt {x y : Q} {i j : ZMod 3} :
    (pt x i : Pt Q) = pt y j ↔ x = y ∧ i = j := by
  simp [Prod.ext_iff]

@[simp] theorem pt_ne_star {x : Q} {i : ZMod 3} : (pt x i : Pt Q) ≠ star := by simp

namespace Frame

/-- Bloque de fila. -/
def rowBlock (x y : Q) (i : ZMod 3) : Finset (Pt Q) :=
  {pt x i, pt y i, pt (F.op x y) (i + 1)}

/-- Bloque de columna, triángulo o `K₄` según `k4`. -/
def colBlock (x : Q) : Finset (Pt Q) :=
  if F.k4 then {star, pt x 0, pt x 1, pt x 2} else {pt x 0, pt x 1, pt x 2}

/-- Bloque con el punto extra, para puntos no fijos. -/
def starBlock (x : Q) (i : ZMod 3) : Finset (Pt Q) :=
  {star, pt x i, pt (F.s x) (i + 1)}

/-- El bloque que contiene a la arista `{(x,i), (s x, i+1)}`. -/
def diagBlock (x : Q) (i : ZMod 3) : Finset (Pt Q) :=
  if F.s x = x then F.colBlock x else F.starBlock x i

/-- Dueño de una arista interna. -/
def ownIn (x : Q) (i : ZMod 3) (y : Q) (j : ZMod 3) : Finset (Pt Q) :=
  if i = j then F.rowBlock x y i
  else if j = i + 1 then
    (if y = F.s x then F.diagBlock x i else F.rowBlock x (F.solve x y) i)
  else
    (if x = F.s y then F.diagBlock y j else F.rowBlock y (F.solve y x) j)

/-- Dueño de una arista incidente al punto extra. -/
def ownStar (x : Q) (i : ZMod 3) : Finset (Pt Q) :=
  if F.s x = x then (if F.k4 then F.colBlock x else F.starBlock (F.tw x) (i - 1))
  else F.starBlock x i

/-- La función dueño. -/
def own : Pt Q → Pt Q → Finset (Pt Q)
  | Sum.inl (x, i), Sum.inl (y, j) => F.ownIn x i y j
  | Sum.inl (x, i), Sum.inr _ => F.ownStar x i
  | Sum.inr _, Sum.inl (y, j) => F.ownStar y j
  | Sum.inr _, Sum.inr _ => ∅

/-- La familia completa de bloques. -/
def blocks : Finset (Finset (Pt Q)) :=
  ((Finset.univ : Finset (Q × Q × ZMod 3)).filter (fun p => p.1 ≠ p.2.1)).image
      (fun p => F.rowBlock p.1 p.2.1 p.2.2)
    ∪ ((Finset.univ : Finset Q).filter (fun x => F.s x = x)).image F.colBlock
    ∪ ((Finset.univ : Finset (Q × ZMod 3)).filter (fun p => F.s p.1 ≠ p.1)).image
        (fun p => F.starBlock p.1 p.2)

/-! ### Pertenencia a la familia -/

theorem rowBlock_mem {x y : Q} (i : ZMod 3) (hxy : x ≠ y) : F.rowBlock x y i ∈ F.blocks := by
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  exact Finset.mem_image.2 ⟨(x, y, i), Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy⟩, rfl⟩

theorem colBlock_mem {x : Q} (hx : F.s x = x) : F.colBlock x ∈ F.blocks := by
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem starBlock_mem {x : Q} (i : ZMod 3) (hx : F.s x ≠ x) : F.starBlock x i ∈ F.blocks := by
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.2 ⟨(x, i), Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩

theorem blocks_cases {K : Finset (Pt Q)} (hK : K ∈ F.blocks) :
    (∃ x y i, x ≠ y ∧ K = F.rowBlock x y i) ∨ (∃ x, F.s x = x ∧ K = F.colBlock x) ∨
      (∃ x i, F.s x ≠ x ∧ K = F.starBlock x i) := by
  rcases Finset.mem_union.1 hK with h | h
  · rcases Finset.mem_union.1 h with h | h
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
      exact Or.inl ⟨p.1, p.2.1, p.2.2, (Finset.mem_filter.1 hp).2, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact Or.inr (Or.inl ⟨x, (Finset.mem_filter.1 hx).2, rfl⟩)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
    exact Or.inr (Or.inr ⟨p.1, p.2, (Finset.mem_filter.1 hp).2, rfl⟩)

/-! ### Simetría de los bloques de fila -/

theorem rowBlock_comm (x y : Q) (i : ZMod 3) : F.rowBlock x y i = F.rowBlock y x i := by
  unfold rowBlock
  rw [F.op_comm x y, Finset.insert_comm]

/-! ### Los valores del dueño -/

theorem ownIn_eq {x y : Q} {i : ZMod 3} : F.ownIn x i y i = F.rowBlock x y i := by
  simp [ownIn]

theorem ownIn_succ {x y : Q} {i j : ZMod 3} (hij : j = i + 1) (hy : y ≠ F.s x) :
    F.ownIn x i y j = F.rowBlock x (F.solve x y) i := by
  subst hij
  rw [ownIn, if_neg (zmod3_ne_succ i), if_pos rfl, if_neg hy]

theorem ownIn_succ_diag {x y : Q} {i j : ZMod 3} (hij : j = i + 1) (hy : y = F.s x) :
    F.ownIn x i y j = F.diagBlock x i := by
  subst hij
  rw [ownIn, if_neg (zmod3_ne_succ i), if_pos rfl, if_pos hy]

theorem ownIn_pred {x y : Q} {i j : ZMod 3} (hij : i = j + 1) (hx : x ≠ F.s y) :
    F.ownIn x i y j = F.rowBlock y (F.solve y x) j := by
  have h1 : i ≠ j := by rw [hij]; exact fun h => zmod3_ne_succ j h.symm
  have h2 : ¬ (j = i + 1) := fun h => zmod3_not_both h hij
  rw [ownIn, if_neg h1, if_neg h2, if_neg hx]

theorem ownIn_pred_diag {x y : Q} {i j : ZMod 3} (hij : i = j + 1) (hx : x = F.s y) :
    F.ownIn x i y j = F.diagBlock y j := by
  have h1 : i ≠ j := by rw [hij]; exact fun h => zmod3_ne_succ j h.symm
  have h2 : ¬ (j = i + 1) := fun h => zmod3_not_both h hij
  rw [ownIn, if_neg h1, if_neg h2, if_pos hx]

@[simp] theorem own_inl_inl (x : Q) (i : ZMod 3) (y : Q) (j : ZMod 3) :
    F.own (pt x i) (pt y j) = F.ownIn x i y j := rfl

@[simp] theorem own_inl_inr (x : Q) (i : ZMod 3) :
    F.own (pt x i) star = F.ownStar x i := rfl

@[simp] theorem own_inr_inl (y : Q) (j : ZMod 3) :
    F.own star (pt y j) = F.ownStar y j := rfl


/-! ## 3. Cada bloque es el dueño de sus propias aristas -/

theorem mem_colBlock {x : Q} {a : Pt Q} :
    a ∈ F.colBlock x ↔ ((F.k4 = true ∧ a = star) ∨ ∃ i, a = pt x i) := by
  unfold colBlock
  cases hk : F.k4 with
  | false =>
    simp only [Bool.false_eq_true, if_false, Finset.mem_insert, Finset.mem_singleton,
      false_and, false_or]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    · rintro ⟨i, rfl⟩
      rcases zmod3_mem i with rfl | rfl | rfl
      exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  | true =>
    simp only [if_true, Finset.mem_insert, Finset.mem_singleton, true_and]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [Or.inl rfl, Or.inr ⟨0, rfl⟩, Or.inr ⟨1, rfl⟩, Or.inr ⟨2, rfl⟩]
    · rintro (rfl | ⟨i, rfl⟩)
      · exact Or.inl rfl
      · rcases zmod3_mem i with rfl | rfl | rfl
        exacts [Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
          Or.inr (Or.inr (Or.inr rfl))]

theorem pt_mem_colBlock (x : Q) (i : ZMod 3) : (pt x i : Pt Q) ∈ F.colBlock x :=
  F.mem_colBlock.2 (Or.inr ⟨i, rfl⟩)

theorem star_mem_colBlock {x : Q} (hk : F.k4 = true) : (star : Pt Q) ∈ F.colBlock x :=
  F.mem_colBlock.2 (Or.inl ⟨hk, rfl⟩)

theorem rowBlock_own {x y : Q} {i : ZMod 3} (hxy : x ≠ y) {a b : Pt Q}
    (ha : a ∈ F.rowBlock x y i) (hb : b ∈ F.rowBlock x y i) (hab : a ≠ b) :
    F.rowBlock x y i = F.own a b := by
  have hcx : F.op x y ≠ F.s x := fun h => hxy (F.op_inj h).symm
  have hcy : F.op x y ≠ F.s y := fun h => hxy (F.op_inj (by rw [← F.op_comm x y]; exact h))
  have hsx : F.solve x (F.op x y) = y := F.solve_op x y
  have hsy : F.solve y (F.op x y) = x := by rw [F.op_comm x y]; exact F.solve_op y x
  simp only [rowBlock, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · rw [own_inl_inl, F.ownIn_eq]
  · rw [own_inl_inl, F.ownIn_succ rfl hcx, hsx]
  · rw [own_inl_inl, F.ownIn_eq, F.rowBlock_comm]
  · exact absurd rfl hab
  · rw [own_inl_inl, F.ownIn_succ rfl hcy, hsy, F.rowBlock_comm]
  · rw [own_inl_inl, F.ownIn_pred rfl hcx, hsx]
  · rw [own_inl_inl, F.ownIn_pred rfl hcy, hsy, F.rowBlock_comm]
  · exact absurd rfl hab

theorem colBlock_own {x : Q} (hx : F.s x = x) {a b : Pt Q}
    (ha : a ∈ F.colBlock x) (hb : b ∈ F.colBlock x) (hab : a ≠ b) :
    F.colBlock x = F.own a b := by
  have hdiag : ∀ j : ZMod 3, F.diagBlock x j = F.colBlock x := fun j => if_pos hx
  rcases F.mem_colBlock.1 ha with ⟨hk, rfl⟩ | ⟨i, rfl⟩
  · rcases F.mem_colBlock.1 hb with ⟨-, rfl⟩ | ⟨j, rfl⟩
    · exact absurd rfl hab
    · rw [own_inr_inl, ownStar, if_pos hx, if_pos hk]
  · rcases F.mem_colBlock.1 hb with ⟨hk, rfl⟩ | ⟨j, rfl⟩
    · rw [own_inl_inr, ownStar, if_pos hx, if_pos hk]
    · have hij : i ≠ j := fun h => hab (by rw [h])
      rcases zmod3_tri i j with h | h | h
      · exact absurd h hij
      · rw [own_inl_inl, F.ownIn_succ_diag h hx.symm, hdiag]
      · rw [own_inl_inl, F.ownIn_pred_diag h hx.symm, hdiag]

theorem mem_starBlock {x : Q} {i : ZMod 3} {a : Pt Q} :
    a ∈ F.starBlock x i ↔ (a = star ∨ a = pt x i ∨ a = pt (F.s x) (i + 1)) := by
  simp [starBlock]

theorem starBlock_own {x : Q} {i : ZMod 3} (hx : F.s x ≠ x) {a b : Pt Q}
    (ha : a ∈ F.starBlock x i) (hb : b ∈ F.starBlock x i) (hab : a ≠ b) :
    F.starBlock x i = F.own a b := by
  have hk : F.k4 = false := F.k4_false_of_nonfixed hx
  have hdiag : F.diagBlock x i = F.starBlock x i := if_neg hx
  have hstar : F.ownStar x i = F.starBlock x i := by rw [ownStar, if_neg hx]
  have hstar' : F.ownStar (F.s x) (i + 1) = F.starBlock x i := by
    rw [ownStar, if_pos (F.s_s x), if_neg (by simp [hk]), F.tw_of_s hx, add_sub_cancel_right]
  rw [mem_starBlock] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · rw [own_inr_inl, hstar]
  · rw [own_inr_inl, hstar']
  · rw [own_inl_inr, hstar]
  · exact absurd rfl hab
  · rw [own_inl_inl, F.ownIn_succ_diag rfl rfl, hdiag]
  · rw [own_inl_inr, hstar']
  · rw [own_inl_inl, F.ownIn_pred_diag rfl rfl, hdiag]
  · exact absurd rfl hab

/-- **Cada bloque es el dueño de sus aristas.** -/
theorem own_spec {K : Finset (Pt Q)} (hK : K ∈ F.blocks) (a b : Pt Q)
    (hab : s(a, b) ∈ pairs K) : K = F.own a b := by
  obtain ⟨ha, hb, hne⟩ := mk_mem_pairs.1 hab
  rcases F.blocks_cases hK with ⟨x, y, i, hxy, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, i, hx, rfl⟩
  · exact F.rowBlock_own hxy ha hb hne
  · exact F.colBlock_own hx ha hb hne
  · exact F.starBlock_own hx ha hb hne

/-! ## 4. Cardinales de los bloques -/

private theorem card_triple {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ({a, b, c} : Finset α).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

private theorem card_quad {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]), card_triple hbc hbd hcd]

theorem card_rowBlock {x y : Q} (i : ZMod 3) (hxy : x ≠ y) : (F.rowBlock x y i).card = 3 :=
  card_triple (by simp [hxy]) (by simp [zmod3_ne_succ i]) (by simp [zmod3_ne_succ i])

theorem card_starBlock (x : Q) (i : ZMod 3) : (F.starBlock x i).card = 3 :=
  card_triple (by simp) (by simp) (by simp [zmod3_ne_succ i])

private theorem h01 (x : Q) : (pt x 0 : Pt Q) ≠ pt x 1 := by
  intro h; exact absurd (pt_inj h).2 (by decide +kernel)

private theorem h02 (x : Q) : (pt x 0 : Pt Q) ≠ pt x 2 := by
  intro h; exact absurd (pt_inj h).2 (by decide +kernel)

private theorem h12 (x : Q) : (pt x 1 : Pt Q) ≠ pt x 2 := by
  intro h; exact absurd (pt_inj h).2 (by decide +kernel)

theorem card_colBlock (x : Q) :
    (F.colBlock x).card = if F.k4 then 4 else 3 := by
  unfold colBlock
  cases hk : F.k4 with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact card_triple (h01 x) (h02 x) (h12 x)
  | true =>
    simp only [if_true]
    exact card_quad (by simp) (by simp) (by simp) (h01 x) (h02 x) (h12 x)

theorem card_blocks_mem {K : Finset (Pt Q)} (hK : K ∈ F.blocks) : K.card = 3 ∨ K.card = 4 := by
  rcases F.blocks_cases hK with ⟨x, y, i, hxy, rfl⟩ | ⟨x, -, rfl⟩ | ⟨x, i, -, rfl⟩
  · exact Or.inl (F.card_rowBlock i hxy)
  · rw [F.card_colBlock x]; cases F.k4 <;> simp
  · exact Or.inl (F.card_starBlock x i)

/-! ## 5. El empaquetamiento -/

/-- El empaquetamiento mixto de `K_{Pt Q}` determinado por el marco. -/
def packing : Packing (⊤ : SimpleGraph (Pt Q)) :=
  Owner.packingOfOwn F.blocks F.own (fun _ hK => F.card_blocks_mem hK)
    (fun _ hK a b hab => F.own_spec hK a b hab)

@[simp] theorem packing_pieces : F.packing.pieces = F.blocks := rfl

/-! ## 6. Cobertura -/

theorem diagBlock_mem (x : Q) (i : ZMod 3) : F.diagBlock x i ∈ F.blocks := by
  unfold diagBlock
  by_cases hx : F.s x = x
  · rw [if_pos hx]; exact F.colBlock_mem hx
  · rw [if_neg hx]; exact F.starBlock_mem i hx

theorem pt_mem_diagBlock (x : Q) (i : ZMod 3) : (pt x i : Pt Q) ∈ F.diagBlock x i := by
  unfold diagBlock
  by_cases hx : F.s x = x
  · rw [if_pos hx]; exact F.pt_mem_colBlock x i
  · rw [if_neg hx]; exact F.mem_starBlock.2 (Or.inr (Or.inl rfl))

theorem pt_s_mem_diagBlock (x : Q) (i : ZMod 3) :
    (pt (F.s x) (i + 1) : Pt Q) ∈ F.diagBlock x i := by
  unfold diagBlock
  by_cases hx : F.s x = x
  · rw [if_pos hx, hx]; exact F.pt_mem_colBlock x (i + 1)
  · rw [if_neg hx]; exact F.mem_starBlock.2 (Or.inr (Or.inr rfl))

theorem ownIn_mem_blocks (x y : Q) (i j : ZMod 3) (h : (pt x i : Pt Q) ≠ pt y j) :
    F.ownIn x i y j ∈ F.blocks := by
  rcases zmod3_tri i j with rfl | hij | hij
  · have hxy : x ≠ y := fun hx => h (by rw [hx])
    rw [F.ownIn_eq]
    exact F.rowBlock_mem i hxy
  · by_cases hy : y = F.s x
    · rw [F.ownIn_succ_diag hij hy]; exact F.diagBlock_mem x i
    · rw [F.ownIn_succ hij hy]; exact F.rowBlock_mem i (F.solve_ne_self hy).symm
  · by_cases hx : x = F.s y
    · rw [F.ownIn_pred_diag hij hx]; exact F.diagBlock_mem y j
    · rw [F.ownIn_pred hij hx]; exact F.rowBlock_mem j (F.solve_ne_self hx).symm

theorem mem_pairs_ownIn (x y : Q) (i j : ZMod 3) (h : (pt x i : Pt Q) ≠ pt y j) :
    s(pt x i, pt y j) ∈ pairs (F.ownIn x i y j) := by
  refine mk_mem_pairs.2 ⟨?_, ?_, h⟩ <;> rcases zmod3_tri i j with rfl | hij | hij
  · have hxy : x ≠ y := fun hx => h (by rw [hx])
    rw [F.ownIn_eq]; simp [rowBlock]
  · by_cases hy : y = F.s x
    · rw [F.ownIn_succ_diag hij hy]; exact F.pt_mem_diagBlock x i
    · rw [F.ownIn_succ hij hy]; simp [rowBlock]
  · by_cases hx : x = F.s y
    · rw [F.ownIn_pred_diag hij hx, hij, hx]; exact F.pt_s_mem_diagBlock y j
    · rw [F.ownIn_pred hij hx, hij]
      simp only [rowBlock, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (by rw [F.op_solve y x]))
  · have hxy : x ≠ y := fun hx => h (by rw [hx])
    rw [F.ownIn_eq]; simp [rowBlock]
  · by_cases hy : y = F.s x
    · rw [F.ownIn_succ_diag hij hy, hij, hy]; exact F.pt_s_mem_diagBlock x i
    · rw [F.ownIn_succ hij hy, hij]
      simp only [rowBlock, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (by rw [F.op_solve x y]))
  · by_cases hx : x = F.s y
    · rw [F.ownIn_pred_diag hij hx]; exact F.pt_mem_diagBlock y j
    · rw [F.ownIn_pred hij hx]; simp [rowBlock]

/-- Toda arista que no toca al punto extra está cubierta. -/
theorem coverage_inner (x y : Q) (i j : ZMod 3) (h : (pt x i : Pt Q) ≠ pt y j) :
    s(pt x i, pt y j) ∈ F.blocks.biUnion pairs :=
  Finset.mem_biUnion.2 ⟨F.ownIn x i y j, F.ownIn_mem_blocks x y i j h,
    F.mem_pairs_ownIn x y i j h⟩

/-! ### Aristas incidentes al punto extra -/

/-- La hipótesis que hace que el punto extra quede completamente cubierto: o bien las columnas
son `K₄`, o bien cada punto fijo tiene un compañero no fijo. -/
def HasPartner : Prop :=
  ∀ x : Q, F.s x = x → F.k4 = true ∨ (F.s (F.tw x) = x ∧ F.tw x ≠ x)

theorem ownStar_mem_blocks (hp : F.HasPartner) (x : Q) (i : ZMod 3) :
    F.ownStar x i ∈ F.blocks := by
  unfold ownStar
  by_cases hx : F.s x = x
  · rw [if_pos hx]
    by_cases hk : F.k4 = true
    · rw [if_pos hk]; exact F.colBlock_mem hx
    · rw [if_neg hk]
      rcases hp x hx with h | ⟨h1, h2⟩
      · exact absurd h hk
      · exact F.starBlock_mem _ (by rw [h1]; exact fun hh => h2 hh.symm)
  · rw [if_neg hx]; exact F.starBlock_mem i hx

theorem star_mem_ownStar (x : Q) (i : ZMod 3) : (star : Pt Q) ∈ F.ownStar x i := by
  unfold ownStar
  by_cases hx : F.s x = x
  · rw [if_pos hx]
    by_cases hk : F.k4 = true
    · rw [if_pos hk]; exact F.star_mem_colBlock hk
    · rw [if_neg hk]; exact F.mem_starBlock.2 (Or.inl rfl)
  · rw [if_neg hx]; exact F.mem_starBlock.2 (Or.inl rfl)

theorem pt_mem_ownStar (hp : F.HasPartner) (x : Q) (i : ZMod 3) :
    (pt x i : Pt Q) ∈ F.ownStar x i := by
  unfold ownStar
  by_cases hx : F.s x = x
  · rw [if_pos hx]
    by_cases hk : F.k4 = true
    · rw [if_pos hk]; exact F.pt_mem_colBlock x i
    · rw [if_neg hk]
      rcases hp x hx with h | ⟨h1, -⟩
      · exact absurd h hk
      · refine F.mem_starBlock.2 (Or.inr (Or.inr ?_))
        rw [h1, zmod3_sub_add]
  · rw [if_neg hx]; exact F.mem_starBlock.2 (Or.inr (Or.inl rfl))

/-- Toda arista incidente al punto extra está cubierta. -/
theorem coverage_star (hp : F.HasPartner) (x : Q) (i : ZMod 3) :
    s((star : Pt Q), pt x i) ∈ F.blocks.biUnion pairs :=
  Finset.mem_biUnion.2 ⟨F.ownStar x i, F.ownStar_mem_blocks hp x i,
    mk_mem_pairs.2 ⟨F.star_mem_ownStar x i, F.pt_mem_ownStar hp x i, by simp⟩⟩

/-! ## 7. Las dos formas de la cobertura -/

theorem biUnion_subset : F.blocks.biUnion pairs ⊆ (⊤ : SimpleGraph (Pt Q)).edgeFinset :=
  F.packing.biUnion_subset_edgeFinset

/-- **Descomposición completa.**  Con compañeros, los bloques cubren todas las aristas. -/
theorem biUnion_eq_edgeFinset (hp : F.HasPartner) :
    F.blocks.biUnion pairs = (⊤ : SimpleGraph (Pt Q)).edgeFinset := by
  refine Finset.Subset.antisymm F.biUnion_subset (fun e he => ?_)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact he
    match a, b with
    | Sum.inl (x, i), Sum.inl (y, j) => exact F.coverage_inner x y i j hab
    | Sum.inl (x, i), Sum.inr u =>
        have : (Sum.inr u : Pt Q) = star := by cases u; rfl
        rw [this, Sym2.eq_swap]
        exact F.coverage_star hp x i
    | Sum.inr u, Sum.inl (y, j) =>
        have : (Sum.inr u : Pt Q) = star := by cases u; rfl
        rw [this]
        exact F.coverage_star hp y j
    | Sum.inr u, Sum.inr v => exact absurd (by cases u; cases v; rfl) hab

/-- Sin compañeros y sin `K₄`, el punto extra queda aislado. -/
theorem star_notMem_of_fixed (hk : F.k4 = false) (hfix : ∀ x : Q, F.s x = x)
    {K : Finset (Pt Q)} (hK : K ∈ F.blocks) : (star : Pt Q) ∉ K := by
  rcases F.blocks_cases hK with ⟨x, y, i, -, rfl⟩ | ⟨x, -, rfl⟩ | ⟨x, i, hx, -⟩
  · simp [rowBlock]
  · rw [mem_colBlock]
    rintro (⟨h, -⟩ | ⟨j, hj⟩)
    · exact absurd h (by simp [hk])
    · exact absurd hj.symm (by simp)
  · exact absurd (hfix x) hx

/-! ## 8. El recuento de piezas `K₄` -/

theorem colBlock_injective : Function.Injective F.colBlock := by
  intro x y h
  have hx : (pt x 0 : Pt Q) ∈ F.colBlock y := by rw [← h]; exact F.pt_mem_colBlock x 0
  rcases F.mem_colBlock.1 hx with ⟨-, hs⟩ | ⟨i, hi⟩
  · exact absurd hs (by simp)
  · exact (pt_inj hi).1

theorem all_card_three (hk : F.k4 = false) {K : Finset (Pt Q)} (hK : K ∈ F.blocks) :
    K.card = 3 := by
  rcases F.blocks_cases hK with ⟨x, y, i, hxy, rfl⟩ | ⟨x, -, rfl⟩ | ⟨x, i, -, rfl⟩
  · exact F.card_rowBlock i hxy
  · rw [F.card_colBlock x, if_neg (by simp [hk])]
  · exact F.card_starBlock x i

theorem filter_card_four_eq_empty (hk : F.k4 = false) :
    F.blocks.filter (fun K => K.card = 4) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun {K} hK => ?_
  rcases F.blocks_cases hK with ⟨x, y, i, hxy, rfl⟩ | ⟨x, -, rfl⟩ | ⟨x, i, -, rfl⟩
  · rw [F.card_rowBlock i hxy]; omega
  · rw [F.card_colBlock x, if_neg (by simp [hk])]; omega
  · rw [F.card_starBlock x i]; omega

theorem filter_card_four_card (hk : F.k4 = true) (hfix : ∀ x : Q, F.s x = x) :
    (F.blocks.filter (fun K => K.card = 4)).card = Fintype.card Q := by
  classical
  have hset : F.blocks.filter (fun K => K.card = 4)
      = (Finset.univ : Finset Q).image F.colBlock := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hK, hcard⟩
      rcases F.blocks_cases hK with ⟨x, y, i, hxy, rfl⟩ | ⟨x, -, rfl⟩ | ⟨x, i, -, rfl⟩
      · rw [F.card_rowBlock i hxy] at hcard; omega
      · exact ⟨x, rfl⟩
      · rw [F.card_starBlock x i] at hcard; omega
    · rintro ⟨x, rfl⟩
      exact ⟨F.colBlock_mem (hfix x), by rw [F.card_colBlock x, if_pos hk]⟩
  rw [hset, Finset.card_image_of_injective _ F.colBlock_injective, Finset.card_univ]

theorem card_Pt : Fintype.card (Pt Q) = 3 * Fintype.card Q + 1 := by
  simp [Pt, Fintype.card_sum, Fintype.card_prod]
  ring

end Frame

end ThreeRegime.Latin
