import FarExploration.CleanupThreshold
import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
# Grafos rígidos de masa casi cuadrática: la construcción de Ruzsa–Szemerédi

## Qué se decide aquí

La hipótesis de trabajo natural para demostrar `CodegreeCleanupAt` por dispersión es:

> *«en un grafo, la rigidez obliga a ser disperso: un grafo cuyas aristas están cada una en un
> único triángulo es una unión de triángulos disjuntos, y su masa triangular es lineal en `n`».*

Este módulo construye, dentro de Lean, la familia clásica que **refuta** esa hipótesis: el grafo
tripartito de Ruzsa–Szemerédi asociado a un conjunto `A ⊆ ZMod N` sin progresiones aritméticas de
longitud tres,

```
rsGraph A  sobre  Fin (3*N),   partes  {v0 x}, {v1 x}, {v2 x},
v0 x ~ v1 y ↔ y - x ∈ A,  v1 x ~ v2 y ↔ y - x ∈ A,  v0 x ~ v2 y ↔ ∃ a ∈ A, y - x = a + a.
```

Sus propiedades demostradas abajo:

* **todos sus items son triángulos** (`item_card_eq_three`): es tripartito, luego no tiene `K₄`;
* **cada arista está en un único triángulo** (`rsGraph_rigid`): es la rigidez literal, y sale de
  que `A` no tiene progresiones de tres términos;
* **tiene `N·|A|` triángulos** (`card_supports_ge`), es decir `n²·|A|/(9N)` con `n = 3N`.

Con `|A|` de densidad constante `δ` la masa triangular es `δ·n²/9`: **cuadrática y rígida a la
vez**.  La unión de triángulos disjuntos no es, ni de lejos, el único grafo rígido.

Lo que sí es cierto —y es el teorema `(6,3)` de Ruzsa–Szemerédi, no formalizado aquí— es que la
densidad de un conjunto sin progresiones tiende a cero; por eso la familia no refuta
`CodegreeCleanupAt`, sino que **empuja su umbral**.  La cuantificación está en
`FarExploration.CleanupRigidVerdict`.

Las hipótesis sobre `A` son dos y ambas explícitas en cada enunciado: no tener progresiones de
tres términos (`ThreeAPFree`) y que la duplicación `a ↦ a + a` sea inyectiva sobre `A`
(`hdbl`); la segunda es automática si `N` es impar, y se comprueba en el módulo del veredicto
para la familia concreta que se usa.
-/

namespace FarExploration.RuzsaSzemeredi

open Finset MixedRounding FarExploration.CleanupLP FarExploration.CleanupBridge

variable {N : ℕ} [NeZero N]

/-! ## 1. Los vértices, en tres partes -/

/-- Vértice `x` de la parte `0`. -/
def v0 (x : ZMod N) : Fin (3 * N) :=
  ⟨x.val, by have h := ZMod.val_lt x; omega⟩

/-- Vértice `x` de la parte `1`. -/
def v1 (x : ZMod N) : Fin (3 * N) :=
  ⟨x.val + N, by have h := ZMod.val_lt x; omega⟩

/-- Vértice `x` de la parte `2`. -/
def v2 (x : ZMod N) : Fin (3 * N) :=
  ⟨x.val + N * 2, by have h := ZMod.val_lt x; omega⟩

/-- La parte en la que vive un vértice. -/
def typ (u : Fin (3 * N)) : Fin 3 :=
  ⟨u.val / N, by
    have := u.isLt
    exact Nat.div_lt_of_lt_mul (by omega)⟩

/-- La coordenada en `ZMod N` de un vértice. -/
def vval (u : Fin (3 * N)) : ZMod N := (u.val : ZMod N)

@[simp] lemma typ_v0 (x : ZMod N) : typ (v0 x) = 0 := by
  apply Fin.ext
  simp [typ, v0, Nat.div_eq_of_lt (ZMod.val_lt x)]

@[simp] lemma typ_v1 (x : ZMod N) : typ (v1 x) = 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  apply Fin.ext
  simp [typ, v1, Nat.add_div_right _ hN, Nat.div_eq_of_lt (ZMod.val_lt x)]

@[simp] lemma typ_v2 (x : ZMod N) : typ (v2 x) = 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  apply Fin.ext
  simp only [typ, v2, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt (ZMod.val_lt x)]
  rfl

@[simp] lemma vval_v0 (x : ZMod N) : vval (v0 x) = x := by
  simp [vval, v0, ZMod.natCast_val, ZMod.cast_id]

@[simp] lemma vval_v1 (x : ZMod N) : vval (v1 x) = x := by
  simp [vval, v1, ZMod.natCast_val, ZMod.cast_id]

@[simp] lemma vval_v2 (x : ZMod N) : vval (v2 x) = x := by
  simp [vval, v2, ZMod.natCast_val, ZMod.cast_id]

lemma v0_injective : Function.Injective (v0 (N := N)) := by
  intro x y h
  have := congrArg vval h
  simpa using this

lemma v1_injective : Function.Injective (v1 (N := N)) := by
  intro x y h
  have := congrArg vval h
  simpa using this

lemma v2_injective : Function.Injective (v2 (N := N)) := by
  intro x y h
  have := congrArg vval h
  simpa using this

/-- Todo vértice está en una de las tres partes. -/
lemma exists_repr (u : Fin (3 * N)) :
    (∃ x, u = v0 x) ∨ (∃ x, u = v1 x) ∨ (∃ x, u = v2 x) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set r := u.val % N with hr
  have hrlt : r < N := Nat.mod_lt _ hN
  set x : ZMod N := (r : ZMod N) with hx
  have hxval : x.val = r := ZMod.val_cast_of_lt hrlt
  have hq : u.val / N < 3 := Nat.div_lt_of_lt_mul (by have := u.isLt; omega)
  have hdm : N * (u.val / N) + r = u.val := Nat.div_add_mod u.val N
  interval_cases h : (u.val / N)
  · left; exact ⟨x, Fin.ext (by simp only [v0, hxval]; omega)⟩
  · right; left; exact ⟨x, Fin.ext (by simp only [v1, hxval]; omega)⟩
  · right; right; exact ⟨x, Fin.ext (by simp only [v2, hxval]; omega)⟩

lemma repr_of_typ_zero {u : Fin (3 * N)} (h : typ u = 0) : ∃ x, u = v0 x := by
  rcases exists_repr u with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨x, rfl⟩
  · rw [typ_v1] at h; exact absurd h (by decide)
  · rw [typ_v2] at h; exact absurd h (by decide)

lemma repr_of_typ_one {u : Fin (3 * N)} (h : typ u = 1) : ∃ x, u = v1 x := by
  rcases exists_repr u with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [typ_v0] at h; exact absurd h (by decide)
  · exact ⟨x, rfl⟩
  · rw [typ_v2] at h; exact absurd h (by decide)

lemma repr_of_typ_two {u : Fin (3 * N)} (h : typ u = 2) : ∃ x, u = v2 x := by
  rcases exists_repr u with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [typ_v0] at h; exact absurd h (by decide)
  · rw [typ_v1] at h; exact absurd h (by decide)
  · exact ⟨x, rfl⟩

/-! ## 2. El grafo -/

/-- La relación dirigida que genera las aristas. -/
def Link (A : Finset (ZMod N)) (u v : Fin (3 * N)) : Prop :=
  (typ u = 0 ∧ typ v = 1 ∧ vval v - vval u ∈ A) ∨
  (typ u = 1 ∧ typ v = 2 ∧ vval v - vval u ∈ A) ∨
  (typ u = 0 ∧ typ v = 2 ∧ ∃ a ∈ A, vval v - vval u = a + a)

/-- **El grafo de Ruzsa–Szemerédi** de un conjunto `A ⊆ ZMod N`. -/
def rsGraph (A : Finset (ZMod N)) : SimpleGraph (Fin (3 * N)) where
  Adj u v := Link A u v ∨ Link A v u
  symm := fun _ _ h => h.symm
  loopless := ⟨by
    intro u h
    rcases h with h | h <;>
      rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
        · rw [h1] at h2; exact absurd h2 (by decide)⟩

noncomputable instance instDecidableRelRs (A : Finset (ZMod N)) :
    DecidableRel (rsGraph A).Adj := Classical.decRel _

lemma adj_v0_v1 {A : Finset (ZMod N)} (x y : ZMod N) :
    (rsGraph A).Adj (v0 x) (v1 y) ↔ y - x ∈ A := by
  simp [rsGraph, Link]

lemma adj_v1_v2 {A : Finset (ZMod N)} (x y : ZMod N) :
    (rsGraph A).Adj (v1 x) (v2 y) ↔ y - x ∈ A := by
  simp [rsGraph, Link]

lemma adj_v0_v2 {A : Finset (ZMod N)} (x y : ZMod N) :
    (rsGraph A).Adj (v0 x) (v2 y) ↔ ∃ a ∈ A, y - x = a + a := by
  simp [rsGraph, Link]

omit [NeZero N] in
lemma not_link_same {A : Finset (ZMod N)} {u v : Fin (3 * N)} (h : typ u = typ v) :
    ¬ Link A u v := by
  intro hl
  rcases hl with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
    · rw [h, h2] at h1; exact absurd h1 (by decide)

omit [NeZero N] in
/-- **El grafo es tripartito**: dos vértices de la misma parte nunca son adyacentes. -/
lemma not_adj_same {A : Finset (ZMod N)} {u v : Fin (3 * N)} (h : typ u = typ v) :
    ¬ (rsGraph A).Adj u v := by
  rintro (h' | h')
  · exact not_link_same h h'
  · exact not_link_same h.symm h'

/-! ## 3. Los items son exactamente los triángulos canónicos -/

/-- El triángulo canónico `x, x+a, x+2a`. -/
def tri (x a : ZMod N) : Finset (Fin (3 * N)) := {v0 x, v1 (x + a), v2 (x + a + a)}

lemma mem_tri {u : Fin (3 * N)} {x a : ZMod N} :
    u ∈ tri x a ↔ u = v0 x ∨ u = v1 (x + a) ∨ u = v2 (x + a + a) := by
  simp [tri]

lemma v0_ne_v1 (x y : ZMod N) : v0 x ≠ v1 y := by
  intro h; have h' := congrArg typ h; simp at h'

lemma v0_ne_v2 (x y : ZMod N) : v0 x ≠ v2 y := by
  intro h; have h' := congrArg typ h; simp at h'

lemma v1_ne_v2 (x y : ZMod N) : v1 x ≠ v2 y := by
  intro h; have h' := congrArg typ h; simp at h'

lemma card_tri (x a : ZMod N) : (tri x a).card = 3 := by
  rw [tri, Finset.card_insert_of_notMem (by simp [v0_ne_v1, v0_ne_v2]),
    Finset.card_insert_of_notMem (by simp [v1_ne_v2]), Finset.card_singleton]

/-- Cada triángulo canónico con `a ∈ A` es un item del grafo. -/
lemma isItem_tri {A : Finset (ZMod N)} {a : ZMod N} (ha : a ∈ A) (x : ZMod N) :
    IsItem (rsGraph A) (tri x a) := by
  have h01 : (rsGraph A).Adj (v0 x) (v1 (x + a)) := by
    rw [adj_v0_v1]; simpa using ha
  have h12 : (rsGraph A).Adj (v1 (x + a)) (v2 (x + a + a)) := by
    rw [adj_v1_v2]; simpa using ha
  have h02 : (rsGraph A).Adj (v0 x) (v2 (x + a + a)) := by
    rw [adj_v0_v2]
    exact ⟨a, ha, by ring⟩
  refine ⟨?_, Or.inl (card_tri x a)⟩
  intro u hu v hv huv
  rw [mem_tri] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | exact h01
      | exact h12
      | exact h02
      | exact h01.symm
      | exact h12.symm
      | exact h02.symm

omit [NeZero N] in
lemma typ_injOn {A : Finset (ZMod N)} {K : Finset (Fin (3 * N))} (hK : IsItem (rsGraph A) K) :
    Set.InjOn typ (K : Set (Fin (3 * N))) := by
  intro u hu v hv h
  by_contra hne
  exact not_adj_same h (hK.1 u hu v hv hne)

/-- **No hay `K₄`**: el grafo es tripartito, luego todo item es un triángulo. -/
lemma item_card_eq_three {A : Finset (ZMod N)} {K : Finset (Fin (3 * N))}
    (hK : IsItem (rsGraph A) K) : K.card = 3 := by
  have hle : K.card ≤ 3 := by
    have := Finset.card_le_card_of_injOn (f := typ) (t := (Finset.univ : Finset (Fin 3)))
      (fun u _ => by simp) (typ_injOn hK)
    simpa using this
  rcases hK.2 with h | h <;> omega

lemma exists_of_typ {A : Finset (ZMod N)} {K : Finset (Fin (3 * N))}
    (hK : IsItem (rsGraph A) K) (t : Fin 3) : ∃ u ∈ K, typ u = t := by
  classical
  have hcard : (K.image typ).card = 3 := by
    rw [Finset.card_image_of_injOn (typ_injOn hK), item_card_eq_three hK]
  have huniv : K.image typ = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard)
  have hmem : t ∈ K.image typ := by rw [huniv]; exact Finset.mem_univ _
  obtain ⟨u, hu, hut⟩ := Finset.mem_image.1 hmem
  exact ⟨u, hu, hut⟩

/-- **Clasificación de los items.**  Todo item del grafo de Ruzsa–Szemerédi es uno de los
triángulos canónicos `tri x a` con `a ∈ A`.  Aquí es donde se usa que `A` no tiene progresiones
aritméticas de tres términos. -/
lemma item_eq_tri {A : Finset (ZMod N)} (hA3 : ThreeAPFree (A : Set (ZMod N)))
    {K : Finset (Fin (3 * N))} (hK : IsItem (rsGraph A) K) :
    ∃ x a, a ∈ A ∧ K = tri x a := by
  obtain ⟨u, huK, hu⟩ := exists_of_typ hK 0
  obtain ⟨v, hvK, hv⟩ := exists_of_typ hK 1
  obtain ⟨w, hwK, hw⟩ := exists_of_typ hK 2
  obtain ⟨x, rfl⟩ := repr_of_typ_zero hu
  obtain ⟨y, rfl⟩ := repr_of_typ_one hv
  obtain ⟨z, rfl⟩ := repr_of_typ_two hw
  have huv : (rsGraph A).Adj (v0 x) (v1 y) := hK.1 _ huK _ hvK (v0_ne_v1 x y)
  have hvw : (rsGraph A).Adj (v1 y) (v2 z) := hK.1 _ hvK _ hwK (v1_ne_v2 y z)
  have huw : (rsGraph A).Adj (v0 x) (v2 z) := hK.1 _ huK _ hwK (v0_ne_v2 x z)
  rw [adj_v0_v1] at huv
  rw [adj_v1_v2] at hvw
  rw [adj_v0_v2] at huw
  obtain ⟨c, hc, hcz⟩ := huw
  have hsum : (y - x) + (z - y) = c + c := by rw [← hcz]; ring
  have hac : y - x = c :=
    hA3 (Finset.mem_coe.2 huv) (Finset.mem_coe.2 hc) (Finset.mem_coe.2 hvw) hsum
  have hbc : z - y = c :=
    hA3 (Finset.mem_coe.2 hvw) (Finset.mem_coe.2 hc) (Finset.mem_coe.2 huv)
      (by rw [← hsum]; ring)
  have hab : y - x = z - y := by rw [hac, hbc]
  refine ⟨x, y - x, huv, ?_⟩
  have hy : x + (y - x) = y := by ring
  have hz2 : y + (y - x) = z := by rw [hab]; ring
  have hsub : tri x (y - x) ⊆ K := by
    intro t ht
    rw [mem_tri, hy, hz2] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [item_card_eq_three hK, card_tri])).symm

/-! ## 4. Rigidez: cada arista en un único triángulo -/

lemma typ_ne_of_mem_tri {x a : ZMod N} {u v : Fin (3 * N)} (huv : u ≠ v)
    (hu : u ∈ tri x a) (hv : v ∈ tri x a) : typ u ≠ typ v := by
  rw [mem_tri] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | simp

lemma eqn_of_mem_two {x a y b : ZMod N} {u : Fin (3 * N)}
    (hu1 : u ∈ tri x a) (hu2 : u ∈ tri y b) :
    (typ u = 0 ∧ x = y) ∨ (typ u = 1 ∧ x + a = y + b) ∨
      (typ u = 2 ∧ x + a + a = y + b + b) := by
  rw [mem_tri] at hu1 hu2
  rcases hu1 with rfl | rfl | rfl <;> rcases hu2 with h | h | h
  · exact Or.inl ⟨by simp, v0_injective h⟩
  · exact absurd h (v0_ne_v1 _ _)
  · exact absurd h (v0_ne_v2 _ _)
  · exact absurd h.symm (v0_ne_v1 _ _)
  · exact Or.inr (Or.inl ⟨by simp, v1_injective h⟩)
  · exact absurd h (v1_ne_v2 _ _)
  · exact absurd h.symm (v0_ne_v2 _ _)
  · exact absurd h.symm (v1_ne_v2 _ _)
  · exact Or.inr (Or.inr ⟨by simp, v2_injective h⟩)

/-- **Dos triángulos canónicos con una arista común coinciden.** -/
lemma tri_eq_of_common_edge {A : Finset (ZMod N)}
    (hdbl : ∀ a ∈ A, ∀ b ∈ A, a + a = b + b → a = b)
    {x a y b : ZMod N} (ha : a ∈ A) (hb : b ∈ A)
    {u v : Fin (3 * N)} (huv : u ≠ v)
    (hu1 : u ∈ tri x a) (hu2 : u ∈ tri y b)
    (hv1 : v ∈ tri x a) (hv2 : v ∈ tri y b) : x = y ∧ a = b := by
  have htyp := typ_ne_of_mem_tri huv hu1 hv1
  rcases eqn_of_mem_two hu1 hu2 with ⟨htu, h1⟩ | ⟨htu, h1⟩ | ⟨htu, h1⟩ <;>
    rcases eqn_of_mem_two hv1 hv2 with ⟨htv, h2⟩ | ⟨htv, h2⟩ | ⟨htv, h2⟩
  · exact absurd (htu.trans htv.symm) htyp
  · exact ⟨h1, by linear_combination h2 - h1⟩
  · exact ⟨h1, hdbl a ha b hb (by linear_combination h2 - h1)⟩
  · exact ⟨h2, by linear_combination h1 - h2⟩
  · exact absurd (htu.trans htv.symm) htyp
  · refine ⟨?_, ?_⟩
    · linear_combination h1 - (h2 - h1)
    · linear_combination h2 - h1
  · exact ⟨h2, hdbl a ha b hb (by linear_combination h1 - h2)⟩
  · refine ⟨?_, ?_⟩
    · linear_combination h2 - (h1 - h2)
    · linear_combination h1 - h2
  · exact absurd (htu.trans htv.symm) htyp

/-- Los triángulos canónicos son distintos para parámetros distintos. -/
lemma tri_inj {A : Finset (ZMod N)}
    (hdbl : ∀ a ∈ A, ∀ b ∈ A, a + a = b + b → a = b)
    {x a y b : ZMod N} (ha : a ∈ A) (hb : b ∈ A) (h : tri x a = tri y b) :
    x = y ∧ a = b := by
  have hu1 : v0 x ∈ tri x a := by rw [mem_tri]; exact Or.inl rfl
  have hv1 : v1 (x + a) ∈ tri x a := by rw [mem_tri]; exact Or.inr (Or.inl rfl)
  exact tri_eq_of_common_edge hdbl ha hb (v0_ne_v1 _ _) hu1 (h ▸ hu1) hv1 (h ▸ hv1)

/-! ## 5. El sistema de items del grafo: rígido, de rango tres y de tamaño `N·|A|` -/

/-- Todos los soportes del sistema de items tienen rango `3`. -/
lemma graphSystem_three (A : Finset (ZMod N)) :
    ∀ S ∈ (graphSystem (rsGraph A)).supports, S.card = 3 := by
  intro S hS
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  have e32 : Nat.choose 3 2 = 3 := by decide
  rw [card_pairs, item_card_eq_three hK, e32]

/-- **La rigidez del grafo de Ruzsa–Szemerédi**: cada arista pertenece a un único item. -/
lemma graphSystem_rigid {A : Finset (ZMod N)} (hA3 : ThreeAPFree (A : Set (ZMod N)))
    (hdbl : ∀ a ∈ A, ∀ b ∈ A, a + a = b + b → a = b) :
    (graphSystem (rsGraph A)).Rigid := by
  classical
  intro S hS T hT e heS heT
  obtain ⟨K, hK, rfl⟩ := mem_supports.1 hS
  obtain ⟨L, hL, rfl⟩ := mem_supports.1 hT
  obtain ⟨x, a, ha, rfl⟩ := item_eq_tri hA3 hK
  obtain ⟨y, b, hb, rfl⟩ := item_eq_tri hA3 hL
  induction e using Sym2.ind with
  | _ p q =>
    rw [mk_mem_pairs] at heS heT
    obtain ⟨hpK, hqK, hpq⟩ := heS
    obtain ⟨hpL, hqL, -⟩ := heT
    obtain ⟨rfl, rfl⟩ := tri_eq_of_common_edge hdbl ha hb hpq hpK hpL hqK hqL
    rfl

/-- **Hay al menos `N·|A|` items**: uno por cada par `(x, a)` con `a ∈ A`. -/
lemma card_supports_ge {A : Finset (ZMod N)}
    (hdbl : ∀ a ∈ A, ∀ b ∈ A, a + a = b + b → a = b) :
    N * A.card ≤ (graphSystem (rsGraph A)).supports.card := by
  classical
  have hsub : ((Finset.univ : Finset (ZMod N)) ×ˢ A).image (fun p => pairs (tri p.1 p.2))
      ⊆ (graphSystem (rsGraph A)).supports := by
    intro S hS
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hS
    have ha : p.2 ∈ A := (Finset.mem_product.1 hp).2
    exact Finset.mem_image.2 ⟨tri p.1 p.2, mem_items.2 (isItem_tri ha p.1), rfl⟩
  have hinj : ∀ p ∈ (Finset.univ : Finset (ZMod N)) ×ˢ A,
      ∀ q ∈ (Finset.univ : Finset (ZMod N)) ×ˢ A,
      pairs (tri p.1 p.2) = pairs (tri q.1 q.2) → p = q := by
    intro p hp q hq h
    have hpa : p.2 ∈ A := (Finset.mem_product.1 hp).2
    have hqa : q.2 ∈ A := (Finset.mem_product.1 hq).2
    have htri : tri p.1 p.2 = tri q.1 q.2 :=
      pairs_injOn_items (isItem_tri hpa p.1) (isItem_tri hqa q.1) h
    obtain ⟨h1, h2⟩ := tri_inj hdbl hpa hqa htri
    exact Prod.ext h1 h2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun p hp q hq h => hinj p hp q hq h)] at hcard
  simpa [Finset.card_product, ZMod.card] using hcard

end FarExploration.RuzsaSzemeredi
