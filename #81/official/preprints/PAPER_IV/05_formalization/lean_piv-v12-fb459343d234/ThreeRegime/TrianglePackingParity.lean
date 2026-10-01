import ThreeRegime.CompleteStateObligation

/-!
# La obligación sólo-triángulos no es satisfacible

`ThreeRegime.centre_closes_of_triangle_packing` reduce el estado completo a un empaquetamiento de
triángulos arista-disjuntos de `K_n` con `n(n−2) ≤ 6t`. Ese enunciado es **verdadero**, pero su
hipótesis es **insatisfacible para toda la familia `n ≡ 4 (mod 6)`** —`n = 4, 10, 16, 22, …`—, de
modo que no sirve como obligación pendiente: no es que falte construir el empaquetamiento, es que
no existe.

## Por qué

Sea `P` un empaquetamiento de triángulos de `K_n`. Fijado `v`, cada pieza que contiene a `v`
consume exactamente **dos** de las `n−1` aristas incidentes a `v`, y piezas distintas consumen
aristas distintas. Luego

```text
2 · |{K ∈ P : v ∈ K}| ≤ n − 1,
```

y si `n` es par el lado derecho es impar, así que la cota real es `n − 2`. Sumando sobre `v` y
usando que cada triángulo se cuenta tres veces,

```text
6 · |P| ≤ n · (n − 2).
```

Con la hipótesis `n(n−2) ≤ 6·|P|` esto fuerza la igualdad `6·|P| = n(n−2)`, es decir `6 ∣ n(n−2)`.
Pero con `n = 6k+4` se tiene `n(n−2) = 36k² + 36k + 8 ≡ 2 (mod 6)`. Contradicción.

Es la cota clásica de empaquetamiento de ternas (Spencer, Schönheim); aquí sólo se necesita su
mitad fácil, que es el conteo por vértice.

## Qué hacer en su lugar

`centre_closes_of_gain` da la forma correcta: lo que hace falta es **`n(n−2) ≤ 3·g(P)`** con `P`
mixto. Con sólo triángulos `g = 2|P|` y se recupera el enunciado anterior; con `q` piezas `K₄` se
obtiene `n(n−2) ≤ 6t + 15q`, y el defecto de la familia `n ≡ 4 (mod 6)` se absorbe. No es
casualidad que el caso más pequeño de esa familia sea `n = 4`, donde —como ya observa
`centre_route_closes_on_small_complete`— la ruta del centro cierra **con la pieza `K₄` sola**.
-/

namespace ThreeRegime.TrianglePackingParity

open Finset PaperIV PaperIV.FarRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Las aristas de una pieza incidentes a un vértice suyo -/

/-- Las parejas de `K` que contienen a `v` son exactamente las que unen `v` con otro vértice
de `K`. -/
theorem filter_mem_pairs {K : Finset V} {v : V} (hv : v ∈ K) :
    (pairs K).filter (fun e => v ∈ e) = (K.erase v).image (fun u => s(v, u)) := by
  classical
  refine Finset.Subset.antisymm (fun e he => ?_) (fun e he => ?_)
  · obtain ⟨hpair, hmem⟩ := Finset.mem_filter.1 he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.1 hpair
      rcases Sym2.mem_iff.1 hmem with rfl | rfl
      · exact Finset.mem_image.2 ⟨b, Finset.mem_erase.2 ⟨fun h => hab h.symm, hb⟩, rfl⟩
      · exact Finset.mem_image.2
          ⟨a, Finset.mem_erase.2 ⟨hab, ha⟩, by rw [Sym2.eq_swap]⟩
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hne, huK⟩ := Finset.mem_erase.1 hu
    exact Finset.mem_filter.2
      ⟨mk_mem_pairs.2 ⟨hv, huK, fun h => hne h.symm⟩, Sym2.mem_mk_left v u⟩

/-- Y son exactamente `|K| − 1`. -/
theorem card_filter_mem_pairs {K : Finset V} {v : V} (hv : v ∈ K) :
    ((pairs K).filter (fun e => v ∈ e)).card = K.card - 1 := by
  classical
  rw [filter_mem_pairs hv, Finset.card_image_of_injOn, Finset.card_erase_of_mem hv]
  intro x _ y _ hxy
  rcases Sym2.eq_iff.1 hxy with ⟨-, h⟩ | ⟨rfl, rfl⟩
  · exact h
  · rfl

/-! ## 2. Cota por vértice -/

/-- `pairs` es monótona. -/
private theorem pairs_mono {K L : Finset V} (h : K ⊆ L) : pairs K ⊆ pairs L := by
  intro e he
  obtain ⟨hall, hdiag⟩ := mem_pairs.1 he
  exact mem_pairs.2 ⟨fun a ha => h (hall a ha), hdiag⟩

/-- **Cada vértice soporta a lo sumo `(n−1)/2` triángulos del empaquetamiento.**

Las dos aristas que cada pieza consume en `v` son distintas de las de cualquier otra pieza, y
todas viven entre las `n−1` parejas incidentes a `v`. -/
theorem two_mul_card_pieces_at_le (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) (v : V) :
    2 * (P.pieces.filter (fun K => v ∈ K)).card ≤ Fintype.card V - 1 := by
  classical
  set S := P.pieces.filter (fun K => v ∈ K) with hS
  -- las aristas incidentes a `v` dentro de cada pieza, reunidas
  have hdisj : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Disjoint ((pairs K).filter (fun e => v ∈ e)) ((pairs L).filter (fun e => v ∈ e)) := by
    intro K hK L hL hne
    exact ((P.edgeDisjoint K (Finset.mem_filter.1 hK).1 L (Finset.mem_filter.1 hL).1
      hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hcards : ∀ K ∈ S, ((pairs K).filter (fun e => v ∈ e)).card = 2 := by
    intro K hK
    obtain ⟨hKP, hvK⟩ := Finset.mem_filter.1 hK
    rw [card_filter_mem_pairs (Finset.mem_coe.1 hvK), htri K hKP]
  have hsum : (S.biUnion fun K => (pairs K).filter (fun e => v ∈ e)).card = 2 * S.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hcards, Finset.sum_const,
      smul_eq_mul, Nat.mul_comm]
  have hsub : (S.biUnion fun K => (pairs K).filter (fun e => v ∈ e)) ⊆
      (pairs (Finset.univ : Finset V)).filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨K, hK, hmem⟩ := Finset.mem_biUnion.1 he
    obtain ⟨hpair, hv⟩ := Finset.mem_filter.1 hmem
    exact Finset.mem_filter.2 ⟨pairs_mono (Finset.subset_univ K) hpair, hv⟩
  have htotal : ((pairs (Finset.univ : Finset V)).filter (fun e => v ∈ e)).card
      = Fintype.card V - 1 := by
    rw [card_filter_mem_pairs (Finset.mem_univ v), Finset.card_univ]
  rw [← hsum, ← htotal]
  exact Finset.card_le_card hsub

/-! ## 3. Doble conteo y la cota global -/

private theorem sum_card_filter_mem (S : Finset (Finset V)) :
    ∑ v : V, (S.filter (fun K => v ∈ K)).card = ∑ K ∈ S, K.card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, Nat.mul_one]

/-- **La cota de empaquetamiento de ternas, en su mitad fácil.**

Si el orden es par, `6·|P| ≤ n(n−2)`. La paridad es esencial: el conteo por vértice da `n−1`, que
es impar, de modo que la cota real es `n−2`. -/
theorem six_mul_card_pieces_le (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) (heven : Fintype.card V % 2 = 0) :
    6 * P.pieces.card ≤ Fintype.card V * (Fintype.card V - 2) := by
  classical
  set n := Fintype.card V with hn
  have hper : ∀ v : V, 2 * (P.pieces.filter (fun K => v ∈ K)).card ≤ n - 2 := by
    intro v
    have h := two_mul_card_pieces_at_le P htri v
    omega
  have hsum : ∑ v : V, 2 * (P.pieces.filter (fun K => v ∈ K)).card ≤ ∑ _v : V, (n - 2) :=
    Finset.sum_le_sum fun v _ => hper v
  rw [← Finset.mul_sum, sum_card_filter_mem, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← hn] at hsum
  have hthree : ∑ K ∈ P.pieces, K.card = 3 * P.pieces.card := by
    rw [Finset.sum_congr rfl htri, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [hthree] at hsum
  omega

/-! ## 4. La consecuencia: la obligación sólo-triángulos es vacía en `n ≡ 4 (mod 6)` -/

/-- **No existe el empaquetamiento que la reducción sólo-triángulos pide.**

Para `n ≡ 4 (mod 6)` —es decir `n = 4, 10, 16, 22, …`— ningún empaquetamiento de triángulos
arista-disjuntos de `K_n` cumple `n(n−2) ≤ 6·|P|`. El caso `n = 10` es el primero no trivial: la
hipótesis pide `14` triángulos y el máximo es `13`. -/
theorem not_triangle_obligation_of_four_mod_six
    (hn : Fintype.card V % 6 = 4) (P : Packing (⊤ : SimpleGraph V))
    (htri : ∀ K ∈ P.pieces, K.card = 3) :
    ¬ (Fintype.card V * (Fintype.card V - 2) ≤ 6 * P.pieces.card) := by
  intro hge
  have heven : Fintype.card V % 2 = 0 := by omega
  have hle := six_mul_card_pieces_le P htri heven
  -- la igualdad forzada `6·|P| = n(n−2)` exige `6 ∣ n(n−2)`, y `n = 6k+4` da resto `2`
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card V = 6 * k + 4 := ⟨Fintype.card V / 6, by omega⟩
  have h2 : Fintype.card V - 2 = 6 * k + 2 := by omega
  have hprod : Fintype.card V * (Fintype.card V - 2)
      = 6 * (6 * (k * k) + 6 * k + 1) + 2 := by
    rw [h2, hk]; ring
  omega

/-! ## 5. La forma correcta de la obligación -/

/-- **Reformulación mixta, satisfacible.**  Lo que hace falta en un estado completo es
`n(n−2) ≤ 3·g(P)` con `P` mixto.  Con sólo triángulos es `n(n−2) ≤ 6·|P|`; con `q` piezas `K₄`
se convierte en `n(n−2) ≤ 6t + 15q`, y ahí sí cabe la familia `n ≡ 4 (mod 6)`. -/
theorem centre_closes_of_gain (P : Packing (⊤ : SimpleGraph V))
    (hgain : Fintype.card V * (Fintype.card V - 2) ≤ 3 * P.gain) :
    ∃ Q : CliquePartition (⊤ : SimpleGraph V),
      Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize (Fintype.card V) := by
  refine ThreeRegime.centre_closes_of_packing_gain P ?_
  have hchoose : 6 * Nat.choose (Fintype.card V) 2 = 3 * (Fintype.card V * (Fintype.card V - 1)) :=
    ThreeRegime.six_mul_choose_two _
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hs | hb
  · have hz : Nat.choose (Fintype.card V) 2 = 0 := Nat.choose_eq_zero_of_lt hs
    omega
  · obtain ⟨j, hj⟩ : ∃ j, Fintype.card V = j + 2 := ⟨Fintype.card V - 2, by omega⟩
    have hsub : Fintype.card V - 2 = j := by omega
    have hsub1 : Fintype.card V - 1 = j + 1 := by omega
    rw [hsub, hj] at hgain
    rw [hchoose, hsub1, hj]
    nlinarith [hgain]

end ThreeRegime.TrianglePackingParity
