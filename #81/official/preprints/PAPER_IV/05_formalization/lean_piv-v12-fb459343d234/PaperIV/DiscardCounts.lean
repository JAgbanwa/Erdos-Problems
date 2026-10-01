import PaperIV.RegularityFormat

/-!
# Los cuatro conteos de descartes (RC01, ecuación (15.1))

Cierra el bloque de §15 que quedaba abierto: derivar `b₀, b₁, b₂, b₃` de la propia partición
`EqualRegularity`, en vez de recibirlos como hipótesis.

## Moneda: pares ordenados

Todo se cuenta con `SimpleGraph.interedges`, es decir en **pares ordenados** de vértices
adyacentes.  Es la moneda de Mathlib para densidades y evita pelearse con conjuntos de aristas
no orientadas.  Cada arista descartada aporta exactamente dos pares ordenados, así que el paso
final —`card_Bdesc_le_of_ordered`— divide entre dos.

## Los cuatro descartes

| | qué se descarta | cota (ordenada) |
|---|---|---|
| `B₀` | aristas incidentes en la basura `V₀` | `2δn²` |
| `B₁` | aristas internas a una parte | `n²/k₀` |
| `B₂` | aristas de parejas excepcionales de partes | `δn²` |
| `B₃` | aristas de parejas de partes con densidad `< d` | `dn²` |

Total `(3δ + 1/k₀ + d)n²`; dividido entre dos, `(3δ/2 + 1/(2k₀) + d/2)n²`, que está **dentro**
de la cota (15.1) `(2δ + 1/(2k₀) + d/2)n²` porque `3δ/2 ≤ 2δ`.  El margen sobrante es holgura
real de la fuente, no un ajuste.

## De dónde sale cada factor

El único ingrediente no trivial es `card_parts_mul_size_le`: las partes son disjuntas y de
tamaño común, luego `k·t ≤ n`.  Con eso:

* `B₁`: `k·t² = (k·t)·t ≤ n·t`, y de `k₀·t ≤ k·t ≤ n` sale `t ≤ n/k₀`;
* `B₂`: `|bad|·t² ≤ δk²t² = δ(k·t)² ≤ δn²`;
* `B₃`: hay a lo sumo `k²` parejas, y en cada una `|E(P,Q)| = d(P,Q)·t² ≤ d·t²`.

La identidad `|E(P,Q)| = d(P,Q)·|P||Q|` es la definición de densidad
(`SimpleGraph.edgeDensity_def`), no una estimación.

## Una precisión sobre `bad`

El campo `EqualRegularity.bad` es un `Finset (Finset α × Finset α)` cualquiera: la estructura
sólo acota su cardinal, no obliga a que sus elementos sean partes.  Por eso `B₂` **filtra** las
parejas de partes: descartar una pareja excepcional que no lo sea no tendría sentido, y el
filtro sólo puede bajar el cardinal.
-/

namespace PaperIV.DiscardCounts

open Finset SimpleGraph
open PaperIV.RegularityFormat

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

/-! ## 0. Las partes caben en el grafo -/

/-- **`k·t ≤ n`.**  Las partes son disjuntas y todas de tamaño `size`. -/
theorem card_parts_mul_size_le {δ : ℚ} (R : EqualRegularity G δ) :
    R.parts.card * R.size ≤ Fintype.card α := by
  classical
  have hbi : (R.parts.biUnion id).card = ∑ P ∈ R.parts, P.card :=
    Finset.card_biUnion (fun P hP Q hQ hne => R.pairwise_disjoint P hP Q hQ hne)
  have hsum : ∑ P ∈ R.parts, P.card = R.parts.card * R.size := by
    rw [Finset.sum_congr rfl (fun P hP => R.card_part P hP), Finset.sum_const, smul_eq_mul]
  have hle : (R.parts.biUnion id).card ≤ Fintype.card α := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-- La misma cota en `ℚ`. -/
theorem card_parts_mul_size_le_rat {δ : ℚ} (R : EqualRegularity G δ) :
    (R.parts.card : ℚ) * (R.size : ℚ) ≤ (Fintype.card α : ℚ) := by
  exact_mod_cast card_parts_mul_size_le R

/-- `|E(P,Q)| = d(P,Q)·|P||Q| ≤ d·|P||Q|`: la definición de densidad, no una estimación. -/
theorem card_interedges_le_of_density {P Q : Finset α} {d : ℚ}
    (hP : 0 < P.card) (hQ : 0 < Q.card) (h : G.edgeDensity P Q ≤ d) :
    ((G.interedges P Q).card : ℚ) ≤ d * (P.card : ℚ) * (Q.card : ℚ) := by
  have hP' : (0 : ℚ) < (P.card : ℚ) := by exact_mod_cast hP
  have hQ' : (0 : ℚ) < (Q.card : ℚ) := by exact_mod_cast hQ
  have hden : (0 : ℚ) < (P.card : ℚ) * (Q.card : ℚ) := mul_pos hP' hQ'
  rw [G.edgeDensity_def, div_le_iff₀ hden] at h
  calc ((G.interedges P Q).card : ℚ) ≤ d * ((P.card : ℚ) * (Q.card : ℚ)) := h
    _ = d * (P.card : ℚ) * (Q.card : ℚ) := by ring

/-- Unión sobre una familia de parejas, con una cota común por pareja. -/
theorem card_biUnion_pairs_le (F : Finset (Finset α × Finset α)) (M : ℚ)
    (hterm : ∀ q ∈ F, ((G.interedges q.1 q.2).card : ℚ) ≤ M) :
    ((F.biUnion (fun q => G.interedges q.1 q.2)).card : ℚ) ≤ (F.card : ℚ) * M := by
  classical
  have hb := Finset.card_biUnion_le (s := F) (t := fun q => G.interedges q.1 q.2)
  have hb' : ((F.biUnion (fun q => G.interedges q.1 q.2)).card : ℚ)
      ≤ ∑ q ∈ F, ((G.interedges q.1 q.2).card : ℚ) := by exact_mod_cast hb
  calc ((F.biUnion (fun q => G.interedges q.1 q.2)).card : ℚ)
      ≤ ∑ q ∈ F, ((G.interedges q.1 q.2).card : ℚ) := hb'
    _ ≤ ∑ _q ∈ F, M := Finset.sum_le_sum hterm
    _ = (F.card : ℚ) * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 1. `B₀`: la basura -/

/-- Los pares ordenados adyacentes con algún extremo en `V₀`. -/
def B₀ (G : SimpleGraph α) [DecidableRel G.Adj] (V₀ : Finset α) : Finset (α × α) :=
  G.interedges V₀ univ ∪ G.interedges univ V₀

/-- **`b₀ ≤ 2δn²`.** -/
theorem card_B₀_le {δ : ℚ} (V₀ : Finset α) (hV₀ : (V₀.card : ℚ) ≤ δ * (Fintype.card α : ℚ)) :
    ((B₀ G V₀).card : ℚ) ≤ 2 * δ * (Fintype.card α : ℚ) ^ 2 := by
  have hn0 : (0 : ℚ) ≤ (Fintype.card α : ℚ) := by positivity
  have h1 := G.card_interedges_le_mul V₀ univ
  have h2 := G.card_interedges_le_mul univ V₀
  rw [Finset.card_univ] at h1 h2
  have h1' : ((G.interedges V₀ univ).card : ℚ) ≤ (V₀.card : ℚ) * (Fintype.card α : ℚ) := by
    exact_mod_cast h1
  have h2' : ((G.interedges univ V₀).card : ℚ) ≤ (Fintype.card α : ℚ) * (V₀.card : ℚ) := by
    exact_mod_cast h2
  have hu : ((B₀ G V₀).card : ℚ)
      ≤ ((G.interedges V₀ univ).card : ℚ) + ((G.interedges univ V₀).card : ℚ) := by
    have hcu := Finset.card_union_le (G.interedges V₀ univ) (G.interedges univ V₀)
    rw [B₀]
    exact_mod_cast hcu
  nlinarith [hu, h1', h2', hV₀, hn0]

/-! ## 2. `B₁`: las aristas internas -/

/-- Los pares ordenados adyacentes dentro de una misma parte. -/
def B₁ {δ : ℚ} (R : EqualRegularity G δ) : Finset (α × α) :=
  R.parts.biUnion (fun P => G.interedges P P)

/-- **`b₁ ≤ n²/k₀`.**  Es `k·t² ≤ n²/k₀`, que sale de `k·t ≤ n` y `k₀ ≤ k`. -/
theorem card_B₁_le {δ : ℚ} (R : EqualRegularity G δ) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hk : k₀ ≤ R.parts.card) :
    ((B₁ R).card : ℚ) ≤ (1 / (k₀ : ℚ)) * (Fintype.card α : ℚ) ^ 2 := by
  classical
  have hterm : ∀ P ∈ R.parts, (G.interedges P P).card ≤ R.size * R.size := by
    intro P hP
    have h := G.card_interedges_le_mul P P
    rwa [R.card_part P hP] at h
  have hb : (B₁ R).card ≤ R.parts.card * (R.size * R.size) := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ P ∈ R.parts, (G.interedges P P).card
        ≤ ∑ _P ∈ R.parts, R.size * R.size := Finset.sum_le_sum hterm
      _ = R.parts.card * (R.size * R.size) := by rw [Finset.sum_const, smul_eq_mul]
  have hcard : ((B₁ R).card : ℚ)
      ≤ (R.parts.card : ℚ) * ((R.size : ℚ) * (R.size : ℚ)) := by exact_mod_cast hb
  have hk₀pos : (0 : ℚ) < (k₀ : ℚ) := by exact_mod_cast hk₀
  have hk₀k : (k₀ : ℚ) ≤ (R.parts.card : ℚ) := by exact_mod_cast hk
  have ht0 : (0 : ℚ) ≤ (R.size : ℚ) := by positivity
  have hn0 : (0 : ℚ) ≤ (Fintype.card α : ℚ) := by positivity
  have hkt := card_parts_mul_size_le_rat R
  have h1 : (k₀ : ℚ) * (R.size : ℚ) ≤ (Fintype.card α : ℚ) :=
    le_trans (mul_le_mul_of_nonneg_right hk₀k ht0) hkt
  have hkt0 : (0 : ℚ) ≤ (R.parts.card : ℚ) * (R.size : ℚ) := by positivity
  have h2 : ((k₀ : ℚ) * (R.size : ℚ)) * ((R.parts.card : ℚ) * (R.size : ℚ))
      ≤ (Fintype.card α : ℚ) * (Fintype.card α : ℚ) := mul_le_mul h1 hkt hkt0 hn0
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hk₀pos]
  nlinarith [mul_le_mul_of_nonneg_right hcard (le_of_lt hk₀pos), h2]

/-! ## 3. `B₂`: las parejas excepcionales -/

/-- Las parejas excepcionales que efectivamente son parejas de partes. -/
def bad₂ {δ : ℚ} (R : EqualRegularity G δ) : Finset (Finset α × Finset α) :=
  R.bad.filter (fun q => q.1 ∈ R.parts ∧ q.2 ∈ R.parts)

/-- Los pares ordenados adyacentes de una pareja excepcional de partes. -/
def B₂ {δ : ℚ} (R : EqualRegularity G δ) : Finset (α × α) :=
  (bad₂ R).biUnion (fun q => G.interedges q.1 q.2)

/-- **`b₂ ≤ δn²`.**  Es `|bad|·t² ≤ δk²t² = δ(k·t)² ≤ δn²`. -/
theorem card_B₂_le {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ) :
    ((B₂ R).card : ℚ) ≤ δ * (Fintype.card α : ℚ) ^ 2 := by
  classical
  have hterm : ∀ q ∈ bad₂ R,
      ((G.interedges q.1 q.2).card : ℚ) ≤ (R.size : ℚ) * (R.size : ℚ) := by
    intro q hq
    rw [bad₂, Finset.mem_filter] at hq
    have h := G.card_interedges_le_mul q.1 q.2
    rw [R.card_part q.1 hq.2.1, R.card_part q.2 hq.2.2] at h
    exact_mod_cast h
  have hb : ((B₂ R).card : ℚ) ≤ ((bad₂ R).card : ℚ) * ((R.size : ℚ) * (R.size : ℚ)) :=
    card_biUnion_pairs_le _ _ hterm
  have hbad : ((bad₂ R).card : ℚ) ≤ δ * (R.parts.card : ℚ) ^ 2 := by
    refine le_trans ?_ R.card_bad
    have : (bad₂ R).card ≤ R.bad.card := by rw [bad₂]; exact Finset.card_filter_le _ _
    exact_mod_cast this
  have ht0 : (0 : ℚ) ≤ (R.size : ℚ) := by positivity
  have hn0 : (0 : ℚ) ≤ (Fintype.card α : ℚ) := by positivity
  have hkt := card_parts_mul_size_le_rat R
  have hkt0 : (0 : ℚ) ≤ (R.parts.card : ℚ) * (R.size : ℚ) := by positivity
  have hsq : ((R.parts.card : ℚ) * (R.size : ℚ)) ^ 2 ≤ (Fintype.card α : ℚ) ^ 2 := by
    nlinarith [hkt, hkt0, hn0]
  nlinarith [hb, hbad, hsq, hδ, mul_nonneg ht0 ht0]

/-! ## 4. `B₃`: las parejas de densidad baja -/

/-- Las parejas de partes con densidad `< d`. -/
def lowPairs {δ : ℚ} (R : EqualRegularity G δ) (d : ℚ) : Finset (Finset α × Finset α) :=
  (R.parts ×ˢ R.parts).filter (fun q => G.edgeDensity q.1 q.2 < d)

/-- Los pares ordenados adyacentes de una pareja de densidad baja. -/
def B₃ {δ : ℚ} (R : EqualRegularity G δ) (d : ℚ) : Finset (α × α) :=
  (lowPairs R d).biUnion (fun q => G.interedges q.1 q.2)

/-- **`b₃ ≤ dn²`.**  Hay a lo sumo `k²` parejas, y en cada una `|E(P,Q)| ≤ d·t²`. -/
theorem card_B₃_le {δ : ℚ} (R : EqualRegularity G δ) (d : ℚ) (hd : 0 ≤ d) :
    ((B₃ R d).card : ℚ) ≤ d * (Fintype.card α : ℚ) ^ 2 := by
  classical
  have hterm : ∀ q ∈ lowPairs R d,
      ((G.interedges q.1 q.2).card : ℚ) ≤ d * ((R.size : ℚ) * (R.size : ℚ)) := by
    intro q hq
    rw [lowPairs, Finset.mem_filter, Finset.mem_product] at hq
    have hP : 0 < q.1.card := by rw [R.card_part q.1 hq.1.1]; exact R.size_pos
    have hQ : 0 < q.2.card := by rw [R.card_part q.2 hq.1.2]; exact R.size_pos
    have h := card_interedges_le_of_density hP hQ (le_of_lt hq.2)
    rw [R.card_part q.1 hq.1.1, R.card_part q.2 hq.1.2] at h
    calc ((G.interedges q.1 q.2).card : ℚ) ≤ d * (R.size : ℚ) * (R.size : ℚ) := h
      _ = d * ((R.size : ℚ) * (R.size : ℚ)) := by ring
  have hb : ((B₃ R d).card : ℚ)
      ≤ ((lowPairs R d).card : ℚ) * (d * ((R.size : ℚ) * (R.size : ℚ))) :=
    card_biUnion_pairs_le _ _ hterm
  have hlow : ((lowPairs R d).card : ℚ) ≤ (R.parts.card : ℚ) ^ 2 := by
    have h1 : (lowPairs R d).card ≤ (R.parts ×ˢ R.parts).card := by
      rw [lowPairs]; exact Finset.card_filter_le _ _
    rw [Finset.card_product] at h1
    have h2 : ((lowPairs R d).card : ℚ) ≤ (R.parts.card : ℚ) * (R.parts.card : ℚ) := by
      exact_mod_cast h1
    calc ((lowPairs R d).card : ℚ) ≤ (R.parts.card : ℚ) * (R.parts.card : ℚ) := h2
      _ = (R.parts.card : ℚ) ^ 2 := by ring
  have ht0 : (0 : ℚ) ≤ (R.size : ℚ) := by positivity
  have hn0 : (0 : ℚ) ≤ (Fintype.card α : ℚ) := by positivity
  have hkt := card_parts_mul_size_le_rat R
  have hkt0 : (0 : ℚ) ≤ (R.parts.card : ℚ) * (R.size : ℚ) := by positivity
  have hsq : ((R.parts.card : ℚ) * (R.size : ℚ)) ^ 2 ≤ (Fintype.card α : ℚ) ^ 2 := by
    nlinarith [hkt, hkt0, hn0]
  have hdt : (0 : ℚ) ≤ d * ((R.size : ℚ) * (R.size : ℚ)) := by positivity
  calc ((B₃ R d).card : ℚ)
      ≤ ((lowPairs R d).card : ℚ) * (d * ((R.size : ℚ) * (R.size : ℚ))) := hb
    _ ≤ (R.parts.card : ℚ) ^ 2 * (d * ((R.size : ℚ) * (R.size : ℚ))) :=
        mul_le_mul_of_nonneg_right hlow hdt
    _ = d * ((R.parts.card : ℚ) * (R.size : ℚ)) ^ 2 := by ring
    _ ≤ d * (Fintype.card α : ℚ) ^ 2 := mul_le_mul_of_nonneg_left hsq hd

/-! ## 5. El total, y (15.1) -/

/-- **El total ordenado.**  La unión de los cuatro descartes. -/
theorem card_discards_le {δ : ℚ} (hδ : 0 ≤ δ) (R : EqualRegularity G δ) (d : ℚ) (hd : 0 ≤ d)
    {k₀ : ℕ} (hk₀ : 0 < k₀) (hk : k₀ ≤ R.parts.card)
    (V₀ : Finset α) (hV₀ : (V₀.card : ℚ) ≤ δ * (Fintype.card α : ℚ)) :
    (((B₀ G V₀ ∪ B₁ R ∪ B₂ R ∪ B₃ R d).card : ℕ) : ℚ)
      ≤ (3 * δ + 1 / (k₀ : ℚ) + d) * (Fintype.card α : ℚ) ^ 2 := by
  classical
  have hu1 := Finset.card_union_le (B₀ G V₀ ∪ B₁ R ∪ B₂ R) (B₃ R d)
  have hu2 := Finset.card_union_le (B₀ G V₀ ∪ B₁ R) (B₂ R)
  have hu3 := Finset.card_union_le (B₀ G V₀) (B₁ R)
  have hall : ((B₀ G V₀ ∪ B₁ R ∪ B₂ R ∪ B₃ R d).card : ℚ)
      ≤ ((B₀ G V₀).card : ℚ) + ((B₁ R).card : ℚ) + ((B₂ R).card : ℚ) + ((B₃ R d).card : ℚ) := by
    have h : (B₀ G V₀ ∪ B₁ R ∪ B₂ R ∪ B₃ R d).card
        ≤ (B₀ G V₀).card + (B₁ R).card + (B₂ R).card + (B₃ R d).card := by omega
    exact_mod_cast h
  have h0 := card_B₀_le (G := G) V₀ hV₀
  have h1 := card_B₁_le R hk₀ hk
  have h2 := card_B₂_le hδ R
  have h3 := card_B₃_le R d hd
  linarith [hall, h0, h1, h2, h3]

/-- **(15.1).**  Cada arista descartada aporta dos pares ordenados, así que dividir entre dos
el total de `card_discards_le` cae dentro de la cota de la fuente: `3δ/2 ≤ 2δ`. -/
theorem card_Bdesc_le_of_ordered {δ d B n k₀ : ℚ} (hδ : 0 ≤ δ) (hk₀ : 0 < k₀)
    (hord : 2 * B ≤ (3 * δ + 1 / k₀ + d) * n ^ 2) :
    B ≤ (2 * δ + 1 / (2 * k₀) + d / 2) * n ^ 2 := by
  have he : 1 / (2 * k₀) = (1 / k₀) / 2 := by
    field_simp
  rw [he]
  nlinarith [hord, mul_nonneg hδ (sq_nonneg n)]

end PaperIV.DiscardCounts
