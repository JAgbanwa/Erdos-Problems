import PaperIV.CountingTelescope

/-!
# La estimación de un paso: regularidad sin condiciones de tamaño

Cuarta pieza de **GAP-RP01**, y la última obligación que quedaba de la rama del conteo
enraizado (`E01_BRIDGE_STATUS.md` §22).

## El problema con la forma cruda de `IsUniform`

`SimpleGraph.IsUniform G ε s t` dice
```
∀ s' ⊆ s, ∀ t' ⊆ t,  (#s)·ε ≤ #s' →  (#t)·ε ≤ #t' →  |d(s',t') − d(s,t)| < ε,
```
con **dos condiciones de tamaño**.  En un telescopado eso es un problema: cada paso
produciría un caso «rectángulo demasiado pequeño» que habría que arrastrar, y de ahí sale la
cascada de limpiezas que GAP-RP01 quiere evitar.

## La forma que sí compone

`interedges_approx` elimina las condiciones absorbiendo los casos pequeños en la propia
cota:

```
∀ s' ⊆ s, ∀ t' ⊆ t :   | #E(s',t')  −  d(s,t)·#s'·#t' |  ≤  ε·#s·#t.
```

**Sin hipótesis sobre `#s'` ni `#t'`.**  Si el rectángulo es grande, la cota sale de
`IsUniform`; si es pequeño, ambos términos están ya por debajo de `ε·#s·#t` y la diferencia
también.  El error se mide siempre contra `#s·#t`, que es lo que el telescopado necesita: una
cota **uniforme** por paso.

Con eso, `CountingTelescope.telescoping_bound` se aplica sin casos y la rama queda cerrada:

```
segundo momento enraizado          ← RootedCounting.second_moment_of_counts     DEMOSTRADO
 = conteo de patrón + del duplicado ← RootedCountingBridge.sum_fiber_card(_sq)  DEMOSTRADO
 telescopado: m parejas → m pasos   ← CountingTelescope.telescoping_bound       DEMOSTRADO
 constante (4ℓ−1)                   ← CountingTelescope.second_moment_constant  DEMOSTRADO
 cota de raíces malas               ← RootedCounting.card_bad_roots_le          DEMOSTRADO
 estimación de UN paso              ← `interedges_approx` (aquí)                DEMOSTRADO
```

## Lo que sigue faltando, dicho con precisión

Esto cierra la **aritmética y la estimación local**.  Lo que **no** hace es construir la
sucesión híbrida `f : ℕ → ℚ` del telescopado para un patrón concreto: hay que definir los
conteos intermedios (indicadores sustituidos por densidades, una pareja a la vez) y
comprobar que cada paso encaja en `interedges_approx` — lo cual, para `K₃`, requiere ver que
al fijar el tercer vértice `c` el rectángulo relevante es
`(N(c) ∩ V_i , N(c) ∩ V_j)`, y análogamente para `K₄`.

Ése es trabajo de construcción, no de estimación, y es el siguiente paso natural.
-/

namespace PaperIV.OneStepEstimate

open Finset

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]
variable {s t : Finset α}

/-- El número de aristas entre dos conjuntos es su densidad por el producto de los tamaños.
Vale también cuando alguno es vacío (ambos lados son cero). -/
theorem card_interedges_eq (a b : Finset α) :
    (#(G.interedges a b) : ℚ) = G.edgeDensity a b * #a * #b := by
  rcases eq_or_ne ((#a : ℚ) * #b) 0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with ha | hb
    · have ha' : a = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast ha)
      subst ha'
      rw [SimpleGraph.interedges_empty_left]
      simp
    · have hb' : b = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast hb)
      subst hb'
      have hemp : G.interedges a ∅ = ∅ := by
        rw [SimpleGraph.interedges_def]; simp
      rw [hemp]; simp
  · have ha0 : (#a : ℚ) ≠ 0 := fun hz => h0 (by rw [hz]; ring)
    have hb0 : (#b : ℚ) ≠ 0 := fun hz => h0 (by rw [hz]; ring)
    rw [← SimpleGraph.card_interedges_div_card]
    field_simp

/-- **La estimación de un paso, sin condiciones de tamaño.**  Para una pareja `ε`-uniforme y
**cualesquiera** subconjuntos, el número de aristas entre ellos dista a lo sumo `ε·#s·#t` de
lo que predice la densidad global.

Ésta es la forma que compone en un telescopado: la cota es uniforme, medida siempre contra
`#s·#t`, y no arrastra casos. -/
theorem interedges_approx {ε : ℚ} (hε : 0 ≤ ε) (h : G.IsUniform ε s t)
    {s' t' : Finset α} (hs' : s' ⊆ s) (ht' : t' ⊆ t) :
    |(#(G.interedges s' t') : ℚ) - G.edgeDensity s t * #s' * #t'| ≤ ε * #s * #t := by
  classical
  have hs'c : (#s' : ℚ) ≤ #s := by exact_mod_cast Finset.card_le_card hs'
  have ht'c : (#t' : ℚ) ≤ #t := by exact_mod_cast Finset.card_le_card ht'
  have hs'0 : (0 : ℚ) ≤ #s' := by positivity
  have ht'0 : (0 : ℚ) ≤ #t' := by positivity
  by_cases hbig : (#s : ℚ) * ε ≤ #s' ∧ (#t : ℚ) * ε ≤ #t'
  · -- rectángulo grande: la regularidad se aplica directamente
    have huni := h hs' ht' hbig.1 hbig.2
    have hid : (#(G.interedges s' t') : ℚ) = G.edgeDensity s' t' * #s' * #t' :=
      card_interedges_eq s' t'
    rw [hid]
    have hfac : G.edgeDensity s' t' * #s' * #t' - G.edgeDensity s t * #s' * #t'
        = (G.edgeDensity s' t' - G.edgeDensity s t) * (#s' * #t') := by ring
    rw [hfac, abs_mul]
    have habs : |((#s' : ℚ) * #t')| = (#s' : ℚ) * #t' := abs_of_nonneg (by positivity)
    rw [habs]
    have hstep : |G.edgeDensity s' t' - G.edgeDensity s t| ≤ ε := le_of_lt huni
    calc |G.edgeDensity s' t' - G.edgeDensity s t| * ((#s' : ℚ) * #t')
        ≤ ε * ((#s' : ℚ) * #t') := by
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
      _ ≤ ε * ((#s : ℚ) * #t) := by
          have : (#s' : ℚ) * #t' ≤ (#s : ℚ) * #t := by nlinarith
          exact mul_le_mul_of_nonneg_left this hε
      _ = ε * #s * #t := by ring
  · -- rectángulo pequeño: ambos términos ya están por debajo de la cota
    have hsmall : (#s' : ℚ) * #t' ≤ ε * ((#s : ℚ) * #t) := by
      rcases not_and_or.1 hbig with hns | hnt
      · have h1 : (#s' : ℚ) ≤ (#s : ℚ) * ε := le_of_lt (lt_of_not_ge hns)
        nlinarith
      · have h1 : (#t' : ℚ) ≤ (#t : ℚ) * ε := le_of_lt (lt_of_not_ge hnt)
        nlinarith
    have hA : (0 : ℚ) ≤ #(G.interedges s' t') := by positivity
    have hA' : (#(G.interedges s' t') : ℚ) ≤ (#s' : ℚ) * #t' := by
      have hnat := G.card_interedges_le_mul s' t'
      exact_mod_cast hnat
    have hB : (0 : ℚ) ≤ G.edgeDensity s t * #s' * #t' := by
      have := G.edgeDensity_nonneg s t
      positivity
    have hB' : G.edgeDensity s t * #s' * #t' ≤ (#s' : ℚ) * #t' := by
      have hd := G.edgeDensity_le_one s t
      nlinarith
    rw [abs_le]
    constructor <;> nlinarith

/-! ## El formato (3.2) de RC01, como predicado

`interedges_approx` es exactamente la desigualdad (3.2) del contrato de regularidad de RC01
(§3.3) con `d` igual a la densidad global.  Darle nombre propio —con la densidad como
**parámetro libre**— sirve para dos cosas:

1. los lemas de conteo dejan de depender de `SimpleGraph.IsUniform` y pasan a consumir
   literalmente (3.2), que es lo que el adaptador de regularidad entrega;
2. se puede **restringir** a subconjuntos (recortar las partes para igualar tamaños) pagando
   sólo un factor constante, cosa que `IsUniform` no permite.
-/

/-- **Formato (3.2).**  La discrepancia de cortes: entre cualesquiera subconjuntos, el conteo
de aristas dista de lo que predice `d` a lo sumo `ε·#s·#t`.  Sin condiciones de tamaño. -/
def DiscrepAt (G : SimpleGraph α) [DecidableRel G.Adj] (ε d : ℚ) (s t : Finset α) : Prop :=
  ∀ s' ⊆ s, ∀ t' ⊆ t,
    |(#(G.interedges s' t') : ℚ) - d * #s' * #t'| ≤ ε * #s * #t

/-- Una pareja `ε`-uniforme cumple (3.2) con su densidad global.  Es `interedges_approx`. -/
theorem discrepAt_of_isUniform {ε : ℚ} (hε : 0 ≤ ε) (h : G.IsUniform ε s t) :
    DiscrepAt G ε (G.edgeDensity s t) s t :=
  fun _ hs' _ ht' => interedges_approx hε h hs' ht'

/-- (3.2) es monótona en el parámetro. -/
theorem DiscrepAt.mono {ε ε' d : ℚ} (h : DiscrepAt G ε d s t) (hle : ε ≤ ε') :
    DiscrepAt G ε' d s t := by
  intro s' hs' t' ht'
  refine (h s' hs' t' ht').trans ?_
  have hst : (0 : ℚ) ≤ (#s : ℚ) * #t := by positivity
  calc ε * #s * #t = ε * ((#s : ℚ) * #t) := by ring
    _ ≤ ε' * ((#s : ℚ) * #t) := mul_le_mul_of_nonneg_right hle hst
    _ = ε' * #s * #t := by ring

/-- De (3.2) sale que `d` aproxima la densidad verdadera. -/
theorem DiscrepAt.abs_density_sub_le {ε d : ℚ} (h : DiscrepAt G ε d s t)
    (hs : 0 < #s) (ht : 0 < #t) : |G.edgeDensity s t - d| ≤ ε := by
  have hkey := h s Finset.Subset.rfl t Finset.Subset.rfl
  rw [card_interedges_eq] at hkey
  have hs0 : (0 : ℚ) < #s := by exact_mod_cast hs
  have ht0 : (0 : ℚ) < #t := by exact_mod_cast ht
  have hpos : (0 : ℚ) < (#s : ℚ) * #t := mul_pos hs0 ht0
  have hfac : (G.edgeDensity s t : ℚ) * #s * #t - d * #s * #t
      = (G.edgeDensity s t - d) * ((#s : ℚ) * #t) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (le_of_lt hpos)] at hkey
  have hkey' : |G.edgeDensity s t - d| * ((#s : ℚ) * #t) ≤ ε * ((#s : ℚ) * #t) := by
    calc |G.edgeDensity s t - d| * ((#s : ℚ) * #t) ≤ ε * #s * #t := hkey
      _ = ε * ((#s : ℚ) * #t) := by ring
  exact le_of_mul_le_mul_right hkey' hpos

/-- **Recorte.**  (3.2) sobre `s, t` se restringe a subconjuntos `u ⊆ s`, `v ⊆ t` pagando el
cuadrado de la razón de tamaños.  Es lo que hace falta para igualar los tamaños de las partes
de una equipartición sin perder la discrepancia. -/
theorem DiscrepAt.restrict {ε d c : ℚ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (h : DiscrepAt G ε d s t)
    {u v : Finset α} (hu : u ⊆ s) (hv : v ⊆ t)
    (hcu : (#s : ℚ) ≤ c * #u) (hcv : (#t : ℚ) ≤ c * #v) :
    DiscrepAt G (c * c * ε) d u v := by
  intro s' hs' t' ht'
  refine (h s' (hs'.trans hu) t' (ht'.trans hv)).trans ?_
  have hu0 : (0 : ℚ) ≤ #u := by positivity
  have ht0 : (0 : ℚ) ≤ #t := by positivity
  calc ε * #s * #t = ε * ((#s : ℚ) * #t) := by ring
    _ ≤ ε * ((c * #u) * (c * #v)) := by
        refine mul_le_mul_of_nonneg_left ?_ hε
        exact mul_le_mul hcu hcv ht0 (mul_nonneg hc hu0)
    _ = c * c * ε * #u * #v := by ring

/-- **Cambio de densidad.**  Si (3.2) vale con un `d` cualquiera, vale con la densidad
verdadera al doble de coste.  Permite que el último paso del telescopado siga siendo
gratuito. -/
theorem DiscrepAt.reDensity {ε d : ℚ} (hε : 0 ≤ ε) (h : DiscrepAt G ε d s t)
    (hs : 0 < #s) (ht : 0 < #t) :
    DiscrepAt G (2 * ε) (G.edgeDensity s t) s t := by
  intro s' hs' t' ht'
  have hd := h.abs_density_sub_le hs ht
  have hb := h s' hs' t' ht'
  have hs'c : (#s' : ℚ) ≤ #s := by exact_mod_cast Finset.card_le_card hs'
  have ht'c : (#t' : ℚ) ≤ #t := by exact_mod_cast Finset.card_le_card ht'
  have hs'0 : (0 : ℚ) ≤ #s' := by positivity
  have ht'0 : (0 : ℚ) ≤ #t' := by positivity
  have hpos : (0 : ℚ) ≤ (#s' : ℚ) * #t' := mul_nonneg hs'0 ht'0
  have hprod : (#s' : ℚ) * #t' ≤ (#s : ℚ) * #t :=
    mul_le_mul hs'c ht'c ht'0 (by positivity)
  have hscale : ε * ((#s' : ℚ) * #t') ≤ ε * ((#s : ℚ) * #t) :=
    mul_le_mul_of_nonneg_left hprod hε
  rw [abs_le] at hb hd ⊢
  have hup := mul_le_mul_of_nonneg_right hd.2 hpos
  have hlo := mul_le_mul_of_nonneg_right hd.1 hpos
  constructor
  · linarith [hb.1, hb.2, hup, hlo, hscale]
  · linarith [hb.1, hb.2, hup, hlo, hscale]

end PaperIV.OneStepEstimate
