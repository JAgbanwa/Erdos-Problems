import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity

/-!
# De qué depende realmente el umbral de la rama cercana

El umbral de la rama cercana —hoy `n ≥ 4·10^12`; antes de esta revisión, `2·10^13`— no es una
elección. Sale de una cadena de tres
desigualdades escalares que se estorban entre sí, y este módulo la aísla: **ninguna de ellas
menciona grafos**, de modo que se puede ver de un vistazo qué constante hay que atacar y cuánto
paga atacarla.

## Las tres desigualdades

Escribimos `B` para el **presupuesto de regularización** —el `65536` de
`PaperIV.RootVocab.card_strays_le` y compañía, que aparece siempre en la forma
`B · (aristas exteriores + incidencias faltantes) ≤ |P|²`—, `alpha` para la fracción del orden que
ocupa el núcleo (`33/100` en el árbol, estructuralmente `≈ 1/3`), y `eps` para el radio del
entorno de la familia completo-split dentro del cual se localiza el grafo.

1. **Cuenta física de edición.** El defecto de la raíz es a lo sumo `eps·n² + u·n`, donde `u` son
   los vértices que el núcleo comparador pierde al quedarse con su clique máxima. Tiene que caber
   en el presupuesto: `B · defecto ≤ a²` con `a ≥ alpha·n`.
2. **Codimensión cordal.** `u` sólo está acotado por `u(u+1)/2 ≤ eps·n²`, es decir
   `u ≈ √(2 eps)·n`, y esa cota es **aguda** (se alcanza cuando el complemento del núcleo es una
   clique). Luego el término `u·n` del punto 1 es `√(2 eps)·n²`, no `eps·n²`.
3. **Contracción del descenso.** La localización exige que el presupuesto total de defecto,
   `20·(eta·n² + n/6 + 1/24)`, sea una fracción del entorno: `< (eps/4)·n²`. El sumando `n/6` es
   el término lineal del objetivo y es irreducible, así que esto fuerza `n ≳ 1/eps`.

Las dos primeras empujan `eps` **hacia abajo** —como `1/B²`, por la raíz cuadrada del punto 2— y
la tercera empuja `n` **hacia arriba** como `1/eps`. Resultado:

```text
N_cercano = Θ(B² / alpha⁴).
```

## Lo que eso significa en números

| `B` | cota inferior `80·B²` | umbral suficiente `1280·B²/alpha⁴` |
|---|---|---|
| `65536` (el del árbol) | `3.4·10^11` | `4.6·10^14` |
| `8192` | `5.4·10^9` | `7.2·10^12` |
| `1024` | `8.4·10^7` | `1.1·10^11` |

El árbol alcanza `4·10^12`, por debajo de ambas columnas, porque sus márgenes reales son de un
10 % y no del factor dos con el que aquí se demuestra. Lo que no cambia con los márgenes es el
**exponente**: el umbral cercano es cuadrático en el presupuesto de regularización.

## La desigualdad que hoy manda (sección 5)

Con `eps` fijo, el umbral lo fija **sólo** la contracción del descenso, y ésta depende de dos
cosas que antes se regalaban:

* la **barrera** con la que se invoca el descenso.  `H1DescentBarrier` sólo pide
  `contracted ≤ barrier ≤ outer - 1/n`; tomar `barrier = eps/2` y `contracted = barrier/2`
  regalaba un factor cuatro.  La barrera máxima admisible es `eps - 1/n`;
* la **constante del presupuesto de cuentas** `K` en `m + A ≤ K·(déficit)`.  Con el par
  conservador `(1/20, 1/2)` sale `K = 20`; con los coeficientes L10Q ya demostrados
  `(117/1825, 12687/20000)` sale `K = 16`.

Con esos dos ajustes la desigualdad que manda es

```text
K·(eta·n² + n/6 + 1/24) < (eps - 1/n)·n²,
```

que es `descent_threshold_maximal_barrier`, y cuya condición suficiente limpia es
`K/6 + 1 + K/24 < (eps - K·eta)·n`.  Para `K = 16`, `eps = 10^{-12}`, `eta = 10^{-16}` eso da
`n > 3.68·10^12`; el árbol usa `4·10^12`.  `near_threshold_binding` demuestra que la desigualdad
**falla** para `n ≤ 3.6·10^12`, de modo que el umbral actual está a menos de un 10 % del mejor
posible con este `eps` y este `K`.  Bajarlo más exige subir `eps` —lo impide la cuenta de
edición del punto 1, que permite a lo sumo `eps ≈ 1.38·10^{-12}`— o bajar `K`.

## Dónde está la holgura

`B = 65536` no lo pide la cordalidad. El único sitio donde la cordalidad interviene
—`PaperIV.RootVocab.hubs_isClique`— compara un vecindario común de tamaño `≈ 1.48·|P|` contra un
clique exterior de tamaño `≤ |P|/128`: ahí sobraría `B ≈ 8`. Los `65536` los piden los campos
numéricos de `PaperIV.NearH1RootRegularization.RegularizedRoot` —`99·|ref| ≤ 100·|root|`,
`400·e' < |ref|²`, `2000·(mi' + 2e') ≤ 11·|ref|²`—, y contra **esos** el margen es de un factor
doce, no de cuatro mil. Bajar `B` a `8192` es por tanto un reajuste, no un teorema nuevo, y
dividiría el umbral por sesenta y cuatro.

## Advertencia sobre para qué sirve esto

El umbral global es `N = max{N_lejano, N_cercano}` y `N_lejano` es de tipo torre mientras la rama
lejana pase por la regularidad. **Bajar `N_cercano` no mueve `N`.** Este módulo dice qué costaría
hacerlo, no que convenga hacerlo ahora.
-/

namespace PaperIV.NearThresholdSensitivity

/-! ## 1. El presupuesto físico acota `eps` por debajo de `1/B²` -/

/-- **Necesidad.** Si el defecto físico cabe en el presupuesto `B` y los pares faltantes están
saturados, entonces `eps` no puede pasar de `2/B²`.

Se usa sólo que la raíz `a` no excede el orden y que el presupuesto es el del árbol,
`B · defecto ≤ a²`. La hipótesis `hsat` dice que `u` es tan grande como la cota de codimensión
permite, salvo un factor dos; es el caso agudo, el que decide la constante. -/
theorem eps_le_of_physical_budget {n u a eps B : ℚ}
    (hB : 0 < B) (hBn : B ≤ n) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (ha : a ≤ n)
    (hsat : eps * n ^ 2 ≤ u * (u + 1))
    (hfit : B * (eps * n ^ 2 + u * n) ≤ a ^ 2) :
    eps * B ^ 2 ≤ 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hBn
  rcases le_or_gt eps 0 with hneg | hpos
  · nlinarith [sq_nonneg B]
  · have hepsn : 0 < eps * n ^ 2 := by positivity
    have hasq : a ^ 2 ≤ n ^ 2 := by nlinarith
    have hun : B * (u * n) ≤ n ^ 2 := by nlinarith
    have huB : u * B ≤ n := by nlinarith
    have huB0 : (0 : ℚ) ≤ u * B := mul_nonneg hu hB.le
    have hsq : (u * B) ^ 2 ≤ n ^ 2 := by
      nlinarith [mul_self_le_mul_self huB0 huB]
    have hlin : (u * B) * B ≤ n * B := by nlinarith
    have hnB : n * B ≤ n ^ 2 := by nlinarith
    nlinarith

/-! ## 2. La contracción del descenso acota `n` por debajo de `1/eps` -/

/-- **La contracción.** Con `eta` despreciable frente a `eps`, la desigualdad del descenso vale en
cuanto `eps·n ≥ 160`, y no antes: el sumando `n/6` del presupuesto de defecto es lineal y el
entorno es cuadrático, así que el cruce ocurre en `n ≍ 1/eps`. -/
theorem descent_threshold {n eps eta : ℚ}
    (hetaSmall : 160 * eta ≤ eps)
    (hn1 : 1 ≤ n) (hn : 160 ≤ eps * n) :
    20 * (eta * n ^ 2 + n / 6 + 1 / 24) < eps / 4 * n ^ 2 := by
  have hn0 : (0 : ℚ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hquad : 20 * n ≤ eps / 8 * n ^ 2 := by nlinarith
  have hetaq : 20 * (eta * n ^ 2) ≤ eps / 8 * n ^ 2 := by nlinarith
  nlinarith

/-! ## 3. Suficiencia: el umbral cuadrático en el presupuesto -/

/-- **Suficiencia.** Tomando el mayor `eps` compatible con el presupuesto,
`eps = alpha⁴/(8B²)`, la contracción del descenso vale a partir de
`n ≥ 1280·B²/alpha⁴`. -/
theorem near_threshold_of_budget {B alpha eta n : ℚ}
    (hB : 1 ≤ B) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hetaSmall : 1280 * B ^ 2 * eta ≤ alpha ^ 4)
    (hn : 1280 * B ^ 2 ≤ alpha ^ 4 * n) :
    20 * (eta * n ^ 2 + n / 6 + 1 / 24) <
      (alpha ^ 4 / (8 * B ^ 2)) / 4 * n ^ 2 := by
  have hB0 : (0 : ℚ) < B := lt_of_lt_of_le zero_lt_one hB
  have hB2 : (0 : ℚ) < B ^ 2 := by positivity
  have ha4 : (0 : ℚ) < alpha ^ 4 := by positivity
  have ha2le : alpha ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg halpha.le (sub_nonneg.2 halpha1)]
  have ha4le : alpha ^ 4 ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg alpha) (sub_nonneg.2 ha2le)]
  set eps : ℚ := alpha ^ 4 / (8 * B ^ 2) with heps
  have heps0 : 0 < eps := by rw [heps]; positivity
  have hmul : eps * (8 * B ^ 2) = alpha ^ 4 := by
    rw [heps]; field_simp
  have hn1 : (1 : ℚ) ≤ n := by nlinarith
  have hepsn : 160 ≤ eps * n := by nlinarith
  have hetaS : 160 * eta ≤ eps := by nlinarith
  exact descent_threshold hetaS hn1 hepsn

/-! ## 4. Y con ese `eps` la cuenta física sí cabe -/

/-- **Compatibilidad.** Con `eps ≤ alpha⁴/(8B²)` el defecto físico —incluido el término
`u·n` que produce la codimensión cordal— cabe en el presupuesto `B·mA ≤ a²`.

Junto con el resultado anterior, esto cierra el círculo: `eps` de ese tamaño es a la vez
suficiente para la cuenta física y el mayor que la hace caber, y el umbral que impone al descenso
es `Θ(B²/alpha⁴)`. -/
theorem edit_mass_of_budget {n u a mA alpha B eps : ℚ}
    (hB : 1 ≤ B) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hn : 0 ≤ n) (hu : 0 ≤ u) (heps0 : 0 ≤ eps)
    (hfit : 8 * eps * B ^ 2 ≤ alpha ^ 4)
    (hmissing : u * (u + 1) / 2 ≤ eps * n ^ 2)
    (ha : alpha * n ≤ a)
    (hedit : mA ≤ eps * n ^ 2 + u * n) :
    B * mA ≤ a ^ 2 := by
  have hB0 : (0 : ℚ) < B := lt_of_lt_of_le zero_lt_one hB
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have husq : u ^ 2 ≤ 2 * (eps * n ^ 2) := by nlinarith
  have hkey : (u * B) ^ 2 ≤ (alpha ^ 2 * n / 2) ^ 2 := by nlinarith
  have hrhs : (0 : ℚ) ≤ alpha ^ 2 * n / 2 := by positivity
  have huB : u * B ≤ alpha ^ 2 * n / 2 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon, hrhs, hkey]
  have hun : B * (u * n) ≤ alpha ^ 2 * n ^ 2 / 2 := by nlinarith
  have hBB : eps * B ≤ eps * B ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg heps0 hB0.le) (sub_nonneg.2 hB)]
  have ha42 : alpha ^ 4 ≤ alpha ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg alpha) (sub_nonneg.2 halpha1))
      (by linarith : (0 : ℚ) ≤ 1 + alpha)]
  have h8 : eps * B ≤ alpha ^ 2 / 8 := by nlinarith
  have hn2 : (0 : ℚ) ≤ n ^ 2 := sq_nonneg n
  have hepsB : B * (eps * n ^ 2) ≤ alpha ^ 2 * n ^ 2 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right h8 hn2]
  have han : (0 : ℚ) ≤ alpha * n := mul_nonneg halpha.le hn
  have hasq : alpha ^ 2 * n ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_self_le_mul_self han ha]
  nlinarith

/-! ## 5. La desigualdad que fija el umbral actual

Las dos secciones anteriores explican la dependencia en `B` y `alpha`.  Las dos siguientes
aíslan la desigualdad que, con `eps` ya fijado, decide el umbral: el descenso con la barrera
**máxima** admisible `eps - 1/n` y con la constante de presupuesto `K` del ledger. -/

/-- **Contracción con la barrera máxima.**  El descenso sólo exige
`contracted ≤ barrier ≤ outer - 1/n`; con `barrier = contracted = eps - 1/n` la condición de
contracción se reduce a una desigualdad lineal en `n`.

Es la desigualdad que fija el umbral de la rama cercana: para `K = 16`, `eps = 10^{-12}` y
`eta = 10^{-16}` se satisface desde `n > 3.68·10^12`. -/
theorem descent_threshold_maximal_barrier {n eps eta K : ℚ}
    (hK : 0 ≤ K) (hn1 : 1 ≤ n)
    (hn : K / 6 + 1 + K / 24 < (eps - K * eta) * n) :
    K * (eta * n ^ 2 + n / 6 + 1 / 24) < (eps - 1 / n) * n ^ 2 := by
  have hn0 : (0 : ℚ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hexp : (eps - 1 / n) * n ^ 2 = eps * n ^ 2 - n := by field_simp
  rw [hexp]
  have hmul := mul_lt_mul_of_pos_right hn hn0
  nlinarith [hmul, hK, hn1]

/-- **El umbral actual es casi óptimo.**  Con los valores del árbol —`K = 16`,
`eps = 10^{-12}`, `eta = 10^{-16}`— la contracción con barrera máxima **falla** para todo
`n ≤ 3.6·10^12`.  Como el árbol usa `4·10^12`, el margen que queda es inferior al 12 %: lo que
hay que atacar para bajar más no es el umbral sino `eps` o `K`. -/
theorem near_threshold_binding {n : ℚ} (hn0 : 0 < n) (hle : n ≤ 36 * 10 ^ 11) :
    ¬ (16 * ((1 / 10 ^ 16 : ℚ) * n ^ 2 + n / 6 + 1 / 24) <
        ((1 / 10 ^ 12 : ℚ) - 1 / n) * n ^ 2) := by
  have hexp : ((1 / 10 ^ 12 : ℚ) - 1 / n) * n ^ 2 = (1 / 10 ^ 12 : ℚ) * n ^ 2 - n := by
    field_simp
  rw [hexp]
  push_neg
  nlinarith

end PaperIV.NearThresholdSensitivity
