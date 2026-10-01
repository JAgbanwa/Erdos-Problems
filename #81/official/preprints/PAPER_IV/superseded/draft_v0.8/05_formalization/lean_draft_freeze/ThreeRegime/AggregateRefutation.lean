import ThreeRegime.Selector
import ThreeRegime.CompleteStateCentre
import ThreeRegime.CompleteStateExtreme
import ThreeRegime.CompleteStateSeparator

/-!
# Por qué la desigualdad agregada no es el objetivo correcto

Este módulo reúne los tres hechos geométricos sobre un estado completo y los
confronta con la desigualdad agregada propuesta

`C_centro(G) + C_extremo(G) + C_separador(G) ≤ 3 · M(|G|)`.

En un estado completo `K_n` con `n ≥ 4`:

* la ruta del separador **no existe** (borrar cualquier clique deja un grafo
  completo, luego conexo): `complete_state_has_no_separator`;
* la ruta extrema **no se financia**: para toda raíz equilibrada la reserva
  exacta de defecto central es estrictamente menor que las aristas que hay que
  crear: `extreme_route_fails_on_complete`;
* para `n ≤ 4` la ruta del centro sí cierra: `centre_route_closes_on_small_complete`.

Por tanto, con cualquier tarificación honesta de una ruta indisponible o
fallida (coste por encima del presupuesto, o `+∞`), la agregada es **falsa**
en `K₄`, mientras que la disyunción es **verdadera**.  La agregada es una
condición suficiente estrictamente más fuerte que la que consume el principio
de Bellman, y en la familia completa ya se rompe.

Conclusión operativa: el objetivo de investigación debe seguir siendo la
disyunción (equivalentemente `min ≤ M`), no la suma; y en los estados
completos la disyunción colapsa a un único certificado, el del centro.
-/

namespace ThreeRegime
namespace AggregateRefutation

open Finset PaperIV PaperIV.FarRounding PaperIV.SplitUniformIncidence SimpleGraph

/-- **Cuadro de `K₄`.**  De las tres rutas, sólo el centro cierra: el
separador no existe y la reserva extrema no paga el arreglo. -/
theorem K4_picture :
    (∃ Q : CliquePartition (⊤ : SimpleGraph (Fin 4)),
        Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize 4) ∧
      (∀ Core : Finset (Fin 4), 1 ≤ Core.card →
          Core.card ≤ (Finset.univ \ Core).card →
          PaperIV.targetSize (centerDefect 4 Core.card) <
            editDist (⊤ : SimpleGraph (Fin 4))
              (splitGraph Core (Finset.univ \ Core))) ∧
      (∀ S : Set (Fin 4), ((Set.univ : Set (Fin 4)) \ S).Nonempty →
          ((⊤ : SimpleGraph (Fin 4)).induce ((Set.univ : Set (Fin 4)) \ S)).Connected) := by
  have hcard : Fintype.card (Fin 4) = 4 := by simp
  refine ⟨?_, ?_, fun S hS => complete_state_has_no_separator S hS⟩
  · have := centre_route_closes_on_small_complete (V := Fin 4)
      (by rw [hcard]; norm_num) (by rw [hcard])
    rwa [hcard] at this
  · intro Core hk hband
    have := extreme_route_fails_on_complete (V := Fin 4) Core hk hband
      (by rw [hcard])
    rwa [hcard] at this

/-- **La agregada falla allí donde la disyunción cierra.**  Si el centro cabe
en el presupuesto pero alguna de las otras rutas está indisponible (y se
tarifica, honestamente, por encima del presupuesto total), la disyunción es
cierta y la agregada es falsa. -/
theorem aggregate_fails_under_unavailability_pricing
    (centreCost extremeCost separatorCost budget : ℕ)
    (hcentre : centreCost ≤ budget)
    (hunavailable : 3 * budget < separatorCost) :
    (centreCost ≤ budget ∨ extremeCost ≤ budget ∨ separatorCost ≤ budget) ∧
      ¬ (centreCost + extremeCost + separatorCost ≤ 3 * budget) :=
  ⟨Or.inl hcentre, by omega⟩

/-- En un estado donde dos rutas fallan, la disyunción es exactamente el
certificado del centro: no hay reparto posible de holgura entre rutas. -/
theorem disjunction_collapses_to_centre
    (centreCost extremeCost separatorCost budget : ℕ)
    (hE : budget < extremeCost) (hS : budget < separatorCost) :
    (centreCost ≤ budget ∨ extremeCost ≤ budget ∨ separatorCost ≤ budget) ↔
      centreCost ≤ budget := by
  omega

end AggregateRefutation
end ThreeRegime
