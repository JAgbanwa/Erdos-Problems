import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# La ruta del separador no existe en un estado completo

La acción *separador* consiste en borrar una clique que **desconecta** el
estado y recurrir sobre las componentes resultantes.  En un grafo completo esa
acción no está disponible: al borrar cualquier conjunto de vértices, lo que
queda vuelve a ser un grafo completo, luego conexo.

Esto no es una dificultad de contabilidad, sino la ausencia literal del
certificado: no hay ningún separador que produzca dos o más componentes.
-/

namespace ThreeRegime

open SimpleGraph

variable {V : Type*}

/-- Todo subgrafo inducido de un grafo completo es completo. -/
theorem induce_top_eq_top (s : Set V) :
    (⊤ : SimpleGraph V).induce s = ⊤ := by
  ext u v
  simp [Subtype.ext_iff]

/-- **Un estado completo no tiene separador.**  Después de borrar cualquier
conjunto `S` de vértices (en particular cualquier clique), el grafo inducido
sobre el resto sigue siendo conexo mientras quede algún vértice. -/
theorem complete_state_has_no_separator (S : Set V)
    (hne : ((Set.univ : Set V) \ S).Nonempty) :
    ((⊤ : SimpleGraph V).induce ((Set.univ : Set V) \ S)).Connected := by
  have : Nonempty ↑((Set.univ : Set V) \ S) := Set.Nonempty.to_subtype hne
  rw [induce_top_eq_top]
  exact connected_top

/-- Forma cuantificada sobre pares: dos vértices supervivientes distintos
siguen siendo adyacentes, luego nunca caen en componentes distintas. -/
theorem surviving_adj (S : Set V) {u v : ↑((Set.univ : Set V) \ S)}
    (huv : u ≠ v) :
    ((⊤ : SimpleGraph V).induce ((Set.univ : Set V) \ S)).Adj u v := by
  rw [induce_top_eq_top]
  exact huv

end ThreeRegime
