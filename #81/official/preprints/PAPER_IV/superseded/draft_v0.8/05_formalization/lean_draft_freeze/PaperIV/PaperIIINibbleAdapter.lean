import PaperIV.NibblePort
import Nibble.FracNibbleRepaired

/-!
# Adapter verificable al nibble casi-perfecto de Paper III

`PaperIV.NibblePort.NearPerfectNibbleAt` reproduce el enunciado de
`Nibble.fracNibbleWeighted_nearPerfect` para que Paper IV pueda describir su
interfaz sin importar el árbol completo de Paper III. Este módulo demuestra que
la interfaz no es una hipótesis nueva: es una traducción literal del teorema
formalizado en el freeze de Paper III.

El módulo queda fuera del agregado `PaperIV` mientras se decide la frontera
editorial de dependencias. Su única dependencia no-Mathlib es el proyecto Lean
auditado de Paper III, fijado localmente en `lakefile.toml`.
-/

namespace PaperIV.PaperIIINibbleAdapter

open PaperIV.NibblePort

/-- El nibble casi-perfecto de Paper III satisface literalmente la interfaz
local de Paper IV. -/
theorem nearPerfectNibbleAt : NearPerfectNibbleAt := by
  intro r hr β hβ
  obtain ⟨γ, hγ, η, hη, hmain⟩ :=
    Nibble.fracNibbleWeighted_nearPerfect r hr β hβ
  refine ⟨γ, hγ, η, hη, ?_⟩
  intro W _ _ H w Exc huniform hnonneg hupper hlower hexception hcodegree
  have huniform' : _root_.Hypergraph.IsUniform H r := huniform
  obtain ⟨M, hM, hMcard, hMmass⟩ :=
    hmain H w Exc huniform' hnonneg hupper hlower hexception hcodegree
  exact ⟨M, ⟨hM.subset, hM.disjoint⟩, hMcard, hMmass⟩

end PaperIV.PaperIIINibbleAdapter
