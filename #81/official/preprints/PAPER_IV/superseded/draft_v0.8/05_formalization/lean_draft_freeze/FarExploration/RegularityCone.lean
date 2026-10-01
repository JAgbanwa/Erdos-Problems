import FarExploration.CodegreeCleanup
import PaperIV.RC01Final
import Lean.Elab.Command

/-!
# ¿Dónde vive realmente la regularidad? — auditoría por cono de constantes

Los imports mienten.  Para localizar el uso de la regularidad no basta mirar qué módulos
importa `PaperIV.RC01Final`: hay que recorrer el cono transitivo de constantes del término de
demostración y ver cuáles pertenecen al aparato de regularidad.

Este fichero hace exactamente eso, con la misma maquinaria que `PaperIV.ConeAudit`.  Cuenta
como «constante de regularidad» toda constante cuyo nombre contiene el literal `Regularity`
(`SzemerediRegularity.*` de Mathlib, `PaperIV.RegularityFormat.*`, `EqualRegularity`, …).

El veredicto que imprime es el contenido de la pregunta 1:

* la **puerta física** (`exists_packing_loss_le_of_slackMarkedQuota`), el **nibble de rango
  acotado** (`Nibble.fracNibble_leUniform`, que por dentro es Beck–Fiala) y la **rama de pocos
  triángulos** no usan ni una sola constante de regularidad;
* tampoco la usa `uniformRoundingTarget_of_codegreeCleanup`, es decir: el contrato de redondeo
  **entero**, una vez concedida la limpieza de codegree;
* `PaperIV.RC01Final.rc01_uniformRoundingTarget` sí las usa, y son precisamente las que
  producen esa limpieza.
-/

open Lean Elab Command

namespace FarExploration.RegularityCone

private partial def cone (env : Environment) : List Name → NameSet → NameSet
  | [], acc => acc
  | n :: rest, acc =>
      if acc.contains n then cone env rest acc
      else
        let acc := acc.insert n
        match env.find? n with
        | none => cone env rest acc
        | some info =>
            let fromType := info.type.getUsedConstants.toList
            let fromValue := match info.value? with
              | some v => v.getUsedConstants.toList
              | none => []
            cone env (fromType ++ fromValue ++ rest) acc

/-- Una constante pertenece al aparato de regularidad si su nombre contiene `Regularity`. -/
private def isRegularity (n : Name) : Bool :=
  (n.toString.splitOn "Regularity").length > 1

/-- Enunciados que **no** deben usar regularidad. -/
private def clean : List Name :=
  [ `Nibble.fracNibble_leUniform,
    `PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuota,
    `PaperIV.RC01TriangleSchedule.lowTriangle_branch_free_scheduled,
    `FarExploration.CodegreeCleanup.uniformRoundingTarget_of_codegreeCleanup ]

/-- Enunciados que **sí** la usan, y por eso arrastran la torre. -/
private def dirty : List Name :=
  [ `PaperIV.RC01Final.rc01_uniformRoundingTarget ]

elab "regularityCone" : command => do
  let env ← getEnv
  let mut bad := 0
  for t in clean do
    match env.find? t with
    | none => do
        bad := bad + 1
        logError m!"ausente del entorno: {t}"
    | some _ =>
        let used := (cone env [t] {}).toList
        let regs := used.filter isRegularity
        if regs.isEmpty then
          logInfo m!"LIBRE  {t}\n      total {used.length} | regularidad 0"
        else
          bad := bad + 1
          logError m!"{t} usa regularidad: {regs.take 10}"
  for t in dirty do
    match env.find? t with
    | none => do
        bad := bad + 1
        logError m!"ausente del entorno: {t}"
    | some _ =>
        let used := (cone env [t] {}).toList
        let regs := used.filter isRegularity
        if regs.isEmpty then
          bad := bad + 1
          logError m!"se esperaba regularidad en {t} y no aparece"
        else
          logInfo m!"USA    {t}\n      total {used.length} | regularidad {regs.length}"
  if bad == 0 then
    logInfo m!"VEREDICTO: la regularidad no aparece en la puerta física, ni en el nibble, ni en \
      la rama de pocos triángulos, ni en el contrato de redondeo concedida la limpieza de \
      codegree; sólo aparece en la ruta que fabrica esa limpieza."
  else
    logError m!"VEREDICTO: {bad} discrepancias."

regularityCone

end FarExploration.RegularityCone
