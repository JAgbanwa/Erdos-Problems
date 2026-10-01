# Paper IV v1.22 — respuesta a la revalidación v1.21-r1

Fecha: 1 de octubre de 2026. Estado: `EDITORIAL_DRAFT_WITH_OPEN_GATES`.
Esta respuesta es del autor/editor; no es un nuevo veredicto del auditor.

## Alcance y autoridades

Base semántica: los dos Markdown de `../v1.21_editorial_candidate/`, identificados en `PROTECTED_BASELINE.json`. Autoridad de composición: sus plantillas TeX de la serie y figuras, copiadas sin adoptar otra plantilla. Los dos Markdown v1.22 son la fuente de sus TeX/PDF. Se mantiene el título, el resumen, todos los enunciados, hipótesis, constantes finales, etiquetas y bloques Lean. No se cambian fuentes ni configuraciones del corte `piv-v12-fb459343d234`.

La auditoría `run_v1.21_r1` concluyó INCONCLUSIVE global, con E4 PASS por reutilización verificada. Se preserva completa; no se sobreescribe su informe ni se sustituyen sus hashes. Su ZIP final tiene SHA-256 `11659a97b0a4f2bffadb6968159cc5b66562b4470053939a45c1e8a42db7a638`.

## Respuesta por hallazgo

| Hallazgo | Cambio o tratamiento | Revisión solicitada |
|---|---|---|
| A2-4 / X-05 | C.3 define `initialBound`, la recurrencia `stepBound`, el número de iteraciones y `bound`; desarrolla el límite inferior tras dos pasos, la absorción por B⁶ y la comparación superior con T(h+7). A.2 remite ahora a C.3, no a una recurrencia inexistente en §6.3. | Rederivar el texto y contrastar E18/E19; no heredar PASS de este informe. |
| X-12 | `E34.lemma3` y `E34.transfer` reciben formato explícito de identificador en ambos Markdown. | Identidad textual y partición visible de líneas en PDF. |
| X-15 | Se traducen los residuos de matching/packing en prosa española, sin tocar identificadores ni títulos citados. En la figura del flujo de estabilidad, «baseline» pasa a «valor base». | Paridad semántica y visual ES/EN. |
| NEW-01 | Se retira el formato de código de Regularization en el encabezado y la fila descriptiva ingleses, y de Nibble en el encabezado español. Se restaura el formato del namespace Model donde corresponde. | Distinguir palabras descriptivas de nombres formales. |
| NEW-02 | El título de [6] vuelve a «Integer and fractional packings in dense graphs» en español. | Cotejar el título con la entrada inglesa y la evidencia bibliográfica ya auditada. |
| R-02 | C.2 aclara que la suma considera todos los perfiles activos que contienen las dos clases del par, no un par elegido por perfil. | Contrastar `PatternTransfer.servingT`. |
| Ortografía E7 | PreferenceLabs pasa a Preference Labs, sin cambiar la atribución. | Control editorial puntual. |
| R-01 | Se mantiene la cita de las estimaciones de segundo momento; no se presenta como una nueva derivación desarrollada aquí. El auditor la clasificó como observación, no como gate abierto. | Conservar explícitamente ese alcance. |
| E8-01 | El barrido del autor anterior cubría 844 registros; el auditor lo amplió a 1266, con cero alertas. Se reutiliza esa evidencia con atribución, sin reescribir el informe anterior. | Cotejar el registro E8 y su alcance. |
| E8-02 / X-28 | No se aplica el parche propuesto a los runners congelados. Se conserva la mitigación por detector externo y revisión transitiva de axiomas; tampoco se atribuye al parche una modificación ya ejecutada. | Mantener la limitación declarada. |
| E8-03 | La carpeta nueva no copia los ZIP provisionales anteriores; sólo se sella un paquete r1 al finalizar. | Verificar el inventario del nuevo objetivo. |

Las demás observaciones históricas e incidencias del proceso se conservan, sin eliminarlas para obtener un veredicto favorable.

## Correspondencia del nuevo desarrollo de C.3

| Tramo de exposición | Fuente existente |
|---|---|
| I, H, t y B | Mathlib `Combinatorics/SimpleGraph/Regularity/Bound.lean`: `initialBound`, `stepBound`, `bound` |
| I = k₀, H = h, B = t_h 16^(t_h) | `E18/Numeric.lean`: `initialBound_eq`, `floor_iter_eq`, `BE_eta0` |
| Cinco términos y coeficientes exactos | `E18/Numeric.lean`: `NfarE_eta0_le_of_B`, `NfarE_eta0_le` |
| Dos iteraciones dominan G₁, G₂, G₃ | `E19/Tower.lean`: `two_pow_two_pow_le_iterate`; `E19/Main.lean`: `G1_le_Tnum`, `G2_le_Tnum`, `G3_le_Tnum` |
| Absorción por B⁶ | `E19/Main.lean`: `absorb_abstract`, `NfarE_eta0_le_clean` |
| 4t_j ≤ T(j+5) | `E19/Tower.lean`: `four_mul_iterate_le_tower2`; `E19/Main.lean`: `four_mul_Tnum_le` |
| B⁶ ≤ T(h+7) | `E19/Main.lean`: `B6_le_two_pow_two_pow`, `NfarE_eta0_le_tower` |

No se afirma que dos iteraciones basten para producir una partición regular: sólo dominan las constantes auxiliares, mientras la recurrencia se itera h veces.

## Controles del editor

`check_increment.py` comprueba la conservación de todos los displays existentes, etiquetas, párrafos de enunciados y bloques Lean; compara las fórmulas nuevas entre idiomas y realiza 18 comprobaciones exactas o controles de regresión y negativos. Comprueba también las 615 identidades de fuentes/configuración/documentación. No ejecuta Lean. Los controles finitos no sustituyen las inducciones que justifica el texto.

Los cambios se documentan en `CHANGES_en.diff` y `CHANGES_es.diff`. La revisión de estilo se limita a estos pasajes: se usan definiciones, cuentas y conectores explícitos, sin nuevas afirmaciones de novedad, prioridad o superioridad. El formato conserva la plantilla de la serie. Los informes de artefactos y revisión visual registran la comprobación posterior a la última compilación.

## Independencia: precisión necesaria

El auditor declara que `run_v1.21_r1` fue una continuación en la **misma sesión** de `run_v1.2_r1`, no una sesión nueva. Debe mantenerse esa declaración. La sesión inicial pudo ser separada de la investigación y sujetarse a lecturas restringidas, pero la revalidación conoce el informe anterior; no es ciega ni una revisión entre familias distintas. No se presenta la restricción de lectura como aislamiento técnico del disco.

## Decisión siguiente

Solicitar una revisión acotada de E0, E2/C.3 y E6, con controles de regresión sobre E1/E3/E7 y confirmación documental de E4. El auditor debe emitir su propio resultado y conservar INCONCLUSIVE si la explicación sigue siendo insuficiente. No se autoriza otro build ni publicación.
