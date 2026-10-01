# Paper IV v1.21 — respuesta del autor a la auditoría v1.2-r1

Fecha: 30 de septiembre de 2026. Estado: **correcciones contrastadas con el informe final; revalidación pendiente**. La ejecución externa v1.2-r1 terminó con INCONCLUSIVE global por E2 y PASS formal E4.

Esta respuesta no modifica los hallazgos ni los veredictos del auditor. Se refiere a la candidata separada `v1.21_editorial_candidate`. El objeto auditado v1.2, sus paquetes, los 607 módulos Lean y la ejecución externa completada permanecen intactos. No se inició otro build Lean, no se instaló Mathlib, no se delegaron tareas a otros agentes y no se publicó nada.

## 1. Disposición completa

«Corregido» en esta tabla significa que el autor aplicó el cambio y aporta evidencia para revisarlo, no que el auditor haya cerrado el hallazgo.

| Hallazgo | Corrección o decisión | Lugar / comprobación |
|---|---|---|
| X-01 | Desarrollada la limpieza bilateral por desviación, la cota superior que controla la carga de cada arista y la cuenta de retención. | C.1–C.2; contraste con `RC01DeviationCleanup`, `RC01CleanFiber`, `RC01RootwiseRetention`. Requiere rederivación E2. |
| X-02 | Desarrolladas las cuentas de vértices retirados, masa de ausencias, ventanas de tamaño y reservas de la normalización. | E.1 y enlace E.4; `IndepAllBounds`, `IndepAllParams`. |
| X-03 | Añadida la eliminación conjunta de excepciones, incluidos los recursos omitidos y el error final n/9. | E.1, antes del análisis de tres casos; `IndepAllPeel`, `IndepAllObstr`. |
| X-04 | «Margen» para el déficit del grafo, incluida la introducción; «holgura del selector» sólo para su capacidad auxiliar. | Edición ES, figuras y §1.1. |
| X-05 | Definidos todos los parámetros del calendario y desarrollada la cadena de desigualdades hasta el selector y los tres enteros finales. | C.3; E18/E19; controles racionales complementarios. La comparación final de la recurrencia de torre sigue siendo simbólica, no una expansión del entero. |
| X-06 | Separadas la localización fraccional de [15] y su construcción integral final. | Tabla 4 y §8.1. |
| X-07 | Corregida la dirección de la comparación de hipótesis usando cp ≤ c₄. | §8.1. |
| X-08 | Reconocido que la prueba de (1.5) en [15] ya usa L=4; no se reclama esa diferencia como nueva. | §8.1. |
| X-09 | Añadida [15, Corolario 1.2] a la atribución de la cota irrestricta para todo orden. | Resumen y Teorema A. |
| X-10 | Conservada la firma bibliográfica «Anonymous», con créditos del README fijado de [5]; declarada la relación de Jacobian con ese proyecto. | Referencia [5] y herramientas computacionales. Fuente primaria: README en commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. No se confunden créditos del repositorio y autoría impresa. |
| X-11 | Precisado que la reducción del umbral se compara con versiones históricas propias. | §4. |
| X-12 | Identificadores formales en monoespaciado también en Markdown; saltos explícitos con flecha en PDF. | Tablas, §7, A.1, F.4–F.5; controles visuales. |
| X-13 | Subíndices descriptivos comunes `far`, `cross`, `clean`, `covered` en ambas lenguas; `mis` se define como número de discrepancias. | Lista exacta de renombramientos en `SEMANTIC_CHECKS.json`. No cambia ninguna cantidad ni identificador Lean. |
| X-14 | Símbolos Unicode originales, incluidos ⦃ y ⦄, y sangría conservada; bloques de código completos mantenidos juntos. | A.1; fuente de símbolos ya instalada, no una nueva dependencia Lean. |
| X-15 | Traducidos los anglicismos señalados en la prosa ES y corregida la concordancia resultante. | «valor base», «compilación», «empaquetamientos», «objetivos», «registros», «brecha». Código, nombres propios y títulos bibliográficos no se traducen. |
| X-16 | Sustituida la referencia inexistente a §3.2 por Lema 3.2 y C.1–C.2. | A.2. |
| X-17 | Sin cambio: la construcción explícita está en la prueba; el tipo Lean existencial no es un defecto. | Se conserva la distinción entre enunciado y testigo construido. |
| X-18 | Sin cambio: τ ≥ 0 es una especialización lícita del teorema Lean para τ real. | Corolario 6.1a. |
| X-19 | Se retienen las declaraciones de biblioteca sin módulos: quitarlas cambiaría innecesariamente la identidad ya compilada. No se presentan como dependencias matemáticas. | Nota de configuración en `EVIDENCE_AND_ANNEX_CORRIGENDUM.md`. |
| X-20 | Recontados los 19 registros: 314 salidas estándar y 147 listas de elaboradores, 461 en total. | `AXIOM_COUNT_RECONCILIATION.json`. Errata nueva, sin reescribir el informe interno. |
| X-21 | El auditor resolvió la duda: recompiló 607 módulos y obtuvo 607 objetos byte-idénticos a los registros del autor. | E4_RECORD y olean_vs_author; no se reescribe el antecedente. |
| X-22 | Conservado el desacuerdo sobre suficiencia expositiva; ampliaciones propuestas en C.2, C.3 y E.1. | La nueva revisión debe dictaminar cada fila de A.2, sin heredar el PASS interno. |
| X-23 | Añadido el paso que da 113/64. | §5.1 y control racional. |
| X-24 | No adoptadas optimizaciones opcionales de constantes o hipótesis. | Se conservan los enunciados aprobados y el mismo Lean. |
| X-25 | Corregida por suplemento la referencia antigua del README del anexo: §8.2 histórico corresponde a G.1 actual. | `EVIDENCE_AND_ANNEX_CORRIGENDUM.md`; ZIP del anexo intacto. |
| X-26 | Se distingue ejecución separada en sesión nueva de diversidad de modelos. Según la declaración del auditor, no consultó los árboles excluidos; no se afirma aislamiento técnico del disco. | El mismo modelo no anula la separación operativa. Este nuevo ciclo conoce el informe anterior; no es ciego ni entre familias distintas. |
| X-27 | Explicitada la dependencia histórica de Alon–Shapira en las dos interfaces de clasificación irrestricta E32, sin alterar el teorema ni la cadena seleccionada para el Teorema C explícito. | §7, E.2, Tabla 9, [23]; AuditorASProbe.log. No se renombra ni mueve código. |
| X-28 | Detector complementario corregido y probado contra el negativo capturado y variantes sintéticas; reescaneo de registros existentes. Parche mínimo propuesto fuera del corte. | sorry_log_recheck.py y SORRY_RECHECK.json. No se aplica el parche a los runners congelados, ni se ejecuta Lean. |
| X-29 | Se incorpora el resultado final de reproducción byte-idéntica, junto con los límites de caché compartida y ausencia de replay independiente. | 607 módulos principales, 19 targets y 50 módulos del anexo PASS; el nuevo texto no hereda PASS editorial. |
| AUD-P1, AUD-C1, AUD-C2 | Incidencias del auditor, no errores del manuscrito; se conservan sus registros y aclaraciones. | No se alteran archivos de la ejecución externa. |

También se añadió la cita de la Figura 3 en el cuerpo, se corrigió «Existen γ y un umbral», se regeneraron figuras con fuentes TrueType (sin Type3), se mantuvo unido `import PaperIV` y se sincronizó el estado histórico del build con ambas auditorías completadas, distinguiendo el PASS formal del INCONCLUSIVE expositivo.

## 2. Protección matemática y comprobaciones

La skill `mathematical-paper-editor` guio la separación entre sustancia protegida y presentación. No se ha cambiado un teorema, hipótesis, constante, etiqueta de ecuación o bloque Lean. Las 227 fórmulas desplegadas previas se conservan **salvo cinco renombramientos descriptivos declarados**, iguales en ambas lenguas. Hay tres nuevos bloques explicativos. Los encabezados se comparan permitiendo sólo monoespaciado, concordancia de «Existe/Existen» y traducción del título «gap mixto nulo».

`editorial_checks.py check` comprueba ese contrato y trece comparaciones racionales. `artifact_checks.py` comprueba paridad de las fórmulas añadidas, símbolos de código, etiquetas y defectos detectables de maquetación. La única normalización lingüística de la paridad matemática es «que sirve / serving» dentro de un subíndice textual. Ninguno de estos scripts prueba por sí solo los lemas estructurales ni reemplaza la revisión matemática de la nueva prosa.

Los dos PDFs se producen secuencialmente con las herramientas ya instaladas y recursos TeX de caché. El primer intento falló al resolver una ruta absoluta de fuente; se conserva su diagnóstico en `review_history/`. Se utilizó después una copia local de la fuente instalada. `typeset_runtime/` es un recurso local de compilación y **no se distribuye**. No se descarga ni instala una fuente o un motor.

La primera comprobación de paridad detectó la diferencia lingüística «que sirve / serving», no una diferencia matemática; el resultado previo está conservado y la normalización es explícita. Las comprobaciones y la revisión visual finales están en `ARTIFACT_CHECKS.json` y `VISUAL_REVIEW_v1.21.md`.

## 3. Qué queda antes de emitir un veredicto nuevo

1. Verificar el paquete y la vinculación con el informe final y su evidencia; revisar los controles autorales, no aceptarlos como veredictos.
2. Ejecutar el nuevo ciclo identificado en `REVIEW_HANDOFF_v1.21.md`: E0 nuevo, E2 sobre la exposición añadida, E6 y E7 nuevos, y E1/E3 sobre la diferencia editorial; resolver X-27 y X-28 expresamente.
3. Reutilizar E4 sólo tras comprobar identidad y cobertura. No se autoriza nuevo build. Si falta evidencia, detenerse y explicarlo, no recompilar por defecto.

Una corrección autoral no es un PASS. No se autorizan publicación, depósito, push ni una nueva revisión automática desde este documento.
