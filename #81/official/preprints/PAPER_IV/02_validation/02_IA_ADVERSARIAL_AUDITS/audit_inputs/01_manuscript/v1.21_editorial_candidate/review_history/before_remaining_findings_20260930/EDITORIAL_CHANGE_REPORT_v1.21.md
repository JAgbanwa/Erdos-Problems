# Paper IV v1.21 — candidata editorial separada

Fecha: 30 de septiembre de 2026.

**Veredicto de esta entrega: EDITORIAL_DRAFT_WITH_OPEN_GATES.** Hay dos manuscritos de trabajo en Markdown. No es una nueva liberación, un congelado ni un veredicto de auditoría.

## 1. Objetivo y límites

La v1.21 desarrolla los pasos que la revisión externa de v1.2 consideró insuficientemente explicados y corrige comparaciones y terminología. El trabajo sigue la skill `mathematical-paper-editor`: se conserva la sustancia protegida, se documentan las ampliaciones y no se convierte un resultado formal en una afirmación de suficiencia expositiva.

Los archivos de partida son los manuscritos sellados de `../v1.2_full_rebuild_candidate/`. La auditoría externa sigue examinando esa versión. **No se modificaron esos insumos, las fuentes Lean, la ejecución del auditor ni las dependencias compartidas. No se lanzó otro build, ni agentes, ni una compilación de PDF.**

La notación de versión solicitada, **1.21**, se conserva literalmente. No se interpreta como 1.2.1 ni se cambia el número de versión del proyecto Lean.

## 2. Manuscritos preparados

- [Manuscrito inglés](PAPER_IV_preprint_v1.21_en.md).
- [Manuscrito español](PAPER_IV_preprint_v1.21_es.md).
- [Diferencias EN](CHANGES_en.diff) y [diferencias ES](CHANGES_es.diff).
- [Control de elementos protegidos](SEMANTIC_CHECKS.json).
- [Controles expositivos y aritméticos](EXPOSITORY_CHECKS.json).

Las figuras se conservaron como recursos; no se redibujaron. No hay TeX ni PDF de v1.21 todavía. Es deliberado: primero se revisa el texto y se deja terminar el build externo costoso.

## 3. Cambios y observaciones atendidas

Los identificadores X corresponden a `run_v1.2_r1/30_REPORT/FINDINGS.csv`, consultado durante la ejecución. Su registro permanece intacto. «Incorporado» significa que se escribió una propuesta de solución, **no** que el auditor haya cerrado el hallazgo.

| Hallazgo | Cambio en la candidata | Estado |
|:--|:--|:--|
| X-01: factibilidad por arista | C.2 distingue volumen, referencia por par, desviación bilateral, carga superviviente y capacidad transferida. Desarrolla también el costo de borrar raíces malas y la retención. | Incorporado; requiere revisión matemática del texto. |
| X-02: normalización | E.1 declara las entradas localizadas y deriva poda de la raíz, masa exterior, conjuntos pesado/ligero, clasificación de excepciones, cotas de filas y columnas y elección de la reserva. E.4 consume esas mismas cuentas. | Incorporado; no se presenta la localización como consecuencia del defecto por sí solo. |
| X-03: desigualdad conjunta | E.1 desarrolla la elección de no vecinos, la eliminación por tres tipos de vértice, las incidencias omitidas y el error total que cabe en n/9. | Incorporado; revisión independiente pendiente. |
| X-04: margen/holgura | Se corrigen los tres usos señalados de «holgura» para el margen del grafo en ES. Se conserva «holgura del selector» para el concepto auxiliar. | Incorporado en ES. |
| X-05: constantes del nibble | C.3 da el calendario y las definiciones que conectan sus parámetros con el selector, incluyendo el cambio de rango. | Definiciones incorporadas; la dominación completa de la torre sigue resumida. |
| X-06: mecanismo de [15] | Tabla 4 y §8.1 distinguen la aproximación auxiliar para localizar de la construcción final por contraejemplo mínimo y triángulos. | Incorporado en ambas lenguas. |
| X-07: dirección de la hipótesis | Se cambia «más fuerte» por «más débil» y se escribe la implicación mediante cp ≤ c₄. | Incorporado en ambas lenguas. |
| X-08: elección L=4 | Se reconoce que la prueba de (1.5) en [15] ya hace esa elección. Lo propio se describe mediante el perfil finito retenido y su certificación. | Incorporado en ambas lenguas. |
| X-09: antecedentes de la cota global | Resumen y comentario del Teorema A citan también [15, Corolario 1.2], para la conclusión sobre particiones irrestrictas. | Incorporado; no se atribuye automáticamente a [15] una conclusión enunciada para c₄. |
| X-11: comparación de umbrales | Se aclara que 10³² → 4·10¹² compara versiones de nuestro constructor cercano, no umbrales globales de distintos papers. | Incorporado. |
| X-16: referencia inexistente | Se sustituye «§3.2» por «Lema 3.2 y C.1–C.2» en la tabla de A.2. | Incorporado. |
| X-23: origen de 113/64 | §5.1 explica la cuenta 129/64 − 1/4 y los dos tipos de vértices del nuevo exterior. | Incorporado. |

La comparación bibliográfica se corrigió a partir de las verificaciones literales documentadas por el auditor en `20_EVIDENCE/E7/E7_LEAD_VERIFICATION.md`. Esta edición no constituye una búsqueda bibliográfica nueva ni una auditoría independiente de ese informe.

## 4. Correspondencia de las ampliaciones con Lean

Todas las rutas siguientes son relativas al corte existente `05_formalization/lean_piv-v12-fb459343d234/`.

| Explicación añadida | Fuentes consultadas |
|:--|:--|
| Limpieza bilateral y carga por arista | `PaperIV/RC01DeviationCleanup.lean`, `RC01CleanFiber.lean`, `RC01CleanedSpreadPacking.lean` |
| Referencias, momentos y costo de eliminación | `PaperIV/RC01RootwiseReference.lean`, `RC01RootwiseCleanupBudget.lean`, `RC01RootwiseRetention.lean`, `RC01RootedMomentAdapter.lean` |
| Datos y conjuntos de la normalización | `A4S1/IndepAllSetup.lean`, `IndepAllBounds.lean`, `IndepAllParams.lean` |
| Eliminación conjunta y error n/9 | `A4S1/IndepAllPeel.lean`, `IndepAllObstr.lean` |
| Calendario numérico y selector | `E18/NibbleSchedule.lean`, `NibbleOracle.lean`, `NibbleChain.lean` |

Los nombres de archivos son una guía para contrastar la exposición, no sustitutos de las cuentas añadidas. No se ha agregado ninguna hipótesis al teorema público, debilitado su conclusión ni cambiado sus constantes. Los cálculos nuevos en el manuscrito explicitan pasos de la cadena existente; no se presentan como nuevos teoremas.

## 5. Controles ejecutados

`editorial_checks.py check` finalizó con código cero. El script y sus resultados quedan junto a los manuscritos y no llaman a Lean, a un solver ni a la red.

- Los SHA-256 de los Markdown de v1.2 siguen siendo EN `a501d53b527da22f20112db2b05917fb61f46dd8e080faf14b69349b240cc152` y ES `2b6f73bf09ef905ea2c92206ee254b4ae46e64f1a51533cb4d8bcdc4e68c7be9`.
- Se conservan, en orden y literalmente, las **227 fórmulas desplegadas preexistentes** de cada lengua. Se añaden tres: dos bloques de definiciones del calendario y una cuenta de incidencias.
- Se conservan las etiquetas de ecuaciones, los encabezados de enunciados y los bloques de código. Las tres fórmulas desplegadas añadidas coinciden en ES y EN.
- Ocho comparaciones de coeficientes se comprobaron con racionales exactos: error conjunto, masa de ausencias, dos presupuestos de limpieza, dos cuentas de grado, ventana del núcleo y umbral de ausencias ligeras.

**Límite:** estos controles mecánicos no certifican por sí solos la semántica de toda la prosa, la exactitud de las citas o la suficiencia de una demostración. Los controles racionales no son censos de grafos ni demuestran los lemas estructurales. La lectura editorial de los párrafos paralelos es preliminar; todavía falta la revisión bilingüe posterior a la maquetación.

## 6. Consultas y trabajo aún abierto

| Consulta | Acción siguiente |
|:--|:--|
| CQ-01 — suficiencia de C.2 y E.1 | Pedir al revisor que derive las conclusiones usando las nuevas cuentas y contraste las entradas con Lean; no marcar X-01–X-03 como cerrados unilateralmente. |
| CQ-02 — tabla numérica C.1 | Decidir si desarrollar también las comparaciones exponenciales y las iteraciones de la torre o mantenerlas explícitamente como cálculo formal resumido. Definir los parámetros corrige la omisión, pero no reemplaza esa revisión. |
| CQ-03 — procedencia de Jacobian y [5] (X-10) | Verificar la fuente primaria que vincula sus responsables antes de añadir una atribución personal. Se conserva por ahora la firma bibliográfica del documento. |
| CQ-04 — maquetación (X-12, X-14) | Al generar TeX/PDF, revisar identificadores Lean partidos, flechas de continuación, sangría y representación literal de los delimitadores implícitos. |
| CQ-05 — lengua y notación (X-13, X-15) | Revisar anglicismos y subíndices; no renombrar fórmulas en una sola lengua ni confundir un ajuste notacional con un cambio del modelo. |
| CQ-06 — evidencia y cuentas (X-20, X-22) | Conservar el desacuerdo con la auditoría interna y aclarar la cuenta de registros; no modificar informes históricos ni equiparar registros con teoremas distintos. |
| CQ-07 — anexos y configuración (X-19, X-25) | Tratar referencias antiguas de anexos y residuos de configuración por separado, después del resultado del build. No tocar el corte que se está auditando. |

No se adoptaron las posibles mejoras de constantes de X-24: no son necesarias para esta revisión y abrirían una tarea matemática distinta. Las observaciones de alcance X-17, X-18 y X-21 y las limitaciones de independencia X-26 se conservan; no son errores que deban ocultarse.

## 7. Orden de cierre propuesto

1. Dejar terminar la compilación externa y sus controles de tipos, axiomas y exportaciones sobre el corte actual. Un contador parcial de módulos PASS no es un PASS final.
2. Revisar estos Markdown y resolver CQ-01–CQ-03. Mantener el contenido formal intacto salvo que aparezca un problema real que requiera otra decisión.
3. Preparar TeX/PDF de v1.21 y resolver los hallazgos de maquetación, con revisión visual de ambas lenguas.
4. Identificar por hashes los nuevos manuscritos y su relación con el mismo corte Lean; actualizar el mandato del siguiente ciclo sin reemplazar la evidencia anterior.
5. Revisar nuevamente exposición, atribución, correspondencia Lean–texto y paridad. Si las fuentes, opciones y dependencias Lean no cambiaron y el auditor lo acepta, referenciar la evidencia del build completado; no reiniciar automáticamente una compilación completa por cambios de prosa.

No se publicará, hará push ni emitirá un DOI a partir de esta entrega sin autorización del usuario.
