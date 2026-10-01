# Respuesta al feedback para v0.8

Fecha: 21-09-2026. Base protegida: v0.7 española.
Archivo leído: `../draft_v0.7_es/FEEDBACK_EDITOR_v0.8.md`, localizado en `e81p4`; la ruta comunicada bajo `erdos/preprints` no existe en esta máquina.
Estado: **EDITORIAL_DRAFT_WITH_OPEN_GATES**.

| Petición | Decisión y lugar |
|---|---|
| «Los tres papers anteriores de la serie» | Aplicada literalmente al inicio de la Introducción. |
| C1: la barrera rígida no se extiende igual a cordales | Incorporada en §8.3. Se cuenta por PEO, con n≥2: e≤2n−3 y 3T≤e. No hace falta introducir treewidth para esta cuenta. |
| C2: los contratos son universales, la aplicación es cordal | Verificado en `MixedRounding/Defs.lean`, `FarExploration/CodegreeCleanup.lean` y `PaperIV/RC01FarAssembly.lean`; explicitado en §8.3. |
| E1: DOI del depósito | Verificado por la API pública de Zenodo y añadido a [2]–[4]: DOI de versión y de concepto, fecha y depósito conjunto v3. GitHub queda como complemento. |
| E2: cronología | Añadida al inicio de §8: depósito de la serie el 23 de agosto; fechas de [5] y [15] el 8 y 15 de septiembre. Sin adjudicación de prioridad. |
| E3: posible contacto al autor de [15] | No se enviaron mensajes. Es decisión del autor. No se afirma una dependencia oculta ni independencia histórica demostrada por una inspección de ingredientes. |
| F1: gap triangular acotado | Incorporado como resultado complementario en §8.2, (8.1a), tras revisar las fuentes y ejecutar su auditoría. Se mantiene explícita la diferencia con el gap mixto universal. |
| F2: forma por anchura | Incorporada con el contrato literal de bolsas≤d+1 y la equivalencia demostrada. No se atribuye a Mathlib un operador general treewidth. |
| D1–D4: publicación, inglés, literatura anunciada y referencias de serie | Conservados como pendientes de publicación. No se hizo push, no se creó una versión inglesa ni se contactó a terceros en este encargo. |

## Precisiones sobre la observación cordal

El término −1 de la hipótesis de masa importa: εn²/30−1≤(2n−3)/3 se simplifica exactamente a n≤20/ε para n≥2. No se incorpora un umbral meramente aproximado.

No se escribe que todos los grafos de la familia tripartita sean no cordales. La contradicción excluye las instancias densas que sustentan la barrera superpolinómica; una instancia pequeña o degenerada puede ser cordal. Tampoco se convierte la desaparición de este testigo en una prueba de limpieza cordal, ni en una cota superior O(1/ε) para ella.

Esta observación se expone como argumento escrito, no como una nueva declaración formal auditada. La formalización de un contrato cordal y de su adaptador de redondeo no se inició durante la edición.

## Alcance de las auditorías

Se ejecutan cuatro targets usando la caché existente. Sus resultados exactos, hashes y códigos de salida constan en `AUDIT_SUMMARY.json` y `AUDIT_SNAPSHOT.json`. La comprobación de `BoundedCliqueGap` revisa transitivamente los axiomas de las declaraciones de esa biblioteca, pero su chequeo de nombres `Erdos81*` se refiere a los nombres introducidos allí: no es por sí solo el mismo veto transitivo que aplica `PaperIV.ConeAudit`. No se suman los recuentos ni se adopta como auditado aquí el total 817 del informe recibido.

No se cambiaron archivos del árbol Lean. Se incorporó la biblioteca al snapshot de fuentes de esta entrega, no al conjunto de premisas del teorema principal.

## Material anterior preservado

Se mantienen la explicación de `canonicalBad`, el perímetro condicional formal de [5], la advertencia contra equiparar monotonía de margen con mejora automática, y la delimitación de la barrera de limpieza. Los dos bloques antes aparcados no se vuelven a presentar como pendientes. Las 115 fórmulas desplegadas de v0.7 y sus etiquetas se conservan.
