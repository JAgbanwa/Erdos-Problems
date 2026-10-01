# Informe editorial — Paper IV v0.8 española

Fecha: 21 de septiembre de 2026.
Veredicto: **EDITORIAL_DRAFT_WITH_OPEN_GATES**.

## Admisión y alcance

Base: v0.7 española; su huella está en `PROTECTED_BASELINE.json`. Destino: siguiente borrador de revisión del autor, no publicación. Estilo de serie contrastado con Paper III v1.5 español. Se aplicó mathematical-paper-editor para preservar el contenido matemático, distinguir el feedback de la evidencia y registrar los límites de cada afirmación. No se editó el árbol Lean ni se enviaron encargos externos.

## Registro de cambios

| ID | Lugar | Clase | Cambio | Riesgo y control |
|---|---|---|---|---|
| ED08-01 | Introducción | Voz | «Los tres papers anteriores de la serie» | Literalmente solicitado. |
| ED08-02 | §8.3 | Exposición matemática | Se desarrolla la cuenta del feedback para cordales rígidos: PEO, aristas, triángulos y umbral de masa | No se infiere un redondeador cordal ni una cota superior de su umbral. No se presenta como nueva formalización. |
| ED08-03 | §8.2 | Incorporación documentada | Gap triangular con clique máxima acotada; forma por anchura de bolsas | Se consultaron enunciados y pruebas Lean. Se distinguen conteo triangular y ganancia mixta. |
| ED08-04 | §7 y §8 | Alcance formal | Complementos separados de la cadena principal | Presencia en el paquete, auditoría, reexportación y publicación no se identifican. |
| ED08-05 | §8 y referencias [2]–[4] | Fuentes | DOI de versión/concepto, depósito conjunto y cronología | Metadata verificada en API pública; no se afirma prioridad ni dependencia de otro autor. |
| ED08-06 | Bibliografía | Composición | Dos páginas equilibradas con URLs visibles | Conserva tipografía de serie; ninguna entrada queda separada por un salto interno. |

## Integridad semántica

Las 115 fórmulas desplegadas de v0.7 se conservan; se añaden (8.1a), (8.4) y (8.5). No se cambian cuantificadores, hipótesis ni constantes de los resultados previos. La cuenta nueva reproduce y explicita el argumento del feedback, incluida la cancelación exacta que da n≤20/ε para n≥2. La proposición sobre grafos arbitrarios permanece intacta.

El resultado complementario de §8.2 no sustituye RC01 ni se agrega como premisa del teorema principal. La interpretación de anchura usa el árbol de cliques de la biblioteca, no una definición general de treewidth de Mathlib. El control automático de fórmulas, etiquetas y ocho fragmentos Lean literales queda en `SEMANTIC_DIFF_CHECK.json` y `LEAN_LITERAL_EXCERPTS.json`.

No se transfiere la obstrucción general al caso cordal; tampoco se afirma que toda instancia pequeña de la construcción tripartita sea no cordal. No se afirma originalidad bibliográfica a partir del cono formal. Las fechas de [5] y [15] identifican las versiones ya contrastadas en v0.7; esta vuelta no constituye una nueva auditoría matemática integral de esos trabajos.

## Verificación y reproducibilidad

Se ejecutan cuatro targets sobre el entorno con caché existente: `PaperIV/Audit.lean`, `PaperIV/ConeAudit.lean`, `SupplementAudit.lean` y `BoundedCliqueGap/AxiomCheck.lean`. Las salidas, códigos de terminación y huellas anteriores/posteriores están en `AUDIT_SNAPSHOT.json`; los recuentos exactos, en `AUDIT_SUMMARY.json`. No se afirma un rebuild limpio de todas las dependencias. Los recuentos se solapan y no deben sumarse como declaraciones distintas.

La auditoría de axiomas de BoundedCliqueGap comprueba las dependencias fundacionales de sus declaraciones. Su comprobación de nombres propios no equivale a un veto transitivo de todos los nombres importados: se conserva esa distinción. La inspección editorial no modifica los estándares de aceptación del proyecto.

El suplemento `LEAN_SOURCE_SNAPSHOT_v0.8.zip` contiene sólo las fuentes y configuración enumeradas en `LEAN_CUT.json`, con evidencia de auditoría. No incluye secretos, binarios ni cachés. Es un corte local identificado por contenido, no un commit público congelado.

Resultado de esta ejecución: los cuatro targets terminaron con código 0 y las 479 fuentes/configuraciones inventariadas permanecieron idénticas. Se obtuvieron 83 impresiones de axiomas principales, 57 comprobaciones de conos y 12 impresiones suplementarias; la auditoría interna de BoundedCliqueGap comprobó 632 declaraciones. Son ámbitos solapados. Las huellas observadas sólo contienen `propext`, `Classical.choice` y `Quot.sound`. La búsqueda de tokens en las fuentes inventariadas no encontró `sorry`, `admit`, nuevas declaraciones `axiom`, `native_decide` ni `implemented_by`, excluidos comentarios y cadenas. El control editorial confirmó 115 fórmulas previas conservadas, 118 finales y ocho fragmentos Lean literales. El control de artefactos terminó sin avisos TeX de maquetación ni imports propios ausentes.

## Artefactos y voz

Fuente semántica: Markdown v0.8. Derivados: TeX entregado y PDF de 41 páginas, con tres figuras y las ocho tablas previas. La compilación y la revisión visual corresponden a la última edición, incluida la etiqueta v0.8 de portada. `ARTIFACT_CHECK.json` registra sincronización y avisos; `qa/VISUAL_QA.md` registra revisión visual. `MANIFEST_SHA256.md` se genera al final.

Se mantuvieron conectores de causa y consecuencia en las cuentas nuevas. No se añadieron eslóganes, una competición entre pruebas ni nuevas tablas de PASS. Los identificadores Lean quedan donde permiten comprobar un alcance concreto. La bibliografía usa el depósito estable y deja GitHub como complemento. La atribución a Papers I–III y la sección de herramientas se conservan.

## Consultas y límites de publicación

| ID | Lugar y asunto | Responsable / acción | Efecto |
|---|---|---|---|
| CQ-PUB | §7: corte público | Autor: elegir commit y enlace permanentes después de reproducir el paquete | Bloquea publicación, no este borrador. |
| CQ-EN | Versión inglesa | Traducción con control de paridad de fórmulas, hipótesis y referencias | Pendiente para envío. |
| CQ-LIT | [16]: manuscrito anunciado | Autor: obtenerlo o conservar explícita la indisponibilidad; no comparar resultados no leídos | Cierre bibliográfico. |
| CQ-SER | Referencias históricas IV/V | Autor: coordinar notas y enlaces de la serie | Consistencia editorial. |
| CQ-READ | Argumentos y complementos | Revisión humana independiente; la cuenta escrita de §8.3 no se atribuye a Lean | Validación independiente, sin nueva conjetura en la prueba principal. |

No se efectuó publicación, envío editorial ni contacto a autores. No se declara `READY_FOR_RELEASE`.
