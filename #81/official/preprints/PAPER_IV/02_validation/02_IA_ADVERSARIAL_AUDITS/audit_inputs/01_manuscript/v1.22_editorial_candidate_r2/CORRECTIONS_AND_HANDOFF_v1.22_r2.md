# Paper IV v1.22 — revisión editorial r2

## Identidad y alcance

Se conserva la versión del manuscrito **v1.22**. Esta entrega es el paquete **v1.22-r2**, una revisión exclusivamente española del candidato `v1.22_editorial_candidate` (r1). No se sobrescribe ningún insumo ni informe auditado. La revisión externa r2 aún no ha comenzado.

La revisión externa r1 terminó con veredicto global PASS, E6 PASS_WITH_FINDINGS y E8 PASS_WITH_OBSERVATIONS. El objetivo de r2 es verificar las correcciones menores y emitir un informe consolidado de todas las puertas; no sustituir la historia por un PASS sin trazabilidad.

## Correcciones y rectificación

1. **X-15:** once apariciones de `matching`/`matchings` en la prosa española se sustituyen por `emparejamiento`/`emparejamientos`; una de `packing`, por `empaquetamiento`. No se traducen títulos bibliográficos, identificadores ni código. El informe narrativo del auditor indica doce matching(s), pero su escaneo y el texto fuente contienen once; la comprobación de cierre debe hacerse sobre las apariciones literales, no sobre ese recuento narrativo.
2. **NEW-01:** en §7.2 se presenta `Model` como identificador de código.
3. **NEW-03 — rectificación del editor:** la respuesta editorial anterior dio por terminadas las dos correcciones anteriores cuando aún no estaban aplicadas en los artefactos entregados. Esa afirmación era incorrecta. Esta entrega aporta el diff y los artefactos corregidos; se conserva la respuesta anterior como evidencia histórica, sin reescribirla.

## Protección matemática y editorial

`CHANGES_es.diff` contiene el cambio literal. `SEMANTIC_CHECKS.json` documenta la comparación de ecuaciones, matemáticas en línea, bloques de código y enunciados protegidos. No se cambian hipótesis, constantes, demostraciones, numeración, citas, figuras ni referencias. La única nueva marca de código es `Model`.

Los tres archivos ingleses (Markdown, TeX y PDF) son byte-idénticos a r1. Las 615 entradas del manifiesto de fuentes Lean coinciden con el corte congelado `piv-v12-fb459343d234`. No se ejecutó Lean, no se instaló Mathlib y no se modificaron fuentes ni anexos formales.

El PDF español se regeneró con la misma plantilla y herramientas locales. Conserva 73 páginas: 18 cambian de representación gráfica y 55 permanecen idénticas. La expansión de términos españoles provoca algunos desplazamientos posteriores de texto, sin añadir contenido matemático. Véanse `ARTIFACT_CHECKS.json` y `VISUAL_REVIEW_v1.22_r2.md`.

Las menciones de estado de revisiones anteriores dentro de los manuscritos se mantienen como metadatos históricos. No se actualiza el inglés para describir r2: el estado vigente del paquete corresponde a este documento y, después de la revisión, al informe consolidado del auditor.

## Entrega y próximo control

El manifiesto `MANUSCRIPT_REVIEW_MANIFEST.json` identifica los archivos de r2; el ZIP y sus sumas se generan después de cerrar esta documentación. La solicitud externa se encuentra en `../../02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r2.md`.

El auditor debe verificar las correcciones españolas y la identidad del inglés y de Lean, y consolidar E0–E8 con la evidencia histórica aplicable. La ausencia de cambios permite proponer reutilizar el build externo ya validado; no significa que se haya ejecutado un build nuevo. Las observaciones metodológicas anteriores que no desaparecen por estas correcciones deben conservarse.

**Estado:** preparado por el editor; revalidación externa r2 pendiente. No se ha publicado ni enviado el paquete.
