# Entrega para revalidación — Paper IV v1.22-r1

Estado: candidata editorial preparada; auditoría nueva no iniciada; publicación no autorizada.

## Qué cambió

La versión 1.22 responde al resultado INCONCLUSIVE de `run_v1.21_r1`. C.3 desarrolla la recurrencia de regularidad, sus cotas inferiores, la absorción de los cinco términos y el paso a la torre. Son explicaciones de pruebas existentes en E18/E19, no nuevos teoremas. Se corrigen también los hallazgos de presentación, traducción e identificadores y la remisión de A.2.

La skill `mathematical-paper-editor` se aplicó con protección de los enunciados: se conservan los 230 displays anteriores de cada idioma, las etiquetas, los párrafos de resultados y los bloques Lean. Las siete fórmulas nuevas concuerdan entre ES/EN. Los 18 controles racionales, de regresión y negativos pasan. Los PDF se regeneraron secuencialmente y se revisaron después de la última edición; véanse los informes adjuntos.

Las 615 entradas del manifiesto formal permanecen idénticas. No se ejecutó Lean ni Lake, no se descargó Mathlib y no se modificaron los informes de auditorías previas. La evidencia formal PASS anterior se puede reutilizar sólo después de verificar sus identidades; no equivale a un nuevo build.

## Cómo solicitar el siguiente ciclo

Entregue al auditor este mandato completo:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r1.md`

Su identidad e insumos están en `AUDIT_TARGET_v1.22.json`, en la misma carpeta. El objetivo editorial se sella con `MANUSCRIPT_REVIEW_MANIFEST.json` y `PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip`; sus archivos SHA-256 se generan al finalizar la preparación.

Los nuevos resultados deben quedar exclusivamente en:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r1/`

El mandato prohíbe recompilar: solicita E0, la rederivación de C.3, revisión bilingüe y regresiones, con E4 reutilizado documentalmente. Si cambia una fuente o aparece una insuficiencia formal, corresponde detenerse y consultar, no lanzar un build automáticamente.

## Qué falta

El auditor debe decidir si A2-4/X-05 puede cerrarse y emitir su propio veredicto. El editor no cambia INCONCLUSIVE por PASS. Se mantienen las limitaciones de independencia declaradas: la revalidación anterior continuó la misma sesión, no fue ciega ni entre familias distintas. El nuevo auditor debe declarar sus propias condiciones.

No se ha publicado, enviado a servicios externos, creado un DOI ni cambiado la selección pública del repositorio. Las versiones y evidencias históricas se conservan.
