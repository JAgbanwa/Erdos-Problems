# Correcciones y entrega para revalidación — Paper IV v1.22-r3

Fecha: 1 de octubre de 2026. Versión del manuscrito: **1.22**. Identificador de paquete: **r3**. Estado: **EDITORIAL_DRAFT_WITH_OPEN_GATES**; preparado para revisión externa, no para afirmar un PASS externo nuevo ni publicar.

## Diagnóstico y cambios

La última revisión fue PASS_WITH_OBSERVATIONS, no FAIL: no quedaron hallazgos MINOR o superiores abiertos. E6 y E8 conservaron observaciones. No se altera ese informe ni se convierte retrospectivamente en PASS limpio.

| Punto | Corrección o evidencia nueva | Estado que puede afirmar el editor |
|---|---|---|
| NEW-04: estados desactualizados | Cinco párrafos por idioma: portada, §7, nota de Tabla 7, alcance A.2 y cierre F.4. Se registra la aceptación de C.3 y de las siete derivaciones, manteniendo los límites del informe r2. | Aplicado en MD/TeX/PDF ES y EN; cierre externo pendiente. |
| X-28: detector del runner histórico | Verificador suplementario obligatorio, fuera del freeze, con inventario por hash de 1266 logs; reconoce `sorryAx` y avisos de `sorry` con comillas y capitalización. | 15 controles unitarios y cuatro corrupciones de extremo a extremo pasan; barrido histórico sin alertas. El runner histórico sigue sin modificar. |
| E8-02: alcance del parche | La regla de errores conserva su sensibilidad a mayúsculas; sólo la regla de sorry se refuerza. | Comprobado explícitamente. No se presenta como parche aplicado al runner congelado. |
| Cobertura E1 incompleta | Mapa complementario con 13 cabeceras, hipótesis, traducciones y origen del build; incluye G.2 y la construcción acotada necesaria para D.3. | Correspondencia estática revisada por el editor; requiere confirmación individual del auditor. |
| E6: paridad e identidad | Diffs completos, identidad de fórmulas/código/etiquetas/tablas/referencias, regeneración y revisión visual. | Inglés y español cambian sólo en cinco párrafos documentales. El inglés ya NO es byte-idéntico a r2. |

## Reproducción de la mitigación E8

El runner histórico aislado **no basta** para el control de sorry. Para esta entrega, su evidencia debe usarse junto con los controles de axiomas/conos y este postcontrol:

```text
python verify_frozen_logs.py --inventory LOG_INVENTORY.json --output <archivo-nuevo-del-auditor>.json
```

Ejecutar desde la carpeta r3 en su posición declarada dentro de Paper IV. El resultado falla ante logs ausentes, adicionales, con hash distinto o con alertas. No ejecuta Lean. El inventario reúne 608 logs externos principales, 50 del anexo y los dos segmentos del autor de 422 y 186. Son 1266 archivos, no 1266 pruebas matemáticas.

`LOG_VERIFIER_TESTS.json` conserva las salidas de las pruebas y del barrido. `test_log_verifier.py` es la fuente de las pruebas; para repetirla, copiar el arnés y el verificador a la carpeta de evidencia propia del auditor y conservar la estructura/ruta de Paper IV o ajustar sólo su resolución de rutas en la copia, documentándolo. No sobrescribir los resultados sellados. El comando anterior admite directamente una salida nueva y es el postcontrol reproducible sobre el corte.

## Observaciones históricas que no se borran

- X-17: distinguir la familia explícita de la prosa del enunciado existencial Lean.
- X-18: los parámetros reales permiten la especialización no negativa utilizada.
- X-19: entradas adicionales del lakefile no convierten módulos no alcanzados en parte de un build; se conserva la lista literal de targets.
- X-22: discrepancia histórica entre valoración interna y externa de A.2; su revisión posterior no cambia los veredictos originales.
- X-24: no se incorporan constantes opcionales ni nueva matemática.
- X-29: build del autor reanudado en dos tramos; no afecta a la identidad de fuentes. Se conserva además la evidencia del build externo.
- R-01: estimaciones de segundo momento de C.2 citadas y aceptadas como resumen, no expandidas de nuevo en r3.
- X-26: límites de independencia; no se presenta como ciega ni de otra familia una revisión que no lo fue.

Estas observaciones describen alcance o historia; no son defectos matemáticos que deban ocultarse para obtener una etiqueta. Corresponde al auditor decidir si, tras las correcciones, permiten PASS sin acciones pendientes o si debe mantener PASS_WITH_OBSERVATIONS. Solicitamos una explicación concreta de cualquier acción aún necesaria.

## Invariantes y entrega

Sin cambios en teoremas, pruebas, constantes, citas, figuras ni fuentes Lean; las 615 entradas congeladas conservan sus hashes. No hubo build Lean, descarga de Mathlib, publicación ni envío externo. Se regeneraron únicamente los documentos.

Los estados del manuscrito son registros fechados de r2. La evaluación de r3 se adjuntará por separado y no exige reescribir un documento ya auditado para atribuirle su propio veredicto. Los informes históricos permanecen intactos.

Ver `ARTIFACT_CHECKS.json`, `VISUAL_REVIEW_v1.22_r3.md`, `STATUS_DELTA.json`, `CHANGES_*.diff`, `SEMANTIC_COVERAGE_SUPPLEMENT.md` y el manifiesto final. El siguiente paso es ejecutar el mandato r3 y emitir un informe consolidado E0–E8, no sólo una lista de correcciones.
