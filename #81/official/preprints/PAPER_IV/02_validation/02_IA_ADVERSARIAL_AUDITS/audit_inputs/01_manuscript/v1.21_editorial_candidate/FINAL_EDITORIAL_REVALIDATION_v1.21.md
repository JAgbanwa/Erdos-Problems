# Paper IV v1.21-r1 — cierre autoral y entrega para revalidación

Estado: **RETURN_TO_AUDIT**. No es un PASS independiente, una publicación ni una modificación del congelado Lean.

El informe final de v1.2-r1 deja E2 INCONCLUSIVE por cuatro pasajes, no por un error matemático demostrado. E4 pasa: 607 módulos principales, 19 objetivos, 224 controles de exportación y 50 módulos del anexo. Los 607 objetos principales coinciden byte a byte con los registrados por el autor.

## Cambios finales sobre la candidata provisional

- Se conservan y someten a rederivación las ampliaciones de C.1–C.3 y E.1/E.4 preparadas para A2-3/4/5/6; todas las filas de A.2 recibirán dictamen explícito.
- Se corrige la procedencia de la clasificación irrestricta: las dos interfaces E32 todavía dependen de la cadena histórica de Alon–Shapira. §7, E.2, Tabla 9 y [23] lo indican en ambos idiomas. No se cambia la prueba seleccionada para el Teorema C ni se afirma independencia de esa cadena para toda la publicación.
- Se registra el resultado externo terminado, manteniendo la diferencia entre validación formal y suficiencia expositiva.
- Se aporta fuera del congelado un reescáner de avisos y un parche mínimo no aplicado para los dos runners históricos. Reconoce el negativo real con acentos graves; no ejecuta Lean. El informe conserva hashes de cada registro examinado.
- La instrucción diferencia ejecución independiente en sesión nueva de diversidad de familias. La restricción de lectura declarada por el auditor no se transforma en una afirmación falsa de aislamiento técnico.

La skill de edición de papers exige preservar sustancia protegida y volver a comprobar los artefactos tras la última edición; por ello se sincronizan MD/TeX/PDF ES/EN y se renueva su identidad, sin modificar Lean. `SEMANTIC_CHECKS.json`, `EXPOSITORY_CHECKS.json` y `ARTIFACT_CHECKS.json` describen los controles y sus límites. No hay cambio de teoremas, hipótesis, constantes ni bloques Lean; se conservan los renombramientos descriptivos declarados en la primera pasada.

`EDITORIAL_CHANGE_REPORT_v1.21.md` documenta la primera pasada, con sus estados históricos. La respuesta completa actual es `RESPONSE_TO_AUDIT_v1.21.md`; este documento y `REVIEW_HANDOFF_v1.21.md` fijan la entrega vigente. El paquete provisional anterior y su mandato permanecen conservados fuera de la identidad nueva.

## Evidencia y aceptación

`EXTERNAL_EVIDENCE_BINDING.json` vincula el informe externo y sus registros finales; `LEAN_IDENTITY_CHECK.json` compara las 615 entradas del congelado. El auditor deberá comprobarlos, no aceptar sólo la palabra del autor. El mandato nuevo prohíbe otro build y dispone STOP ante diferencias formales.

No quedan cambios autorales previstos antes de esta revisión. Sí queda que el auditor acepte o rechace la suficiencia de las ampliaciones y corrobore paridad, atribución, procedencia y evidencia. Las observaciones informativas pueden mantenerse declaradas; los bloqueos o dudas matemáticas no se deben convertir artificialmente en PASS.

Plan activo: revalidar v1.21-r1. Estado matemático: fuentes congeladas sin cambios y E4 externo previo PASS. Estado editorial: correcciones listas para examen. Pendiente: nuevo veredicto externo. Publicación: no autorizada por esta entrega.
