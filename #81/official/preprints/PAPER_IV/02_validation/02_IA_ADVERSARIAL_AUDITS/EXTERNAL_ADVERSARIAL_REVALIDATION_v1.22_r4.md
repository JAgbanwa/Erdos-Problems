# Revalidación final de NEW-05 y dictamen consolidado — v1.22-r4

## 1. Alcance del PASS solicitado

El propietario solicita cerrar el proceso concreto de auditoría adversarial **E0–E8**. La revisión humana por pares es un **hito futuro independiente, fuera de este encargo**: no es un requisito pendiente de E0–E8 ni una condición para emitir PASS aquí. El informe puede recomendarla y debe aclarar que no la sustituye, pero su ausencia no convierte una puerta satisfecha en INCONCLUSIVE, PASS_WITH_FINDINGS o PASS_WITH_OBSERVATIONS.

Lo mismo vale para los límites de independencia y hechos históricos ya aceptados sin acción pendiente. Deben permanecer declarados, sin ser presentados como defectos no resueltos del alcance contratado. **PASS significa que todos los criterios E0–E8 aplicables se satisfacen sin acciones correctivas abiertas en este paquete; no significa ausencia de límites, revisión humana realizada ni autorización de publicación.**

Esto no autoriza forzar un veredicto: si hay un defecto real dentro del alcance, identificarlo y mantener FAIL/INCONCLUSIVE o el veredicto correspondiente. El objetivo es corregir defectos, no borrar observaciones históricas.

## 2. Delta y objetivo

Versión del manuscrito: **1.22**; paquete **r4**. Baseline: r3, cuyo informe concluyó PASS_WITH_FINDINGS exclusivamente por NEW-05. Su §10 dice que corregirlo sin más cambios dejaría cero acciones abiertas.

Se modifican sólo dos expresiones españolas:

1. A.2: «la programación numérica de C.3» → «el calendario numérico de C.3».
2. F.4: «cota adaptada con muestra fijada» → «cota adaptada con muestras con anclajes».

Son dos sustituciones terminológicas, no literalmente dos tokens. El inglés MD/TeX/PDF es byte-idéntico a r3, y el corte Lean no cambia. El español se regeneró desde su TeX corregido. No se actualizan de nuevo los párrafos históricos de auditoría: describen r2/r3 con fecha, como aceptó el auditor en r3; el estado de r4 quedará en este nuevo informe.

Raíz: `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV`.

Objetivo: `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r4.json` y su SHA-256. Manuscritos: `01_manuscript/v1.22_editorial_candidate_r4/`.

Escribir sólo en:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/`

No ejecutar Lean/Lake ni un nuevo build, no instalar Mathlib, no modificar caches, originales ni evidencia histórica. No publicar ni enviar datos fuera del equipo. Un proceso pesado como máximo. Si cambia la identidad formal o falta evidencia para heredar E4, emitir STOP y solicitar instrucciones, no compilar por cuenta propia.

## 3. Insumos permitidos

- Paquetes r4 y r3; revisiones anteriores r2/r1 sólo cuando la trazabilidad lo requiera.
- Informes, objetivos, scripts y evidencia de `run_v1.2_r1`, `run_v1.21_r1` y `run_v1.22_r1` a `run_v1.22_r3`.
- Fuente congelada `05_formalization/lean_piv-v12-fb459343d234/`, manifiesto `03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json`, ZIP de fuentes y anexo, para identidad/consulta estática.
- Los 1266 logs y registros identificados por LOG_INVENTORY.json; el verificador suplementario sigue siendo obligatorio en el perfil r4 y es idéntico al validado en r3.

No leer árboles `ar_*`, `handoff_*`, Paper V, credenciales ni investigación ajena al corte. Mantener registro de lecturas, modelo/proveedor y continuidad de sesión. No declarar independencia ciega, de sesión o de familia que no exista. No se solicita nueva revisión bibliográfica, pues las citas no cambian.

## 4. Comprobaciones

Orden: E0 inicial → NEW-05/E6 → control de impacto/herencia → informe consolidado → E0 final.

**E0:** comprobar hashes, miembros y CRC del paquete nuevo y sus antecedentes, identidad del inglés, del verificador y del inventario, de las 615 fuentes y del anexo. Los manifiestos y ZIP históricos permanecen intactos.

**NEW-05/E6:** verificar las dos sustituciones completas en MD, TeX y PDF. Contrastar con los términos establecidos en C.3 y F.5/Tabla 10. Comprobar que no cambia ninguna otra parte del texto, encabezados, fórmulas, hipótesis, etiquetas, referencias ni identificadores. Inspeccionar las páginas modificadas a resolución legible y controlar los desplazamientos/paginación; la lista exacta está en ARTIFACT_CHECKS.json. El inglés no necesita recompilarse. Revalidar su evidencia E6 por identidad con r3.

**Herencia:** consolidar E1–E5 y E7, los 33 registros del mapa E1 de r3 (21 históricos y 12 nuevos), las siete ACCEPTABLE_SUMMARY de A.2, y la mitigación obligatoria de E8. Para E4 usar registros originales del build externo de v1.2: 607 módulos, 19 targets, 224 exportaciones, 50 módulos del anexo. No usar aisladamente el SUMMARY sobrescrito por AuditorChecks. No presentar impresiones repetidas de axiomas como teoremas distintos. Expresar siempre «heredado y revalidado por identidad», no «ejecutado en r4».

**E8:** confirmar que el verificador sigue obligatorio y sin cambios. Puede repetirse sólo el lector de logs, con salida propia, sin Lean. X-28 mantiene la deficiencia histórica del runner, pero la acción de control ya fue cerrada por la mitigación validada en r3. Separar el estado histórico del defecto del cumplimiento actual del control. La mera existencia de ese antecedente no implica que E8 incumpla hoy sus criterios.

## 5. Entrega y criterio de cierre

Entregar `30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md` y PDF correspondiente, `SUMMARY.json`, `FINDINGS.csv`, mapa de afirmaciones y `TRACEABILITY_MATRIX.csv`. El informe será autosuficiente: identidad actual, tabla E0–E8 con veredictos actuales, comprobaciones nuevas, PASS heredados y rutas/hashes de evidencia, historial íntegro sin reescritura retrospectiva, estado de cada hallazgo y límites de alcance.

Registrar NEW-05 como cerrado sólo tras verificarlo. Conservar las siete observaciones aceptadas y X-28 como límites/hechos históricos **sin acción abierta**, si siguen cumpliéndose sus condiciones. Reservar una sección separada a hitos fuera del encargo, incluida revisión humana futura; no incluirlos en pendientes que condicionan el PASS E0–E8.

Si NEW-05 queda cerrado y no aparece otro defecto, emitir el veredicto correspondiente al cumplimiento total del proceso: **PASS**, explicando su alcance limitado y la evidencia heredada. Si no procede, identificar exactamente qué criterio E0–E8 falla y qué acción concreta falta. Nunca emitir PASS por presión del solicitante.

Al acabar verificar E0 otra vez, generar manifiesto y `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r4.zip`, SHA-256, CRC y lista de miembros. El PDF debe corresponder al Markdown final, con método de generación real y revisión visual registrados. No sobrescribir informes anteriores. Ante un bloqueo, informe parcial inmediato y STOP; ante límite de tiempo, INCONCLUSIVE para lo pendiente.

Este documento prepara el encargo; no afirma un PASS externo de r4 ni inicia la ejecución.
