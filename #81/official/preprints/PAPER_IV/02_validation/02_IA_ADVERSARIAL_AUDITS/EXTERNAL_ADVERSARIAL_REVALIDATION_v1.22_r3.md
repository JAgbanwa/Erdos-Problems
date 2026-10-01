# Revalidación documental y dictamen consolidado — Paper IV v1.22-r3

## Encargo y límites

Revisar las correcciones posteriores a `run_v1.22_r2` y emitir un informe **consolidado E0–E8**, que identifique lo validado ahora y todos los PASS históricos todavía aplicables. El último veredicto fue PASS_WITH_OBSERVATIONS, no FAIL. No se solicita conseguir un resultado predeterminado: un defecto real debe conservar su severidad y su veredicto.

La versión es **1.22**, paquete **r3**. No ejecutar Lean, Lake, replay del kernel ni un nuevo build; no instalar otro Mathlib ni modificar caches. Las 615 entradas del corte formal permanecen intactas. Si no se puede demostrar la identidad necesaria para heredar E4, emitir STOP e INCONCLUSIVE; no reconstruir por cuenta propia. Un proceso pesado como máximo; no publicar ni enviar datos a servicios externos.

Raíz: `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV`.

Leer primero `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r3.json` y verificar su sidecar. Escribir exclusivamente bajo:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r3/`

Si ya existe una ejecución, reanudar sin sobrescribir evidencias. No modificar manuscritos ni informes previos.

## Insumos autorizados

- `01_manuscript/v1.22_editorial_candidate_r3/`: documentos, suplementos, controles, manifiesto y ZIP.
- Sus comparadores `v1.22_editorial_candidate_r2/` y `v1.22_editorial_candidate/`.
- Los cuatro informes y evidencias de `run_v1.2_r1`, `run_v1.21_r1`, `run_v1.22_r1` y `run_v1.22_r2`, con sus objetivos y mandatos.
- `03_reproducibility/build_piv-v12-fb459343d234/`, el corte `05_formalization/lean_piv-v12-fb459343d234/`, su ZIP y el anexo `LEAN_BOUNDED_GAP_ANNEX_v1.0.zip`, sólo para identidad y lectura estática.
- Archivos de auditoría interna identificados por las cuatro agrupaciones de `LOG_INVENTORY.json` y los E8 históricos; registrar sus rutas antes de leerlos.
- Literatura citada sólo si una cuestión nueva lo requiere; registrar versión y fecha. No se autoriza una búsqueda en árboles de investigación ajenos al corte.

No consultar `ar_*`, `handoff_*`, Paper V, credenciales ni otras conversaciones de investigación. Registrar todos los archivos adicionales consultados. Declarar modelo, proveedor, continuidad de sesión y familia; no convertir continuidad de revisión en independencia ciega. El auditor anterior declaró la misma sesión y familia.

## Trabajo nuevo, en este orden

1. **E0 inicial.** Hashes, CRC y miembros de los ZIP, manifiesto r3, paquetes históricos y 615 fuentes. Inglés y español han cambiado en r3: no exigir ni afirmar identidad byte a byte del inglés con r2. Sí exigir identidad del contenido protegido, Lean, figuras y antecedentes.
2. **E6 / NEW-04.** Comparar íntegramente los cinco párrafos documentales por lengua con la evidencia r2: portada, §7, nota de Tabla 7, A.2 y F.4. Verificar que C.3 y las siete filas A.2 ya no se presentan como pendientes, y que no se inventa un PASS limpio. Examinar ambos PDF (73 y 72 páginas), las páginas cambiadas en detalle y el resto en vista general. La lista y los hashes están en ARTIFACT_CHECKS.json. Los estados r2 son registros fechados; el dictamen sobre r3 irá en el informe adjunto, no exige editar retroactivamente el manuscrito para que se atribuya su propia aprobación.
3. **E1/E3 suplementarios.** Completar filas individuales para Teorema 5.0 (dos interfaces), Corolario 5.4 (geometría y densidad), dicotomía (1.5), optimalidad cuadrática y lineal, (6.7b), D.3 y G.2/Proposición G.1. Verificar las 13 cabeceras de SEMANTIC_HEADERS contra los archivos originales, namespaces, tipos e hipótesis heredadas, y el mapa SEMANTIC_COVERAGE_SUPPLEMENT. Son extracciones estáticas del autor, no nuevos tipos elaborados ni nuevos veredictos. Atención: C no se afirma clique de G; la diferencia de tamaños no es diferencia simétrica; D.3 usa además el constructor de orden acotado; los coeficientes reales usan ampliación racional. Añadir estas filas al mapa consolidado, sin fingir que estaban en el E1 original.
4. **E8 / X-28 y E8-02.** Evaluar el verificador suplementario como control obligatorio del perfil de reproducción r3. El runner congelado conserva su patrón histórico insuficiente; no se afirma que haya sido parcheado. Inspeccionar `verify_frozen_logs.py`, su inventario y los controles; repetirlo con salida propia. Reproducir los 15 casos y las cuatro corrupciones en una copia de prueba, sin sobrescribir el paquete. Confirmar que el refuerzo de sorry no cambia la sensibilidad a mayúsculas de la regla histórica de errores. Verificar las cuatro agrupaciones y 1266 logs; no sumar barridos repetidos como pruebas distintas. Determinar si cierra la acción de control de la entrega, manteniendo la observación histórica del runner y la evidencia de axiomas/conos.
5. **Herencia de E2/E4/E5/E7 y consolidación.** Comprobar el impacto de los cambios y la identidad que permite conservar los resultados. No volver a ejecutar matemática o bibliografía sin motivo. Recuperar los siete ACCEPTABLE_SUMMARY de A.2, la observación R-01 y los límites de revisión escrita. Mantener X-17, X-18, X-19, X-22, X-24 y X-29 como hechos históricos/de alcance cuando correspondan, sin convertirlos en errores nuevos ni borrarlos. Cualquier hallazgo nuevo se registra.
6. **E0 final y sellado.** Verificar que los insumos no cambiaron durante la revisión.

## Evidencia formal que debe conservarse con precisión

E4 procede de `run_v1.2_r1`, no de una compilación r3: 607 módulos principales, 19 targets, 224 export checks y 50 módulos del anexo. Verificar registros originales, consola y códigos de salida. No usar aisladamente el SUMMARY de E4_main sobrescrito por AuditorChecks. Los 461 registros de axiomas no son 461 teoremas distintos: 314 salidas de print y registros repetidos. Conservar el alcance exacto de las 18 declaraciones principales y 50 conos públicos.

E5 conserva 59 comprobaciones distintas y siete controles añadidos según la clasificación del auditor; los nuevos controles del lector de logs pertenecen a E8, no prueban teoremas. Las pruebas finitas y Certo no sustituyen pruebas universales.

## Informe final autónomo obligatorio

Entregar en `30_REPORT/`:

- `FINAL_CONSOLIDATED_AUDIT_REPORT.md` y `.pdf`;
- `SUMMARY.json`, `FINDINGS.csv` y `TRACEABILITY_MATRIX.csv`;
- mapa completo de afirmaciones, con las filas nuevas diferenciadas.

El informe debe incluir la identidad actual (versión 1.22, r3), la tabla de veredictos actuales E0–E8, alcance y procedencia por puerta, todos los PASS históricos aplicables, historial original de veredictos y estado de cada hallazgo. No reescribir INCONCLUSIVE históricos. Identificar «ejecutado en r3» frente a «heredado y revalidado por identidad». Explicar ausencia de nuevo build y límites de independencia.

Para cada observación aceptada, indicar si queda alguna **acción necesaria antes de publicar** o si es sólo un límite documentado. Si todos los criterios del encargo pasan sin acciones abiertas, puede emitirse PASS conservando explícitos esos límites. Si el criterio profesional exige PASS_WITH_OBSERVATIONS, mantenerlo y explicar por qué: la etiqueta no debe imponerse para satisfacer al autor.

Todo bloqueo produce informe parcial y checkpoint STOP; un límite de tiempo produce INCONCLUSIVE en lo pendiente. No declarar PASS sin completar las comprobaciones.

Guardar scripts, entradas y salidas en `00_CONTROL/`, `10_SCRIPTS/` y `20_EVIDENCE/`. Registrar el método real de generación del PDF, comprobarlo visualmente y vincularlo al Markdown final. Crear `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r3.zip` con manifiesto y SHA-256, verificar miembros y CRC. Enlazar los ZIP históricos por ruta/hash; no es necesario duplicarlos. No actualizar los informes históricos: el nuevo informe consolida su evidencia.

Esta solicitud prepara la revisión; no la inicia ni certifica su resultado.
