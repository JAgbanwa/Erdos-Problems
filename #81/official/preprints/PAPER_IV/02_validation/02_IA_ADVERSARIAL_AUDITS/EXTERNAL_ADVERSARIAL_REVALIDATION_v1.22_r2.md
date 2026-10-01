# Solicitud de revalidación y dictamen consolidado — Paper IV v1.22-r2

## 1. Encargo

Verifica las correcciones menores españolas posteriores al PASS global de v1.22-r1 y entrega **un informe final consolidado, autónomo y comprensible de E0–E8**. No basta informar «las correcciones revisadas pasan». El informe debe explicar qué está validado para el paquete actual, qué PASS histórico se conserva, su evidencia y sus límites.

No se solicita ni autoriza otro build de Lean. El inglés y el corte formal deben permanecer byte-idénticos. Si esa identidad falla, detente en STOP y solicita instrucciones: no reconstruyas ni repares por tu cuenta.

## 2. Insumos y límites de lectura

Raíz local: `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV`.

Identidad del objetivo: `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r2.json`, con su sidecar SHA-256. Verifica las identidades allí declaradas antes de continuar.

Insumos autorizados:

- `01_manuscript/v1.22_editorial_candidate_r2/`: MD/TeX/PDF ES y EN, correcciones, diff, controles, imágenes, manifiesto y ZIP.
- `01_manuscript/v1.22_editorial_candidate/`: corte r1 de comparación, sin modificaciones.
- `02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r1/`, `run_v1.21_r1/` y `run_v1.2_r1/`: informes, evidencia, scripts, registros y paquetes históricos.
- Los mandatos y objetivos de esas revisiones, para reconstruir el alcance histórico.
- `03_reproducibility/build_piv-v12-fb459343d234/` y `05_formalization/lean_piv-v12-fb459343d234/`, sólo para identidad y consulta estática.
- `05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip` y `LEAN_BOUNDED_GAP_ANNEX_v1.0.zip`, y los insumos de auditoría interna expresamente identificados por E8 en los informes anteriores. Registra sus rutas antes de consultarlos.
- Literatura citada, sólo si surge una cuestión nueva; registra versión y fecha, sin trasladar automáticamente una comparación a una versión posterior.

No leas otros árboles de investigación, `ar_*`, `handoff_*`, documentos de Paper V, credenciales ni resultados ajenos al alcance. Declara cada archivo adicional consultado y por qué. No instales Mathlib ni dependencias, no modifiques caches ni originales, no ejecutes `lake`, `lean` ni replay del kernel, no publiques ni envíes datos a servicios externos. Usa las herramientas locales de documentos ya disponibles; un proceso pesado como máximo.

Escribe exclusivamente en:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r2/`

Conserva insumos y revisiones anteriores. Si existe una ejecución r2, inspecciona y reanuda sin sobrescribir evidencia; cualquier ejecución adicional debe tener un identificador nuevo declarado.

## 3. Comprobaciones nuevas

**E0, identidad.** Verifica hashes, miembros y CRC del ZIP nuevo, el manifiesto y los paquetes históricos utilizados. Compara MD/TeX/PDF ingleses byte por byte con r1. Verifica las 615 entradas del manifiesto Lean congelado y la identidad del anexo. Repite la comprobación al finalizar.

**E6, correcciones españolas y paridad.** Comprueba X-15: once apariciones literales de matching(s) y una de packing se traducen en la prosa, no en bibliografía ni identificadores. El informe anterior cuenta doce matching(s), mientras su escaneo y la fuente contienen once: resuelve explícitamente esta discrepancia de recuento. Comprueba NEW-01: `Model` monoespaciado en §7.2. Contrasta el diff completo, contenido protegido, referencias y numeración; no confíes sólo en los scripts del editor. Verifica que el PDF corresponde al TeX corregido. Examina las 73 páginas en conjunto y las 18 páginas modificadas con detalle (lista en `VISUAL_REVIEW_v1.22_r2.md`), incluyendo desplazamientos de texto. No es necesario regenerar el inglés inalterado.

**NEW-03, rectificación.** Evalúa la admisión del editor en `CORRECTIONS_AND_HANDOFF_v1.22_r2.md`: las correcciones fueron declaradas antes de estar aplicadas. El informe anterior y esa afirmación deben permanecer en la historia; el hallazgo sólo puede cerrarse mediante el artefacto corregido y la rectificación, no borrando la evidencia.

**Puertas restantes.** Examina si el delta afecta a alguna conclusión previa. Para E1, E2, E3, E4, E5, E7 y E8, reutiliza únicamente evidencia cuyo alcance e identidad puedas enlazar al objetivo actual. Si surge un cambio sustantivo o falta evidencia, registra INCONCLUSIVE o FAIL según corresponda y detente ante un bloqueo. No fuerces PASS para satisfacer el objetivo editorial.

## 4. Informe consolidado obligatorio

Entrega `30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md` y `.pdf`, `30_REPORT/SUMMARY.json`, `30_REPORT/FINDINGS.csv` y una matriz de trazabilidad por puerta. El informe debe poder leerse sin abrir los anteriores, aunque cada conclusión tenga referencias verificables a ellos.

Incluye:

1. Identidad exacta actual: manuscrito v1.22, paquete r2, hashes ES/EN, freeze Lean, anexo, manifiesto y ZIP. Estado y fecha reales de la ejecución.
2. Una tabla completa E0–E8 con veredicto **actual**, alcance, comprobación nueva o evidencia heredada, revisión de procedencia, fecha y ruta/hash de evidencia. Escribe «PASS heredado y revalidado por identidad» cuando corresponda; no «ejecutado en r2».
3. Historial de revisiones v1.2 → v1.21 → v1.22-r1 → v1.22-r2: veredictos originales, hallazgos y cómo quedaron resueltos o mitigados. No conviertas retrospectivamente FAIL/INCONCLUSIVE en PASS. Incorpora todos los PASS históricos que sigan siendo aplicables; conserva también observaciones y límites.
4. Cobertura matemática consolidada: teoremas A, B, C y C′, estabilidad, corolarios públicos y anexo, enlazados al mapa de afirmaciones auditado. Recupera la evaluación individual de las siete derivaciones de A.2, incluyendo el cierre de C.3 en r1. Si la lista literal del mapa difiere, consigna la diferencia, no inventes cobertura.
5. E4: describe el build externo de `run_v1.2_r1`, sus registros originales, códigos de salida, módulos, targets, exportaciones y huellas de axiomas. Contrasta el alcance documentado de 607 módulos, 19 targets, 224 export checks y 50 del anexo. No confundas registros repetidos de impresión de axiomas con teoremas distintos. Explica por qué se conserva su validez para r2 y declara que **no se ejecutó un nuevo build ni replay independiente del kernel**. No uses aisladamente el SUMMARY de E4_main que fue sobrescrito por AuditorChecks: consulta el registro original, consola, logs de módulos y E4_RECORD correspondientes.
6. E5/E8: conserva las pruebas, controles negativos, verificación de certificados y observaciones realmente auditados. Contrasta los recuentos con la evidencia del auditor (incluida la discrepancia histórica 1266/844), sin sumar dos veces repeticiones. Mantén la mitigación del detector del runner congelado X-28 y la limitación R-01 del resumen de segundo momento cuando sigan vigentes.
7. Una lista completa de hallazgos históricos y nuevos con estado actual, prueba de cierre, responsable de la corrección y revisión en que se verificó. Distingue cerrado, mitigado y observación aceptada.
8. Independencia y límites: identifica modelo, proveedor, sesión y continuidad. Una sesión separada no garantiza familia distinta; esta revalidación puede heredar una revisión de la misma familia y sesión que las anteriores. No declares revisión ciega ni independencia de familia inexistente. Declara lectura de evidencia previa, caché compartida y ausencia de ejecución dinámica nueva.
9. Veredicto global razonado y pendientes reales. PASS_WITH_FINDINGS/PASS_WITH_OBSERVATIONS no deben convertirse silenciosamente en PASS sin observaciones. Explica al lector qué certifica y qué no certifica la revisión consolidada.

El texto histórico de estado dentro de los manuscritos no se ha actualizado en r2 para mantener intacto el inglés. Distingue esas referencias temporales del estado actual del paquete; indica si generan un problema editorial real, sin modificar los originales.

## 5. Orden y sellado

Orden: E0 → E6/NEW-03 → control de impacto y trazabilidad E1/E2/E3/E7 → herencia E4/E5/E8 → dictamen consolidado → E0 final. No hay build al final.

Un bloqueo produce inmediatamente un informe parcial, checkpoint STOP y estados INCONCLUSIVE para lo no resuelto. Un límite de tiempo no permite declarar PASS.

Guarda scripts, entradas, salidas y evidencia nueva bajo `00_CONTROL/`, `10_SCRIPTS/`, `20_EVIDENCE/`, `30_REPORT/` y `40_PACKAGE/`. El PDF debe corresponder al Markdown final y ser revisado visualmente; registra el método de generación real. El paquete `EXTERNAL_REVALIDATION_run_v1.22_r2.zip` debe contener el informe consolidado, manifiesto y respaldo de sus comprobaciones. No necesita duplicar todos los ZIP históricos: identifica y enlaza cada paquete por hash y ruta y conserva la cadena de custodia. Verifica CRC, miembros y SHA-256 después de comprimir. Actualiza SUMMARY y hallazgos con el estado final, sin tocar los reportes anteriores.

Esta solicitud prepara la revisión; no acredita por sí misma que r2 haya pasado.
