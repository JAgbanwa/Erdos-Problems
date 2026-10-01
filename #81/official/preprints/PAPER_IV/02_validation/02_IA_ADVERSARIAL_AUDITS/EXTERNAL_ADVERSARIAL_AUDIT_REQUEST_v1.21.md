# Paper IV v1.21-r1 — revisión adversarial de correcciones

**DOCUMENTO PROVISIONAL SUPERADO; NO EJECUTAR.** El mandato vigente tras el informe final es `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.21_r1.md`, en esta misma carpeta, vinculado por `AUDIT_TARGET_v1.21.json`. El contenido siguiente se conserva como historial de preparación anterior al cierre de v1.2-r1.

## 1. Objeto y restricciones

El objeto editorial es:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.21_editorial_candidate/`

Compruebe `MANUSCRIPT_REVIEW_MANIFEST.json` y su huella antes de leer el contenido. El Lean sigue siendo `05_formalization/lean_piv-v12-fb459343d234`, respecto de la raíz `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/`. No mezcle árboles de trabajo, Paper V, b=0, `ar_*`, `handoff_*`, chats ni credenciales. Lea y aplique las restricciones de independencia, entradas locales, dependencias fijadas, recursos y conservación de evidencia del mandato `EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.2.md`, **con las sustituciones de objeto y evidencia indicadas aquí**. El objeto manuscrito anterior es sólo antecedente para comparar diferencias, no el nuevo objetivo.

No instale, clone ni descargue otro Mathlib. No cambie los pines ni borre cachés. No inicie compilaciones mientras la ejecución anterior siga activa. Un solo proceso pesado y ningún subagente que compile en paralelo. Declare modelo, familia, exposición previa y toda lectura adicional. Una nueva sesión de la misma familia no equivale a revisión entre familias.

## 2. Comprobación previa obligatoria

1. El propietario ha pedido iniciar este ciclo.
2. La ejecución `run_v1.2_r1` ha terminado y conserva su informe y evidencia final. Un FAIL editorial con build formal PASS no invalida por sí solo la evidencia de ese build; debe examinarse cada gate.
3. El autor ha contrastado los hallazgos finales con `RESPONSE_TO_AUDIT_v1.21.md`. No dé por supuesto que la lista preliminar era la definitiva.
4. Los seis manuscritos y figuras coinciden con el manifiesto nuevo; las 615 entradas del corte Lean siguen idénticas al manifiesto congelado.
5. No hay un fallo matemático, de fuentes o formal pendiente que el pase editorial pretenda ocultar.

Si falta un requisito, registre `NOT_STARTED` y solicite el insumo. No complete hashes con valores de otra versión ni lance un build para compensar un bloqueo editorial.

## 3. Trabajo prioritario

Primero haga una lectura independiente de las secciones modificadas y guarde sus conclusiones; después contraste la respuesta del autor. Los hallazgos previos sí son insumos autorizados. Los checks del autor son material a revisar, no un veredicto heredado.

- **E0:** nueva identidad editorial y permanencia de fuentes/configuración. No cambie evidencia histórica.
- **E2:** rederive X-01–X-03 y X-05: limpieza bilateral y carga por arista (C.2), normalización (E.1), eliminación conjunta y n/9 (E.2d), calendario/selector/tres enteros/tower (C.3). Dictamine las siete filas A.2 por separado. El detalle añadido puede contener errores; confróntelo con las fuentes, no sólo con sus nombres.
- **E7:** repita las comparaciones [15] y la atribución [5]/Jacobian. Compruebe especialmente localización frente a construcción, L=4 en (1.5), dirección cp ≤ c₄ y alcance de la cota para todo orden. Registre nuevas versiones públicas si existen.
- **E6:** revise ambos MD/TeX/PDF y todas las páginas. Compruebe subíndices renombrados consistentemente, `mis` definido, delimitadores ⦃/⦄ reales, sangría, monoespaciado, saltos con flecha, figuras, lenguaje ES y estado de evidencia.
- **E1/E3:** compruebe que los cambios no alteran enunciados, constantes, hipótesis, códigos Lean ni cuantificadores. El manifiesto y la comparación mecánica no sustituyen esta lectura.
- **E5:** controle de forma independiente las nuevas cuentas numéricas y revalide negativos pertinentes; no atribuya universalidad a búsquedas finitas.
- **E8:** conserve el desacuerdo con el PASS interno y la errata 314 + 147 = 461. Revise el suplemento del anexo G.1 y no cuente registros como teoremas distintos.

## 4. Evidencia formal y coste de reconstrucción

Al terminar v1.2-r1, identifique por hashes su build externo aislado, 607 módulos, 19 targets, 224 controles de exportación y el build separado del anexo. Examine logs completos, códigos de salida, tipos, axiomas y manifiestos. Verifique misma fuente, toolchain, opciones y dependencias; distinga una compilación parcial de un resultado final.

Si la evidencia externa válida cubre exactamente ese corte inmutable, el auditor **puede reutilizarla expresamente** para E4 y conservar la revisión dinámica ya hecha de tipos y axiomas. Registre `PASS` con la calificación `reused_verified_external_build`, los hashes y el alcance, no «recompilado en este ciclo». Si no la acepta o falta evidencia, registre `INCONCLUSIVE` e indique el control mínimo necesario. No reinicie por defecto una compilación completa por cambios editoriales. Una diferencia formal relevante requiere nueva autorización de alcance y compilación, secuencial y sin otro Mathlib.

## 5. Veredictos, detención y entrega

Use PASS/FAIL/INCONCLUSIVE por gate. Un bloqueo confirmado detiene trabajo caro y produce informe parcial inmediato; una preocupación seria sin resolver en 30 minutos debe quedar INCONCLUSIVE, no convertirse en un PASS. No repare insumos del autor. Preserve fallos, controles negativos e informes anteriores. Un cambio posterior del objetivo requiere otra identidad.

Resultados en:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/`

Use `00_CONTROL`, `10_LOGS`, `20_EVIDENCE/E0...E8`, `30_REPORT` y `40_PACKAGE`; cree carpetas al usarlas. Declare `NOT_STARTED` hasta que se cumpla §2. Entregue reportes por gate y general en MD/PDF, scripts, entradas, resultados, manifiestos y ZIP, preservando las limitaciones de independencia. El informe final debe distinguir suficiencia expositiva, validez matemática, correspondencia, reutilización de evidencia formal y revisión visual. No hay PASS global si queda un gate obligatorio abierto.
