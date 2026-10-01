# Paper IV v1.21 — siguiente revisión

Revisión propuesta: **v1.21-r1**, sólo editorial/expositiva sobre el mismo Lean congelado. No es una auditoría iniciada ni una versión publicada.

## Insumos

- Los seis manuscritos ES/EN en MD, TeX y PDF y las figuras de esta carpeta, identificados en `MANUSCRIPT_REVIEW_MANIFEST.json`.
- `RESPONSE_TO_AUDIT_v1.21.md`, diferencias de texto `CHANGES_*.diff`, comprobaciones semánticas, de artefactos y revisión visual.
- `EVIDENCE_AND_ANNEX_CORRIGENDUM.md` y recuento reproducido de axiomas.
- El mismo corte Lean `piv-v12-fb459343d234`, manifiesto `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`, y el mismo anexo `BoundedCliqueGap`. No se añaden fuentes matemáticas.
- La ejecución externa `run_v1.2_r1`, ya terminada: informe final INCONCLUSIVE por E2, E4 PASS, registros, tipos, axiomas, exportaciones y anexo. `EXTERNAL_EVIDENCE_BINDING.json` identifica la evidencia reutilizada. No sustituirla por un contador.

## Preparación y condición de inicio

El mandato está en:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.21_r1.md`

Destino reservado para los resultados, sin iniciar la revisión:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/`

Los hallazgos finales X-01–X-29 están tratados en la respuesta. X-27 precisa la cadena histórica de la clasificación irrestricta; X-28 aporta un detector y un parche complementarios fuera del congelado. El ZIP vigente es `PAPER_IV_v1.21_REVIEW_PACKAGE_r1.zip`. El paquete provisional anterior se conserva por historia y no es el objetivo nuevo. Verifique el manifiesto y `AUDIT_TARGET_v1.21.json` junto al mandato antes de empezar.

El auditor deberá verificar y declarar la reutilización del E4 anterior para las mismas fuentes, opciones y dependencias. **No se autoriza ningún nuevo build, ni total ni parcial.** Si aparece una discrepancia formal, debe detenerse y pedir dirección. Los textos nuevos sí requieren E0, E2, E6, E7 y la correspondencia E1/E3; no se hereda PASS editorial.

No se permite publicar, lanzar otro build simultáneo, instalar Mathlib, modificar el corte antiguo ni ocultar los informes anteriores.
