# E8 — Evidencia del autor, atribución del alcance y empaquetado (r2)

| Ítem | r2 | Estado |
|---|---|---|
| X-28: detector `sorry` de los runners congelados | Los runners `tools/paperiv_build.py` y `tools/audit_publication.py` mantienen el hash del manifiesto (615/615). El parche no se aplicó. Repetí el detector externo (`e8_detector_check.py` → `E8_DETECTOR_RERUN.json`): 10/10 casos correctos, incluido el log negativo real capturado. | **MITIGADO** (vigente): los runners históricos conservan el patrón insuficiente |
| 1266 / 844 | El barrido del auditor cubre 1266 logs = 608 (auditor, principal) + 50 (auditor, anexo) + 422 (autor, segmento 1) + 186 (autor, segmento 2), con 0 hits. El barrido antiguo del autor cubría 844 = 1266 − 422 logs: omitía los 422 del segmento 1 del autor (E8-01; desglose según el registro E8 de run_v1.21_r1). El resultado de r2 es idéntico al de run_v1.21_r1. Ese conjunto se cuenta una sola vez y el alcance de 1266 se atribuye al barrido del auditor de run_v1.21_r1, no al autor. | **Atribución correcta (E8-01 resuelto en r1)** |
| E8-02 | El parche propuesto también añadía `re.I` a la rama `error`, lo que amplía el alcance. | OBSERVATION vigente (sin efecto mientras no se aplique) |
| E8-03: paquete único | E0: el único ZIP del directorio r2 es `PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip` (129 miembros = 127 del manifiesto + el manifiesto + su sidecar; CRC correcto). | Resuelto (r1) y conservado (r2) |
| Documentos del editor r2 | `ARTIFACT_CHECKS.json`, `SEMANTIC_CHECKS.json`, `VISUAL_REVIEW_v1.22_r2.md` y `prepare_r2.py` se contrastaron con mi propia evidencia (E6): las 18 páginas, 11 + 1 + 1 sustituciones, inglés idéntico, 615 entradas y diff idéntico, todo coincide. No se usan como PASS heredado. | Coinciden |
| NEW-03 | Rectificación explícita en `CORRECTIONS_AND_HANDOFF_v1.22_r2.md` más artefacto corregido (E6/NEW03_RECORD.md). | **CERRADO** |
| Errata X-20 (461 = 314 + 147) | Sin cambios. | Resuelto (v1.21) |

**Veredicto E8 (r2): PASS_WITH_OBSERVATIONS** (X-28 mitigado, E8-02).
