# Paper IV v1.22-r4 — Informe final consolidado de auditoría externa adversarial (E0–E8)

**Ejecución:** `run_v1.22_r4`, completada el 2026-10-01. Las horas reales están en `00_CONTROL/AUDITOR_DECLARATION.json` y en `20_EVIDENCE/E0/E0_INITIAL.json` y `E0_FINAL.json`. La solicitó el propietario en el chat con el mandato `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md`.

## Veredicto global: PASS

Para el proceso de auditoría adversarial E0–E8 del paquete Paper IV versión 1.22, r4, todos los criterios aplicables se cumplen y no queda ninguna acción correctiva abierta:
- NEW-05 queda cerrado tras su verificación.
- No aparece ningún defecto nuevo.
- E4 es un PASS heredado y revalidado por identidad: **no se ejecutó un build nuevo ni un replay independiente del kernel**.

**Qué significa este PASS.** No significa que no haya límites, que se haya hecho una revisión humana ni que se autorice la publicación. Los límites y hechos históricos aceptados (§8 y §9) siguen declarados. Los hitos fuera de este encargo están en la §10.

---

## 1. Identidad actual

| Objeto | Ruta | SHA-256 |
|---|---|---|
| Objetivo r4 | `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r4.json` | `99ff96c9cb51c0d887548333ad41a7b6af0c1fc3523345ba0ec2f6dd03bce888` (= sidecar) |
| Mandato r4 | `…/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md` | `5d89f1c9f8af371989bbeb2b0d847b17891eceb8fb4b9413b5b6b2c27c2733fa` |
| Manuscrito | **versión 1.22**, paquete **r4**: `01_manuscript/v1.22_editorial_candidate_r4/` | — |
| Manifiesto r4 (129 archivos) | `MANUSCRIPT_REVIEW_MANIFEST.json` | `f35bf2a9c383f6cf814bbca6a67a2fc2337eb051b97521ad492a79cae8fc1075` |
| ZIP r4 (131 miembros, CRC correcto) | `PAPER_IV_v1.22_REVIEW_PACKAGE_r4.zip` | `8f20048c50968c93f768be774f2f6a571301dc67fe3c9023b331d15a359494e9` |
| ES MD / TeX / PDF (73 p.) | `PAPER_IV_preprint_v1.22_es.*` | `a8e20305…` / `e5a26672…` / `638cad07…` |
| EN MD / TeX / PDF (72 p.), **byte-idénticos a r3** | `PAPER_IV_preprint_v1.22_en.*` | `d3415df3…` / `c6b14105…` / `4280b03e…` |
| Verificador suplementario e inventario (= r3) | `verify_frozen_logs.py`, `LOG_INVENTORY.json` | `c55225f3…` / `938dcdcc…` |
| Freeze Lean (615 entradas) | `05_formalization/lean_piv-v12-fb459343d234/` | manifiesto `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5` |
| ZIP de fuentes / anexo | `LEAN_SOURCE_piv-v12-fb459343d234.zip` / `LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` | `cb274145…a62e6` / `2847a422…4837d` |
| Paquetes históricos | run_v1.2_r1 / v1.21_r1 / v1.22_r1 / r2 / r3 | `886ed7f0…` / `11659a97…` / `9c74d673…` / `626571be…` / `8ca5a69a1fdbb96823bf415de8de89265d14a8d2897acfed01a86c2a70fd3ddd` |

Los hashes completos están en `20_EVIDENCE/E0/E0_INITIAL.json`.

## 2. Veredictos actuales E0–E8

| Puerta | Veredicto actual | Base | Comprobación nueva en r4 | Evidencia |
|---|---|---|---|---|
| E0 | **PASS** | ejecutado en r4 (inicial y final) | identidad completa (§1); el inglés, el verificador, el inventario y las figuras son iguales a r3 | `20_EVIDENCE/E0/` |
| E1 | **PASS** | heredado y revalidado por identidad | control de impacto | `30_REPORT/CLAIM_MAP_CONSOLIDATED.md` (33 registros) |
| E2 | **PASS** | heredado y revalidado por identidad | control de impacto | `E2_RECORD.md` de run_v1.2_r1, run_v1.21_r1 y run_v1.22_r1 |
| E3 | **PASS** | heredado y revalidado por identidad | — | `20_EVIDENCE/E3/E3_RECORD.md` |
| E4 | **PASS — reused_verified_external_build** | heredado y revalidado por identidad; sin build ni replay | script documental repetido (resultado idéntico) | consola `ef5b01c7…`, records `0f2d8495…`, anexo `57ce1895…`; `E4_REUSE_CHECK.json` |
| E5 | **PASS** | heredado y revalidado por identidad | — | `20_EVIDENCE/E5/E5_RECORD.md` |
| E6 | **PASS** | ejecutado en r4 (delta ES); el inglés, heredado y revalidado por identidad | diff de palabras MD/TeX, contenido protegido, tokens del PDF, raster, pp. 40 y 66 legibles | `20_EVIDENCE/E6/E6_RECORD.md`, `E6_R4_DELTA.json` |
| E7 | **PASS** | heredado y revalidado por identidad | referencias idénticas | `20_EVIDENCE/E7/E7_RECORD.md` |
| E8 | **PASS** | lector de logs ejecutado en r4; lo demás heredado | verificador repetido: PASS sobre 1266 (idéntico a r3) | `20_EVIDENCE/E8/E8_RECORD.md` |

La matriz por puerta está en `30_REPORT/TRACEABILITY_MATRIX.csv`.

**Cambios de etiqueta respecto de r3.**
- E6 pasa de PASS_WITH_FINDINGS a PASS porque NEW-05, el único hallazgo, queda cerrado.
- E8 pasa de PASS_WITH_OBSERVATIONS a PASS. La evidencia no ha cambiado; lo que cambia es la clasificación, según el criterio del mandato: el defecto histórico de X-28 se mantiene como hecho y la acción de control está cumplida. No se borra ninguna observación.

## 3. Comprobación nueva: NEW-05 (E6)

Las dos sustituciones están completas en MD (l.1355, l.2356), en TeX (l.1317, l.2159) y en el PDF (pp. 40 y 66):
- A.2: «**el calendario numérico** de C.3». Coincide con l.1599 y con el encabezado de C.3, «Un calendario explícito».
- F.4: «cota adaptada con **muestras con anclajes**». Coincide con el encabezado de F.5 y con la Tabla 10.

No cambia nada más:
- Son idénticos fórmulas, código, etiquetas, encabezados, entradas en negrita, filas de tablas, imágenes y referencias.
- El diff del editor coincide con el del auditor.
- El diff de tokens del PDF tiene solo las 2 regiones esperadas.
- Solo cambian en raster las páginas 40 y 66. Sus límites de página y su número de líneas no cambian, así que la paginación tampoco.

Las inspeccioné a 130 y 160 dpi. **NEW-05 queda CERRADO.**

## 4. Mapa de afirmaciones y matemática (heredados por identidad)

El mapa tiene **33 registros**. Son los de r3, sin filas nuevas en r4:
- **21 históricos** de run_v1.2_r1: todos MATCH salvo G.2, que en v1.2 quedó como «no re-extraída».
- **12 nuevos** de run_v1.22_r3 (N1–N12): todos MATCH. Cubren:
  - el Teorema 5.0, en sus dos interfaces;
  - el Corolario 5.4, geometría y densidad;
  - la dicotomía (1.5);
  - la optimalidad cuadrática y lineal;
  - la identidad (6.7b);
  - la Proposición D.3;
  - G.2 / Proposición G.1, que deja así cubierto el G.2 histórico.

Las siete derivaciones de A.2 son **ACCEPTABLE_SUMMARY**:
- A2-1, A2-2 y A2-7 desde v1.2;
- A2-3, A2-5 y A2-6 desde v1.21;
- A2-4 desde v1.22-r1.

## 5. E4: evidencia formal (heredada y revalidada por identidad)

**Build externo** de run_v1.2_r1, 2026-09-30, de 15:09 a 21:33 UTC. Runner del auditor sin Lake, Lean 4.28.0, fuentes extraídas del ZIP.

**Registros originales:**
- Consola: **607** módulos con PASS, `EXIT 0` y **19** targets en PASS.
- `records.jsonl`: 608 filas, todas PASS con salida 0.
- **224** `#check` en `ReleaseExportCheck`, con 0 errores.
- Anexo: **50/50**.
- Los 607 oleans son idénticos byte a byte a los del autor.

**Axiomas** (no son teoremas distintos):
- 461 registros, de los cuales 314 son salidas de `#print axioms` y el resto repeticiones.
- 18 declaraciones principales con {propext, Classical.choice, Quot.sound}.
- 50 conos públicos sin axiomas no estándar, sin `sorryAx` y sin `Erdos81`.

El `SUMMARY.json` sobrescrito por AuditorChecks no se usa.

**Por qué sigue valiendo en r4:**
- r4 solo cambia dos frases en español.
- E0 confirma que Lean, el ZIP de fuentes, el anexo y la evidencia de run_v1.2_r1 siguen intactos.
- El script documental reproduce exactamente el mismo resultado.

## 6. E5 y E8

**E5:** 59 comprobaciones distintas más 7 controles negativos, todos rechazados. Las repeticiones no se suman. Las pruebas finitas y Certo no sustituyen pruebas universales.

**E8:**
- El verificador `verify_frozen_logs.py` sigue siendo **obligatorio** y es idéntico a r3.
- Lo repetí con salida propia: **PASS sobre 1266 logs**, que son 608 + 50 + 422 + 186 archivos y se cuentan una sola vez.
- Se heredan las pruebas de r3: 15/15 casos, 4/4 corrupciones y la regla de errores sensible a mayúsculas (E8-02 cerrado).
- **Historia y cumplimiento actual de X-28.** Los runners congelados conservan su patrón insuficiente; es un hecho histórico, no se han parcheado y así se registra. El control que lo mitiga está vigente y verificado, y hay además evidencia de axiomas y conos. No queda ninguna acción abierta.

## 7. Historial original de veredictos (sin reescribir)

| Revisión | Ejecución | Veredicto global original |
|---|---|---|
| v1.2 | run_v1.2_r1 | **INCONCLUSIVE**: E2 por A2-3…A2-6 |
| v1.21 | run_v1.21_r1 | **INCONCLUSIVE**: E2 por A2-4 |
| v1.22-r1 | run_v1.22_r1 | **PASS**, con hallazgos MINOR no bloqueantes |
| v1.22-r2 | run_v1.22_r2 | **PASS_WITH_OBSERVATIONS** |
| v1.22-r3 | run_v1.22_r3 | **PASS_WITH_FINDINGS**: NEW-05 |
| v1.22-r4 | **run_v1.22_r4** | **PASS** |

## 8. Hallazgos: estado actual

`FINDINGS.csv` tiene 54 filas.

| Clase | IDs | Acción abierta |
|---|---|---|
| Cerrados (30) | X-01…X-16, X-20, X-21, X-23, X-25, X-27, NEW-01…NEW-05, R-02, E8-01, E8-02, E8-03 | ninguna |
| Mitigado, con control vigente | X-28: el defecto histórico del runner se conserva | ninguna |
| Observaciones aceptadas, límites o hechos históricos (7) | X-17 (que ahora cubre también N8), X-18, X-19, X-22, X-24, X-29 y R-01 | ninguna |
| Información | X-26 (independencia) | ninguna |
| Correcciones conservadas del auditor y del proceso (15) | AUD-P1, AUD-C1, AUD-C2, C2-01…C2-08, C3-01…C3-03, C4-01…C4-03, C5-01 | ninguna |

C5-01 es un error de índice en un campo de informe de mi script de E6. Lo recalculé correctamente y no afecta al veredicto.

## 9. Independencia y límites declarados

Estos límites no son defectos del alcance contratado.
- **Modelo:** Claude Opus 5.5 (`claude-opus-5-5`), proveedor Anthropic.
- **Sesión:** esta revalidación es **continuación de la misma sesión** que produjo las cinco ejecuciones anteriores. **No es ciega, no es una sesión nueva y no es independiente de familia.** El manuscrito declara el uso de Claude.
- **Lecturas:** leí la evidencia previa y los documentos del editor, y los contrasté con evidencia propia. Están registrados en `00_CONTROL/INPUT_ACCESS_LOG.csv`.
- **Entorno:** misma máquina y misma caché que el build histórico.
- **Ejecución:** sin Lean, sin build y sin replay del kernel.
- **Alcance de la comprobación escrita:** es a nivel de resumen frente a enunciados formales congelados.
- **Páginas no reinspeccionadas:** las páginas ES que no cambiaron (raster idénticas) y todas las EN (byte-idénticas) heredan la inspección visual de r3.

## 10. Hitos fuera de este encargo (no condicionan este PASS)

- La revisión humana por pares es un hito futuro e independiente; se recomienda, y este informe no la sustituye.
- Opcionalmente, una auditoría de otra familia de modelos en una sesión separada, con un build de sala limpia o un replay del kernel.
- La decisión de publicar corresponde al propietario. Este informe no la autoriza.

## 11. E0 final, PDF y sellado

- **E0 final:** `20_EVIDENCE/E0/E0_FINAL.json`. Su objeto `checks` es idéntico al del inicial (`20_EVIDENCE/logs/E0_final.log`).
- **PDF:** generado con pandoc (Markdown → HTML y TeX independiente) más PyMuPDF Story (HTML → PDF). **No se compiló desde TeX.** Lo revisé visualmente (`30_REPORT/PDF_VISUAL_CHECK.csv`).
- **Paquete:** `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r4.zip`, con su `RUN_MANIFEST.json`, su SHA-256, CRC verificado y la lista de miembros en `PACKAGE_INDEX.json`. Los ZIP históricos se enlazan por ruta y hash (§1), sin duplicarlos.
- **Sin efectos externos:** no se publicó nada, no se hizo push ni se enviaron datos fuera del equipo. No se modificaron los originales ni los informes previos.
