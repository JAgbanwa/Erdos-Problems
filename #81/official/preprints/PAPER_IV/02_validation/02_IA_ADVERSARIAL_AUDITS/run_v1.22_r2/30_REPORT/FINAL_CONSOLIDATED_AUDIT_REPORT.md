# Paper IV v1.22-r2 — Informe final consolidado de auditoría externa adversarial (E0–E8)

Ejecución: `run_v1.22_r2`. Estado: **completada** el 2026-10-01: inicio 11:00:18 UTC (E0 inicial 11:01:08 UTC); cierre tras el E0 final de la §11. Fue solicitada por el propietario en el chat («haz la rerevision») con el mandato `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r2.md`.

**Veredicto global actual: PASS_WITH_OBSERVATIONS.** No queda ningún hallazgo de severidad MINOR o superior abierto. Siguen vigentes nueve observaciones aceptadas (ocho históricas y la nueva NEW-04, §8), una mitigación (X-28) y los límites de independencia de la §9. No es una revisión por pares humana ni autoriza publicar.

---

## 1. Identidad exacta del paquete revisado

| Objeto | Ruta | SHA-256 |
|---|---|---|
| Objetivo r2 | `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r2.json` | `f931776370dcc101c637cb978273d8757b298ff79e99d50fff815104d4e00583` (coincide con el sidecar) |
| Mandato r2 | `…/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r2.md` | `d085621334d1f5ae14f9e637d237817d7d0fe6673709cfd5fcbad6f4c984ba3e` |
| Manuscrito | versión **v1.22**, paquete **r2**: `01_manuscript/v1.22_editorial_candidate_r2/` | — |
| Manifiesto r2 | `MANUSCRIPT_REVIEW_MANIFEST.json` (127 archivos) | `0fcaf0589c389f70fdb85959f4c69c45f97a131a64a7234a78e40328f7509c0a` |
| ZIP r2 | `PAPER_IV_v1.22_REVIEW_PACKAGE_r2.zip` (129 miembros, CRC correcto) | `d4f3b33d647744a54c93098e0944b18d01a3377c4bbc9a3ecc5f8789e9973635` |
| ES MD / TeX / PDF (73 p.) | `PAPER_IV_preprint_v1.22_es.*` | `ec227eb5…e0e97e` / `356f03c1…222d02c` / `8ebfccd7…6eb0df` |
| EN MD / TeX / PDF (72 p.) | `PAPER_IV_preprint_v1.22_en.*` — **byte-idénticos a r1** | `99a1159d…65c94f` / `34a3081b…9c1100` / `5bbb730e…cd79e0` |
| Corte Lean (freeze) | `05_formalization/lean_piv-v12-fb459343d234/`, 615 entradas | manifiesto `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5` |
| ZIP de fuentes Lean | `05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip` (615 miembros = manifiesto) | `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6` |
| Anexo | `05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` (40 miembros) | `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d` |
| Corte r1 de comparación | `01_manuscript/v1.22_editorial_candidate/` (sin cambios) | manifiesto `d9e559a3…2984029a`; ZIP `2b87b746…f9e2b098` |
| Paquetes históricos | `run_v1.2_r1/40_PACKAGE/EXTERNAL_AUDIT_run_v1.2_r1.zip` | `886ed7f033bca42a530944d48f91ef45e79f6be4cb0d74080c5d8d6efc4f5e2b` |
| | `run_v1.21_r1/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.21_r1.zip` | `11659a97b0a4f2bffadb6968159cc5b66562b4470053939a45c1e8a42db7a638` |
| | `run_v1.22_r1/40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r1.zip` | `9c74d673206ab17a5b4586209ececca30536f1768fcc91ffdd39db551193a1fa` |

Los hashes completos del manuscrito están en `20_EVIDENCE/E0/E0_INITIAL.json`. E0 inicial y E0 final dan resultados idénticos (§11). Ningún insumo ni evidencia histórica cambió.

## 2. Tabla E0–E8: veredicto actual

| Puerta | Veredicto actual | Alcance | Base del veredicto | Procedencia (ejecución, fecha) | Evidencia (ruta / hash) |
|---|---|---|---|---|---|
| E0 identidad | **PASS** | objetivo, manifiestos, ZIP, inglés, Lean, anexo, paquetes históricos | **ejecutado en r2** (inicial y final) | run_v1.22_r2, 2026-10-01 | `20_EVIDENCE/E0/E0_INITIAL.json`, `E0_FINAL.json` |
| E1 enunciados | **PASS** | 21 afirmaciones del mapa; constantes y etiquetas | **PASS heredado y revalidado por identidad**, más un control de impacto nuevo | run_v1.2_r1 (2026-09-30), run_v1.21_r1, run_v1.22_r1 (2026-10-01) | `run_v1.2_r1/20_EVIDENCE/E1/E1_RECORD.md`; `20_EVIDENCE/IMPACT/IMPACT_CHECK.json` |
| E2 matemática | **PASS** (observación R-01) | 56 componentes; 7 filas de A.2 | **PASS heredado y revalidado por identidad** | A2-1/2/7: run_v1.2_r1; A2-3/5/6: run_v1.21_r1; A2-4: run_v1.22_r1 | `run_v1.2_r1/…/E2_RECORD.md`; `run_v1.21_r1/…/E2_RECORD.md`; `run_v1.22_r1/…/E2_RECORD.md` |
| E3 correspondencia | **PASS** | cabeceras Lean, identificadores, X-27 | **PASS heredado y revalidado por identidad**, más la resolución de `Model` | run_v1.2_r1 → run_v1.22_r1 | `20_EVIDENCE/E3/E3_RECORD.md` |
| E4 build | **PASS — reused_verified_external_build** | 607 módulos, 19 targets, 224 exportaciones, 50 módulos del anexo | **PASS heredado y revalidado por identidad**; **sin build ni replay del kernel** | build de run_v1.2_r1, 2026-09-30 15:09–21:33 UTC | consola `ef5b01c7…`, records `0f2d8495…`, anexo `57ce1895…`; `20_EVIDENCE/E4/E4_REUSE_CHECK.json` |
| E5 falsación | **PASS** | T01–T24; 21 + 14 comprobaciones exactas | **PASS heredado y revalidado por identidad**, con repetición de los scripts aritméticos | run_v1.2_r1, run_v1.21_r1, run_v1.22_r1 | `20_EVIDENCE/E5/*_RERUN.json` |
| E6 bilingüe / PDF | **PASS_WITH_OBSERVATIONS** | delta ES r1→r2, 73 páginas, PDF frente a TeX | **ejecutado en r2** | run_v1.22_r2 | `20_EVIDENCE/E6/E6_RECORD.md`, `E6_R2_DELTA.json`, `PAGE_INSPECTION_LOG.csv` |
| E7 literatura | **PASS** | bibliografía, atribución | **PASS heredado y revalidado por identidad** (referencias idénticas) | run_v1.2_r1 → run_v1.22_r1 | `20_EVIDENCE/E7/E7_RECORD.md` |
| E8 evidencia del autor | **PASS_WITH_OBSERVATIONS** | detector, alcance 1266/844, paquete, NEW-03 | detector **repetido en r2** y atribución heredada | run_v1.21_r1 (barrido 1266), run_v1.22_r2 | `20_EVIDENCE/E8/E8_RECORD.md`, `E8_DETECTOR_RERUN.json` |

La matriz completa (veredicto por revisión, comprobación nueva, evidencia heredada y enlace de identidad) está en `30_REPORT/TRACEABILITY_MATRIX.csv`.

## 3. Historial de revisiones

| Revisión | Ejecución | Veredicto global original | Puertas no PASS | Qué abrió o cerró |
|---|---|---|---|---|
| v1.2 | run_v1.2_r1 (2026-09-30) | **INCONCLUSIVE** | E2 INCONCLUSIVE (A2-3, A2-4, A2-5 y A2-6: REQUIRES_EXPANSION); E3, E6 y E8 PASS_WITH_FINDINGS; E7 PASS_WITH_MINOR_FINDINGS | Hallazgos X-01…X-29: 5 MODERATE, 13 MINOR, 11 OBS/INFO. Build externo 607/607, 19/19, 50/50, oleans idénticos byte a byte. X-27 (procedencia de E32) |
| v1.21 | run_v1.21_r1 (2026-09-30/10-01) | **INCONCLUSIVE** | E2 INCONCLUSIVE (A2-4 seguía abierto); E1 PASS_WITH_MINOR; E6 PASS_WITH_FINDINGS; E8 PASS_WITH_OBSERVATIONS | Cerró A2-3, A2-5 y A2-6 (X-01, X-02, X-03) y otros 15. Abrió NEW-01, NEW-02, R-01, R-02, E8-01…03. X-05, X-12 y X-15 quedaron parciales |
| v1.22-r1 | run_v1.22_r1 (2026-10-01) | **PASS** («con hallazgos MINOR no bloqueantes») | E6 PASS_WITH_FINDINGS; E8 PASS_WITH_OBSERVATIONS | Cerró A2-4/X-05 (C.3), X-12, NEW-02, R-02, E8-01, E8-03 y la ortografía de X-10. Dejó parciales X-15 y NEW-01 (ES). Abrió NEW-03 |
| v1.22-r2 | **run_v1.22_r2** (2026-10-01) | **PASS_WITH_OBSERVATIONS** | E6 y E8 PASS_WITH_OBSERVATIONS | Cierra X-15, NEW-01 y NEW-03. Registra la observación NEW-04 y la corrección del auditor C3-01 |

Los INCONCLUSIVE de v1.2 y v1.21 **se mantienen como veredictos de esas revisiones**. El PASS actual se refiere al paquete v1.22-r2 y no las convierte retroactivamente.

## 4. Cobertura matemática consolidada

### 4.1 Afirmaciones públicas

Mapa de afirmaciones de run_v1.2_r1, E1 (21 filas). Su texto es idéntico en r2.

| Afirmación | Declaración Lean | Semántica (E1) | Demostración escrita (E2) | Formal (E3/E4) |
|---|---|---|---|---|
| Teorema A (todos los órdenes, aditiva) | `Erdos81AllOrders.erdos81_all_orders_additive`; explícita `ExplicitThreshold.erdos81_all_orders_bounded_additive` | MATCH | ensamblaje rederivado; b = N² ≤ T(h+8) vía C.3 (A2-4, cerrado en r1) | compilado, axiomas estándar |
| Teorema B (1.1) cota y (1.2) máximo | `Erdos81Unconditional.erdos81_cliquePartition`; `PaperTheorems.erdos81_max_eq` | MATCH, MATCH | rederivado (ramas L/C, Corolario 3.5, Teorema 5.0, Lema 5.3) | idem |
| Teorema C (defecto fijo) | `DefectExplicitPublication.rooted_defect_eventual/_maximum` | MATCH (rsd equivalente a [15]) | E.1–E.4; A2-5 y A2-6 cerrados en v1.21 | idem; cono sin Alon–Shapira |
| Teorema C′ (6.12), (6.13); Cor. 6.3 (6.17); clasificación (6.18) | `SublinearResearch.fixed_defect_joint_stability_real`, `fixed_defect_exact_extremal_edit_real`, `E32.cp_classification_of_theoremCPrimeC` | MATCH (C′a–d) | rederivado; la misma raíz antes de Q y τ | idem; **X-27**: la clasificación cp usa la cadena histórica [23], declarado |
| Estabilidad cordal: Teorema 6.1, Cor. 6.1a, 6.2 | `IntegralStability…`, `chordal_joint_stability_real`, `ExtremalClassification.chordal_extremal_classification` | MATCH | rederivado (componente 26) | idem |
| Prop. 6.3a (raíz cuadrada) | `OptimalTemplateObstruction.*` | MATCH; X-17 (Lean existencial) | rederivado | idem |
| Prop. 6.4, Teorema 6.5, Cor. 6.6, (C.4) | `certified_*_all_orders`, `uniform_*`, `sequence_arbitrary_orders_*`, `E35.theoremC_tower*`, `E35.NfarE_le_tower_poly` | MATCH | estático y rederivado; la torre de (C.4) se compara en C.3 | idem |
| Teorema 3.1, Cor. 3.5 | `RC01Final.rc01_uniformRoundingTarget`, `FarRegimeAllGraphs…` | MATCH | C.1–C.3; A2-3 cerrado en v1.21 | idem |
| Prop. D.2, D.3, D.1 | `DefectSharpPublication.order_three_insufficient`, `SplitMixedGap.mixed_gap_zero`, `ThreeRegime.CompleteStateAllOrders` | D.2 MATCH | componentes 52–53 rederivados; A2-7 | idem |
| F.3a/b | `exists_clique_additive_defect`, `recover_clique_from_edit` | MATCH | rederivado | idem |
| Anexo G.1 | `BoundedCliqueGap.chordal_gap_linear_cliqueFree` | MATCH | — | anexo 50/50, 633 declaraciones, axiomas estándar |
| G.2 (Prop. G.1) | `FarExploration.CleanupRigidVerdict.threshold_gt_exp` | **no re-extraída** (solo texto estático) | — | compilado dentro del corte |

**Diferencias declaradas.** La Tabla 7 del manuscrito incluye entradas que **no tienen fila semántica propia en E1**: Teorema 5.0 (ventana reforzada e interfaz anterior), Cor. 5.4, Dicotomía (1.5), optimalidad de los coeficientes cuadrático y lineal, identidad (6.7b) y Prop. D.3. Están cubiertas solo por el registro de componentes de E2 (componentes 14, 22, 24, 26 y 53, rederivados) y por la correspondencia estática de E3 más la compilación de E4. No les atribuyo una cobertura semántica que no existe. G.2 sigue sin re-extraer.

### 4.2 Las siete derivaciones de A.2

| ID auditor | Fila literal de A.2 en el manuscrito (ES p. 41 / EN p. 40) | v1.2 (run_v1.2_r1) | v1.21 | v1.22-r1 | Estado actual |
|---|---|---|---|---|---|
| A2-1 | «§5.1, (5.4) y (5.7)» | ACCEPTABLE_SUMMARY | idem (X-23: frase 113/64 añadida) | heredado | **ACCEPTABLE_SUMMARY** |
| A2-2 | «C.2, (3.8) y (3.10)» | ACCEPTABLE_SUMMARY | idem | heredado | **ACCEPTABLE_SUMMARY** |
| A2-3 | «Lema 3.2 y C.1–C.2» | REQUIRES_EXPANSION (la carga por arista no se seguía del texto) | **ACCEPTABLE_SUMMARY** (limpieza bilateral, carga ≤ 1, retención; X-01) | heredado; R-02 aclarado | **ACCEPTABLE_SUMMARY** (R-01 obs.) |
| A2-4 | «C.3, Tabla C.1» | REQUIRES_EXPANSION | REQUIRES_EXPANSION (faltaba la recurrencia de regularidad y la comparación con la torre) | **ACCEPTABLE_SUMMARY**: 6 comprobaciones contra Mathlib `initialBound`/`stepBound`/`bound` y E18/E19 | **ACCEPTABLE_SUMMARY** |
| A2-5 | «E.1» (normalización) | REQUIRES_EXPANSION | **ACCEPTABLE_SUMMARY** (X-02) | heredado | **ACCEPTABLE_SUMMARY** |
| A2-6 | «E.1, (E.2b) y (E.2d)» | REQUIRES_EXPANSION | **ACCEPTABLE_SUMMARY** (X-03) | heredado | **ACCEPTABLE_SUMMARY** |
| A2-7 | «D.1» | ACCEPTABLE_SUMMARY | idem | heredado | **ACCEPTABLE_SUMMARY** |

Diferencias entre las filas literales y los ID del auditor:
- A2-1: el auditor citaba también (5.3).
- A2-3: el auditor la describía como «§3.2/C.2, cotas de fibra, (3.8), factibilidad por arista», mientras que el manuscrito agrupa (3.8) en la fila C.2.
- A2-5: el auditor incluía además las cuentas de E.4.

El contenido cubierto es el mismo, pero esas son las diferencias de redacción.

## 5. E4: build externo y por qué sigue valiendo

**Qué se hizo** (run_v1.2_r1, 2026-09-30):
- Runner propio del auditor, sin Lake, con Lean 4.28.0. Fuentes extraídas del ZIP (615/615) y objetos nuevos, sin usar oleans del autor. Mathlib compartido en solo lectura; caché de 113 821 archivos sin cambios.
- El primer intento falló por un error del auditor (C-04); el segundo corrió de 15:09 a 21:33 UTC.

**Registros originales:**
- **Consola:** `modules_planned 607, pass 607`, sin fallos, 607 líneas `PASS n 607`, `EXIT 0`, y los 19 targets de FREEZE_SCOPE en PASS.
- **records.jsonl:** 608 filas (607 + AuditorChecks), todas PASS, con código de salida 0 y hashes de fuente iguales al manifiesto.
- **Logs:** 608 logs de módulo sin «sorry». `ReleaseExportCheck` tiene 224 `#check` y 0 errores.
- **Anexo:** 50/50 PASS; 633 declaraciones auditadas con axiomas estándar.
- **Identidad:** los 607 oleans son idénticos byte a byte a los del autor.

**Huella de axiomas.** No son teoremas distintos:
- 461 *registros* de axiomas según la regla del autor, de los cuales 314 son salidas de `#print axioms` y el resto líneas de auditoría repetidas.
- 18 declaraciones principales con `#print axioms` = {propext, Classical.choice, Quot.sound}.
- Conos propios de 50 declaraciones públicas: 0 axiomas no estándar, 0 `sorryAx`, 0 constantes `Erdos81`.

`E4_main/SUMMARY.json` fue sobrescrito por la invocación de AuditorChecks: ahora dice «555 planned» y solo lista AuditorChecks. **No se usa** como evidencia.

**Por qué sigue valiendo para r2.**
- r2 no toca Lean.
- E0 confirma, al inicio y al final, las 615/615 entradas, el ZIP de fuentes igual al manifiesto, el anexo y los registros de run_v1.2_r1 sin cambios.
- El script documental (idéntico al de r1) reproduce exactamente el mismo resultado.

**No se ejecutó en r2 ningún build nuevo ni un replay independiente del kernel.**

## 6. E5 y E8: pruebas, controles y recuentos

**E5.**
- Inventario de comprobaciones:
  - T01–T24 de run_v1.2_r1: 24 pruebas con controles negativos predeclarados. La verificación del certificado Certo confirma una partición exacta de K3∨I3 en 6 piezas, solo como factibilidad.
  - 21 comprobaciones exactas de v1.21.
  - 14 de C.3 (r1), más el control negativo corregido de C3m y 6 controles negativos complementarios.
- En total, 59 comprobaciones distintas y 7 controles añadidos. Las repeticiones de r2 dan resultados idénticos y **no se suman** como pruebas nuevas.
- Las comprobaciones sobre rangos finitos son regresión, no prueba universal; la prueba universal está en E2 y en E19.

**E8.**
- El barrido de 1266 logs = 608 + 50 (auditor) + 422 + 186 (segmentos del autor) es del auditor de run_v1.21_r1. El barrido antiguo del autor cubría 844 = 1266 − 422 y omitía el segmento 1 (E8-01).
- r2 repitió el mismo barrido con resultado idéntico (0 alertas). Cuenta una sola vez.
- **X-28 sigue MITIGADO:** los runners congelados mantienen un patrón insuficiente, su hash no cambió y el parche no se aplicó. La mitigación es el detector externo (10/10 casos) más los conos de axiomas.
- **R-01 sigue como limitación:** las cotas de segundo momento de C.2 se citan.

## 7. Comprobaciones nuevas de r2

- **X-15.** La prosa española de r1 tenía 11 «matching(s)» y 1 «packing»; en r2 no queda ninguno.
  - Las 4 apariciones que permanecen son títulos citados ([6], [7], [9], [12]) y no se tradujeron, como corresponde. No hay ninguna en identificadores.
  - **Discrepancia de recuento resuelta:** el «×12 matching(s)» de los informes anteriores era un error del auditor. Contaba la referencia [9], y el escaneo no detectaba la forma plural. El recuento correcto es 11 + 1 (CORRECTIONS C3-01).
  - **CERRADO.**
- **NEW-01.** `Model` en monoespaciado en §7.2: MD l.1203, TeX l.1084 y PDF p. 35 (140 dpi). **CERRADO.**
- **Diff completo.** Mi diff coincide byte a byte con `CHANGES_es.diff`. Hay 13 cambios de palabra en 11 líneas, idénticos en MD y TeX.
  - Display (237), en línea (1989), bloques de código (5), etiquetas (146) y referencias: idénticos.
  - Ninguna línea cambiada es un enunciado; una está dentro de una demostración (Lema 5.3).
- **El PDF corresponde al TeX.** El texto del PDF r2 coincide con el de r1 tras las sustituciones del inventario, salvo 3 diferencias tipográficas verificadas visualmente:
  - espaciado de una línea matemática en p. 55;
  - la Tabla 9, que ahora cabe en una sola página.
  - El log está limpio (0 Overfull, solo 5 Underfull) y el preámbulo es idéntico.
- **Páginas.**
  - Cambian 18 páginas en raster (16, 18, 20, 21, 35, 55, 56, 61–71); coincide con la lista del editor.
  - Revisé las 73 páginas. Las páginas 55, 56 y 61–71 se compararon además lado a lado r1|r2, revisando los desplazamientos; no hay texto perdido ni duplicado, y las referencias siguen empezando en p. 72.
  - Las comparaciones r1|r2 de las páginas 16, 18, 20, 21 y 35 no llegaron a mostrarse (C3-02). Esas páginas se verificaron en las hojas r2 y, la 35, también a 140 dpi.
- **NEW-03.** La rectificación explícita del editor y el artefacto corregido cierran el hallazgo. La respuesta r1 y el hallazgo histórico se conservan. **CERRADO.**
- **Impacto en E1, E2, E3 y E7.** Ninguna conclusión previa cambia (§2).

## 8. Hallazgos: lista completa y estado actual

Hay 49 filas en `FINDINGS.csv`: todas las históricas conservadas más 4 nuevas.

- **Cerrados (27):**
  - X-01, X-02, X-03 y X-04 (MODERATE), cerrados en v1.21.
  - X-05, cerrado en v1.22-r1.
  - X-06…X-11 y X-13, X-14, X-16 (MINOR), cerrados en v1.21; X-12, en v1.22-r1.
  - X-15, en v1.22-r2.
  - X-20, X-21, X-23 y X-25 (OBS).
  - X-27 (MODERATE), cerrado por declaración en v1.21: el código Lean no cambió y la declaración se conserva.
  - NEW-01 (v1.22-r2), NEW-02 (v1.22-r1), NEW-03 (v1.22-r2), R-02 (v1.22-r1), E8-01 y E8-03 (v1.22-r1).
  - Responsables: el editor o autor corrigió el texto; el auditor verificó en la revisión indicada.
- **Mitigado (1):** X-28, el detector de los runners congelados.
- **Observaciones aceptadas (8 vigentes + NEW-04):**
  - X-17 (Prop. 6.3a, existencial en Lean) y X-18 (τ real).
  - X-19 (residuo del lakefile) y X-22 (desacuerdo interno/externo sobre A.2, conservado).
  - X-24 (constantes opcionales no adoptadas) y X-29 (reproducción en dos tramos del autor).
  - R-01 (segundo momento citado) y E8-02 (alcance del parche).
  - **NEW-04 (nueva).** El texto histórico de estado del manuscrito (ES/EN p. 1, §7 «Estado de auditoría», nota de la Tabla 7 y alcance de A.2) dice que las ampliaciones de v1.22 «esperan revalidación». Responsable: el editor, antes de publicar.
- **Información:** X-26, sobre independencia.
- **Correcciones conservadas (11):**
  - del proceso v1.2: AUD-P1, AUD-C1 y AUD-C2;
  - del auditor en r1: C2-01 a C2-08;
  - del auditor en r2: C3-01 (recuento), C3-02 (filas de inspección no vistas, descartadas) y C3-03 (ruta de salida de un script).

## 9. Independencia y límites

- **Auditor:** Claude Opus 5.5 (`claude-opus-5-5`), proveedor Anthropic.
- **Sesión:** esta revalidación es **continuación de la misma sesión de Claude Code** que produjo run_v1.2_r1, run_v1.21_r1 y run_v1.22_r1, con compactación de contexto. **No es una sesión nueva, no es ciega y no es independiente de familia.** El manuscrito declara el uso de Claude (Anthropic): misma familia.
- **Lecturas:** leí la evidencia previa y los documentos del editor, contrastándolos con la mía. Las lecturas están en `00_CONTROL/INPUT_ACCESS_LOG.csv`. La restricción de lectura es operativa, no un aislamiento técnico.
- **Entorno:** misma máquina y misma caché Mathlib compartida que en el build histórico. En r2 no hubo ejecución dinámica nueva de Lean: sin build, sin replay del kernel y sin leanchecker. Solo scripts Python de solo lectura.
- **Alcance de la revisión escrita:** la comprobación de las demostraciones es a nivel de resumen ejecutable frente a enunciados formales congelados. **No sustituye la revisión humana por pares.**
- **Inspección visual:** hojas a 90 dpi, comparaciones a 110 dpi y zoom a 140 dpi. Algunas imágenes no llegaron a mostrarse, y esas filas se descartaron (C3-02).

## 10. Veredicto razonado y pendientes reales

**PASS_WITH_OBSERVATIONS** para el paquete v1.22-r2.

**Qué certifica esta revisión consolidada:**
- la identidad exacta del paquete revisado;
- que las correcciones españolas pedidas están aplicadas y no alteran el contenido protegido;
- que el PDF corresponde al TeX;
- que el inglés y el corte Lean son los mismos que se auditaron;
- que los PASS de E1–E5 y E7 siguen enlazados por identidad a su evidencia original;
- que no queda ningún hallazgo MINOR o superior abierto.

**Qué no certifica:**
- no es una revisión por pares humana ni una verificación independiente de familia o sesión;
- no hay un build nuevo ni un replay del kernel;
- no prueba la novedad universal;
- no autoriza publicar;
- no cubre semánticamente, fila por fila, las entradas de la Tabla 7 enumeradas en §4.1.

**Pendientes reales:**
1. **Antes de publicar**, actualizar el texto histórico de estado en ambos idiomas (NEW-04). Esto rompe la identidad byte a byte del inglés y exige un control de identidad y un E6 nuevos.
2. Las observaciones aceptadas siguen vigentes (R-01, X-28, X-17, X-18 y demás).
3. Una revisión por pares humana y, si se quiere independencia real, una auditoría de otra familia de modelos en una sesión separada, con un build de sala limpia o un replay del kernel.

**Texto histórico de estado.**
- Las menciones de los manuscritos («la revalidación de 1.21…», «esperan revalidación», «espera una nueva revisión») describen el estado anterior a run_v1.22_r1. No son el estado actual del paquete; el estado actual es el de este informe.
- Mientras el paquete sea un candidato de revisión, no causan un error matemático ni de correspondencia.
- **Sí son un problema editorial real si se publica tal cual**, porque el lector creería que C.3 no está revisado.

## 11. E0 final y sellado

- **E0 final:** `20_EVIDENCE/E0/E0_FINAL.json`. Su objeto `checks` es idéntico al del inicial (resultado detallado en `20_EVIDENCE/logs/E0_final.log`).
- **Paquete:** `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r2.zip`, con este informe, su PDF, SUMMARY, FINDINGS, la matriz, los registros, los scripts, las salidas, las imágenes de E6 y `RUN_MANIFEST.json`. Los ZIP históricos no se duplican: se enlazan por ruta y hash (§1).
- **Generación del PDF:** pandoc (Markdown → HTML y TeX independiente) más PyMuPDF Story (HTML → PDF). **No se compila desde TeX**, el mismo método declarado en las ejecuciones anteriores. El PDF se revisó visualmente.
- **Sin efectos externos:** nada se publicó, se hizo push ni se envió a terceros. No se modificaron el manuscrito, los originales ni las revisiones anteriores.
