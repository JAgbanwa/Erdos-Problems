# Paper IV v1.22-r3 — Informe final consolidado de auditoría externa adversarial (E0–E8)

**Ejecución:** `run_v1.22_r3`. Se completó el 2026-10-01, con inicio a las 14:52:23 UTC y el E0 inicial a las 14:53:23 UTC; el E0 final está en la §11. La solicitó el propietario en el chat con el mandato `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r3.md`.

**Veredicto global actual: PASS_WITH_FINDINGS.**
- Todas las comprobaciones del encargo se completaron.
- NEW-04 (estado documental desactualizado) queda cerrado. Quedan cerradas también la acción de control de X-28 y el hallazgo E8-02.
- Se añaden 12 filas semánticas nuevas, todas MATCH.
- Queda abierto **un hallazgo MINOR nuevo, NEW-05**: dos términos españoles introducidos en los párrafos reescritos en r3. Exige una corrección de dos palabras antes de publicar.
- No hay ningún defecto matemático, formal ni de identidad.
- Siguen vigentes siete observaciones aceptadas, que son límites documentados y no exigen acción, más la mitigación X-28.
- Esta revisión no sustituye una revisión por pares ni autoriza la publicación.

---

## 1. Identidad actual

| Objeto | Ruta | SHA-256 |
|---|---|---|
| Objetivo r3 | `02_validation/02_IA_ADVERSARIAL_AUDITS/AUDIT_TARGET_v1.22_r3.json` | `df89c3dd33df19be5ddc4a42afaf5dd9053977623c7bc2a30fd12143b1044970` (coincide con su sidecar) |
| Mandato r3 | `…/EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r3.md` | `abfcaec9ae3ce5759b4177e0152bcd570e7ee31bb15e3f3df53553e6fb50d92f` |
| Manuscrito | **versión 1.22**, paquete **r3**, en `01_manuscript/v1.22_editorial_candidate_r3/` | — |
| Manifiesto r3 (226 archivos) | `MANUSCRIPT_REVIEW_MANIFEST.json` | `82217fe36719f4d2373bd63d30eb4efdb68e70b3ad95ef2f98217d3a6a5765bb` |
| ZIP r3 (228 miembros, CRC correcto) | `PAPER_IV_v1.22_REVIEW_PACKAGE_r3.zip` | `c1acd8669d6cbcd89f7835933130416ae716c407250c5e690e5cf64fa837d2ec` |
| ES MD / TeX / PDF (73 p.) | `PAPER_IV_preprint_v1.22_es.*` | `81db7bbb…` / `17c1306d…` / `d1048a62…` |
| EN MD / TeX / PDF (72 p.) | `PAPER_IV_preprint_v1.22_en.*` | `d3415df3…` / `c6b14105…` / `4280b03e…` |
| Figuras (18 archivos) | `figures/`, `figures_en/` | idénticas a r2 |
| Freeze Lean (615 entradas) | `05_formalization/lean_piv-v12-fb459343d234/` | manifiesto `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5` |
| ZIP de fuentes Lean (615 miembros) | `05_formalization/LEAN_SOURCE_piv-v12-fb459343d234.zip` | `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6` |
| Anexo (40 miembros) | `05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip` | `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d` |
| Paquetes históricos | `run_v1.2_r1/…/EXTERNAL_AUDIT_run_v1.2_r1.zip` | `886ed7f0…f5e2b` |
| | `run_v1.21_r1/…/EXTERNAL_REVALIDATION_run_v1.21_r1.zip` | `11659a97…7a638` |
| | `run_v1.22_r1/…/EXTERNAL_REVALIDATION_run_v1.22_r1.zip` | `9c74d673…193a1fa` |
| | `run_v1.22_r2/…/EXTERNAL_REVALIDATION_run_v1.22_r2.zip` | `626571be…1e480684` |

Notas sobre la identidad:
- Los hashes completos están en `20_EVIDENCE/E0/E0_INITIAL.json`.
- En r3 cambian el inglés y el español, como declara el editor. **No se exige ni se afirma identidad byte a byte del inglés con r2.** Lo que sí se exige y se verifica es la identidad del contenido protegido (E6), de Lean y de las figuras, y que los antecedentes no hayan cambiado.

## 2. Veredictos actuales E0–E8

| Puerta | Veredicto actual | Alcance | Base | Procedencia | Evidencia |
|---|---|---|---|---|---|
| E0 | **PASS** | identidad completa | **ejecutado en r3** (inicial y final) | run_v1.22_r3 | `20_EVIDENCE/E0/E0_INITIAL.json`, `E0_FINAL.json` |
| E1 | **PASS** | 21 filas históricas + 12 nuevas | **heredado y revalidado por identidad** (21) + **ejecutado en r3** (12) | run_v1.2_r1 E1; run_v1.22_r3 | `30_REPORT/CLAIM_MAP_CONSOLIDATED.md`; `20_EVIDENCE/E1/E1E3_HEADERS_CHECK.json` |
| E2 | **PASS** (observación R-01) | 56 componentes; las siete filas de A.2 | **heredado y revalidado por identidad** | A2-1/2/7: v1.2; A2-3/5/6: v1.21; A2-4: v1.22-r1 | `E2_RECORD.md` de run_v1.2_r1, run_v1.21_r1 y run_v1.22_r1 |
| E3 | **PASS** | cabeceras, identificadores, X-27 | **heredado y revalidado por identidad** + cabeceras estáticas **ejecutadas en r3** | run_v1.2_r1 → r3 | `20_EVIDENCE/E3/E3_RECORD.md` |
| E4 | **PASS — reused_verified_external_build** | 607 módulos, 19 targets, 224 export checks, 50 módulos del anexo | **heredado y revalidado por identidad**; **sin build nuevo ni replay del kernel** | build de run_v1.2_r1 (2026-09-30, 15:09–21:33 UTC) | consola `ef5b01c7…`, records `0f2d8495…`, anexo `57ce1895…`; `20_EVIDENCE/E4/E4_REUSE_CHECK.json` |
| E5 | **PASS** | 59 comprobaciones + 7 controles | **heredado y revalidado por identidad** | v1.2, v1.21, v1.22-r1 | `20_EVIDENCE/E5/E5_RECORD.md` |
| E6 | **PASS_WITH_FINDINGS** (NEW-05) | delta EN+ES, 145 páginas, PDF frente a TeX | **ejecutado en r3** | run_v1.22_r3 | `20_EVIDENCE/E6/E6_RECORD.md`, `E6_R3_DELTA.json`, `PAGE_INSPECTION_LOG.csv` |
| E7 | **PASS** | bibliografía y atribución | **heredado y revalidado por identidad** (referencias idénticas) | v1.2 → r2 | `20_EVIDENCE/E7/E7_RECORD.md` |
| E8 | **PASS_WITH_OBSERVATIONS** (observación histórica X-28) | verificador suplementario, 1266 logs, alcance 1266/844 | **ejecutado en r3** + atribución heredada | run_v1.21_r1 (barrido); run_v1.22_r3 | `20_EVIDENCE/E8/E8_RECORD.md`, `E8_R3_CHECK.json` |

La matriz por puerta (veredicto en cada revisión, comprobación nueva, evidencia heredada y enlace de identidad) está en `30_REPORT/TRACEABILITY_MATRIX.csv`.

## 3. Historial original de veredictos

Los veredictos INCONCLUSIVE se conservan como veredictos de sus revisiones; no se reescriben.

| Revisión | Ejecución | Veredicto global original | Puertas no PASS |
|---|---|---|---|
| v1.2 | run_v1.2_r1 (2026-09-30) | **INCONCLUSIVE** | E2 INCONCLUSIVE (A2-3, A2-4, A2-5, A2-6); E3/E6/E8 PASS_WITH_FINDINGS; E7 PASS_WITH_MINOR_FINDINGS |
| v1.21 | run_v1.21_r1 | **INCONCLUSIVE** | E2 INCONCLUSIVE (A2-4); E1 PASS_WITH_MINOR; E6 PASS_WITH_FINDINGS; E8 PASS_WITH_OBSERVATIONS |
| v1.22-r1 | run_v1.22_r1 | **PASS** con hallazgos MINOR no bloqueantes | E6 PASS_WITH_FINDINGS; E8 PASS_WITH_OBSERVATIONS |
| v1.22-r2 | run_v1.22_r2 | **PASS_WITH_OBSERVATIONS** | E6, E8 PASS_WITH_OBSERVATIONS |
| v1.22-r3 | **run_v1.22_r3** | **PASS_WITH_FINDINGS** | E6 PASS_WITH_FINDINGS (NEW-05); E8 PASS_WITH_OBSERVATIONS |

Todos los PASS históricos siguen siendo aplicables a r3, porque la identidad está verificada:
- E1, E3, E5 y E7 de run_v1.2_r1;
- el build de E4;
- las aceptaciones de A.2 de v1.21 y v1.22-r1;
- el cierre de X-15, NEW-01 y NEW-03 en r2.

## 4. Mapa de afirmaciones y cobertura matemática

El mapa completo está en `30_REPORT/CLAIM_MAP_CONSOLIDATED.md`. Tiene dos tipos de filas:
- **H**: las 21 filas históricas de run_v1.2_r1. Todas son MATCH salvo G.2, que en v1.2 quedó «no re-extraída» y ahora cubren N11 y N12.
- **N**: 12 filas **nuevas de r3, diferenciadas**. No estaban en el E1 original.

Filas nuevas:

| Fila | Afirmación | Declaración | Veredicto |
|---|---|---|---|
| N1 | Teorema 5.0, ventana reforzada | `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp` | MATCH |
| N2 | Teorema 5.0, interfaz anterior | `…exists_near_partition_paid_by_root` | MATCH |
| N3 | Corolario 5.4, geometría (5.17) | `NearCriticalDichotomy.chordal_far_or_criticalRoot` | MATCH. Lean es algo más fuerte: añade \|\|R\|−\|C\|\| ≤ n/100, que es diferencia de tamaños, no diferencia simétrica. No se afirma que C sea clique de G. |
| N4 | Corolario 5.4, densidad (5.18) | `…chordal_far_or_edge_density` | MATCH, tomando el máximo de ambos umbrales |
| N5 | Dicotomía (1.5) | `HybridDichotomy.chordal_far_or_nearStructure` | MATCH. Los campos de `NearStructureWitness` contienen el comparador, una raíz que es clique (`RegularizedRoot.isClique`), el empaquetamiento del grafo original y las cuentas. |
| N6, N7 | Optimalidad del coeficiente cuadrático | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `…_isLeast` | MATCH. El caso real se obtiene por ampliación racional, argumento válido. |
| N8 | Optimalidad del coeficiente lineal | `LinearCoefficient.linear_coefficient_optimal` | MATCH. Observación de tipo X-17: la cabecera es existencial en G. |
| N9 | Identidad (6.7b) | `RootPartitionStability.sum_rootPieceDefect_eq` | MATCH |
| N10 | Proposición D.3 | `SplitMixedGap.mixed_gap_zero` **y** `SplitCompleteSharpValue.exists_sharp_cliquePartition_allParities` | MATCH. Hacen falta ambas declaraciones más (1.3a). |
| N11, N12 | G.2 / Proposición G.1 | `FarExploration.CleanupRigidVerdict.threshold_gt_exp`, `…_seventy_two` | MATCH. Cierra el «no re-extraída» histórico de G.2. |

Cómo se verificaron las 13 cabeceras:
- Coinciden con los fuentes congelados (hash de manifiesto, línea, texto reextraído, namespace y variables en alcance) y con los logs del build externo (hash, módulo PASS, salida 0).
- Son extracciones estáticas, **no tipos elaborados nuevos**.

**Las siete derivaciones de A.2**:
- A2-1 «§5.1, (5.4) y (5.7)»: ACCEPTABLE_SUMMARY desde v1.2.
- A2-2 «C.2, (3.8) y (3.10)»: ACCEPTABLE_SUMMARY desde v1.2.
- A2-3 «Lema 3.2 y C.1–C.2»: REQUIRES_EXPANSION en v1.2; ACCEPTABLE_SUMMARY desde v1.21.
- A2-4 «C.3, Tabla C.1»: REQUIRES_EXPANSION en v1.2 y v1.21; ACCEPTABLE_SUMMARY desde v1.22-r1.
- A2-5 «E.1»: ACCEPTABLE_SUMMARY desde v1.21.
- A2-6 «E.1, (E.2b), (E.2d)»: ACCEPTABLE_SUMMARY desde v1.21.
- A2-7 «D.1»: ACCEPTABLE_SUMMARY desde v1.2.

**R-01** (cotas de segundo momento citadas en C.2) sigue vigente como límite expositivo declarado.

**Límite de la revisión escrita:** es una comprobación a nivel de resumen frente a enunciados formales congelados, no una revisión humana por pares.

## 5. E4: evidencia formal

**Lo que se hizo** (run_v1.2_r1, intento 2):
- Runner propio del auditor, sin Lake. Lean 4.28.0, fuentes extraídas del ZIP (615/615) y objetos nuevos. Mathlib compartido en solo lectura, con la caché de 113 821 archivos sin cambios.

**Registros originales:**
- Consola: `modules_planned 607, pass 607`, sin fallos, 607 líneas `PASS n 607`, `EXIT 0`, y los 19 targets en PASS.
- `records.jsonl`: 608 filas, todas PASS con salida 0.
- `ReleaseExportCheck`: 224 `#check` y 0 errores.
- Anexo: 50/50 PASS, con 633 declaraciones y axiomas estándar.
- Los 607 oleans son idénticos byte a byte a los del autor.

**Axiomas** (no son teoremas distintos):
- 461 *registros* de axiomas, de los cuales 314 son salidas de `#print axioms`; el resto son repeticiones.
- `#print axioms` sobre **18 declaraciones principales**: siempre {propext, Classical.choice, Quot.sound}.
- **Conos de 50 declaraciones públicas**: 0 axiomas no estándar, 0 `sorryAx` y 0 `Erdos81`.

El `SUMMARY.json` de E4_main, sobrescrito por AuditorChecks, **no se usa**.

**Validez en r3:** r3 solo cambia prosa documental. E0 confirma que Lean, el ZIP de fuentes, el anexo y la evidencia de run_v1.2_r1 no han cambiado, y el script documental (sha `db2eddb8…`) da un resultado idéntico al de r2. **No se ejecutó un build nuevo ni un replay del kernel.**

## 6. E5 y E8

**E5:**
- 59 comprobaciones distintas: T01–T24, 21 de v1.21 y 14 de C.3. A ellas se suman 7 controles negativos añadidos, todos rechazados.
- Las repeticiones no se suman como pruebas nuevas.
- Las pruebas finitas y el certificado Certo (partición exacta de K3∨I3 en 6 piezas, solo factibilidad) no sustituyen las pruebas universales.
- Los controles del lector de logs pertenecen a E8 y no prueban teoremas.

**E8, el verificador suplementario `verify_frozen_logs.py`:**
- Funciona con cierre seguro: un log ausente, sobrante, con hash distinto o con alerta lo hace fallar, igual que un recuento distinto de 1266.
- Lo repetí en su sitio con salida propia: **PASS, 1266 logs**.
- Lo repetí en una copia de prueba, cuyo único cambio es la ruta raíz: **15/15 casos unitarios y 4/4 corrupciones de CLI** con salida 1. El inventario y los casos coinciden con lo sellado, y el paquete no se sobrescribió.
- **E8-02:** la regla de errores es literalmente la alternativa histórica de `audit_publication.py`, sensible a mayúsculas, sin `re.I`. El refuerzo de sorry va en una regex separada. **Cerrado.**
- **Cuatro agrupaciones:** 608 + 50 (auditor) + 422 + 186 (autor) = **1266 archivos, no 1266 pruebas**. Se cuentan una sola vez aunque se barrieron en v1.21, en r2 y dos veces en r3. El barrido antiguo del autor cubría 844 = 1266 − 422 (E8-01).
- **Matiz histórico:** la regla congelada detecta el log negativo real solo por `sorryAx` en la impresión de axiomas, no por el aviso de `sorry`, que lleva backticks. `paperiv_build.py` no lo detecta.

**X-28:**
- La acción de control de la entrega queda **cerrada**: el verificador es un control obligatorio del perfil de reproducción r3.
- Se mantiene la **observación histórica**: los runners congelados conservan su patrón insuficiente y no se afirma que se hayan parcheado.
- La evidencia de axiomas y conos (18 declaraciones y 50 conos) sigue siendo el control sustantivo.

## 7. NEW-04 y paridad (E6)

Hay cinco párrafos documentales por lengua: portada, §7, la nota de la Tabla 7, A.2 y F.4. Los comparé íntegramente con la evidencia de r2. **C.3 y las siete filas de A.2 ya no figuran como pendientes**, y el estado de r2 se describe como PASS_WITH_OBSERVATIONS, sin inventar un PASS limpio. Se conservan los INCONCLUSIVE históricos y los límites. **NEW-04 queda CERRADO.**

Esos párrafos son registros fechados de r2. El dictamen sobre r3 es este informe; no hace falta editar el manuscrito retroactivamente.

Comprobaciones:
- **Contenido protegido idéntico en EN y ES:** fórmulas en display y en línea, etiquetas, bloques de código, filas de tablas, encabezados, imágenes y bibliografía. Los dos códigos en línea añadidos son nombres de ejecuciones.
- **Diffs:** el diff del editor coincide con el del auditor.
- **El PDF corresponde a su TeX:** todas las regiones de diferencia en el texto extraído se explican por los párrafos cambiados.
- **Páginas:** cambian EN 1, 33, 39, 40 y 64, y ES 1–6, 34–36, 39, 40 y 66. Revisé visualmente las 145 páginas.

**NEW-05 (MINOR, nuevo).** El español reescrito en r3 usa dos términos distintos de los ya establecidos en el manuscrito:
- «programación numérica de C.3» en A.2 (l.1355), cuando el texto usa «calendario numérico» y el encabezado de C.3 es «Un calendario explícito»;
- «cota adaptada con muestra fijada» en F.4 (l.2356), cuando F.5 y la Tabla 10 dicen «muestras con anclajes».

**Acción antes de publicar:** restituir esos dos términos y repetir el control de identidad ES y E6.

## 8. Hallazgos: estado actual

`FINDINGS.csv` tiene 53 filas: todas las históricas, más NEW-05 y las correcciones del auditor C4-01, C4-02 y C4-03.

| Clase | IDs | Acción antes de publicar |
|---|---|---|
| **Abierto** | NEW-05 (MINOR) | **Sí:** dos términos en ES |
| **Cerrados (29)** | X-01…X-16, X-20, X-21, X-23, X-25, X-27, NEW-01…NEW-04, R-02, E8-01, E8-02, E8-03 | ninguna |
| **Mitigado** | X-28 | ninguna, siempre que el perfil de reproducción mantenga obligatorio el verificador |
| **Observaciones aceptadas (7)** | X-17 (ahora también N8), X-18, X-19, X-22, X-24, X-29, R-01 | ninguna; son límites documentados o hechos históricos |
| **Información** | X-26 (independencia) | ninguna; se recomienda revisión humana por pares antes de decidir publicar |
| **Correcciones conservadas (14)** | AUD-P1, AUD-C1, AUD-C2, C2-01…C2-08, C3-01…C3-03, C4-01…C4-03 | ninguna |

Responsabilidades: el editor o autor corrigió los textos; el auditor verificó cada cierre en la revisión indicada en `FINDINGS.csv` (columna `revision_verified_r3`).

## 9. Independencia y límites

- **Modelo:** Claude Opus 5.5 (`claude-opus-5-5`), proveedor Anthropic.
- **Sesión:** esta revalidación es **continuación de la misma sesión** de Claude Code que produjo las cuatro ejecuciones anteriores, con compactación de contexto.
- **Independencia:** no es una sesión nueva, no es ciega y no es independiente de familia. El manuscrito declara el uso de Claude, que es la misma familia. Que haya continuidad entre revisiones no la convierte en independiente.
- **Lecturas:** leí la evidencia previa y los documentos del editor, y los contrasté con evidencia propia. Todo está registrado en `00_CONTROL/INPUT_ACCESS_LOG.csv`.
- **Entorno:** misma máquina y misma caché que el build histórico.
- **Ejecución:** no hubo ejecución dinámica nueva de Lean, ni build, ni replay del kernel. Se ejecutaron solo scripts Python de solo lectura y el verificador de logs del autor, en su sitio y en una copia.
- **Inspección visual:** hojas 4-up a 70 dpi y comparaciones a 105 dpi. Las imágenes que no pudieron confirmarse se volvieron a registrar desde hojas que sí se vieron (C4-01).

## 10. Veredicto razonado

**PASS_WITH_FINDINGS.**

**Por qué no es PASS limpio:** queda una acción abierta antes de publicar, NEW-05. Es menor, pero real, y es una incoherencia terminológica nueva introducida en r3. Por criterio del mandato no se emite PASS con acciones abiertas.

**Por qué no es INCONCLUSIVE ni FAIL:**
- todas las comprobaciones se completaron;
- no hay ningún defecto matemático, de correspondencia formal ni de identidad;
- NEW-05 no altera ningún enunciado ni ninguna prueba.

**Qué certifica esta revisión:**
- la identidad exacta del paquete r3;
- que el estado documental (NEW-04) es correcto y coherente con r2;
- que el contenido protegido es idéntico a r2 y que cada PDF corresponde a su TeX;
- que las 12 filas semánticas nuevas corresponden a sus declaraciones;
- que el verificador suplementario funciona y protege el perfil de reproducción;
- que los PASS históricos siguen enlazados por identidad a su evidencia original.

**Qué no certifica:**
- que el manuscrito esté listo para publicar mientras NEW-05 siga abierto;
- una revisión humana por pares;
- un build nuevo o un replay del kernel;
- independencia de familia o de sesión;
- novedad universal;
- autorización para publicar.

**Si solo se corrige NEW-05** y una revalidación documental confirma que únicamente cambiaron esas dos palabras en ES, no quedarían acciones abiertas. El veredicto podría ser entonces PASS, manteniendo explícitos los límites de la §9 y las siete observaciones aceptadas, que son límites de alcance y no defectos.

## 11. E0 final y sellado

- **E0 final:** `20_EVIDENCE/E0/E0_FINAL.json`. El objeto `checks` es idéntico al inicial (`20_EVIDENCE/logs/E0_final.log`).
- **Paquete:** `40_PACKAGE/EXTERNAL_REVALIDATION_run_v1.22_r3.zip`, con su `RUN_MANIFEST.json` y su sidecar SHA-256. Los ZIP históricos no se duplican; se enlazan por ruta y hash (§1).
- **PDF:** generado con pandoc (Markdown → HTML y TeX independiente) más PyMuPDF Story (HTML → PDF). **No se compiló desde TeX.** Se revisó visualmente (`30_REPORT/PDF_VISUAL_CHECK.csv`).
- **Sin efectos externos:** no se publicó nada, no se hizo push ni se enviaron datos a terceros. No se modificaron el manuscrito, los originales ni los informes previos.
