# Paper IV v1.22-r1 — revalidación acotada posterior a v1.21

Estado: preparada para envío; no ejecutada por el editor. No autoriza publicación.

## 1. Objetivo e insumos

Raíz: `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/`.

Objetivo: `01_manuscript/v1.22_editorial_candidate/`, identificado por `MANUSCRIPT_REVIEW_MANIFEST.json`, su SHA-256 y `PAPER_IV_v1.22_REVIEW_PACKAGE_r1.zip`. El archivo `AUDIT_TARGET_v1.22.json`, junto a este mandato, vincula los insumos finales y la evidencia reutilizada. Si falta esa identidad o no coincide, deténgase antes de revisar.

Comparación editorial: v1.21, no v1.2. El informe inmediato anterior es `02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/30_REPORT/FINAL_REVALIDATION_REPORT.md`, con su SUMMARY, FINDINGS, evidencia y paquete sellado. Conserve también `run_v1.2_r1`, origen del build externo PASS.

Lecturas permitidas: este objetivo, los manuscritos v1.21 de comparación, ambas auditorías y sus insumos expresamente identificados, el corte `05_formalization/lean_piv-v12-fb459343d234`, el anexo formal identificado, las dependencias fijadas necesarias y la literatura citada. No consulte árboles de investigación `ar_*`, `handoff_*`, b=0, otros Papers no declarados, chats ni credenciales. Registre todos los archivos adicionales que llegue a consultar y explique por qué. No cambie insumos ni evidencia histórica.

Declare modelo/familia, si la sesión es nueva o continuación, exposición previa y lecturas reales. El auditor de v1.21 declaró continuación en la misma sesión de v1.2; no lo redescriba como sesión nueva. Una sesión separada de la investigación y una familia de modelos diferente son garantías distintas. Esta revisión consulta evidencia previa y no es ciega. La restricción de lectura es operativa, no aislamiento técnico.

## 2. Prohibición de recompilación

**No ejecute Lean, Lake, leanchecker ni otro build, completo, parcial o de negativos. No instale otro Mathlib, modifique pines, borre cachés ni altere objetos compilados.**

Verifique las 615 entradas del manifiesto de fuentes y la identidad de los paquetes previos. E4 sólo se conserva como `PASS — reused_verified_external_build` si confirma la evidencia: 607 módulos principales, 19 targets, 224 controles de exportación y 50 módulos del anexo. El ciclo nuevo no recompila. Para la evidencia inicial, no confíe únicamente en `E4_main/SUMMARY.json`, sobrescrito históricamente por AuditorChecks: use consola, `records.jsonl`, registros completos, E4_RECORD y los manifiestos sellados.

Una diferencia de fuentes o una insuficiencia formal nueva exige STOP/INCONCLUSIVE y consulta al propietario; no habilita un build automático.

## 3. Orden y comprobaciones

E0 inicial → E2 focalizado → E6 → regresiones E1/E3/E7 → E5/E8 pertinentes → E0 final y confirmación documental E4.

Primero examine el texto nuevo y las fuentes; después contraste la respuesta autoral. Los informes del editor no son un PASS heredado.

### E2: cerrar o mantener abierto A2-4 / X-05

En C.3, compruebe bloque por bloque:

1. La definición de I(ε,k₀), H(ε), t₀, t_{j+1} y B coincide con `SzemerediRegularity.initialBound`, `stepBound` y `bound` de Mathlib fijado.
2. En η₀, la desigualdad racional que controla el logaritmo da I=k₀; H coincide exactamente con h de §6.3. Contraste `E18.Numeric.initialBound_eq`, `floor_iter_eq` y `BE_eta0`.
3. El límite inferior tras dos iteraciones domina los tres G_i; no se afirma que dos pasos basten para la regularidad.
4. La sustitución en los cinco términos de C.1, incluidos los techos y la unidad final, coincide con `E18.Numeric.NfarE_eta0_le`. Compruebe particularmente la cota racional del cuarto término.
5. La cuenta B⁶/4 + 7B² ≤ B⁶ y la inducción 4t_j ≤ T(j+5) justifican el límite T(h+7). Contraste `E19.absorb_abstract`, `four_mul_Tnum_le`, `B6_le_two_pow_two_pow` y `NfarE_eta0_le_tower`.
6. La remisión de A.2 ahora apunta a C.3 y no a una recurrencia inexistente en §6.3. Valore si la exposición permite reconstruir realmente la cuenta sin delegarla a nombres de teoremas.

Las otras seis filas de A.2 pueden reutilizar su aceptación previa si el diff confirma que no se alteraron. En C.2 revise la aclaración R-02 de todos los perfiles que contienen el par. Mantenga R-01 como límite expositivo declarado, salvo que encuentre una razón nueva para elevarlo.

### E6 y regresiones

- ES/EN: coteje todas las fórmulas añadidas y los pasajes de C.3; no cambian los enunciados, constantes finales ni etiquetas.
- Revise los MD, TeX y PDF finales, no renders anteriores. Cubra todas las páginas con inspección visual y examine con resolución legible las cambiadas, los identificadores, la figura de estabilidad y la bibliografía.
- X-12: `E34.lemma3`/`E34.transfer` como identificadores. NEW-01: Regularization/Nibble descriptivos y Model como namespace. X-15: emparejamientos/empaquetamiento en prosa, valor base en la figura; no traduzca títulos citados.
- NEW-02: título original de [6] restaurado. Ortografía Preference Labs. No cambie ni amplíe el resultado de la auditoría bibliográfica anterior sin nueva evidencia.
- Compruebe la conservación de la declaración de dependencias X-27 y del alcance real de independencia. Los wrappers E32 históricos siguen declarados; no se cambió Lean.
- E5: puede repetir el script aritmético o producir uno propio, incluidos negativos, sin ejecutar Lean. Distinga regresión finita de prueba universal.
- E8: conserve la ampliación del barrido a 1266 logs hecha por el auditor anterior, no atribuya todo ese alcance al script antiguo del autor. El parche propuesto para los runners no se ha aplicado. La carpeta nueva sólo debe contener un paquete editorial vigente.

## 4. Resultados y criterio de cierre

Escriba en una ejecución nueva:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r1/`

Use `00_CONTROL`, `10_LOGS`, `20_EVIDENCE`, `30_REPORT`, `40_PACKAGE`. Si ya hay una ejecución, reanúdela sin borrar evidencia ni iniciar un segundo trabajo. Entregue reporte general y por puerta en MD/PDF, SUMMARY.json, FINDINGS.csv, scripts/entradas/resultados nuevos, manifiesto y ZIP con hash. Identifique lo repetido, lo heredado y por qué la identidad permite heredarlo; no haga pasar una reutilización por un nuevo build. Actualice la matriz de hallazgos, sin eliminar limitaciones ni incidencias históricas.

Emita PASS sólo si el contenido lo justifica. Observaciones no bloqueantes pueden acompañarlo. Si queda una derivación obligatoria insuficiente, mantenga INCONCLUSIVE con ubicación y paso preciso. Si hay un bloqueo, deténgase y selle un informe parcial; ante un corte de tiempo, registre inmediatamente INCONCLUSIVE en las puertas no completadas. No repare el manuscrito por su cuenta ni altere sus hashes durante la revisión.

No publique, haga push, cree tags/DOI ni envíe datos a terceros. El encargo es revisar y emitir un nuevo veredicto, no conseguir un resultado prefijado.
