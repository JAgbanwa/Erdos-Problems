# Paper IV v1.21-r1 — solicitud de revalidación adversarial

**Estado: preparada; no iniciada.** Sustituye el mandato provisional `EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.21.md`. La ejecución anterior `run_v1.2_r1` terminó: INCONCLUSIVE global por cuatro derivaciones insuficientemente desarrolladas; E4 formal PASS. No se autoriza publicación.

## 1. Insumos e independencia

Raíz: `C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/`.

Objetivo editorial: `01_manuscript/v1.21_editorial_candidate/`, ambos idiomas en MD/TeX/PDF y figuras, identificados por `MANUSCRIPT_REVIEW_MANIFEST.json` y su ZIP. `AUDIT_TARGET_v1.21.json`, junto a este mandato, vincula los insumos y la evidencia externa final. Compare contra v1.2. Verifique las 615 entradas Lean y configuración del manifiesto `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`.

Lecturas permitidas: esos insumos, las fuentes congeladas, el informe externo anterior con toda su evidencia, la literatura citada y las dependencias fijadas necesarias. Excluya árboles `ar_*`, `handoff_*`, investigación b=0, Paper V no declarado, chats y credenciales. Liste toda consulta adicional. No modifique insumos ni registros históricos.

**Independencia de ejecución y diversidad de modelos son cuestiones distintas.** La revisión anterior fue una ejecución separada en una sesión nueva; según su declaración, no consultó los árboles de investigación excluidos ni resultados previos fuera de los insumos autorizados. Usar el mismo modelo o familia no anula esa separación operativa, pero tampoco equivale a una comprobación entre familias diferentes. La restricción de lectura fue operativa, no un aislamiento técnico del disco. Declare modelo, sesión, exposición previa y lecturas reales. Esta revalidación sí consulta el informe anterior: no se presenta como revisión ciega. Mantenga los límites de misma máquina y caché compartida.

## 2. Reutilizar E4; no ejecutar otro build

**No ejecute Lean, Lake, leanchecker ni recompilaciones totales, parciales o de controles negativos.** No instale otro Mathlib, cambie pines, borre cachés ni altere objetos compilados. El Lean no cambió. El nuevo detector de avisos es un suplemento externo al congelado que sólo examina registros existentes.

Valide la identidad y cobertura del E4 anterior: 607/607 módulos principales, 19 objetivos, 224 controles de exportación, 50/50 módulos del anexo, códigos de salida, registros, tipos y axiomas. Los 607 objetos principales fueron reproducidos byte a byte. Si lo confirma, conserve E4 PASS con método `reused_verified_external_build`; no diga «recompilado en este ciclo».

No confíe sólo en `10_LOGS/E4_main/SUMMARY.json`: el control posterior `AuditorChecks` sustituyó el resumen/plan de ese directorio, incidencia documentada por el auditor. Coteje `E4_main_console.log`, `records.jsonl`, registros de módulos, `E4_RECORD.md` y el paquete final. La vinculación de evidencia no sustituye su revisión.

Una discrepancia de fuentes, una evidencia insuficiente o un problema formal nuevo exige STOP/INCONCLUSIVE y solicitud de dirección al propietario; **no autoriza otro build**. Conserve la limitación de dependencias compartidas y ausencia de replay de kernel independiente.

## 3. Puertas y hallazgos a reexaminar

Orden: E0 → E2 → E3 → E7 → E6 → E1 → E5 → E8 → cierre documental E4. Primero evalúe los textos y fuentes; después contraste la respuesta autoral. Los controles del autor no son veredictos heredados.

- **E0:** identidades al inicio y al final, paquete nuevo y evidencia reutilizada.
- **E2:** rederive A2-3/4/5/6 y dictamine individualmente las siete filas de A.2. X-01: limpieza bilateral, carga por arista y retención (C.1–C.2); X-05: calendario, selector y comparación de torre (C.3); X-02: normalización (E.1/E.4); X-03: eliminación conjunta y error n/9 (E.2d). La formalización no sustituye decidir si ahora la prosa permite seguir cada derivación.
- **E3, X-27:** contraste §7, E.2, Tabla 9 y [23] con `AuditorASProbe.log`. `E32.cp_classification_of_theoremCPrimeC` y `E32.ref15Theorem11_of_theoremCPrimeC` todavía usan la cadena histórica de Alon–Shapira mediante `E32.theoremC_at`. No extienda a estas interfaces la exclusión comprobada para el Teorema C explícito y las declaraciones seleccionadas de estabilidad. Es una corrección de procedencia, no de Lean.
- **E7:** revalide X-06–X-11, atribución [15], localización frente a construcción final, dirección cp ≤ c₄, uso previo de L=4 y créditos [5]/Jacobian. Registre versiones consultadas y posteriores disponibles. No infiera originalidad bibliográfica de los conos.
- **E6:** revise ES/EN MD/TeX/PDF y todas las páginas finales: X-04 y X-12–X-16, terminología, referencias, figuras, subíndices, identificadores partidos, flechas, ⦃/⦄ y sangría.
- **E1:** verifique enunciados, hipótesis, constantes, etiquetas y bloques Lean; lea semánticamente los renombramientos descriptivos declarados y las ampliaciones.
- **E5:** revalide cuentas y negativos pertinentes sin compilar. El detector corregido debe reconocer el aviso real capturado con acentos graves, comillas y `sorryAx`.
- **E8, X-28:** examine `sorry_log_recheck.py`, `SORRY_RECHECK.json` y el parche externo propuesto. Los runners históricos permanecen intactos con su patrón insuficiente; la mitigación es el reescaneo y los conos de axiomas. Conserve la errata 314 + 147 = 461, el desacuerdo previo sobre exposición, las incidencias del auditor y el suplemento del anexo G.1. X-21/X-29: registre la reproducción byte-idéntica sin borrar la duda histórica.

## 4. Nuevo veredicto e informe

Resultados en una ejecución nueva, sin sobrescribir la anterior:

`C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.21_r1/`

Use `00_CONTROL`, `10_LOGS`, `20_EVIDENCE/E0...E8`, `30_REPORT`, `40_PACKAGE`. Entregue informes general y por puerta MD/PDF, SUMMARY.json, FINDINGS.csv, scripts, resultados, manifiesto y ZIP. Incluya matriz X-01–X-29 y AUD-P1/C1/C2 con evidencia y resolución. Distinga controles repetidos de evidencia reutilizada.

Observaciones informativas y limitaciones pueden conservarse con PASS si están correctamente declaradas. Un deseo de todos PASS **no es una instrucción de resultado**: no lo emita mientras quede una puerta obligatoria abierta. Si algo sigue siendo insuficiente, indique el paso exacto y mantenga FAIL/INCONCLUSIVE según corresponda. Un bloqueo confirmado detiene la revisión y genera informe parcial; un corte de tiempo deja INCONCLUSIVE en lo no examinado. No repare insumos del autor. No publique, haga push, deposite ni envíe mensajes a terceros.
