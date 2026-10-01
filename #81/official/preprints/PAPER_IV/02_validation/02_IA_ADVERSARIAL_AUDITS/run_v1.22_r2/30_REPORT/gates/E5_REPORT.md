# Informe de puerta E5 — run_v1.22_r2 (Paper IV v1.22-r2)

Veredicto actual: **PASS**. Evidencia: `20_EVIDENCE/E5/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E5 — Falsación y aritmética exacta (r2)

El delta r2 no toca ninguna fórmula ni constante (E6), así que no hace falta ninguna prueba nueva. Para confirmar la integridad de la evidencia heredada repetí, sin Lean, los scripts aritméticos de run_v1.22_r1:

| Conjunto | Origen | r2 | Resultado |
|---|---|---|---|
| T01–T24 (24 pruebas; Certo: certificado de partición exacta de 6 piezas de K3∨I3, solo factibilidad) | run_v1.2_r1 E5 | heredado (texto cubierto idéntico) | 24/24 PASS, controles negativos predeclarados rechazados |
| 21 comprobaciones v1.21 (C.2, calendario C.3, E.1, E.2d) | run_v1.21_r1 | **repetido** (`e5_v121_numerics_RERUN.json`) | todas PASS, todos los negativos rechazados; idéntico a r1 |
| C3a–C3n (14 comprobaciones del C.3 nuevo) | run_v1.22_r1 | **repetido** (`e5_v122_c3_RERUN.json`) | 14/14 PASS; 7 de los 8 negativos en línea rechazados (C3m mal especificado, C2-01); idéntico a r1 |
| Negativo corregido de C3m | run_v1.22_r1 | **repetido** (`e5_v122_c3_negfix_RERUN.json`; C3-03) | rechazado; idéntico |
| Negativos complementarios para C3c, C3e, C3g, C3j, C3l, C3n | run_v1.22_r1 | **repetido** | 6/6 rechazados; idéntico |

**Recuentos sin doble suma.** Son 24 pruebas originales + 21 + 14 comprobaciones = 59 comprobaciones distintas, más 1 + 6 controles negativos añadidos. Las repeticiones de r2 no son comprobaciones nuevas.

**Tipo de evidencia.** C3a–C3g son identidades y desigualdades exactas en los parámetros fijados. C3h, C3i y C3l–C3n son una regresión finita sobre rangos de lemas universales elementales; su prueba universal está en E2 (run_v1.22_r1) y en los teoremas E19, cubiertos por E4.

**Veredicto E5 (r2): PASS** — heredado y revalidado por identidad, con repetición.
