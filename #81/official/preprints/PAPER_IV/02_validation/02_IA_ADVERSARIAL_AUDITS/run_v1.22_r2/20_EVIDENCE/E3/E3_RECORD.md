# E3 — Correspondencia formal y declaración de dependencias (r2)

- **Corte Lean.** Las 615 entradas coinciden, sin archivos extra. El ZIP de fuentes (cb274145…) tiene 615 miembros, CRC correcto y es igual al manifiesto. El anexo (2847a422…) tiene 40 miembros, CRC correcto (E0).
- **Identificadores.** El único código nuevo en ES es `Model`, que resuelve como namespace en el corte (`IMPACT_CHECK.json`). No se elimina ningún identificador (330 → 331 códigos en línea).
- **X-27.** La declaración de la dependencia de los wrappers E32 respecto de la cadena histórica [23] se conserva en §7 (p. 31), en la Tabla 9 (p. 65, ahora en una sola página) y en [23] (p. 73); lo verifiqué visualmente en r2.
- **Herencia.** run_v1.2_r1 E3 (PASS_WITH_FINDINGS por X-27, después declarada) → run_v1.21_r1 PASS → run_v1.22_r1 PASS. Las sondas AuditorASProbe y AuditorChecks se heredan porque el código fuente es idéntico.

**Veredicto E3 (r2): PASS** — heredado y revalidado por identidad.
