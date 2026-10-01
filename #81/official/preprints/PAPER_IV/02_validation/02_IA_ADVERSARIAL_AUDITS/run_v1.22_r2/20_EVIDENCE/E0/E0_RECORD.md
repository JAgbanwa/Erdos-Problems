# E0 — Identidad (r2)

Script: `10_SCRIPTS/e0_v122r2.py`, de solo lectura. Ejecuciones: inicial (2026-10-01T11:01:08Z, antes de cualquier revisión) y final (2026-10-01T11:23:33Z, tras el dictamen). **Los dos objetos `checks` son idénticos.**

| Comprobación | Resultado |
|---|---|
| `AUDIT_TARGET_v1.22_r2.json` (f9317763…) frente a su sidecar | coincide |
| Manifiesto r2, ZIP r2, mandato, manifiesto de fuentes y objetivo base r1: hash y bytes según lo declarado | todo coincide |
| Evidencia anterior: los ZIP de run_v1.22_r1, run_v1.21_r1 y run_v1.2_r1, el ZIP de fuentes Lean y el anexo | hash y bytes coinciden |
| Manifiesto r2 frente al directorio: 127 archivos | 0 discrepancias. Fuera del manifiesto, por declaración, quedan el propio manifiesto y su sidecar, el ZIP y su sidecar, `.aux` y `__pycache__` |
| ZIP r2: 129 miembros (127 + manifiesto + sidecar) | CRC correcto (testzip None), sin rutas inseguras ni faltantes, 0 discrepancias de hash, y los 2 miembros extra iguales a los archivos en disco |
| Otros ZIP en el directorio r2 | ninguno |
| Inglés MD, TeX y PDF de r2 frente a r1 | **byte-idénticos** |
| Corte r1 de comparación | manifiesto d9e559a3… y directorio sin cambios; paquete 2b87b746… |
| Lean | 615/615 entradas, sin extras; ZIP de fuentes con 615 miembros, CRC correcto e igual al manifiesto |
| Anexo | 2847a422…, 40 miembros, CRC correcto |
| run_v1.2_r1, run_v1.21_r1 y run_v1.22_r1 | 1097, 340 y 188 archivos del manifiesto sin cambios; sidecars de los ZIP correctos; CRC correcto en los tres |

**Veredicto E0 (r2): PASS.**
