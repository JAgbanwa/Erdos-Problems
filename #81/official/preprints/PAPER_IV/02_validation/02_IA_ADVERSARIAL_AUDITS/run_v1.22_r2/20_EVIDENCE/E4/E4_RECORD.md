# E4 — Reproducción formal (r2): build externo heredado, confirmación documental

**No se ejecutó un build nuevo ni un replay independiente del kernel.** Tampoco se ejecutaron lean, lake ni leanchecker.

## Build original (run_v1.2_r1, 2026-09-30)
- **Runner.** `auditor_build.py`, escrito por el auditor, sin Lake; Lean v4.28.0 (commit 7e01a1bf).
- **Entradas.** Extracción limpia de `LEAN_SOURCE_piv-v12-fb459343d234.zip` (615/615 hashes) con objetos solo en `05_BUILD/main/obj`. Dependencias Mathlib y paquetes compartidos en solo lectura; caché de 113 821 archivos sin cambios.
- **Intentos.** El intento 1 falló por un error propio del auditor (C-04) y se conserva. El intento 2 corrió de 15:09 a 21:33 UTC.
- **Registros originales:**
  - `10_LOGS/E4_main_console.log` (sha256 ef5b01c7…): `modules_planned 607, pass 607, fail_or_blocked []`, 607 líneas `PASS n 607`, última línea `EXIT 0`, y los 19 targets de FREEZE_SCOPE en PASS.
  - `10_LOGS/E4_main/records.jsonl` (0f2d8495…): 608 filas, 607 módulos del corte más AuditorChecks, todas PASS. El hash de fuente de cada fila coincide con el manifiesto y ningún código de salida es distinto de 0.
  - 608 logs de módulo, sin el texto «sorry» y con 0 líneas de error en `ReleaseExportCheck.log`.
  - `20_EVIDENCE/E4/E4_RECORD.md` (9ca125d2…) y `AuditorChecks.log` (3468cedd…).
- **Exportaciones.** `ReleaseExportCheck.lean` contiene 224 `#check`.
- **Anexo.** `10_LOGS/E4_annex/records.jsonl` (57ce1895…): 50/50 PASS. La auditoría de BoundedCliqueGap informa 633 declaraciones con axiomas ⊆ {propext, Classical.choice, Quot.sound}.
- **Identidad de objetos.** Los 607 `.olean` son idénticos byte a byte a los del autor; una recompilación de 37 módulos confirmó el determinismo.
- **Huella de axiomas. No son recuentos de teoremas distintos:**
  - 461 *registros* de axiomas según la regla del autor, de los cuales 314 son salidas reales de `#print axioms`; los demás son líneas de auditoría que se repiten.
  - En AuditorChecks: `#print axioms` sobre 18 declaraciones principales, todas exactamente con [propext, Classical.choice, Quot.sound].
  - Recorrido propio de conos (tipo + valor) de 50 declaraciones públicas: 0 axiomas no estándar, 0 `sorryAx`, 0 constantes bajo `Erdos81`.
- **SUMMARY sobrescrito.** `10_LOGS/E4_main/SUMMARY.json` (6fbba41f…) dice `modules_planned 555`, `targets_status {AuditorChecks: PASS}` y hora de fin 21:35:58: fue sobrescrito por la invocación de AuditorChecks (C-06). **No se usa como evidencia del alcance.**

## Confirmación en r2
- `10_SCRIPTS/e4_reuse_check.py` es idéntico al de run_v1.22_r1 (sha256 db2eddb8…). Lee la consola, records.jsonl, los logs de módulo, los registros del anexo, AuditorChecks, olean_vs_author y cache_diff; no usa el SUMMARY.
- Resultado: `E4_REUSE_CHECK.json`, **idéntico** al de run_v1.21_r1 y al de run_v1.22_r1. Confirma 607 módulos, 19 targets, 224 exportaciones y 50 módulos del anexo.

## Por qué la validez se conserva en r2
r2 solo modifica prosa española y una marca tipográfica, sin tocar Lean. E0 inicial confirma:
- las 615 entradas del manifiesto de fuentes y el directorio del corte, sin extras;
- el ZIP de fuentes con 615 miembros, CRC correcto e igual al manifiesto;
- el anexo;
- el paquete y el manifiesto de run_v1.2_r1 sin cambios en disco (1097 archivos).

El objeto compilado y auditado es, por tanto, exactamente el corte que cita el manuscrito r2.

## Límites
Misma máquina y caché Mathlib compartida (no es un build de sala limpia), sin replay del kernel, y el build de run_v1.2_r1 lo hizo este mismo auditor y sesión.

**Veredicto E4 (r2): PASS — reused_verified_external_build** (PASS heredado y revalidado por identidad).
