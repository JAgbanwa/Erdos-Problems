# E2 — Matemática (r2: control de impacto)

- **Delta r2.** Una única línea cambiada cae en una demostración (l.688, Lema 5.3: «ni otro empaquetamiento»). Es una sustitución terminológica sin contenido matemático. Ninguna fórmula cambia (E6).
- **Herencia de las siete filas de A.2.** Las evaluaciones individuales se conservan (detalle en el informe consolidado §4):
  - A2-1, A2-2 y A2-7: ACCEPTABLE_SUMMARY desde run_v1.2_r1.
  - A2-3, A2-5 y A2-6: REQUIRES_EXPANSION en run_v1.2_r1; ACCEPTABLE_SUMMARY en run_v1.21_r1.
  - A2-4: REQUIRES_EXPANSION en run_v1.2_r1 y run_v1.21_r1; ACCEPTABLE_SUMMARY en run_v1.22_r1, tras rederivar C.3 contra Mathlib fijado y E18/E19.
  - La herencia es válida porque el texto ES/EN de C.2, C.3, E.1, §5.1 y D.1 es idéntico a r1, salvo las palabras de l.1892, 1917 y 1959 en E.1, que no tocan ninguna fórmula ni cuenta.
- **R-01** (OBSERVATION, vigente): las cotas de segundo momento B_q de C.2 se citan, no se derivan. **R-02:** resuelto en r1.

**Veredicto E2 (r2): PASS** (observación R-01 vigente) — heredado y revalidado por identidad.
