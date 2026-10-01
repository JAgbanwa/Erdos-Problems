# Informe de puerta E1 — run_v1.22_r2 (Paper IV v1.22-r2)

Veredicto actual: **PASS**. Evidencia: `20_EVIDENCE/E1/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E1 — Enunciados, constantes y etiquetas (r2: control de impacto)

- **Delta r2.** Solo cambian 11 líneas de prosa ES (`IMPACT_CHECK.json`). Ninguna pertenece a un párrafo de enunciado ni a una tabla. Las fórmulas en display (237), las fórmulas en línea (1989), las 146 etiquetas y los encabezados de resultado son idénticos a r1 (`E6_R2_DELTA.json`). El inglés es byte-idéntico (E0).
- **Conclusión.** El delta no afecta a ningún enunciado, hipótesis, constante final ni etiqueta.
- **Herencia.** Se conserva el mapa de afirmaciones de run_v1.2_r1 (`run_v1.2_r1/20_EVIDENCE/E1/E1_RECORD.md`, 21 filas: A, B1, B2, C, C′a–d, 6.3a, 6.1, 6.1a, 6.2, 6.4, 6.5, 6.6, C.4, 3.1, D.2, F.3a/b, G.1, G.2), todas MATCH salvo G.2, «no re-extraída». También se conservan su ratificación en run_v1.21_r1 (PASS_WITH_MINOR por NEW-01) y en run_v1.22_r1 (PASS). La herencia es válida porque el texto de esos enunciados es idéntico (cadena de diffs v1.2→v1.21→v1.22-r1→r2) y el corte Lean es el mismo (615/615).
- **Observaciones vigentes:** X-17 (E1-O1, Prop. 6.3a existencial en Lean) y X-18 (E1-O2, τ real en Lean frente a τ ≥ 0 en el texto).

**Veredicto E1 (r2): PASS** — heredado y revalidado por identidad, con control de impacto nuevo.
