# B10: Regresión integrada

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Dos definiciones independientes de cordalidad y modelos literales en un dominio finito explícito.

## Revisión y resultados

Los clasificadores por ciclos inducidos y por eliminación perfecta coinciden en los 33 868 grafos etiquetados de n=0..6: 19 049 cordales. Se incluyen vacíos, desconexos, completos y aislados.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

C4 inducido se rechaza, y añadir una diagonal cambia correctamente el veredicto. Los demás bloques conservan mutaciones específicas de sus certificados.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/cycle_chordality.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. El dominio se enumera por máscaras; no requiere deduplicación por isomorfismo. No es un censo universal ni una prueba de b=0. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
