# B06: Ensamblaje y cuantificadores

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

A para todo orden, B eventual, C para defecto fijo y 6.5 para sucesiones arbitrarias. El régimen lejano conserva todos los grafos.

## Revisión y resultados

Se verificaron diferencias de pisos en n=1..10 000 y 40 000 telescopajes. El mapa contrasta tipos elaborados y prosa, incluida precisión antes de s y la elección de una raíz común antes de cada partición.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

No se reemplaza un resultado para s fijo por s creciente. No se interpreta exceso positivo o(n^2) como igualdad para grafos dispersos.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/target_arithmetic.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. No prueba b=0 universal. Las ramas son exhaustivas; no se afirma exclusión mutua de todos los testigos existenciales. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
