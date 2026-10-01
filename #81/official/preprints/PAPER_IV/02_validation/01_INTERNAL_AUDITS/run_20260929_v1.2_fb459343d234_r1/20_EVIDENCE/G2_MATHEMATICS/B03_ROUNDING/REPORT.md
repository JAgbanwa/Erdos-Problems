# B03: Redondeo mixto y cuotas conjuntas

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Precisión positiva antes del grafo, cargas por arista de ambos tipos y un único matching marcado.

## Revisión y resultados

Se revisaron los pasos de limpieza, fibra, codegrado conjunto, cuotas y desmarcado de C.1-C.2. La regresión K5 distingue dos triángulos (ganancia cuatro) de un K4 (ganancia cinco), aunque la cardinalidad favorece los primeros.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

Se rechaza combinar packings que compiten por una arista y usar cardinalidad como sustituto de ganancia ponderada.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/mixed_weight_regression.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. Se reutiliza el nibble atribuido a Paper III. No se deriva un teorema de redondeo asintótico de ejemplos pequeños. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
