# B05: Constructor cercano y presupuesto neto

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

La raíz es clique real del grafo; ambas fases usan recursos compatibles y la misma partición.

## Revisión y resultados

100 000 vectores racionales, semilla 8104; 6 583 satisfacen ambas premisas del presupuesto y cumplen la conclusión. La cuenta de momentos y su cancelación dan B-m/16-A/2. El delta ConstructorBudget está incluido y compilado.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

Un vector que solo satisface la premisa presupuestaria falsea la conclusión: la premisa física no puede borrarse. No se presenta ese vector como grafo.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/cancel_budget_regression.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. No se infiere realizabilidad de parámetros a partir del test aritmético. La existencia viene de la cadena formal, y AllInput sigue visible en el lema local. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
