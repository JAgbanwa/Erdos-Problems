# B09: Estructura cordal y clique recovery

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Casos degenerados, recuperación de clique real y tres casos exhaustivos del muestreo adaptado.

## Revisión y resultados

Se revisaron F.3a, F.3b y F.5 contra sus declaraciones. Los contraejemplos finitos incluyen grafo vacío, bolsas duplicadas, árbol aislado y hoja con más de un vértice privado.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

Los ejemplos rechazan identificar hoja con un único vértice simplicial o intersección duplicada con separador minimal. Parte positiva y orientación doble de las no-aristas se conservan.

## Reproducción y evidencia

Ejecutar `00_CONTROL/extension_checks.py` desde el expediente extraído. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. Las extracciones contrib fuera del corte no se certifican. La adaptación de de Joannis de Verclos se atribuye y no se confunde con el enunciado publicado literal. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
