# B01: Modelo físico y certificado Certo

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Aristas reales, cobertura exacta, piezas de orden 2 a 4 y ganancia 2/5. Se separa gainOf mixto de la ganancia irrestricta.

## Revisión y resultados

Se recorrieron 33 868 grafos etiquetados hasta seis vértices y se reconstruyeron las particiones literales. Certo certificó una cubierta de seis piezas de K3 join I3; un checker independiente del productor verificó sus doce aristas. Una cota inferior por pesos de cliques demuestra seis, por separado del certificado de cubierta.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

Omisión, solapamiento, pieza no clique, orden indebido y universo incorrecto se rechazan. El replay independiente añade controles de tamaño declarado y no clique a la prueba tamper de Certo.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/literal_model_check.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. La universalidad procede de las declaraciones formales. El certificado Certo por sí solo prueba factibilidad, no optimalidad; aquí la cota inferior es un argumento exacto adicional. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
