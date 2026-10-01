# B02: Óptimo fraccional y dualidad

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Packing de copias reales K3/K4 con cargas no negativas y capacidad uno por arista. Las extensiones finitas mantienen s<=n, y la corrección más fuerte exige 4s<=n.

## Revisión y resultados

Se comprobaron 76 pares primal-dual en todos los grafos etiquetados hasta cuatro vértices. SciPy propone valores; el verificador racional exige factibilidad de ambos lados e igualdad exacta. Se conserva un certificado K4 y el regenerador determinista del resto.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

Los negativos alteran carga, signo, objetivo o cota dual. No se acepta un valor flotante óptimo sin replay racional.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/exact_lp_pairs.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. La regresión no demuestra dualidad fuerte universal ni la cota de defecto para todos los órdenes; sus interfaces y el caso pequeño fueron revisados en G1/G3. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
