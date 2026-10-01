# B07: Testigos, parábola y optimalidad

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Cota inferior irrestricta, doble núcleo máximo y rango 2<=k<=h para gap mixto nulo.

## Revisión y resultados

Se calcularon exactamente cp y c4 en seis splits pequeños; 45 430 identidades parabólicas y 98 órdenes de doble máximo. La familia de 6.3a conserva su déficit exacto y una cota inferior de edición a todo comparador óptimo.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

El caso n=1 módulo tres rechaza elegir siempre un maximizador único. La primera transcripción del script de obstrucción fue corregida y conservada en el historial.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/split_values.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. Igualdad de valores óptimos no significa integralidad del politopo. La obstrucción no contradice la estabilidad lineal hacia una raíz de tamaño no prefijado. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
