# B04: Constantes explícitas y enlace B7

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Torre simbólica, umbral cercano separado del global, mejora completa de limpieza y umbral uniforme E35.

## Revisión y resultados

Los logs de E17.ExplicitFarAudit exigen la ruta mejorada y excluyen finales antiguos. Se comprobaron exactamente la contracción cercana, el cociente 393/100 y 101 evaluaciones de la cuenta de edición en s=0..100. El paso formal retiene la cota polinómica para todo s.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

La desigualdad x^2<=2^x se comprueba en x=4..100 y se conserva x=3 como negativo de una extensión ilegítima. La torre enorme no se evalúa.

## Reproducción y evidencia

Ejecutar `00_CONTROL/extension_checks.py` desde el expediente extraído. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. Las cotas son explícitas, no prácticas. No se confunde el umbral 4 por 10^12 con el umbral global ni se omite la condición de la forma inversa. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
