# B08: Estabilidad, particiones y obstrucción

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación e hipótesis

Una misma raíz controla todas las particiones irrestrictas. Para defecto fijo hay exactamente s vértices de defecto y una clique del grafo original.

## Revisión y resultados

35 457 identidades de partición y 98 119 piezas no canónicas comprobadas; revisión exacta adicional de perfiles a,b<=150 y familias de desplazamiento s<=10,q<=70. E.4 fue cotejado bloque por bloque, incluidos el crédito R y el coste de mover vértices.

El cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.

## Negativos e incidentes

El perfil (3,2) alcanza el factor local diez; la familia de déficit uno refuta una cota puramente lineal a plantillas de tamaño óptimo. Los controles no afirman optimalidad global de 480.

## Reproducción y evidencia

Ejecutar con Python 3.12 `scripts/partition_defect.py`. Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.

Un solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.

## Dictamen y límites

**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. El anexo separado da un gap triangular lineal con ancho acotado, no gap mixto lineal universal. Absorción y reservas mantienen sus hipótesis de recursos libres. Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.
