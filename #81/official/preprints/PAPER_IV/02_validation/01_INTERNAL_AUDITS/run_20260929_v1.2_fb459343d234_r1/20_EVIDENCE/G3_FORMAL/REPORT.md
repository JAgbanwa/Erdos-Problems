# G3: Conformidad y entrada pública

Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.

## Obligación y resultado

607 módulos de fuente; cierre de importación PaperIV de 553; 224 #check importando solo PaperIV. Sin tokens efectivos sorry/admit/native_decide/axiom en la inspección léxica. Esta inspección complementa los axiomas transitivos, no los sustituye.

## Evidencia y método

Este gate se apoya en los archivos de su carpeta, el inventario de entradas, los registros de ejecución y la revisión matemática. No basta el marcador de estado. Los controles de build son de solo lectura; no se recompiló Lean durante esta auditoría.

## Hallazgos y límites

Ver `00_CONTROL/FINDINGS.md`: errores de verificadores corregidos, una referencia cruzada menor aclarada y el alcance del anexo histórico. No se cambió matemática, fuente Lean ni manuscrito. El resultado no sustituye la auditoría externa ni acredita prioridad.

## Reproducción

Los scripts en `00_CONTROL` identifican insumos y archivos de salida. Repetir en una carpeta nueva; conservar intentos previos. No descargar otra Mathlib. Las rutas del entorno documentan esta máquina y no son dependencias del teorema.

## Dictamen

**PASS interno**, con el alcance anterior. El cierre efectivo de G6 y G8 se registra tras revisar los informes y verificar los archivos ZIP; un PDF compilado no es por sí solo una auditoría matemática.
