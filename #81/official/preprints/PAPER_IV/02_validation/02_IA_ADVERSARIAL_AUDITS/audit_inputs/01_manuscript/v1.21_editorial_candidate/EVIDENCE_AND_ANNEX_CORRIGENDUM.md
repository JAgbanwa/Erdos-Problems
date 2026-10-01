# Paper IV v1.21 — aclaraciones de evidencia y anexo

Fecha: 30 de septiembre de 2026. Documento adicional; no sustituye registros históricos.

## Recuento de axiomas (X-20)

El recuento reproducido en `artifact_checks.py`, sobre los 19 logs de `03_reproducibility/full_rebuild_v12_20260929_resume/combined/modules/`, da **314** líneas de salida con `depends on axioms:` y **147** listas de axiomas de elaboradores de auditoría: **461 registros**. Los hashes y subtotales por target están en `AXIOM_COUNT_RECONCILIATION.json`.

La cifra «313 impresiones» del informe interno histórico queda corregida por esta nota. No se deduce de estos totales un número de teoremas distintos. El número 461 del manuscrito era correcto. La certificación del build externo procede de su E4 final, no de este recuento.

## Anexo BoundedCliqueGap (X-25)

En el README histórico del anexo, la remisión a «§8.2» debe leerse como **Apéndice G.1** en las versiones 1.2 y 1.21. El resultado es `BoundedCliqueGap.chordal_gap_linear_cliqueFree`: brecha triangular con número de clique acotado, no brecha mixta universal.

Se preserva el ZIP histórico `05_formalization/LEAN_BOUNDED_GAP_ANNEX_v1.0.zip`, SHA-256 `2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d`. Esta nota debe acompañarlo en la próxima revisión y eventual paquete de publicación. No se ha reemplazado ni recomprimido el ZIP que el auditor reprodujo.

## Configuración conservada (X-19)

Algunas entradas `lean_lib` del archivo Lake no tienen módulos en el corte seleccionado. Son configuración residual, no evidencia de una dependencia del teorema. Se mantienen para no alterar el corte compilado; la lista de 607 módulos, sus imports, los tipos y los conos auditados delimitan el alcance real. No se declara que se haya hecho limpieza de esa configuración.

## Límites preservados (X-21, X-22, X-26)

La recuperación del build autoral fue verificada inicialmente por consistencia de registros. El auditor produjo después evidencia propia: 607 módulos recompilados y 607 objetos byte-idénticos a los registros del autor. Esa comprobación resuelve X-21 sin borrar la limitación histórica. La suficiencia de cuatro pruebas en prosa quedó INCONCLUSIVE pese al PASS interno; el desacuerdo permanece en los informes originales.

La ejecución del auditor fue separada, en una sesión nueva que declaró respetar el límite de lectura y no consultar árboles de investigación excluidos. Esa independencia operativa no equivale a diversidad de familias ni a aislamiento técnico del disco. La nueva revalidación consulta expresamente los hallazgos anteriores.

## Detector de avisos (X-28)

El patrón literal de los runners congelados no reconocía los acentos graves del aviso de Lean 4.28. No se cambia el congelado para disimular ese defecto. `sorry_log_recheck.py` detecta tanto el aviso capturado como variantes y `sorryAx`; reescanea 608 registros externos principales, 50 del anexo y 186 del segmento autoral combinado, sin coincidencias. Los negativos se examinan separadamente y se rechazan. `SORRY_RECHECK.json` contiene hashes y resultados; el parche adjunto es una propuesta no aplicada para una futura identidad de herramientas. Este control de registros no reemplaza los conos de axiomas ya examinados por el auditor.
