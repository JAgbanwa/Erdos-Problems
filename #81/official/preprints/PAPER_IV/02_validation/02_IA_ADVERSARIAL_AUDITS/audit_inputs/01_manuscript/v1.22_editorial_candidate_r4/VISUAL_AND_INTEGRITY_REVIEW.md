# Control editorial y visual — v1.22-r4

Estado: correcciones locales verificadas; pendiente de revalidación externa. Fecha: 1 de octubre de 2026. No es un nuevo dictamen externo.

## Alcance y criterio editorial

Se aplicó mathematical-paper-editor para preservar la sustancia matemática y limitar el delta a NEW-05. La versión del manuscrito sigue siendo 1.22; r4 identifica el nuevo paquete. No se reescriben informes ni paquetes anteriores.

- A.2: «la programación numérica de C.3» pasa a «el calendario numérico de C.3», con la concordancia del artículo corregida.
- F.4: «cota adaptada con muestra fijada» pasa a «cota adaptada con muestras con anclajes», conforme a F.5.
- Sin cambios de enunciados, hipótesis, fórmulas, constantes, referencias, identificadores ni numeración.

## Comprobaciones finales

`check_r4.py` confirma que MD y TeX son exactamente el baseline r3 con esas dos sustituciones. El texto extraído del PDF coincide tras las sustituciones y la normalización de tres cambios de corte de línea, enumerados en ARTIFACT_CHECKS.json. El inglés MD/TeX/PDF/log, las figuras y los recursos tipográficos son byte-idénticos a r3. Las 615 entradas del manifiesto formal conservan sus hashes.

El PDF español final tiene 73 páginas. Se renderizaron todas después de la última edición y se revisaron las 13 hojas de contacto. Se inspeccionaron a resolución legible las páginas modificadas 40 y 66: terminología correcta, sin recortes ni desbordamientos. Las otras 71 páginas son idénticas al baseline en comparación de píxeles; no cambia la paginación. Se conserva la plantilla de la serie, sin rediseño.

Compilación con Tectonic existente y sólo recursos de caché, dos pasadas: salida 0. El log final registra cinco avisos Underfull, sin Overfull, caracteres ausentes, referencias indefinidas ni errores LaTeX. La consola registra un aviso de configuración Fontconfig; la compilación y el render terminaron correctamente, sin defecto visual observado. No se instalaron herramientas ni dependencias.

No se compiló Lean. La evidencia E4 se solicita heredada y revalidada por identidad, no ejecutada en r4. El control visual es editorial, no una nueva demostración matemática ni revisión humana por pares.

## Entrega

ARTIFACT_CHECKS.json identifica los seis artefactos de manuscrito finales; MANUSCRIPT_REVIEW_MANIFEST.json y AUDIT_TARGET_v1.22_r4.json fijan el paquete y el encargo. El auditor debe confirmar el cierre de NEW-05 y emitir su veredicto independiente.
