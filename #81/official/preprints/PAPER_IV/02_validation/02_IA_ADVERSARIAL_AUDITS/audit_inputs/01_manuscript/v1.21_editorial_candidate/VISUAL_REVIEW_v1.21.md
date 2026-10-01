# Paper IV v1.21 — revisión visual autoral

Fecha: 30 de septiembre de 2026. No es una auditoría independiente.

Actualización posterior al informe externo final: se regeneraron ambos PDF después de precisar X-27 y el estado de auditoría. Se volvieron a inspeccionar las 24 hojas de contacto (71 páginas EN y 72 ES), y a resolución de página §7 (página 31 en ambas ediciones) y la Tabla 9 (EN 63, ES 64). No se observan recortes ni superposiciones en esas nuevas adiciones; la tabla continúa correctamente en la edición ES. Los controles de artefactos posteriores a esta última edición siguen sin desbordamientos, glifos ausentes ni fuentes Type3. La exposición ampliada conserva las páginas identificadas en `ARTIFACT_CHECKS.json`; su aceptación matemática queda para E2, no para esta revisión de composición.

Se regeneraron ES y EN secuencialmente desde Markdown mediante Pandoc, la plantilla de la serie y Tectonic con `--only-cached`. Se renderizaron todas las páginas a PNG y hojas de contacto. Se inspeccionaron las hojas de contacto de ambas ediciones y, a resolución de página, los extractos Lean de A.1, las tablas y derivaciones nuevas de C.2–C.3 y las cuentas de normalización/eliminación de E.1. La última modificación de maquetación mantiene juntos los bloques Lean; después se revisaron nuevamente las páginas 39–40 de ambas lenguas.

La versión inglesa tiene 71 páginas; la española, 72. Diferente paginación no implica diferente contenido. Las páginas y hashes concretos están en `ARTIFACT_CHECKS.json`.

Comprobaciones:

- No se detectaron recortes, superposiciones ni ecuaciones fuera de los márgenes en la inspección de conjunto.
- Los fragmentos conservan sangría y los caracteres ⦃/⦄ originales; las cabeceras de teoremas ya no se parten entre páginas.
- Los identificadores de las tablas usan monoespaciado y flechas de continuación cuando se parten; los límites de tabla son legibles.
- Figuras centradas, etiquetas y referencias coherentes; se añadió la cita de la Figura 3 en el texto.
- Los registros finales no contienen `Overfull` ni avisos de glifos ausentes. El inventario de fuentes del PDF no contiene Type3.
- Persisten algunos avisos `Underfull` en texto justificado y tablas, sin desbordamiento observado. La advertencia de configuración general de Fontconfig no impidió resolver las fuentes explícitas ni producir los PDFs.

La fuente de símbolos se toma de la instalación del sistema y se copia a `typeset_runtime/` sólo para resolver una limitación de rutas absolutas de Tectonic. Esa copia no forma parte de la entrega distribuible. Los scripts usan las herramientas y cachés existentes.

Límite: la lectura de hojas de contacto verifica composición general, no es una lectura matemática línea por línea de todas las páginas. La nueva auditoría debe volver a examinar los artefactos finales, los textos nuevos y la paridad; este informe no transfiere el PASS de v1.2 a v1.21.
