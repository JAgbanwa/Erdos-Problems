# Revisión visual editorial — v1.22-r2

Se revisó el PDF español generado desde el TeX final: 73 páginas. Su SHA-256 es `8ebfccd7f9b1cc830280fa7a388682393ecacdca087756e9eaabe5b56d6eb0df`.

- Inspección general de las 73 páginas mediante las trece hojas de contacto de `qa_es/`.
- Inspección individual legible de las 18 páginas cuyo raster cambió: 16, 18, 20, 21, 35, 55, 56, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70 y 71. Se inspeccionaron además portada, página 26 y página 72.
- Se verificaron las sustituciones terminológicas y la presentación de `Model`, así como los desplazamientos de texto posteriores. No se observaron recortes, superposiciones ni fórmulas desbordadas atribuibles a la revisión.
- Las otras 55 páginas son raster-idénticas al PDF español r1. Los tres archivos ingleses son byte-idénticos; no se recompilaron.
- El log no contiene Overfull, caracteres ausentes, referencias indefinidas ni errores de LaTeX. Hay avisos de cajas Underfull y de configuración de fuentes en consola; no se presentaron como errores ni se ocultaron los logs.

Esto es control editorial de los artefactos, no una nueva auditoría matemática ni un veredicto externo. La evidencia gráfica, el log, el diff y los controles reproducibles quedan incluidos en el paquete.
