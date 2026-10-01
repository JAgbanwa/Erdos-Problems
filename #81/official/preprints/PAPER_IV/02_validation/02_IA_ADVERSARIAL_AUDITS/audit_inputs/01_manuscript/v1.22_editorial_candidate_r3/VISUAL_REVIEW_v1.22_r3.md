# Revisión visual y paridad — v1.22-r3

Revisión del editor, 1 de octubre de 2026; no es un veredicto de auditoría externa.

- Se compilaron los TeX entregados con el entorno Tectonic ya instalado y caché local, por separado. ES: 73 páginas; EN: 72. No hubo build Lean.
- Se inspeccionaron las 25 hojas de contacto finales, que cubren las 145 páginas. Sin solapamientos, recortes ni páginas vacías inesperadas detectados.
- Además se inspeccionaron las páginas modificadas a tamaño completo: ES 1–6, 34–36, 39–40 y 66; EN 1, 33, 39–40 y 64. El desplazamiento de texto en las páginas españolas iniciales no elimina ni duplica contenido.
- Respecto de r2, 61 páginas ES y 67 EN son idénticas en raster; las listas exactas se registran en ARTIFACT_CHECKS.json. Es identidad visual, no una nueva revisión matemática.
- Los párrafos de estado conservan paridad: veredicto histórico r2, aceptación de C.3 y A.2, herencia del build, límites de revisión escrita y ausencia de nuevo build. Las dos lenguas mantienen su numeración previa.
- Cinco párrafos documentales cambian por idioma. Fórmulas en línea y desplegadas, etiquetas, bloques de código, filas de tablas, referencias e imágenes permanecen idénticos a r2. Los cambios se pueden inspeccionar íntegramente en los dos diff.
- Logs: ningún Overfull, error de TeX ni glifo ausente; cinco Underfull ES y nueve EN, sin defecto visible asociado. La advertencia de configuración Fontconfig del entorno no impidió generar los documentos. No hay fuentes Type 3.
- ARTIFACT_CHECKS.json vincula los PDF y TeX finales por hash y verifica la procedencia temporal del compilado. La plantilla/preambulo no cambia respecto de r2.

Resultado del control editorial local: documentos preparados para revalidación. No se afirma que esta inspección sustituya E6 del auditor ni una revisión humana por pares.
