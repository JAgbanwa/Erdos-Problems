# Paper IV v1.2 — auditoría interna r1

Autorizada por el autor el 29-09-2026: ejecutar y resolver los hallazgos hasta completar los controles. Auditoría del lado del autor, no independiente. No autoriza publicación ni servicios externos.

## Corte y autoridad

- Fuentes: `piv-v12-fb459343d234`.
- Manuscritos: `piv-v12-manuscripts-2451d43bface`, ES/EN, v1.2.
- Protocolo completo: `../../INTERNAL_AUDIT_STANDARD_v1.0.md`, ampliado por `NEXT_INTERNAL_AUDIT_SCOPE_v1.2.md` del manuscrito sellado. La versión 1.0 del protocolo no sustituye el inventario real de v1.2.
- Se esperan 607 módulos, 19 targets y 224 exports; se recalculan y verifican, no se aceptan por el resumen.
- La evidencia del build completo comprende dos segmentos vinculados por fuentes y procedencia. No se repite el build completo por defecto.

## Reglas de ejecución

1. G0/G1/G3/G4 antes de las regresiones; diez bloques matemáticos B01–B10; revisión ES/EN y visual; procedencia; entrega MD/TeX/PDF/ZIP por parte y general.
2. Un proceso pesado propio a la vez. No otra Mathlib, no cambios de paquetes, no intervención en builds ajenos. Los tests ligeros pueden progresar mientras compila E28 de la línea b=0.
3. Conservar fallos, intentos e identidad de cada corrección. Ningún requisito se relaja para conseguir PASS. Un cambio de fuentes o manuscrito genera nueva identidad y revalida sus dependientes.
4. El usuario autoriza resolver problemas, no debilitar teoremas. Una reparación matemática se separa de la edición y queda documentada; no se modifica silenciosamente el corte congelado.
5. No reutilizar PASS de v1.0 para los resultados nuevos. Los scripts históricos pueden copiarse y ejecutarse de nuevo, con procedencia registrada, sin copiar sus resultados.
6. Todos los gates son inicialmente NOT_STARTED. El PASS global requiere evidencia efectiva, informes, PDF revisados y paquetes íntegros; no significa auditoría externa ni b=0.

## Ampliaciones obligatorias

Teoremas A/B/C/C′, estabilidad conjunta y de particiones, obstrucción de raíz cuadrada, cotas uniformes en s, sucesiones de órdenes arbitrarios, E34/E35 explícitos y exclusión declarada de remoción histórica. E.4 se coteja bloque a bloque; F.3a y los tres casos de F.5 por declaraciones literales. Cada una de las siete derivaciones resumidas de A.2 recibe un dictamen expositivo individual.

## Reanudación

El estado persistente está en `AUDIT_STATE.json`. Los hallazgos se conservan en `FINDINGS.json`. No cerrar el objetivo mientras falte un control obligatorio. No emitir PASS de controles interrumpidos o meramente preparados.
