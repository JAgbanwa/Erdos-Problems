# Informe de puerta E6 — run_v1.22_r2 (Paper IV v1.22-r2)

Veredicto actual: **PASS_WITH_OBSERVATIONS**. Evidencia: `20_EVIDENCE/E6/`. Auditor: Claude Opus 5.5, misma sesión que las ejecuciones anteriores; no se ejecutó Lean.

---

# E6 — Correcciones españolas, paridad y PDF (run_v1.22_r2)

Objetivo: delta ES de `v1.22_editorial_candidate` (r1) a `v1.22_editorial_candidate_r2` (r2). El inglés se trata en E0 (byte-idéntico, no regenerado).

## Método (independiente de los scripts del editor)
1. **Diff propio.** `20_EVIDENCE/E6/auditor_diff_es_md.diff` y `auditor_diff_es_tex.diff`, más un inventario palabra a palabra (`10_SCRIPTS/e6_r2_delta.py` → `E6_R2_DELTA.json`).
   - MD: 2565 → 2565 líneas, con 11 líneas y 13 cambios de palabra.
   - TeX: 2367 → 2367 líneas, con 11 líneas y 13 cambios, en las mismas posiciones lógicas.
   - El `CHANGES_es.diff` del editor es idéntico byte a byte al diff unificado que regeneré (13717 caracteres).
2. **Contenido protegido**, comparado entre r1 y r2:
   - Idénticos: 237 fórmulas en display, 1989 fórmulas en línea, 5 bloques de código, 146 etiquetas `\tag` y la sección de referencias completa.
   - Códigos en línea: pasan de 330 a 331; ninguno se elimina y el único que aumenta es `` `Model` ``.
   - La comparación de «líneas de encabezado o entrada en negrita» da *false* por una sola razón: la línea 578 empieza con la entrada en negrita «Segunda fase…», cuyo texto en negrita no cambia; sí cambia la palabra «matchings» del resto del párrafo.
   - `IMPACT_CHECK.json`: ninguna línea cambiada está en un párrafo de enunciado (Teorema, Lema, Proposición o Corolario), en una tabla ni en la bibliografía. Una cae dentro de una demostración (l.688, Lema 5.3, «ni otro empaquetamiento»).
3. **El PDF corresponde al TeX corregido.**
   - El PDF r2 (sha256 8ebfccd7…, 73 páginas, producido por xdvipdfmx a partir de LaTeX el 2026-10-01 10:50 UTC) se comparó con el r1 por texto extraído en tokens.
   - El cuerpo de r1, aplicando exactamente las sustituciones del inventario, coincide con el cuerpo de r2 salvo en 3 diferencias. Todas son tipográficas y las verifiqué visualmente:
     - 1 y 2, p. 55: la línea «La absorción da mín(u_w,v_w) ≤ |M_w|+t_W+L…» de r1 tenía el espaciado matemático comprimido; en r2 se reparte normalmente. La fórmula es la misma.
     - 3, p. 65–66: en r1, la Tabla 9 se partía entre páginas y repetía el encabezado «Enunciado / Declaración»; en r2 cabe en p. 65, así que el encabezado aparece una sola vez. Las 10 filas están presentes.
   - La bibliografía del PDF es idéntica.
   - El log de compilación no tiene Overfull, «Missing character», referencias indefinidas ni errores. Hay 5 avisos de Underfull, ya declarados por el editor.
   - El preámbulo TeX (40 líneas) es idéntico al de r1.
4. **Raster.** Comparando r1 y r2 a 72 dpi cambian 18 páginas: 16, 18, 20, 21, 35, 55, 56, 61–71. Es exactamente la lista de `ARTIFACT_CHECKS.json` y de `VISUAL_REVIEW_v1.22_r2.md`. Las demás 55 páginas son raster-idénticas. El texto cambia en 17 páginas: la 35 cambia solo en la fuente de `Model`.
5. **Inspección visual** (`PAGE_INSPECTION_LOG.csv`, 73/73 páginas):
   - Las 73 páginas r2 se revisaron en hojas 2-up a 90 dpi (`pairs/`).
   - Las páginas 55, 56 y 61–71 se compararon además lado a lado r1|r2 a 110 dpi (`cmp/`), mirando los desplazamientos.
   - Las páginas 16, 18, 20, 21 y 35 se verificaron en las hojas r2. Sus imágenes `cmp/` no llegaron a mostrarse (C3-02). La p. 35 se vio además a 140 dpi (`zoom/es_r2_p035.png`).
   - Regla de registro: cada fila se escribió solo con la imagen visible en ese momento. Las filas descartadas se conservan en `PAGE_INSPECTION_LOG.discarded_unseen_cmp.csv`.

## X-15 — resolución y recuento
- **Prosa r1: 11 «matching(s)»** (l.526, 578, 746 ×2, 1892, 1917, 1959, 2177, 2182 ×2, 2184) **y 1 «packing»** (l.688), es decir, 12 términos ingleses.
- **Prosa r2: 0.** Las 4 apariciones que quedan están en la bibliografía: [6] «…packings in dense graphs», [7] «…packing of families…», [9] «…spread matching theorems», [12] «…triangle packing formalization». Son títulos citados y deben quedar sin traducir; no hay ninguna en identificadores.
- **Discrepancia histórica.** run_v1.21_r1 habló de «matching(s) ×12» porque contó la referencia [9] y su escaneo no detectaba «matchings». run_v1.22_r1 describió «12 matching(s) + 1 packing» cuando su escaneo listaba 12 apariciones en total. El recuento correcto es **11 + 1**. El editor tiene razón, y la corrección queda registrada contra el auditor (CORRECTIONS C3-01).
- Las traducciones son correctas: «emparejamiento(s)» es el término estándar para *matching* en teoría de grafos, y «empaquetamiento» es coherente con «empaquetamiento mixto» en el resto del texto. La Figura 3 sigue con «valor base», arreglado en r1.
- **X-15: RESUELTO en r2.**

## NEW-01 — `Model`
- MD l.1203 «ganancia acotada de `Model`» y TeX l.1084 `{\ttfamily\small Model}`. En el PDF, p. 35, «Model» se ve en monoespaciado (zoom a 140 dpi).
- Coincide con EN y con la versión ES v1.2. Las demás partes de NEW-01 (encabezados 5.1 y Lema 3.2, fila A.2) siguen corregidas: las vi en p. 14, 44 y 41.
- **NEW-01: RESUELTO en r2.**

## Desplazamientos de texto
- La expansión de los términos añade unas 2 líneas en E.1 y desplaza el texto en p. 55–71.
- En las comparaciones r1|r2 que se mostraron (p. 55, 56 y 61–71) no hay texto perdido ni duplicado, y el corte entre páginas es continuo (p. 61→62, 62→63). Las fórmulas (E.1)–(F.12) y (G.1)–(G.5) son idénticas.
- La Tabla 9 se reubica entera en p. 65 y conserva la declaración de X-27.
- La sección de referencias empieza en p. 72 en ambas versiones, y el total sigue en 73 páginas.

## Texto histórico de estado (inalterado a propósito)
Las p. 1, 33, 39 y 40 (y sus equivalentes EN) dicen que las ampliaciones de v1.22 «esperan revalidación» y presentan run_v1.21_r1 como la última revalidación. Era cierto cuando se preparó r1, pero ya no describe el estado actual (r1 PASS; r2 en curso). No es un error matemático ni de correspondencia. Sí es un **problema editorial real si se publica tal cual**, porque un lector entendería que C.3 no está revisado. Lo registro como **OBSERVATION NEW-04**: debe actualizarse antes de cualquier publicación, en ambos idiomas, lo que rompe la identidad byte a byte del inglés y exigirá un control de identidad nuevo. No lo corrijo (mandato §4).

## Veredicto E6 (r2)
**PASS_WITH_OBSERVATIONS.** X-15 y NEW-01 quedan resueltos en el artefacto; el contenido protegido es idéntico; el PDF corresponde al TeX; las 73 páginas se revisaron. Queda una observación editorial, NEW-04 (texto histórico de estado).


---

# NEW-03 — Rectificación del editor (run_v1.22_r2)

## Historia (se conserva, no se reescribe)
- `01_manuscript/v1.22_editorial_candidate/RESPONSE_TO_REVALIDATION_v1.22.md` (sha256 76c86d77…; el directorio r1 está intacto según E0) sigue diciendo dos cosas:
  - Fila X-15: «Se traducen los residuos de matching/packing en prosa española…».
  - Fila NEW-01: «Se restaura el formato del namespace Model donde corresponde».
- run_v1.22_r1 comprobó que ninguna de las dos afirmaciones era cierta en los artefactos españoles entregados y abrió NEW-03 (MINOR). Sus registros (E6_RECORD.md, E8_RECORD.md, FINDINGS.csv) no han cambiado (E0: 188/188 archivos del manifiesto).

## Rectificación en r2
En `01_manuscript/v1.22_editorial_candidate_r2/CORRECTIONS_AND_HANDOFF_v1.22_r2.md`, §«Correcciones y rectificación», punto 3, el editor:
- admite que la respuesta anterior dio por terminadas las dos correcciones cuando no estaban aplicadas;
- califica esa afirmación de incorrecta;
- conserva la respuesta anterior como evidencia histórica, sin reescribirla.

## Evaluación
- **Exactitud de la admisión.** Coincide con la evidencia de run_v1.22_r1: cuando se hizo la afirmación seguían sin traducir 11 + 1 términos en la prosa, y `Model` en ES seguía en redonda.
- **Conservación.** El archivo de respuesta r1 está intacto (E0). La rectificación se añade en un documento nuevo, sin editar el antiguo.
- **Cierre por el artefacto.** E6_RECORD.md verifica de forma independiente X-15 (prosa r2 con 0 residuos) y NEW-01 (`Model` monoespaciado en MD, TeX y PDF).
- **Recuento.** La rectificación dice que el informe narrativo del auditor cuenta doce y la fuente once. Es correcto: el error de recuento era del auditor (CORRECTIONS C3-01), no del editor.

**NEW-03: CERRADO en r2.** Se cierra por la combinación de (a) el artefacto corregido y verificado y (b) la rectificación explícita del editor. La afirmación histórica y el hallazgo de r1 se conservan.
