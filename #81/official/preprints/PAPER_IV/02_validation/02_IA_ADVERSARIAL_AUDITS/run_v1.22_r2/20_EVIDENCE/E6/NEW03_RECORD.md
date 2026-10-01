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
