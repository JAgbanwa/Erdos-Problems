# E1 — Statements (r3)

## Impact control
`IMPACT_CHECK.json` and `E6_R3_DELTA.json` show that only five documentary paragraphs per language changed. No statement, formula, tag, table row, heading or reference changed. The 21 historical rows of the run_v1.2_r1 map are therefore **inherited and revalidated by identity**; all are MATCH, and G.2 was "not re-extracted".

## Supplementary rows (executed in r3)
The 13 headers in `SEMANTIC_HEADERS.json` were verified independently against the original files (`10_SCRIPTS/e1e3_headers_check.py` → `E1E3_HEADERS_CHECK.json`):
- the source sha256 equals both the manifest and the JSON;
- the line number is correct;
- the header text equals an independent re-extraction (stopping at `:=` at bracket depth 0);
- the namespace is correct, and no hidden hypotheses come from `variable` declarations;
- the run_v1.2_r1 log is hash-bound and its module is PASS with exit 0.

The definitions used (`splitBaseline`, `outsideEdges`, `missingIncidences`, `graphFamDistNorm`, `allSplitSupports`, `CertifiedFractionalOptimum`, `NearStructureWitness`, `RegularizedRoot.isClique`, `rootPieceDefect`/`numericDefect`, `splitGraph`, `CleanupAtWith`, `eps`/`eta`) were read in the frozen sources.

Result: 12 new rows N1–N12, all **MATCH** (`30_REPORT/CLAIM_MAP_CONSOLIDATED.md`). They are labelled as new and are not attributed to the original E1. The cautions of the mandate were checked:
- C is not a clique of G (N3);
- the size difference is not a symmetric difference (N3);
- D.3 also requires the bounded constructor plus identity (1.3a) (N10);
- real coefficients go through rational enlargement (N6, N8);
- G.2 is closed (N11, N12).

One new scope observation: the linear-coefficient header (N8) is existential in G, and the identity cp(G) = M(n) for the named witness comes from (6.2) and Theorem B. This is the same nature as X-17, recorded as an extension of X-17.

Observations still in force: X-17 (now also N8) and X-18. Both are scope limits; no action is needed before publication.

**E1 verdict (r3): PASS.** Historical rows inherited and revalidated by identity; 12 new rows executed in r3.
