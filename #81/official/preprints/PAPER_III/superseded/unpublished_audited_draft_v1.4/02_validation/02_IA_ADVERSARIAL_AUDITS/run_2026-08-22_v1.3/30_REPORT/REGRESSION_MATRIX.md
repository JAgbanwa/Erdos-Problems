# Mandatory regression matrix -- Paper III v1.3

Every item the request lists, with a new disposition and evidence. As the request demands, the
four things below are stated separately and never conflated: **semantic correspondence**,
**successful compilation**, **axiom footprint**, and **independent mathematical rederivation**.
No mathematical item is marked closed merely because a Lean declaration compiles.

| Item | Disposition | Evidence |
|---|---|---|
| stale integrity or axiom labels | **partly closed**. Publication artifacts carry no stale label. `FREEZE_METADATA.json` is stale (`EXT-V13-003`) and the root docstring is stale (`EXT-V13-006`). | E0, E7 |
| overbroad "resolves the split case" wording | **CLOSED**. Zero occurrences in either language. | E1 |
| `A_{2,J}` / `A_{2J}` inconsistency and combined-citation divergence | **CLOSED**. Zero `A_{2,J}`; notation uniform in Markdown and TeX in both languages. `[3,8]` 2/2 and `[11,17]` 2/2, identical EN/ES. | E5 |
| incomplete citation retrieval and bounded novelty search | **OPEN, unchanged**. Zero of 17 references retrieved in this run; no specialist search possible; `erdosproblems.com` returns HTTP 403. The Cavers survey is absent (`EXT-V13-005`). | E6 |
| the two archived comparison-route axioms and dependency closure | **CLOSED**. `Ax2.PartB.Axioms` and `Ax2.PartA.Wlog` are imported by nobody among 704 project modules; no canonical root's transitive closure reaches either; neither appears in any of the 42 axiom footprints. | E4 |
| missing graph/Yuster model bridge | **CLOSED**. Present in v1.3 as seven canonical lemmas, and independently validated against a bridge the auditor built and proved itself. | E3 |
| `K-EPS` | **NOT ATTEMPTED**. The AX1/nibble epsilon ledger, parameter ranges, conversions, exceptional-set and rounding terms, and the accumulation inside `eps n^2`. | E2 |
| `K-CORRIDOR` | **NOT ATTEMPTED**. Sections 5-7. Section 9 uses Lemmas 5.1, 5.2, 6.1 and 7.1 as inputs; this audit verified how Section 9 combines them, not that they are true. | E2 |
| `K-SPARSE` | **NOT ATTEMPTED**. Section 8, which closes the `alpha -> 0` endpoint and supplies `C_0`. Case C of the cover is therefore closed only modulo Section 8. | E2 |
| `K-COVER` | **CLOSED**. Four levels checked: the integer split `q >= 2p-1`; the subsequence trichotomy by Bolzano-Weierstrass on `[0,2]`; the `sqrt p` split inside Case D; and the dispersion dichotomy. Exhaustive and non-overlapping. | E2 |
| `K-GLOBAL` | **PARTIAL**. The minimal-counterexample frame and the step to (9.2) were checked, and the formal counterpart `global_bound_from_eventual_high_degree` was read: it converts an eventual bound with constant 2 into `Phi <= n^2/6 + max(2,N) n` for all split graphs. Not verified: `Phi(G) <= Phi(G-v) + d(v)` for every vertex of every split graph, and the small orders. | E2, E3 |
| correspondence of manuscript AX1/AX2 to `AX1Assumption`/`AX2Assumption` | **CLOSED**. AX1 by an `iff` proved in both directions; AX2 by implication with both coercions checked (`0.9` against `9/10`, `3 divides card` against `card % 3 = 0`). No added split, chordal, density or divisibility hypothesis. | E3 |
| quantitative tolerances and the hypergraph-to-graph bridge | **bridge CLOSED, tolerances NOT ATTEMPTED**. The bridge is proved universally, including that the Nibble side's extra capacities on non-edges are vacuous. The tolerances are `K-EPS`. | E3, E2 |
| independent rederivation of Sections 4-9 | **Sections 4 and 9 rederived; Sections 5-8 not**. Section 9's ten numbered inequalities are exact, three of them tight at their boundaries. | E2 |

## The four statuses, separately

| Status | Result |
|---|---|
| semantic correspondence | **PROVED** for AX1 (iff), AX2 (implication), the decomposition predicate, and the four canonical bridges |
| successful compilation | **YES**: 8,444 jobs, exit 0, zero errors, from an absent project `.lake/build` against the exact pinned revisions |
| axiom footprint | **CLEAN**: 42 surfaces, all foundational, 0 `sorryAx`, 0 project axioms; one surface is even smaller, `[propext, Quot.sound]` |
| independent mathematical rederivation | **PARTIAL**: Sections 4 and 9 yes; the epsilon ledger and Sections 5-8 no |
