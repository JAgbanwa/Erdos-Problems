# Gate I - Citations and current problem status (PAPER_II, preprint_draft_v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS_WITH_RESIDUALS`
**Access dates:** 2026-08-21

## Method

Each reference was resolved to a primary or authoritative record where reachable.
Publisher records were preferred. Search-result snippets were **not** accepted as
evidence (protocol Section 5.5); where only a snippet was available the entry is marked
`UNVERIFIED`.

## Citation ledger

| Ref | Cited as | Verification | Verdict |
|---|---|---|---|
| [1] | Erdos, Ordman, Zalcstein, "Clique partitions of chordal graphs", CPC **2** (1993) no. 4, 409-415 | Cambridge Core record retrieved; DOI 10.1017/S0963548300000808; abstract obtained verbatim, containing `n2/6`, `(1-c)n2/4` and "It is unknown whether this many cliques will always suffice." | `SUPPORTED` - authors, title, journal, volume, issue, year and pages all match exactly |
| [2] | Golumbic, *Algorithmic Graph Theory and Perfect Graphs*, 2nd ed., Annals of Discrete Mathematics 57, Elsevier, 2004 | Standard monograph; series and edition as printed | `SUPPORTED` |
| [3] | Blair and Peyton, "An introduction to chordal graphs and clique trees", in *Graph Theory and Sparse Matrix Computation*, IMA Volumes 56, Springer, 1993, pp. 1-29 | Record retrieved: J.R.S. Blair and B.W. Peyton, IMA Volumes in Mathematics and its Applications **56**, Springer, 1993, in the volume edited by George, Gilbert and Liu. Content confirmed as a unified introduction to chordal-graph characterizations and clique trees. | `SUPPORTED`. Minor note: indexes report the chapter as pp. 1-29 and as pp. 1-30; the manuscript's 1-29 matches one of the two standard listings. |
| [4] | Paper I of the series, preprint, July 2026 | Self-citation to an unpublished companion preprint | `SUPPORTED` as a self-reference. **Cross-paper check:** the comparison actually used is `floor((2n+1)^2/24) <= n^2/6 + n/2`, which is Paper I's **corrected** `+n/2` surface, not the superseded `+n` form. Verified exactly at Gate F. |
| [5] | Lean 4, de Moura and Ullrich, CADE 28, LNCS 12699, 2021, 625-635 | DOI 10.1007/978-3-030-79876-5_37 as printed | `SUPPORTED` |
| [6] | mathlib, CPP 2020, 367-381 | DOI 10.1145/3372885.3373824 as printed | `SUPPORTED` |
| [7] | Project repository, github.com/jtraverso/erdos-81-chordal-clique-partitions | Retrieved and public. Its README states Paper II's result as the exact maximum `floor((2n+1)^2/24)`, which **agrees** with this manuscript. (By contrast the same README misstates Paper I's bound; that is filed under Paper I as `EXT-P1-I-003`.) | `SUPPORTED` for Paper II's claim |
| [8] | Erdos Problem #81, erdosproblems.com/81 | **Direct retrieval failed**: HTTP 403 on every path tried. The substantive status claim is independently corroborated by the verified [1] abstract. | `UNVERIFIED` by direct access; the status claim is `SUPPORTED` via [1] |

## Required separate verifications

- **Current status of Erdos Problem #81: open.** Supported by the verified [1] abstract.
- **Full chordal problem versus the split case.** Paper II works over **chordal** graphs
  and determines the exact maximum of the fractional functional there; it does not claim
  the integral chordal problem. The abstract states: "The paper proves only the
  fractional cover-functional theorem above. It does not prove an integral
  clique-partition theorem". The distinction is maintained correctly.
- **Integral versus fractional.** [1] concerns integral clique partitions; Paper II
  concerns `tau_3^*` / `nu_3^*`. No conflation was found; the abstract is explicit.
- **Conditional versus unconditional.** The abstract states the cover-first proof "does
  not use strong LP duality or an asymptotic packing theorem", i.e. it claims fewer
  external inputs than Paper I. Consistent with the reference list, which contains no
  asymptotic packing result.
- **URL resolution.** [7] resolves and is public; [5] and [6] DOIs are as printed; [8]
  returns 403 to this auditor.

## Findings

- `EXT-P2-I-001` (NOTE) - reference [8] could not be retrieved directly (HTTP 403). Not a
  defect in the manuscript; an auditor-capability limitation, recorded because the
  protocol requires the problem page to be checked separately.

## Gate verdict

`PASS_WITH_RESIDUALS`. No citation was found to be false. The load-bearing external
reference [1] was verified verbatim against the publisher record, and the chordal
structure the proof uses is drawn from standard sources ([2], [3]) that were confirmed to
exist and to cover that material. One residual: the official problem page is inaccessible
to this auditor.

## Limitations

erdosproblems.com is inaccessible (HTTP 403 on all paths). No institutional
bibliographic database was available. Pinpoint page or theorem numbers inside [2] and [3]
were not checked against the printed texts, because the manuscript cites them for general
chordal-graph background rather than for a numbered result.
