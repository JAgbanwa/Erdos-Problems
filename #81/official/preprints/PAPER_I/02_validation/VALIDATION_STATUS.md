# Public validation status

## Main claim

For every split graph \(G\) on \(n\) vertices,

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n.
\]

## Recorded project state

| Dimension | State |
|---|---|
| Mathematical status | `FINAL_PASS` |
| Lifecycle | `FROZEN` |
| Dependency health | `CLEAN` |
| Editorial release | `PREPRINT RELEASE v1.0` |
| Internal validation | AI-assisted adversarial audit |
| Release approval | Editor and researcher approved |
| External peer review | Not performed |
| Novelty / priority review | `NOT ASSESSED / INCOMPLETE` |

## Public evidence

- official preprint in PDF, LaTeX, and Markdown;
- calculation ledger with equation mapping and loss accounting;
- SHA-256 release manifest;
- reproducible LaTeX build instructions.

## Scope boundary

This release does not certify:

- an integral triangle-packing theorem;
- a clique-partition theorem;
- an asymptotic transfer result;
- a theorem for all chordal graphs;
- novelty, priority, or peer-reviewed publication.

## Independent AI adversarial audit (added 2026-07-10)

An independent AI adversarial audit (`PAPER_I_EXT_AUDIT_2026-07-10`, deep protocol)
returned **PASS**: analytic proof independently re-derived; Lean certificate
re-elaborated in a fresh tree (`paperI_main` + `residual_duality`, axioms
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`); 622-split-graph
falsification with no violation. Report under
`02_IA_ADVERSARIAL_AUDITS/20_EVIDENCE/ERDOZ81-P1-FRAC-THM-01/PAPER_I_EXT_AUDIT_2026-07-10/`.
This is an intermediate assurance tier (indep