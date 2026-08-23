# External Adversarial AI Audit Handoff — Papers I–III v1.1.6

**Prepared:** 2026-07-28  
**Editorial state:** near-final candidate for delta audit  
**Release verdict:** `EDITORIALLY_READY_FOR_DELTA_AUDIT`

## Manuscripts

- `PAPER_I_preprint_v1.1.5_near_final_editorial_en.md`
- `PAPER_II_preprint_v1.1.5_near_final_editorial_en.md`
- `PAPER_III_preprint_v1.1.6_near_final_editorial_en.md`

## Frozen Lean packages

| Paper | Snapshot | Build | Project-level mathematical inputs | Archive SHA-256 |
|---|---|---|---|---|
| I | `PAPER_I/05_formalization/lean_v1.1_freeze` | PASS, 8034 jobs | none | `5a1b53324c4d8ee1d45ac22f1d127df98bc7543e5e5bb1e9e07da48d63faa7f0` |
| II | `PAPER_II/05_formalization/lean_v1.0.1_freeze` | PASS, 8059 jobs, 0 errors | none | `dacccc06ff265a2a0da55ed3aac1093486d07806cd0435831738ebca94a4077f` |
| III | `PAPER_III/05_formalization/lean_v1.0_freeze` | PASS, 8060 jobs, 0 errors | exactly AX1 and AX2 | `060957e6b8d54779844dc6adf7cc7c3b8446fc17a87aa8d7a437e9d9d1001b78` |

## Paper III dependency summary

| Regime | External input |
|---|---|
| Bulk | AX1 — Haxell–Rödl/Yuster |
| Sparse independent side | AX2 — Dross + Barber–Kühn–Lo–Osthus, with `E_8` transitively using AX1 as well |
| Near-extremal corridor | none beyond standard Lean foundations |

Lean verifies the internal reduction, construction, and arithmetic layers relative to these inputs.
It does not prove AX1 or AX2.

## Requested audit scope

1. compare manuscript theorem statements with frozen Lean declarations;
2. compare AX1/AX2 with the cited source theorems and their applications;
3. compare dependency descriptions with frozen axiom reports;
4. compare computational claims with packaged scripts and ledgers;
5. check cross-paper notation, versions, and citations;
6. attempt adversarial falsification of mathematics and exposition.

The v1.1.6 pass changed no mathematical content and no Lean source. See the changelog and semantic report.


## Lean-name and audit-folder notes

- Paper II: `PaperII.theorem_1_2` is the historical Lean-ledger name of the declaration corresponding to Theorem 1.1 of the current manuscript, including the attainment statement.
- Paper I: the primary theorem gate is `PaperI.Split.paperI_main_sharp`; `PaperI.paperI_main` is retained only as a traceability gate.
- Paper III: the adversarial audit should reconstruct the counting convention behind the reported 46,481 supplementary checks from the supplied scripts and ledgers.

When copied into paper-specific adversarial-audit folders:

1. update `README.md` to the v1.1.6 manuscript path;
2. update `DELIVERABLE_SPEC.md` to name the v1.1.6 input;
3. update Paper I's `LEAN_VERIFICATION_PROTOCOL.md` as described above;
4. preserve the frozen Lean archive names and hashes already recorded.
