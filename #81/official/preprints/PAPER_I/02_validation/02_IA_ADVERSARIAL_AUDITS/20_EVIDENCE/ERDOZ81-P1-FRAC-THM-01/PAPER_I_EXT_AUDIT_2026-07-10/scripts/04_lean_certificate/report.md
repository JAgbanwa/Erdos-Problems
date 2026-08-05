# Script 04 — Lean Formal Certificate Audit (Gate H)

**Audit:** PAPER_I_EXT_AUDIT · **Script:** `04_lean_certificate.py`
**Toolchain:** Lean 4 `v4.28.0` + Mathlib `v4.28.0` (elan 4.2.3, lake 5.0.0)

## Purpose

Independently verify the manuscript's formal-verification claims for Theorem 1.1
(`paperI_main`) and Proposition B.1 (`residual_duality`).

## Independent build

The release Lean sources were copied to a **fresh directory with no inherited `.lake`
build** (`C:\Users\jtrav\l`), the Mathlib olean cache fetched via `lake exe cache get`
(community Azure cache; not the author's build), and `lake build PaperI.PaperI_Statement`
run to completion. The build log and script are archived as `independent_build.log` /
`independent_build.sh`; the axiom lines as `independent_axioms_and_exit.txt`.
(Windows long-path handling required a short build root + `core.longpaths=true` via
`GIT_CONFIG_*` env; see ENVIRONMENT.md.)

Result: **`Build completed successfully (8027 jobs)`, exit 0.**

```
PaperI.paperI_main            depends on axioms: [propext, Classical.choice, Quot.sound]
PaperI.Split.residual_duality depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one of the ~30 intermediate declarations likewise depends only on the three
standard foundational axioms. No `sorryAx`, no `native_decide`, no added `axiom`.

## Sub-checks

| Check | Result |
|---|---|
| **H1** `paperI_main : Phi ≤ n²/6 + n`, `Phi = edgeCount − 2·nu3star` (= Theorem 1.1) | **PASS** |
| **H2** sources free of real `sorry`/`admit`/`native_decide`/`axiom` (comments excluded) | **PASS** (5/5 files clean) |
| **H3** SHA-256 of released lean tree == `04_integrity/SHA256SUMS.txt` | **PASS** (8/8 files MATCH) |
| **H4** independent fresh-tree build: exit 0; axioms `[propext, Classical.choice, Quot.sound]`; no `sorryAx` | **PASS** |
| **H5** independent axioms == recorded `gate_logs/print_axioms_residual_and_main.log` | **PASS** (identical) |

## Verdict

**GATE H: PASS.** The Lean statement is exactly Theorem 1.1; the released sources are
sorry-/axiom-clean and match the recorded manifest by SHA-256; and an **independent
rebuild** reproduces `Build completed successfully` with `paperI_main` (and the LP-duality
node `residual_duality`) depending only on Lean/Mathlib's three standard foundational
axioms. The finite LP strong duality used in Prop B.1 is derived inside the development
(`residual_duality` ← `covering_packing_duality` ← finite Farkas), not postulated as a
project axio