# Lean formalization — reference for the formalization audit (Block F)

**STATUS: FROZEN, SORRY-FREE.** The Lean 4 / Mathlib formalization is complete at the release
commit recorded in `RELEASE.txt` (`fcb49bb…`, 2026-07-24). `lake build` = 8058 jobs, 0 errors,
0 `sorry`; the trusted base is exactly the two intended Layer-X axioms `AX1`, `AX2`. **Block F
is now live** — run it (do not defer).

## What is shipped here

- **`lean_snapshot/`** — the **actual frozen Lean sources** (`lean_snapshot/lean/…`), bundled
  so this package is self-contained. It must **byte-match** `git archive <release-sha> -- lean`
  (see `RELEASE.txt`); any mismatch is a finding. Mathlib itself is **not** shipped — fetch it
  with `lake exe cache get` for the pinned revision.
- **`RELEASE.txt`** — the frozen commit SHA, toolchain, Mathlib revision, escape-hatch scan,
  and the verbatim axiom report to check against.
- **`lean-toolchain`** — pins `leanprover/lean4:v4.28.0` (copied from the snapshot). A
  different toolchain is itself a finding.
- **`lakefile.toml`** — the Mathlib dependency/revision (copied from the snapshot).
- **`gate.lean`** — the axiom/statement gate (`#print axioms` + `#check`). Copy it into
  `lean_snapshot/lean/` and run `lake env lean gate.lean`.
- **`MODULE_LIST.txt`** — the full module inventory at the release commit (33 modules).

## How to run Block F (self-contained)

```
cd lean_snapshot/lean
lake exe cache get           # fetch Mathlib oleans for the pinned revision
lake build                   # expect 8058 jobs, 0 errors, 0 sorry
cp ../../gate.lean .
lake env lean gate.lean      # axiom report + signature checks (F2/F3)
```
Independently reconstruct and diff to confirm the bundled snapshot is honest:
```
git archive <release-sha> -- lean | tar -x -C /tmp/reconstructed
diff -r /tmp/reconstructed/lean lean_snapshot/lean    # must be empty
```

## Ledger ↔ module map (confirm against the frozen sources)

| Ledger node | Lean declaration(s) | Layer / axioms |
|---|---|---|
| E-3.1 | `PaperIII.E_3_1` (+ `_LP`, `_upper`, `_values`) | E — clean |
| E-4.1 | `PaperIII.E_4_1` (`E_4_agg`) | E — clean |
| E-4.2 | `PaperIII.E_4_2` (+ `_algebra`) | E — clean |
| E-4.3 | `PaperIII.E_4_3` | X — `AX1` |
| E-5.1 / 5.2 / Cor 5.3 | `PaperIII.E_5_1`, `E_5_2`, `cor_5_3` (`E_5`) | E — clean |
| E-6.1 | `PaperIII.E_6_1` (`E_6`) | E — clean |
| E-7.1 | `PaperIII.E_7_1` (`E_7`; via `qqi_family`/`rrq_family`/`irq_family`) | E — clean |
| E-8 | `PaperIII.E_8` (`E_8`, `E_8_Core`, `E_8_Divisible`) | X — `AX1`,`AX2` |
| E-B | `PaperIII.pathCorrection_odd_iff` (`E_B`) | E — clean |
| E-D.1/2/3 | `PaperIII.AppendixD.*` (`konig_edge_coloring`, `galvin_max_degree`, …) (`E_D`) | E — clean |
| Prop 10.1 | `PaperIII.Prop_10_1_low`, `Prop_10_1_mid` | E — clean (no axioms) |
| Theorem 1.1 | `PaperIII.Theorem_1_1` (`Main`) | X — `AX1`,`AX2` |
| Corollary 1.2 | `PaperIII.Corollary_1_2` (`Main`) | X — `AX1`,`AX2` |
| AX1 / AX2 | `PaperIII.AX1`, `PaperIII.AX2` (`AX.lean`) | X — the ONLY two `axiom`s |

**Support machinery proved from scratch (not in Mathlib; must also be `sorry`-free):**
`DiracHamilton` (Hamiltonicity from min-degree), `DiracMatching` (near-perfect matching from
min-degree), the §8 divisibility correction (`E_8_Divisible`), the 1-factorization and
König/Galvin list edge-colouring (`Factorization`, `E_D`). Idiomatic Mathlib-ready drafts of
Dirac/matching live under `PaperIII/Contrib/Submission/` (informational; not load-bearing for
the paper's theorem).

Any renamed, missing, or extra **load-bearing** declaration, any `sorry`/`sorryAx`, or any
third `axiom`, is a finding.
