# Paper III — Lean formalization STATUS (source of truth, on disk)

> Update after every node closed / build / Aristotle submission. Read at session start.
> Verify from the git object (`git show HEAD:<path>`), never from memory (Dropbox flapping).

## Snapshot (2026-07-25)
- **Toolchain:** Lean `leanprover/lean4:v4.28.0` + Mathlib `v4.28.0` (manifest commit `8f9d9cff…`).
- **Modules:** 25 core — **all sorry-free**. (Repo also carries reusable, axiom-clean `DiracHamilton` and `DiracMatching`.)
- **Sorries:** **0**. No escape hatch anywhere (`sorry`/`admit`/`native_decide`/`unsafe`/`opaque`/`implemented_by`/`sorryAx` = 0).
- **Trajectory:** 13 → 12 → 9 → 8 → 7 → 6 → **0** — SORRY-FREE milestone 2026-07-24 (see `AXIOM_REPORT.txt`; full build 8057 jobs, 0 errors, 0 sorries).
- **Axioms:** exactly `AX1`, `AX2` (Layer X). Footprint of `Theorem_1_1`: `[propext, Classical.choice, Quot.sound, AX1, AX2]`.
- **Theorem 1.1: CLOSED**, machine-checked modulo `AX1`, `AX2`; Corollary 1.2 likewise. E-4.3 (bulk) carries `AX1` only; Prop 10.1 and the elementary core carry only the standard triple.
- **Verification note (2026-07-25, this update):** sorry-freeness re-confirmed by source grep of all 34 `.lean` (0 matches) and by reading `AX.lean` (only `AX1`/`AX2`); the 8057-job clean build is recorded in `AXIOM_REPORT.txt`. A fresh `lake build` was **not** re-run in this update; the clean-compile claim rests on that report pending independent reproduction.

## Complete module table

### Sorry-free — OK (all core modules; the four formerly-pending modules E_5, E_7, E_8, E_D are now closed — see below)
| Module | Ledger node / role | Layer |
|---|---|---|
| `Defs.lean` | SplitGraph structure; ν₃, ν₃*, Φ, notation (§0) | E |
| `SplitEdges.lean` | edge-set structure of split graphs | E |
| `Identities.lean` | algebraic identities | E |
| `Counting.lean` | counting helpers | E |
| `Factorization.lean` | χ'(K_t) complete-graph factorizations (§2.3) | E |
| `Duality.lean` | LP weak duality (Farkas) for E-3.1 | E |
| `CorridorDefs.lean` | corridor defs (s, D, aₓ, dispersion) | E |
| `AX.lean` | **AX1, AX2** (the only two axioms; Layer X) | X |
| `E_3_1_LP.lean` | E-3.1 — reduced 4-orbit LP | E |
| `E_3_1_upper.lean` | E-3.1 — upper bound (feasible covers) | E |
| `E_3_1_values.lean` | E-3.1 — the three cover-vertex values | E |
| `E_4_agg.lean` | **E-3.1** assembled + **E-4.1** replication (Lemma 4.1) | E |
| `E_4_2_algebra.lean` | E-4.2 — (4.5) completion-of-squares algebra | E |
| `E_4_2.lean` | **E-4.2** unified fractional margin (Theorem 4.2) | E |
| `E_4_3.lean` | **E-4.3** bulk consequence (uses AX1) | X |
| `E_6.lean` | **E-6.1** polarization inequality (Lemma 6.1) | E |
| `E_B.lean` | **E-B** divisibility correction (Appendix B) | E |
| `Prop_10_1.lean` | **Prop 10.1** low + mid (unconditional corridor) | E |
| `CliquePartition.lean` | cp(G) ≤ |E|−2ν₃ bridge (1.1) | E |
| `Main.lean` | **Theorem 1.1** (E-9) + **Corollary 1.2** assembly | X |
| `Addenda.lean` | Corollaries 10.4 / 10.4b / 12.2 | E/X |

### Formerly pending — now closed (2026-07-24)
All six leaves that were open through v0.9.5 are discharged and sorry-free:
| Module | Ledger node | Closed leaf lemma(s) | Layer |
|---|---|---|---|
| `E_5.lean` | E-5.1 (Lem 5.1), Cor 5.3, E-5.2 (Lem 5.2) | `E_5_1`, `cor_5_3`, `E_5_2` | E |
| `E_7.lean` | E-7.1 (Lem 7.1) | `exists_reserved_gain_packing` | E |
| `E_8.lean` | E-8 (sparse, uses AX2) | `E_8_very_sparse_packing_estimate` | X (AX2) |
| `E_D.lean` | E-D.1/2/3 (Appendix D) | `saturated_vertex_matching` | E |

## Layer classification
- **Unconditional (no axioms):** E-3.1, E-4.1, E-4.2, E-5.1, E-5.2, E-6.1, E-7.1, E-B,
  E-D.1/2/3, **Prop 10.1**, all identities. (All closed and sorry-free.)
- **Axiom-relative (AX1 and/or AX2):** E-4.3 (AX1), E-8 (AX2), and therefore E-9 / Theorem 1.1.

## Aristotle jobs (Paper III)
| project_id | node / prompt | status | retrieved? |
|---|---|---|---|
| (fill as submitted — e.g. E_7 exists_reserved_gain_packing, E_8 very_sparse, E_5 rounding) | | | |

## Next actions
1. Freeze the release: pin the commit, the axiom report (`AXIOM_REPORT.txt`), and the Lean toolchain + manifest.
2. Independent reproduction: fresh `lake build > p3_build.log 2>&1` (expect 0 errors / 0 sorries) and `lake env lean gate.lean > p3_gate.txt` to re-confirm the axiom footprints from a clean checkout.
3. Keep this file in sync with the frozen commit; only then promote the manuscript wording to "formally verified".

## Change log
- 2026-07-25 — updated to the SORRY-FREE state (milestone 2026-07-24, `AXIOM_REPORT.txt`): 0 sorries,
  all 25 core modules closed, Theorem 1.1 machine-checked modulo AX1/AX2. Re-confirmed by source grep
  (34 `.lean`, 0 sorry) and `AX.lean` (only AX1/AX2); fresh `lake build` not re-run in this update.
- 2026-07-21 — status table created; 6 sorries across E_5(3)/E_7/E_8/E_D; M1 + Prop 10.1
  closed; Theorem 1.1 assembly compiles (transitively open).
