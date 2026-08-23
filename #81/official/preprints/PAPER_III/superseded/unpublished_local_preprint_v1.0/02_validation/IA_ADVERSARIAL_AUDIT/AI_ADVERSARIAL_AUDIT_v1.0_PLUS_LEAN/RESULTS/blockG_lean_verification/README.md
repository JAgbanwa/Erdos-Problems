# Block G — Lean Verification

**Verdict: PASS_WITH_OBSERVATIONS**

- **Paper:** "Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing" (Paper III, v1.1.5)
- **Date:** 2026-07-28
- **Auditor:** Claude Opus 4.8 (Anthropic), invoked via Claude Code
- **Lean freeze:** `PAPER_III/05_formalization/lean_v1.0_freeze`

## Environment

- Lean toolchain: `leanprover/lean4:v4.28.0`
- Mathlib: `v4.28.0` (rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`)
- Mathlib **not** reinstalled; existing local cache reused (per protocol).

## Build

```
lake build PaperIII
Build completed successfully (8060 jobs).
```

0 errors; 64 linter warnings (unused variables / simp args / one `push_cast` no-op). Full log:
`results/lake_build.log`.

## Escape-hatch / axiom scan

Independent grep over all `PaperIII/*.lean` sources (see `results/escape_hatch_scan.txt`):

- `sorry`, `admit`, `unsafe`, `native_decide`: **zero** occurrences in source code.
- `axiom` declarations: **exactly two** — `AX1`, `AX2` (both in `PaperIII/AX.lean`), both external
  literature inputs (see Block B). No other project axioms.

## Axiom gates (`#check` + `#print axioms`)

Gate file: `results/AuditGates_PaperIII.lean`; captured output: `results/axiom_gates.txt`. Run via
`lake env lean AuditGates_PaperIII.lean`.

### Node classification

Standard foundation = `{propext, Classical.choice, Quot.sound}`.

| Lean node | Manuscript role | `#print axioms` footprint | Class |
|---|---|---|---|
| `Theorem_1_1` | Theorem 1.1 (assembly, §9) | standard + `AX1` + `AX2` | **AX1+AX2** |
| `Corollary_1_2` | Corollary 1.2 (cp bound) | standard + `AX1` + `AX2` | **AX1+AX2** |
| `E_4_3` | Bulk node (§4.3, §9.1) | standard + `AX1` | **AX1** |
| `E_8` | Sparse node (§8) | standard + `AX1` + `AX2` | **AX1+AX2** (see obs.) |
| `Prop_10_1_low` | Corridor short (§10.5) | standard only | **closed** |
| `Prop_10_1_mid` | Corridor mesoscopic (§10.5) | standard only | **closed** |
| `Phi_le_high_ratio` | High-ratio disposal (§5) | standard only | **closed** |
| `nu3Star_le_tau3Star` | Weak LP duality (§11.6) | standard only | **closed** |
| `factorization_assignment_packing` | Packing corollary (v1.1) | standard only | **closed** |
| `double_factorization_packing` | Packing corollary (v1.1) | standard only | **closed** |
| `reserved_gain_packing_bound_subset` | Packing corollary (v1.1) | standard only | **closed** |
| `Corollary_12_2_bound` | Effective corridor cp-bound | standard only | **closed** |
| `cp_le_Phi` | eq. (1.1) bridge | standard only | **closed** |
| `AX1` | external input | self + standard | axiom |
| `AX2` | external input | self + standard | axiom |

### What matches the manuscript

- **Theorem 1.1 / Corollary 1.2** carry exactly `AX1 + AX2` + standard — matching the manuscript's
  explicit statement that both results are conditional on AX1 and AX2. ✓
- **The corridor is genuinely closed.** `Prop_10_1_low`, `Prop_10_1_mid`, the three v1.1 packing-form
  corollaries, `Corollary_12_2_bound`, `Phi_le_high_ratio`, and `cp_le_Phi` all carry **only**
  `{propext, Classical.choice, Quot.sound}` — no AX1, no AX2. This confirms the manuscript's headline
  structural claim (Abstract; §11.6 line 1822): "Proposition 10.5, the corridor-specific lemmas, ...
  carry only propext, Classical.choice, Quot.sound." ✓
- **AX2 appears only in sparse-type nodes** (`E_8`) and the final assembly; it is absent from `E_4_3`
  (bulk) and the corridor. ✓
- **The bulk node `E_4_3` carries AX1 only** (no AX2). ✓
- Weak duality `nu3Star_le_tau3Star` is a genuine closed theorem (no strong-duality axiom). ✓

### Observation O-G1 (minor): sparse node `E_8` carries AX1 + AX2, not AX2-only

Manuscript §11.6 (line 1822) states: *"The frozen dependency report records ... `AX1` for the bulk
node, and `AX2` for the sparse node,"* and the §11.6 audit table (line 1839) lists the "Sparse node
(§8)" as *"proved, relative to `AX2`."* The `E_8.lean` module docstring likewise lists only
"Dirac, Turán (K₅), **AX2**, and ... E-B."

The gate shows `E_8` depends on **`AX1` and `AX2`**. Root cause (verified by source reading,
`E_8.lean:164-215`): the exposed sparse node `E_8` is stated with hypothesis `2·q ≤ p` (i.e.
`α ≤ 1/2`), and its proof splits on `12·q < p`:

- **very-sparse** subrange `12q < p`: handled by `E_8_very_sparse_packing_estimate` →
  `E_8_packing_exists` → **AX2** (genuinely AX2-only; does not call `E_4_3`);
- **complementary** subrange `p/12 ≤ q ≤ p/2` (i.e. `α ∈ [1/12, 1/2]`): dispatched to
  `E_4_3 (1/12)` (`E_8.lean:170`), which carries **AX1**.

So the *node used in the final assembly* (`E_8`, range `2q ≤ p`) legitimately overlaps the bulk
regime and reuses the bulk lemma there, inheriting AX1.

**Assessment.** This is a **precision/packaging** discrepancy, **not** a mathematical or scope defect:

1. It does not weaken Theorem 1.1, which is `AX1 + AX2` regardless and stated as such.
2. The intermediate range `α ∈ [1/12, 1/2]` genuinely *is* bulk-type; using AX1 there is correct.
3. The manuscript's regime *taxonomy* (bulk = `α ∈ [ε, 2−ε]` → AX1; sparse = `α → 0` → AX2) is
   internally consistent; only the finer statement "the [formalized] sparse node carries AX2 [only]"
   is inaccurate for the `E_8` wrapper actually consumed by `eventual_bound_of_high_degree`. It holds
   for the very-sparse *core* `E_8_very_sparse_packing_estimate`.

**Recommended editorial fix (non-blocking):** amend §11.6 (and the `E_8.lean` docstring) to record the
sparse *node* `E_8` as `AX1 + AX2`, or restate the attribution against the very-sparse core lemma.
Recorded as finding **F-G05** (severity: minor; sub-claim "sparse node depends on AX2 only" =
REFUTED; all headline claims CONFIRMED).

### Observation O-G2 (none): AX1 bundles strong LP duality

See Block B / finding F-B02. AX1 is stated cover-side (`τ₃* − ν₃ = o(n²)`); the equality
`ν₃* = τ₃*` (finite LP strong duality) is folded into the imported axiom, while Lean proves only weak
duality `nu3Star_le_tau3Star`. Both components are standard; disclosed by the authors (§11.6 line 1817).

## Statement-to-manuscript table

| Lean type | Manuscript statement |
|---|---|
| `Theorem_1_1 : ∃ C, ∀ G, ↑G.Phi ≤ ↑G.n^2/6 + C*↑G.n` | Thm 1.1: `|E|−2ν₃ ≤ n²/6 + Cn` |
| `Corollary_1_2 : ∃ C, ∀ G, ↑G.cp ≤ ↑G.n^2/6 + C*↑G.n` | Cor 1.2: `cp(G) ≤ n²/6 + Cn` |
| `AX1 : ∀ ε>0, ∃ n₀, ∀ G large, τ₃*(G) − ν₃(G) ≤ ε·n²` | Thm 2.1 (Haxell–Rödl/Yuster) |
| `AX2 : ∀ ε>0, ∃ n₀, ∀ H tri-divisible large, δ≥(0.9+ε)n → decomposes` | Thm 2.3 (Dross + BKLO) |

## Conditional vs unconditional (protocol requirement)

- **Conditional on AX1 + AX2:** `Theorem_1_1`, `Corollary_1_2`, `E_8` (assembly + sparse node).
- **Conditional on AX1 only:** `E_4_3` (bulk).
- **Unconditional (closed):** corridor (`Prop_10_1_low/mid`, `Phi_le_high_ratio`), weak duality, the
  three packing-form corollaries, `Corollary_12_2_bound`, `cp_le_Phi`, and all E-3/E-4-algebra/E-5/6/7
  layers.

## Conclusion

The freeze builds cleanly (8060 jobs, 0 errors), contains exactly two documented external axioms and
zero escape hatches, and its theorem statements faithfully encode the manuscript claims. The
conditional/unconditional structure matches the manuscript **except** for the minor per-node
attribution issue O-G1 (sparse node `E_8` is `AX1+AX2`, not `AX2`-only). No blocking defect.

**Block G verdict: PASS_WITH_OBSERVATIONS.**
