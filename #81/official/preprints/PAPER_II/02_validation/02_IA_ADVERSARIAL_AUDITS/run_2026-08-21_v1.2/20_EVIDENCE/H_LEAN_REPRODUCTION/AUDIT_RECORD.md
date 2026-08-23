# Gate H - Independent Lean reproduction and conformance (PAPER_II, v1.2)

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Verdict:** `PASS`

## 1. Archive verified before extraction

```
ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895  PAPER_II_lean_v1.2_freeze.zip
```
Matches the protocol Section 9.2 expected hash exactly. Computed **before** extraction.

## 2. Clean room provably free of inherited build state

Extracted into the new, empty short root `C:\erdos_audit\PII`. Immediately after
extraction and **before** any build step, `find` for `.lake` and `*.olean` returned
nothing. **42 project `.lean` files**, matching the freeze metadata's `lean_source_files: 42`.

## 3. Toolchain and pin

| Item | Observed | Protocol expectation | Match |
|---|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.28.0` | 4.28.0 | **yes** |
| Lean actually used | 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` | - | - |
| Mathlib in `lake-manifest.json` | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | same | **yes** |

`lake update` exited 0 and did not mutate the pin. `lake exe cache get` exited 0
("Already decompressed 8010 file(s)").

## 4. Commands, exit codes, elapsed time

All logs are directly visible files under `results/`, not only inside a ZIP.

| Step | Command | Exit | Elapsed |
|---|---|---|---|
| 1-2 | `lake update`; `lake exe cache get` | 0 | - |
| 3 | the exact protocol Section 9.2 command: `lake build PaperII PaperII.AsymptoticCorollaries PaperII.AxiomCheckCorollaries PaperII.Extremizer PaperII.CopyDefect Contrib.Submission.Chordal Contrib.Submission.GeodesicChordless` | **0** | **30m05.109s** |
| 4 | `lake env lean FreezeAxioms.lean` | **0** | - |

**Result:** `Build completed successfully (8063 jobs).` **Zero errors**
(`grep -ciE "^error|error:"` returns 0). The only diagnostics are Mathlib style warnings
about automatically included section variables being unused in three theorems.

**On the job count.** The manuscript records a main build of **8,061** jobs and a separate
supplement build of **8,032**. This run produced **8,063** in a single invocation covering
all seven protocol targets at once. The difference is expected: it is a different target
set, not a discrepancy. Reported here rather than glossed.

## 5. Explicit multi-target build versus aggregate-root coverage

The protocol warns specifically that "the aggregate `PaperII` target does not by itself
prove that `Extremizer` and `CopyDefect` are imported", and asks for the two to be
reported separately.

- The build command names `PaperII.Extremizer` and `PaperII.CopyDefect` as **explicit
  targets**, so their compilation is established by explicit enumeration.
- `FreezeAxioms.lean` imports `PaperII.Unconditional`, `PaperII.Extremizer`,
  `PaperII.CopyDefect`, `PaperII.AsymptoticCorollaries`, `Contrib.Submission.Chordal` and
  `Contrib.Submission.GeodesicChordless` **directly**, so the axiom queries below run in an
  import closure that provably contains those modules - it is not relying on the aggregate
  root to pull them in.
- **No first axiom attempt failed** in this run, so there is no failed-attempt log to
  preserve for this paper. The protocol asks that such a failure be preserved and explained
  if it occurs; it did not occur.

## 6. Theorem-level axiom footprint

`FreezeAxioms.lean` queried **16** declarations, exit code 0. Verbatim output is in
`results/03_FreezeAxioms_run.log`. Summary:

| Declarations | Footprint |
|---|---|
| `PaperII.theorem_1_2`, `Fsat_argmax_unique`, `Fsat_argmax_tie`, `level_set_iff`, `copyDefect_nonneg`, `copyGamma_ge_half_copyDefect`, `phiTau_max_sandwich`, `odd_sq_emod_24`, `phiTau_max_closed` | `[propext, Classical.choice, Quot.sound]` |
| `SimpleGraph.IsChordal.minimalSeparator_isClique`, `exists_isSimplicial`, `exists_two_nonadj_isSimplicial`, `geodesic_adj_imp_edge`, `exists_induced_path_of_walk` | `[propext, Classical.choice, Quot.sound]` |
| **`PaperII.phiTau_max_le_paperI_bound`** | **`[propext, Quot.sound]`** |
| **`SimpleGraph.IsChordal.comap`** | **`[propext, Quot.sound]`** |

**No `sorryAx`. No project-level axiom.**

**A precise conformance point worth highlighting.** Two declarations carry a *strict subset*
of the expected footprint - they do not use `Classical.choice`. The manuscript's Table 5
records exactly `propext`, `Quot.sound` for `phiTau_max_le_paperI_bound`, i.e. the
manuscript reports the reduced footprint rather than the generic triple. That is accurate
reporting at a level of detail that would be easy to get wrong.

## 7. Conformance of the headline statement

`PaperII.theorem_1_2` is the declaration the manuscript names for Theorem 1.1, the exact
chordal maximum `floor((2n+1)^2/24)` with attainment. Its footprint is the expected triple.
The four arithmetic corollaries of Table 5 were additionally verified *mathematically*, not
only formally, at Gate F: the sandwich holds for every integer `n` in `[-20000, 20000]`
including negatives, the residues of `(2n+1)^2 mod 24` are exactly `{1, 9}`, and
`phiTau_max_le_paperI_bound` holds for `n >= 1` and **fails for `n <= 0`**, which confirms
that its `n >= 1` hypothesis is necessary rather than decorative.

## 8. Escape-hatch scan (protocol 5.4 item 9)

Pattern `sorry | admit | ^axiom | native_decide | unsafe | opaque | implemented_by |
@[extern]` over all **42** project `.lean` files, `.lake` excluded, each hit classified:

| Class | Count |
|---|---|
| **ACTIVE CODE** | **0** |
| comment / prose | 2 |

**No escape hatch in active code.** No `native_decide`, no `unsafe`, no `opaque` used as an
escape, no untrusted code generation.

## 9. Local path dependencies

`lake-manifest.json` lists only standard upstream packages. **No undeclared local path
dependency**; no source component was missing.

## 10. Gate verdict

`PASS`. The exact target clean-builds from a verifiably clean room with the protocol's own
command and zero errors; every headline and bridge declaration carries the expected
foundational footprint, with two carrying a strictly smaller one that the manuscript
reports accurately; the explicit-target versus aggregate-root distinction is established;
and there is no escape hatch in active code.

## 11. Limitations

Only the seven targets named in protocol Section 9.2 were built. Modules outside that set
were not compiled and carry no verdict. The auditor did not run a separate
per-declaration query beyond the supplied frozen axiom file for this paper; the frozen file
was, however, verified to import the relevant modules directly, so its queries are not
relying on aggregate-root closure.
