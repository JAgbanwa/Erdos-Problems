# Addendum `XP-001` to the sealed Paper II v1.2 external audit

**Issued under:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1` Section 10.

**Run addended:** `run_2026-08-21_v1.2`
**Addendum date:** 2026-08-22
**Auditor:** Claude (Anthropic), `claude-opus-5`

## The sealed verdict is unchanged

Paper II v1.2 remains **`PASS_WITH_RESIDUALS`**, and the later
`run_2026-08-21_v1.2_pkgfix` remains **`PASS`**. This addendum records a defect in the **audit
package** of this run, found by the auditor in its own output. No claim, proof, formalization
or finding of Paper II is affected.

## Why it is filed now

This defect was **missed** by the cross-paper pass, which checked three sealed packages and
reported the result as if it had checked all of them. It surfaced while validating whether the
Paper II Lean clean room could be released to reclaim disk space -- a validation that
re-verified both Paper II packages and found this one at 55/56.

## Finding `XP-001` (MINOR)

`30_REPORT/FINAL_AUDIT_SUMMARY.json` does not match its entry in
`40_PACKAGE/PACKAGE_MANIFEST.json`:

```
manifest entry  : 35ef62039a572a6479c4fb90f7224c18eb7b971a0a10d5db11b1e4c0f0053cd4
file on disk    : eb8f237b1128764d7645a01f3667a44d9b9c3bcb9e250f375f0fc6944cf5dbdb
copy in the ZIP : 35ef62039a572a6479c4fb90f7224c18eb7b971a0a10d5db11b1e4c0f0053cd4
```

**Cause, fully diagnosed.** The summary's `package_sha256` field holds
`1d352e67ed0690780cb9df0fe482a1c2cc8b8f56a2658f4b72c354440ef4a2b7`, which is exactly the
SHA-256 of `40_PACKAGE/EXTERNAL_AI_ADVERSARIAL_AUDIT_PACKAGE.zip`. The field was written after
the manifest and the ZIP were built, so the loose file is one byte-state ahead of both. This is
a self-referential impossibility rather than a content error: a hash of the ZIP cannot live
inside the ZIP it hashes.

**Scope.** Exactly one file, and the only mismatch among the 56.

| Check | Result |
|---|---|
| loose files against `PACKAGE_MANIFEST.json` | 55 / 56 |
| ZIP members against the manifest | **56 / 56** |
| ZIP against its LF-only sidecar | **matches** |

**Impact.** A third party verifying loose files against the manifest gets 55/56 and is left to
guess why. That is the whole of the harm, and it is a legibility harm.

## Independent confirmation that the sealed evidence is intact

Checked in the same pass, because this run's Gate H evidence had to survive releasing the Lean
clean room: the build log inside this package records
`Build completed successfully (8063 jobs).` with `EXIT_BUILD=0`, the axiom report and the
update/cache log are present, and **no path in this manifest points into the clean room or into
`.lake`**. The package is self-contained, and the freeze archive plus the pinned
`lake-manifest.json` and `lean-toolchain` in the paper's own `05_formalization/` make the build
reproducible from scratch without it.

## Disposition

Do not patch the sealed files. Either accept this addendum as the record, or re-seal in a new
run keeping `package_sha256` as a pointer to the sidecar rather than a value -- the change that
made `run_2026-08-21_v1.2_pkgfix` verify 30/30 on the first attempt.

## The corrected sweep behind this addendum

The cross-paper pass of `EXTERNAL_AI_ADVERSARIAL_AUDIT_CROSS_PAPER_REPORT_v1.2` checked
**three** sealed packages. There are **eight** audit-run directories, six of them carrying a
package manifest. The corrected sweep covers all of them and separates three questions that the
first pass ran together:

| Check | Question |
|---|---|
| A | do the loose files on disk match `PACKAGE_MANIFEST.json`? |
| B | are the ZIP members internally consistent with that same manifest? |
| C | does the ZIP match its LF-only sidecar? |

Corrected result across every package:

| Package | Manifest | A, loose files | B, ZIP | C, sidecar | Issue |
|---|---|---|---|---|---|
| PAPER_I v1.2 (active copy) | **none** | n/a | none | none | never sealed |
| PAPER_I v1.2 (superseded copy) | **none** | n/a | none | none | never sealed |
| PAPER_I v1.3 | 43 | **36/43** | 43/43 | matches | `XP-004`, `XP-003` |
| PAPER_I v1.3 pkgfix | 29 | 28/29 | 29/29 | matches | `XP-001`, `XP-003` |
| PAPER_II v1.2 | 56 | 55/56 | 56/56 | matches | `XP-001` |
| PAPER_II v1.2 pkgfix | 30 | **30/30** | 30/30 | matches | clean |
| PAPER_III v1.2 | 65 | **65/65** | 65/65 | matches | clean |
| PAPER_III residual Gate C | 54 | **54/54** | 54/54 | matches | clean |

**Every ZIP is internally consistent with its own manifest, and every sidecar matches its
ZIP.** In all cases the ZIP is the authoritative sealed artifact; the defects are confined to
the loose directory copies and to what was included at seal time.

One correction to the sweep itself, recorded so a tool artifact is not left looking like a
target defect: a first version flagged nine "scratch" members in the Paper III package because
it treated every `.log` as a LaTeX byproduct. The protocol requires raw evidence logs to use
`.txt` or `.log`, so those are deliverables. Only a `.log` in `30_REPORT` beside a same-named
`.tex` is a byproduct. With that fixed, Paper III is clean.

## Reproduce

```
python xp001_full_sweep.py
```

Evidence: `xp001_full_sweep.json`, alongside the cross-paper report in `preprints/`.
