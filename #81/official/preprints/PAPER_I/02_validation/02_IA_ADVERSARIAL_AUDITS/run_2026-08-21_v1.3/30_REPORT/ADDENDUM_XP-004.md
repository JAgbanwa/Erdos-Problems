# Addendum `XP-004` to the sealed Paper I v1.3 residual audit

**Issued under:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1` Section 10.

**Run addended:** `run_2026-08-21_v1.3`
**Addendum date:** 2026-08-22
**Auditor:** Claude (Anthropic), `claude-opus-5`

## The sealed verdict is unchanged

Paper I v1.3 remains **`PASS_WITH_RESIDUALS`**. This addendum records defects in the **audit
package**, produced by this auditor. No claim, proof, formalization or finding of Paper I is
affected. It is filed because the cross-paper pass did not examine this run at all, and the
corrected sweep found the largest of the packaging defects here.

## Finding `XP-004` (MINOR) -- the loose directory drifted after sealing

Of the 43 manifest entries, **7 loose copies no longer match the sealed state**: three were
overwritten after sealing and four are absent from disk entirely.

**Overwritten after sealing.** The ZIP was written at 13:36:38; these three carry a mtime of
13:39:33, three minutes later:

| File | sealed bytes | on-disk bytes |
|---|---|---|
| `30_REPORT/FINAL_AUDIT_REPORT.pdf` | 129,217 | 135,898 |
| `30_REPORT/FINAL_AUDIT_REPORT.log` | 24,576 | 58,860 |
| `30_REPORT/FINAL_AUDIT_SUMMARY.json` | -- | -- |

The cause is known and is the auditor's: after sealing this run, the report was recompiled to
fix silently dropped mathematical glyphs and clipped tables. The **improved** PDF is the loose
one; the **sealed** ZIP holds the earlier, defective one. That inversion is the substance of
this finding -- a reader opening the loose PDF and a reader opening the ZIP see different
documents, and the better one is outside the seal.

**Absent from disk, preserved in the ZIP.** Four Gate H reuse logs:

```
20_EVIDENCE/H_LEAN_REUSE/results/REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE_01_lake_update_cache_get.log
20_EVIDENCE/H_LEAN_REUSE/results/REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE_02_lake_build_protocol_9_1.log
20_EVIDENCE/H_LEAN_REUSE/results/REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE_03_FreezeAxioms_run.log
20_EVIDENCE/H_LEAN_REUSE/results/REUSED_BYTE_IDENTICAL_EXTERNAL_EVIDENCE_04_independent_axiom_query.log
```

They were reorganized out of the loose tree after sealing. **The ZIP retains all four**, so no
evidence is lost -- but the loose tree is no longer a faithful copy of the audited run.

## What is intact

| Check | Result |
|---|---|
| loose files against `PACKAGE_MANIFEST.json` | 36 / 43 |
| ZIP members against the manifest | **43 / 43** |
| ZIP against its LF-only sidecar | **matches** |

The ZIP is the authoritative artifact and it is complete and self-consistent. Anyone verifying
this run should verify the ZIP, not the loose directory.

## Finding `XP-003` (MINOR) -- scratch sealed

This run also seals one LaTeX byproduct as a manifest member. Build residue, not audit
evidence.

## Disposition

Do not patch the sealed files, and in particular do not re-seal the loose tree over the
manifest -- that would silently redefine what was audited. Either accept this addendum as the
record, or open a new run that re-seals the corrected report with fresh hashes and states in
its own text that it supersedes this one. The general fix, already in place for later runs, is
to seal last and touch nothing afterwards.

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
