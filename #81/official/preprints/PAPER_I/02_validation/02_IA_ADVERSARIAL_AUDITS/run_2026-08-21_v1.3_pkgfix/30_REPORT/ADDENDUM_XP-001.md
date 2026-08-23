# Addendum `XP-001` to the sealed Paper I v1.3 package-fix audit -- CORRECTED

**Supersedes** the first version of this addendum, dated the same day, which reported
`XP-001` as if it were confined to this run. It is not. This corrected version keeps the
original diagnosis, which was right, and fixes the scope claim, which was wrong.

**Issued under:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1` Section 10, which requires
a defect found by the cross-paper pass to be added "by issuing an addendum with its own hash;
never rewrite a sealed report in place."

**Run addended:** `run_2026-08-21_v1.3_pkgfix`
**Corrected:** 2026-08-22
**Auditor:** Claude (Anthropic), `claude-opus-5`

## The sealed verdict is unchanged

Paper I v1.3 package fix remains **`PASS`**. Every finding here is against the **audit
package**, produced by this auditor. No claim, proof, formalization or finding of Paper I is
affected by any of them.

## `XP-001` (MINOR) -- unchanged diagnosis

`30_REPORT/FINAL_AUDIT_SUMMARY.json` does not match its manifest entry:

```
manifest entry  : 5bf32ec04e725251d8fabc58082dc3a1d887a6f83e8fc2a9f3672b6219eb4ba0
file on disk    : 6314800f3eb2c4d0a55a72bd203d314d14415ada2a15fa15b9c0484e3e1e7a04
copy in the ZIP : 5bf32ec04e725251d8fabc58082dc3a1d887a6f83e8fc2a9f3672b6219eb4ba0
```

Cause: the sealing step wrote `package_sha256` -- the ZIP's own hash,
`b1e08710eee274d54331b7aeb5e1c8ae3af8146468207e2365f497f823384386` -- into the summary *after*
the manifest and the ZIP were built, so the loose file is one byte-state ahead of both. A
self-referential impossibility, not a content error: a hash of the ZIP cannot live inside the
ZIP it hashes.

## What the first version of this addendum got wrong

It said Paper II's package "does not have this defect". That is true of
`run_2026-08-21_v1.2_pkgfix`, which verifies 30/30, and **false of
`run_2026-08-21_v1.2`**, which carries the identical `XP-001` signature: 55/56 loose, ZIP
56/56 consistent, sidecar matching, and the summary's `package_sha256` field equal to the ZIP
hash `1d352e67ed0690780cb9df0fe482a1c2cc8b8f56a2658f4b72c354440ef4a2b7`. A separate addendum
has been filed in that run.

The reason for the error is worth stating plainly: the cross-paper pass verified the three
packages it had most recently produced, and reported that as if it had verified all of them.
The sweep was incomplete, and the report did not say so.

## `XP-003` (MINOR) -- unchanged

This run seals LaTeX scratch as manifest members: `30_REPORT/FINAL_AUDIT_REPORT.aux` and
`30_REPORT/FINAL_AUDIT_REPORT.log`. They are build residue, not audit evidence. The package is
internally consistent about them; they simply should not have been sealed. Scratch removal was
added to the sealing step afterwards, which is why Papers II and III do not carry this.

## Disposition

Do not patch the sealed files. Either accept this addendum as the record, or re-seal in a new
run with two changes, both already demonstrated on later packages: keep `package_sha256` as a
pointer to the sidecar rather than a value, and exclude LaTeX scratch. Paper II's package-fix
run verified 30/30 on the first attempt with the first change in place, and Papers II and III
carry no scratch with the second.

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
