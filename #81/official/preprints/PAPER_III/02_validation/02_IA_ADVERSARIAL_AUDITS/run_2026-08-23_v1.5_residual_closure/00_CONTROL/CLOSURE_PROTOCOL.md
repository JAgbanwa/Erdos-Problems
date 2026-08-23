# Closure protocol — `EXT-V15-M01`, Paper III v1.5

Run: `run_2026-08-23_v1.5_residual_closure`.

Request: `EXTERNAL_PASS_CLOSURE_REQUEST_v1.5.md`, SHA-256
`37118ecff3894b8c018c1031cd619f88e05e449e6fd685cce14ff3920bbaf034`. Closure packet
`PAPER_III_v1.5_EXT_V15_M01_PASS_CLOSURE.zip` =
`7972a0b5212bc69d0437fd328886a63e383bc60f54e91c365ab771e5a6be20e4`, matching its sidecar,
13 members, CRC clean.

## Scope

This run performs **only** the residual closure test stated in section 2 of the preserved
`CONDITIONAL_PASS` report, plus checks for defects the correction itself could have introduced.
No gate of the source run is repeated: no rederivation, no literature search, no PDF rebuild,
no Lean build. The source report states that on closure the verdict becomes `PASS` with no
further work required, and this run tests exactly whether closure occurred.

The preserved source report is not rewritten. Its SHA-256,
`4f4537816840c62fb23521190fab4fa1a860085e05a4cb956d8afe1eb3b67596`, was recomputed here and is
byte-identical to this auditor's own copy of that report, so the authority chain is genuine
rather than transcribed.

## Method

The six checks the request enumerates were performed independently, from the target itself.
Neither the author's `verify_EXT_V15_M01_closure.py` nor `EXT_V15_M01_CLOSURE_RESULTS.json` was
used as evidence; the author script was run afterwards only as a contrast, and agreed.

Because the correction was a **file relocation and a deletion**, four checks the request does
not ask for were added, since those are the ways such an edit fails:

- **A** — does anything in the release now point at a moved or deleted file? Every one of the
  1,572 entries in `TREE.txt` was resolved against the filesystem, and every textual reference
  to the six named log files and the removed JSON was resolved as a path.
- **B** — do the local links in `README.md` and the HTML still resolve?
- **C** — is the deleted generic JSON's evidence genuinely preserved elsewhere, or was evidence
  simply lost?
- **D** — does the shadowing pattern recur anywhere else in the release surfaces?

## Auditor tool corrections during this run

Three initial signals were defects in this auditor's own instruments, fixed and recorded rather
than filed against the target:

1. current-log manifest entries looked up by basename when the manifest keys are full
   target-relative paths, which reported 6/6 spurious hash mismatches;
2. a legacy log classified as misfiled whenever the string "v1.5" appeared anywhere in it — a
   LaTeX log is full of package version numbers, so the test must read the **output job name**;
3. a dangling-reference test based on keyword proximity, which flagged correct `TREE.txt`
   entries because in an indented listing the parent directory header sits dozens of sibling
   lines above the filename. Replaced by real path resolution.

## Limitation stated

Byte-identity between the **deleted** generic `MANUSCRIPT_CONSISTENCY_RESULTS.json` and the
copy preserved under `superseded/` cannot be proved: the file is gone, and neither the source
audit nor the closure packet recorded its hash. What is verified is the substance — the
preserved copy describes v1.4 (`md_en = eea753a4…36f`, `PASS` 51/51), which is the same version
the removed file described, so the v1.4 consistency evidence survives in a versioned location.
