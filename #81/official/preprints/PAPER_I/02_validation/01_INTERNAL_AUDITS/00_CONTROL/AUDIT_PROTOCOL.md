# Internal audit protocol -- Paper I v1.3

Status: `ACTIVE`. Normative standard:
`../../../../../../INTERNAL_AUDIT_STANDARD_v1.3.md`.

The common v1.3 standard supersedes the generic v1.2 text formerly stored in
this file. In particular, this internal run reviews the recorded Lean build and
axiom evidence but does not rerun Lean; clean reconstruction is reserved for
the external adversarial audit.

## 1. Freeze the target

Before any test, record the exact SHA-256 of the canonical manuscript, the
formal source manifest, the package manifest, the Lean toolchain, Mathlib
revision, host environment, commands, start time, and auditor identity. A
changed target starts a new audit run; evidence from different targets must
not be merged silently.

## 2. Resolve the claim map

For every claim ID, identify its statement, hypotheses, manuscript location,
formal declaration when present, proof dependencies, boundary cases, and the
specific falsification method. Missing coverage is an open gate, not a pass.

## 3. Use audit gates

Each independent block must live under `20_EVIDENCE/<BLOCK_ID>/` and contain:

- `AUDIT_RECORD.md` with scope, method, target hashes, limitations and verdict;
- `README.md` with one-command reproduction instructions;
- the complete script/source used by the block;
- `results/run.txt` with full stdout/stderr and exit code;
- `results/summary.json` with machine-readable status and counters;
- a block report in Markdown and, when admitted, a synchronized PDF;
- `SHA256_MANIFEST.txt` covering the admitted block.

Scripts must return nonzero on a failed check. Randomized work must record seed,
range and trial count. Search exhaustion must never be presented as proof.

## 4. Required gate families

Apply gates `G0`--`G8` from the common v1.3 standard. Formal conformance is a
static source/evidence review in this internal phase, not a fresh Lean build.
The literature/novelty gate must identify its search date and corpus.

### Paper I v1.3 mandatory residual controls

The eight findings in `04_integrity/EXTERNAL_AUDIT_CORRECTION_MATRIX.md` are
blocking regressions. In particular, the five Spanish passages identified by
`EXT-P1-L-001` must occur exactly once in Markdown, LaTeX and extracted PDF
text; every final page must be rendered after the final PDF build. The audit
must also verify the (4.7) accounting, the `o>=3` domain in A.2, the limited
meaning of `sharp`, the corrected citations, the current integrity baseline and
the absence of the stale repository entry.

The successful external clean-room Lean reconstruction belongs to the frozen
v1.2 audit record. This internal v1.3 run reviews that result and the unchanged
archive hash but does not rebuild Lean.

## 5. Verdict discipline

Allowed block verdicts are `PASS`, `FAIL`, `INCONCLUSIVE`, and `NOT_RUN`.
Allowed overall states are `PASS`, `CONDITIONAL_PASS`, `FAIL`, and
`INCONCLUSIVE`. A report must list unresolved objections and distinguish local
internal evidence from independent external reproduction.

## 6. Admission and packaging

Only evidence reviewed against its hashes may enter `30_PACKAGE/`. The final
Markdown report is the source of truth; TeX/PDF must be synchronized and
visually checked for truncation. No certificate is created before a completed
audit and explicit admission decision.
