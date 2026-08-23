# Internal audit protocol -- Paper II v1.2

Status: `COMPLETED`. Normative standard:
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
