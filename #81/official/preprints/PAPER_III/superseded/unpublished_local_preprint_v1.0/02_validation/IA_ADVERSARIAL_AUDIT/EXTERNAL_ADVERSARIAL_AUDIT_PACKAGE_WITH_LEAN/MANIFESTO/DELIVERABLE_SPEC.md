# Deliverable specification

## Where to run (MANDATORY — see `EXECUTION_PROTOCOL.md`)
Execute the whole audit into **one new, empty output folder** whose location the
operator gives you at run time (default name `EXTERNAL_AUDIT_RESULT/`). **Every** output
lives inside it; nothing required to read or reproduce the audit may live outside it. Do
not overwrite a previous run — create a fresh (or timestamped) folder. Run long scripts
in the background and stream incremental progress (`results/<name>_progress.txt`) so no
job can look hung.

You must return that folder as a single self-contained archive `EXTERNAL_AUDIT_RESULT.zip`
with the structure below and a top-level `SHA256_MANIFEST.txt` hashing every file in it.

```
EXTERNAL_AUDIT_RESULT/
  README.md                        # how to reproduce everything; tool versions
  ADVERSARIAL_AUDIT_REPORT.pdf     # the report (English) — see format below
  ADVERSARIAL_AUDIT_REPORT.md      # Markdown mirror
  ENVIRONMENT.md                   # OS, language/tool versions, solver versions, Lean toolchain
  SHA256_MANIFEST.txt              # SHA-256 of every delivered file
  findings/
    FINDINGS.csv                   # one row per finding (schema below)
  blockA_faithfulness/
    README.md  <scripts>  results/<outputs+*_progress.txt>  certificate_blockA.pdf
  blockB_external_inputs/          # same shape
  blockC_counterexample_search/
  blockD_algebra_rederivation/
  blockE_audit_the_audit/
  blockF_lean_formalization/       # NEW: build log, gate.lean + axiom report, sorry/escape
    README.md  gate.lean  results/{build_log.txt, axioms_report.txt, grep_scan.txt,
    lean_snapshot_sha.txt, *_progress.txt}  certificate_blockF.pdf
    lean_snapshot/                 # sources reconstructed from the frozen release commit
  blockA_faithfulness.zip (+ .sha256)   # per-block zip + hash
  ...
  blockF_lean_formalization.zip (+ .sha256)
  received_inputs.sha256           # SHA-256 of the package you received AND of the frozen
                                   # Lean snapshot (proof of exactly what version you audited)
```

## Per-block folder (mirror of `OUR_INTERNAL_AUDIT/blockNN/`)
- `README.md` — what was attacked, method, how to reproduce, result.
- your **own** script(s) — independent of ours; each writes its full log to `results/`
  **and appends incremental progress** to `results/<name>_progress.txt` (per
  `EXECUTION_PROTOCOL.md`).
- `results/…` — the written outputs (not just console), including the progress files.
- `certificate_blockX.pdf` — one-page English certificate: scope, verdict, evidence
  summary, methodology, SHA-256 of the block's results file, timestamp, auditor identity.
- packaged as `blockX_*.zip` with a `.sha256`.

### Block F specifics (Lean formalization)
`blockF_lean_formalization/` must contain: the `lean_snapshot/` reconstructed from the
frozen release commit (with `lean_snapshot_sha.txt` recording `<sha>`, `lean-toolchain`,
`lake-manifest.json`); the extended `gate.lean`; and under `results/`: `build_log.txt`
(full `lake build`, streamed), `axioms_report.txt` (`#print axioms` for every node),
`grep_scan.txt` (the sorry/escape-hatch scan of the git object), and `*_progress.txt`.
The certificate states the build result, the axiom verdict per layer, and the snapshot SHA.

## `findings/FINDINGS.csv` schema
```
id, claim_ref, block, attack, inputs_or_ranges, outcome, severity, reproduction_cmd, evidence_file
```
- `outcome ∈ {CONFIRMED, PLAUSIBLE, REFUTED, OUT_OF_SCOPE}`
- `severity ∈ {none, minor, major, blocking}` (use `none` for confirmations).

## `ADVERSARIAL_AUDIT_REPORT` format (English)
1. **Executive verdict** — one of:
   - `PASS` — no defect found; all in-scope claims survived adversarial testing.
   - `PASS_WITH_OBSERVATIONS` — claims survive, but with minor issues (typos, tighten-able
     constants, presentational gaps) listed.
   - `FAIL` — at least one blocking defect (counterexample, overstated axiom, circular or
     missing dependency, statement↔claim mismatch, arithmetic error in a load-bearing step,
     **or a Lean defect: a non-sorry-free build, a hidden extra axiom, a `sorryAx` in the
     chain, or a Lean statement that does not match its ledger node**).
2. **Per-claim table** — Theorem 1.1, Prop 10.1, Cor 1.2, Thm 3.1, Thm 4.2, Lemmas
   5.1/5.2/6.1/7.1, Appendix B, Appendix D, AX1, AX2 → verdict + evidence pointer.
   Add a **Lean column** (per node): build-clean? axiom report exactly as expected?
   statement matches ledger? — with the `gate.lean` line as evidence.
3. **Findings** — each with severity and reproduction. A Lean escape hatch or hidden
   axiom is `blocking`.
4. **Coverage statement (mandatory, honest)** — exactly what was tested, at what ranges,
   with what tools, and **what was not tested**. State the exact Lean release commit,
   toolchain, and Mathlib revision audited. If Block F was deferred (formalization not yet
   frozen), say so explicitly and mark the Lean column "NOT YET AUDITED". No implied coverage.
5. **Reproduction appendix** — commands + environment to regenerate all evidence, including
   the `git archive <sha>`, `lake exe cache get`, `lake build`, and `lake env lean gate.lean`
   invocations for Block F.

## Verdict criteria (what we will look for when reading your report)
- Evidence-backed, reproducible conclusions; independence from our tooling.
- Every `CONFIRMED` tied to a script/derivation; every `REFUTED` tied to an explicit
  counterexample or a precisely localized broken step.
- An honest coverage boundary. A narrow-but-honest audit is worth more than a broad claim
  you cannot back.

## Reference implementation
`OUR_INTERNAL_AUDIT/` is provided as a **worked example of the expected shape** (README +
script + written results + PDF certificate + zip + SHA per block, plus a consolidated
`AUDIT_FINAL_REPORT`). It is also a **target**: Block E asks you to break it. Do not copy
our scripts — re-derive independently.
