# Deliverable specification

You must return a single self-contained archive `EXTERNAL_AUDIT_RESULT.zip` with the
structure below and a top-level `SHA256_MANIFEST.txt` hashing every file in it.

```
EXTERNAL_AUDIT_RESULT/
  README.md                        # how to reproduce everything; tool versions
  ADVERSARIAL_AUDIT_REPORT.pdf     # the report (English) — see format below
  ADVERSARIAL_AUDIT_REPORT.md      # Markdown mirror
  ENVIRONMENT.md                   # OS, language/tool versions, solver versions
  SHA256_MANIFEST.txt              # SHA-256 of every delivered file
  findings/
    FINDINGS.csv                   # one row per finding (schema below)
  blockA_faithfulness/
    README.md  <scripts>  results/<outputs>  certificate_blockA.pdf
  blockB_external_inputs/          # same shape
  blockC_counterexample_search/
  blockD_algebra_rederivation/
  blockE_audit_the_audit/
  blockA_faithfulness.zip (+ .sha256)   # per-block zip + hash, as we did
  ...
  received_inputs.sha256           # SHA-256 of the package you received (proof of what
                                   # version you audited)
```

## Per-block folder (mirror of `OUR_INTERNAL_AUDIT/blockNN/`)
- `README.md` — what was attacked, method, how to reproduce, result.
- your **own** script(s) — independent of ours; each writes its full log to `results/`.
- `results/…` — the written outputs (not just console).
- `certificate_blockX.pdf` — one-page English certificate: scope, verdict, evidence
  summary, methodology, SHA-256 of the block's results file, timestamp, auditor identity.
- packaged as `blockX_*.zip` with a `.sha256`.

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
     missing dependency, statement↔claim mismatch, arithmetic error in a load-bearing step).
2. **Per-claim table** — Theorem 1.1, Prop 10.1, Cor 1.2, Thm 3.1, Thm 4.2, Lemmas
   5.1/5.2/6.1/7.1, Appendix B, Appendix D, AX1, AX2 → verdict + evidence pointer.
3. **Findings** — each with severity and reproduction.
4. **Coverage statement (mandatory, honest)** — exactly what was tested, at what ranges,
   with what tools, and **what was not tested**. No implied coverage.
5. **Reproduction appendix** — commands + environment to regenerate all evidence.

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
