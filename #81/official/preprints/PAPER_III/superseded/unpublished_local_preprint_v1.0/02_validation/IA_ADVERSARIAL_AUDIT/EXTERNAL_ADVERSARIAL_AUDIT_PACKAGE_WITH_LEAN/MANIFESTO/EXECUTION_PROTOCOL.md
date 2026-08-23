# Execution protocol — MANDATORY for every script in this audit

These rules are binding on the auditor. They exist because, in a prior run, a
long-running exact computation buffered all its output and appeared "stuck" with no way
to tell whether it was progressing or hung. Do not repeat that.

## R1 — Run long scripts in the background, never blocking

- Every non-trivial script (anything that may run more than ~10 s) MUST be launched
  **in the background** (detached / `run_in_background`), so the session is never
  blocked waiting on it and can keep monitoring and doing other work.
- Never wait on a foreground `sleep` loop. Use a completion signal (the background
  task's own exit / notification) or poll a **progress file** (R2).

## R2 — Print results incrementally; make progress observable

- Each script MUST emit progress **as work is produced**, not only at the end. Two
  required channels:
  1. **stdout line-buffered / flushed** — use `print(..., flush=True)` (Python) or set
     `PYTHONUNBUFFERED=1`; never rely on default block buffering for a redirected log.
  2. a dedicated **`results/<name>_progress.txt`** file, appended (and flushed) after
     each unit of work — e.g. every completed grid slice, every N instances, every
     block phase. One line per update, with a running count, failures so far, and
     elapsed seconds.
- A monitor (e.g. `tail -f results/<name>_progress.txt`, or an `until [ -f <resultfile> ]`
  waiter) must be able to see forward progress within seconds. **Silence for more than
  a minute on a running job is a defect of the script, not acceptable behavior.**
- Write the **final results file atomically at the end** AND keep the progress file, so
  a completed run is unambiguous and a still-running one is observable.

## R3 — No unbounded silent loops; cap and log

- Any potentially expensive exact computation (exact rational simplex, ILP, exhaustive
  enumeration, branch-and-bound) MUST have an explicit per-instance size guard (e.g. a
  triangle-count / variable-count cap). When an instance is skipped for exceeding the
  cap, **log it** ("N larger instances skipped and left to method X") — never truncate
  silently. Silent truncation reads as "covered everything" when it did not.
- Prefer a fast certificate method for full coverage and reserve the slow exact method
  for a bounded, logged spot-check. State which method carries the proof.

## R4 — Every script writes to the run's output folder and exits with a status

- No script writes outside the designated **output folder** (R5). Each writes its full
  log under `<output>/blockX_.../results/` and returns a **non-zero exit code on any
  failure** (a violated check, a solver error, a missing dependency).
- Determinism: fix every RNG seed and record it, so a re-run reproduces bit-for-bit.

## R5 — Create a NEW output folder where instructed; keep ALL results inside it

- The audit MUST be executed into a **new, empty output directory** whose location is
  given at run time (e.g. `EXTERNAL_AUDIT_RESULT/` under a path the operator specifies).
  Do not scatter outputs across the repo, and do not overwrite a previous run's folder —
  create a fresh one (or a timestamped sibling) so runs are never conflated.
- **Everything the run produces** — scripts' logs, `results/`, certificates, per-block
  zips, the report (`.md` + `.pdf`), `FINDINGS.csv`, `SHA256_MANIFEST.txt`,
  `received_inputs.sha256`, `ENVIRONMENT.md` — lives **inside that one folder**. The
  deliverable is that folder (and its zip). Nothing required to reproduce or read the
  audit may live outside it.
- Record, in `<output>/received_inputs.sha256`, the SHA-256 of the package you audited
  (including the frozen Lean snapshot), so the record is unambiguous about which version
  was audited.

## R6 — Monitoring recipe (reference)

```
# launch (background), then watch progress without blocking:
nohup python blockX/verify_X.py >/dev/null 2>&1 &          # or run_in_background
tail -f blockX/results/verify_X_progress.txt                # forward progress, live
until [ -f blockX/results/verify_X_results.txt ]; do sleep 5; done   # completion waiter
```
