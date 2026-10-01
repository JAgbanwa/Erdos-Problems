# Run plan and limits — run_v1.2_r1

Recorded before substantive work (2026-09-30, ~12:22 UTC).

## Limits
- Overall wall-clock budget for this session: 36 h from start; on exhaustion or interruption,
  emit partial report + SUMMARY.json + FINDINGS.csv and seal a partial archive.
- Serious unresolved concern: max 30 min focused diagnosis, then INCONCLUSIVE.
- E4 main build: single heavy process; lake `-j` bounded by Lean default threads; wall-clock
  cap 10 h for the main build, 2 h for the annex build. Started only after PREBUILD_CHECKPOINT
  says PROCEED_TO_BUILD and machine load has been inspected (another `lean` process was
  observed running at intake, owned by another team; it will not be stopped).
- Disk: >= 20 GB free required before E4 (58.6 GB free at intake).
- No network use other than public literature retrieval (arXiv etc.) for E7.

## Order (mandate §4)
1. Readiness, E0, lightweight environment checks (no Lean builds).
2. E7, E1 / static E3, E2.
3. E5, E6, preliminary E8 (only after independent first-pass records for E1/E3, E7, E2, E5, E6 are saved).
4. 00_CONTROL/PREBUILD_CHECKPOINT.json.
5. E4 (main, then annex, serially); dynamic E3/E8; E0 recheck; reports and sealing.

## Deferred reading (until independent first pass is saved)
Author internal verdicts, derivations, computational conclusions, editorial reports,
author build logs' verdict fields, internal audit package contents (hash/CRC only).
