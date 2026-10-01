# Commands (summary; full outputs in 10_LOGS and 20_EVIDENCE)

| Time (−03:00) | Command | Exit |
|---|---|---|
| 10:57 | `python verify_audit_target.py` (in request dir) | 0 |
| 10:59 / 11:26 | `python 20_EVIDENCE/E0/e0_identity.py intake|final` | 0 |
| 10:58 | `elan toolchain list`; `git -C <pkg> rev-parse HEAD`; `git -C <pkg> status --porcelain` (9 packages) | 0 |
| 11:00 | `unzip LEAN_SOURCE_SNAPSHOT_v1.0.zip -d C:/piv_r2/src` ; 11:10 annex to `C:/piv_r2/annex` | 0 |
| 11:06–11:09 | `python 20_EVIDENCE/E3/extract_headers.py …`, `name_check.py`, grep sweeps | 0 |
| 11:11–11:17 | `curl`/`gh api` retrievals listed in INPUT_ACCESS_LOG.csv | 0 |
| 11:19 | `python 20_EVIDENCE/E5/e5_exact.py` | 0 |
| 11:21–11:25 | `python 20_EVIDENCE/E5/e5_search.py` (243.5 s; final print crashed after JSON written, fixed) | 1 (print only) |
| 11:22 | `python 20_EVIDENCE/E6/e6_auto.py` | 0 |
| 11:30 | `python 30_REPORT/make_findings.py`; `python 30_REPORT/render.py` | 0 |

No `lake`, `lean` compilation, cache fetch, `lake update`, clone or install was executed.
