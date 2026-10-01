# Auditor corrections and process notes — run_v1.22_r4

- **C5-01** (auditor script bug): in e6_r4_delta.py, the field page_first_last_lines_equal was indexed off by one (it reported pages 41/67). It was recomputed correctly for pp. 40/66 in-line, the field was replaced in E6_R4_DELTA.json by page_boundaries_changed_pages, and the script was left as run.
