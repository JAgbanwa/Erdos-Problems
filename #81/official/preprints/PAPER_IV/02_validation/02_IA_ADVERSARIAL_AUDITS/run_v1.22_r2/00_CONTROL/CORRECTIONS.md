# Auditor corrections and process notes — run_v1.22_r2

- **C3-01** (against the auditor; the error originated in run_v1.21_r1 and was carried into run_v1.22_r1): the X-15 count.
  - run_v1.21_r1 E6_RECORD stated "'matching(s)' x12 in prose".
  - Its raw scan (run_v1.21_r1/20_EVIDENCE/E6/results/checks.json, key english_in_es/matching) used a whole-word pattern for the singular "matching", which does not match "matchings". It listed 8 lines: 7 prose occurrences plus reference [9] (l.2490, the cited title "Minimum-degree and spread matching theorems").
  - Adding the 4 prose "matchings" (l.526, 578, and 746 twice) gives 12. The narrative "x12" therefore included one cited title, which must not be translated.
  - The MD prose actually contained 11 matching(s) + 1 packing.
  - run_v1.22_r1 listed the 11 + 1 locations correctly (E6_X15_NEW01_SCAN.json: 12 hits), but its E6_RECORD, FINAL report and FINDINGS described them as "12 matching(s) + 1 packing", taking the 12 total hits as the matching count.
  - Correct count: 11 matching(s) + 1 packing = 12 English terms in ES prose.
  - The prior reports are not rewritten; this correction supersedes their narrative count.
- **C3-02** (against the auditor, same failure mode as run_v1.22_r1 C2-02..C2-05): the r1|r2 comparison images for pages 16, 18, 20, 21, 35, 55, 56, 61 and 62 returned "[media removed: request limit]", yet rows describing them were written to PAGE_INSPECTION_LOG.csv. The descriptions for pp. 55, 56, 61 and 62 had been drafted from the text diff, not from the image. Those 9 rows are moved to PAGE_INSPECTION_LOG.discarded_unseen_cmp.csv. Pages 16, 18, 20, 21 and 35 were re-logged from the r2 2-up sheets (and, for p35, the 140 dpi zoom) that were actually displayed. Pages 55, 56, 61 and 62 were re-inspected before being logged again.
- **C3-03** (process): the copied e5_v122_c3_negfix.py writes its output to the current directory regardless of argv. Run from run_v1.22_r2/, it produced run_v1.22_r2/E5_V122_C3_negfix.json, which was moved to 20_EVIDENCE/E5/e5_v122_c3_negfix_RERUN.json. No file outside run_v1.22_r2 was written (E0 final confirms run_v1.22_r1 is unchanged).
