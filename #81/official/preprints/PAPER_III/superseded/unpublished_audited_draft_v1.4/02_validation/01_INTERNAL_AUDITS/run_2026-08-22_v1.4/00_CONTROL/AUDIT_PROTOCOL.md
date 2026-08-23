# Internal audit protocol — Paper III v1.4

**Status:** `EXECUTED_PASS`  
**Normative standard:** `preprints/INTERNAL_AUDIT_STANDARD_v1.3.md`  
**Audit class:** internal / author-side / non-independent  
**Lean rule:** inspect recorded build evidence; do not rerun the full Lean build

All blocking gates G0--G8 of the common standard apply. This run adds the following
mandatory regressions:

1. verify the exact v1.4 archive name/hash in both language and format chains;
2. verify that `PaperIII` reaches the final theorem and `PublicAPI` in the recorded import
   closure;
3. verify all 42 theorem-level axiom queries (35 distinct surfaces), including the integral
   and fractional canonical bridges;
4. classify the author build as `PASS_CLEAN_ORIGIN_RESUMED`, never uninterrupted;
5. rerun the four bounded mathematical suites and review the separate E2 residual ledger;
6. compare EN/ES heading hierarchy, section-block counts, display mathematics, equation
   tags, citations and Lean identifiers;
7. require every protected provenance token in Markdown, generated TeX and extracted PDF;
8. reject duplicated long paragraphs, missing translation sentinels and any v1.3 artifact
   duplicated inside the v1.4 manuscript directory;
9. inspect all 93 rendered PDF pages and retain hash-bound QA evidence;
10. carry forward the external E2/E6 addendum only as intake evidence; independent external
    closure remains required.

Any semantic manuscript correction invalidates downstream TeX/PDF/QA/hash gates. Any Lean
source correction invalidates the freeze and recorded-build gate.
