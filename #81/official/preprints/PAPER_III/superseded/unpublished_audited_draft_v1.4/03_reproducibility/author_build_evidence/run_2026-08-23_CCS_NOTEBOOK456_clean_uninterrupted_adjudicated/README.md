# Paper III v1.4 clean uninterrupted build evidence

This directory preserves the received ZIP and sidecar byte-for-byte. The raw runner summary
reports `FAIL` because its final headline-theorem regex expected an unquoted declaration
name. Lean's actual successful output is:

```text
'PaperIII.Theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every executed command exited zero: dependency cache, the clean 8,455-job `PaperIII` build,
the 8,444-job query-root build and all eight axiom files. The 42 axiom outputs contain no
`sorryAx` and no axiom outside `propext`, `Classical.choice` and `Quot.sound`.

`verify_clean_run_postcheck.py` performs a separate read-only adjudication. It also confirms
that all 707 source/config hashes in the formal freeze match the runner-verified build-kit
manifest. The original `RUN_SUMMARY.json` is not modified or replaced.

The adjudicated classification is
`PASS_CLEAN_UNINTERRUPTED_POSTCHECK_ADJUDICATED`. This remains author-side evidence;
independent external reproduction is still required.
