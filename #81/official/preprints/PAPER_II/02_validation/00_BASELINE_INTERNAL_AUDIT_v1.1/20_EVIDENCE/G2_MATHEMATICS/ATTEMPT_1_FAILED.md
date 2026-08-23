# Attempt 1 -- harness-domain failure

**Status:** `FAILED_TEST_SPECIFICATION`, not a manuscript counterexample.

The first harness required the set of all complete-split maximizers to equal
the integers nearest to `(2n+1)/6`. At `n=2`, the degenerate graph `S_{2,0}`
ties with the saturated-branch extremizer `S_{1,1}`. Proposition 7.1 asserts
attainment by a nearest integer, while the unique/tie declarations are scoped
to the saturated branch. The harness was therefore stronger than the audited
claim. It was corrected to compare the exact argmax only inside that branch and
to require the nearest saturated integer to attain the global value.

Observed exception: `AssertionError: (2, [1, 2], [1])`.

