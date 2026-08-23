# E7 -- release-package integrity

**Verdict: `FAIL`**, on the mandated cross-artifact agreement.

## What passes

**Self-containment.** The manuscript does not require an earlier internal draft. Its three
mentions of the internal audit are status disclosures that assert the opposite of a dependency:
"the author-side internal audit passes. Independent reproduction remains open; the candidate is
a local formal freeze, not yet a public release", and "They do not replace independent
reproduction or external adversarial review."

**Release description.** Paper III is described consistently as a candidate for its first
formal public release, symmetrically in both languages.

**Final hash re-verification: 12/12. The target did not change during the audit.**

## What fails

The request requires that "filenames, hashes, build records, formal names, changelog, metadata
and reproducibility documents agree". `FREEZE_METADATA.json` declares
`"status": "LOCAL_FREEZE_PREPARED_PENDING_INTERNAL_AUDIT"` and
`"internal_audit": "NOT_STARTED"`, while the same package ships an internal audit final report
with overall verdict `PASS`, and the manuscript states that the internal audit passes. See
`EXT-V13-003`.

Two further inconsistencies, both MINOR: the root docstring still calls `PaperIII.lean` a
scaffold (`EXT-V13-006`), and the reproduction protocol's steps 8 and 9 cannot both be followed
as written (`EXT-V13-007`).

Evidence: `scripts/../../E6_PRIOR_ART/scripts/v13_E6_E7.py`, `results/release_package.json`.
