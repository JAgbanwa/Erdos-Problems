# Provenance and trust boundary — draft v0.8

## Logical versus software dependencies

The release's strongest formal claim is about the named theorem terms and
their literal types. The all-orders and eventual results require a finite
simple graph and chordality, not an externally supplied near-case theorem,
rounding theorem or optimum certificate. Such intermediate results are
constructed within the imported proof chain.

The axiom allowlist is `propext`, `Classical.choice`, `Quot.sound`. A scan for
active `sorry`, `admit`, `axiom`, `native_decide` and `implemented_by` is an
additional hygiene check, not a substitute for Lean's axiom traversal.

Lean v4.28.0, Mathlib v4.28.0 and the transitive packages pinned in
`lake-manifest.json` remain software and proof-library dependencies. We do
not describe the package as dependency-free in that sense.

## Series and external work

- `PaperI` contains the rational LP kernel used by the mixed model. The
  manuscript distinguishes this rational implementation from the earlier
  fractional framework.
- `PaperIIIRelease/Nibble` and the included contribution retain the series'
  structured-packing infrastructure. The local comparison report lists
  byte-identical and changed files relative to the official Paper III freeze.
  Of 87 included Lean sources, 86 are byte-identical; the sole difference in
  `Contrib/SpreadMatchingDirac.lean` is two trailing blank lines. No proof text
  differs in that comparison.
- `MixedRounding` is the neutral mixed-piece model; `PaperIV` contains the
  adapters, near-regime construction and theorem assembly used here.
- Other frozen namespaces support the explicitly identified supplementary
  results. Their inclusion is not a claim of several independent global
  proofs.

The manuscript's references and comparison with the external published
development are preserved. The cone audit rejects constants in the root
namespace `Erdos81` for its listed targets. This checks a namespace condition,
not authorship: it cannot detect code copied, adapted and renamed into a
different namespace. This release therefore does not infer independent
code origin or bibliographic originality from that test. The separate
`GalvinRoute` working tree is not silently added to this frozen package.

## Baseline, current evidence and publication identity

The mathematical cut is identified by
`baseline/LEAN_CUT.json` and the original archive hash
`4f6ba1b40ace1d926ae5fab7490c4bc0dc3f236dea28640de4cee0166da60afa`.
The archive and extracted files are unchanged. The original `public_release_commit:
null` field is historical evidence, not a current mutable release field.
The new public commit is obtained from the enclosing Git repository; it
cannot be embedded in its own content without changing that commit.

Original audit reports remain under `baseline` and `recorded_lean_audits`.
New author-side evidence has its own directory and timestamps. No old report
is rewritten to make it appear independently reproduced or newly audited.

This draft is not human peer review or an independent adversarial audit.
External validation and final editorial promotion remain separate steps.
