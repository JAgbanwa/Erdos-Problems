# Validation map — Paper IV draft

The organization follows Papers I–III, but validation verdicts are specific
to this package. Earlier papers' independent audit results are not inherited
by Paper IV.

## Internal author-side checks

`01_INTERNAL_AUDITS/run_draft_20260921/` contains the executable checks, their
results and the final internal report. The same gate families are used as in
the earlier release packages:

| Gate | Evidence sought |
|---|---|
| G0 | Exact artifact identities and archive integrity |
| G1 | Unchanged mathematical source and literal Lean excerpts |
| G2 | Bounded integer-accounting regression checks; explicit mathematical-review limit |
| G3 | Frozen source, complete local imports, pinned dependencies, escape-hatch scan |
| G4 | Lake build, exact theorem contracts, axiom reports and constant cones |
| G5 | Bilingual structural and mathematical parity |
| G6 | Final TeX/PDF binding, clean compiler logs and preserved visual QA |
| G8 | Curated publication, no credentials/cache/obsolete working versions |

G7 (independent mathematical/novelty validation) is **not** relabelled PASS:
it remains outside this author-side packaging audit. This is why the release
is a draft. Bounded arithmetic tests are not universal proofs; the Lean
theorem terms provide the formal evidence, subject to their declared trust
boundary and the interpretation of the formal statements.

## Retained baseline reports

`01_INTERNAL_AUDITS/baseline_v0.8/` preserves earlier editorial reports and
the proof ledger. These documents keep their historical paths and status
language; they are evidence, not the current package navigation or build
instructions. Current instructions are in the package README and
`03_reproducibility/README.md`.

## External audit

`02_IA_ADVERSARIAL_AUDITS/README.md` records the open independent-audit gate.
No third-party PASS report is manufactured or inferred from author-side tests.
