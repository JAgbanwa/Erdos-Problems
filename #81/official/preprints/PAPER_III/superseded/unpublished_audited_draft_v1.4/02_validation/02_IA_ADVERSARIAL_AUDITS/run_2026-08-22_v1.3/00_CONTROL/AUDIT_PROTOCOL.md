# Audit protocol as executed -- Paper III v1.3

**Governing document:** `EXTERNAL_ADVERSARIAL_AUDIT_REQUEST.md`, SHA-256
`a0569fa455d70ee3e8af8ddb4362c52863de69d830bc76975bb6f9d22d9e12c0`.
**Reproduction procedure:** `MATHLIB_REPRODUCTION_PROTOCOL.md`, followed as written; the one
deviation, and why, is recorded below.

## Independence

Primary auditor only. **No adversarial challenger.** Only v1.3 was evaluated: no verdict,
PASS, or author-side conclusion from any earlier run was inherited. Author-side material
(`ESCAPE_HATCH_ASSESSMENT.md`, `FREEZE_METADATA.json`, the internal audit, the recorded build
log) was read as an attack input and is cited only as a claim to be tested, never as evidence.

## Order of work

1. E0 intake, before any substantive work, as the request requires. A byte mismatch would have
   stopped the audit.
2. E1 claims and scope, from the manuscript text.
3. E4 clean-room reproduction, following the reproduction protocol.
4. E3 formal conformance, using an auditor-built bridge rather than the target's lemmas.
5. E2 rederivation of Section 9 in exact symbolic algebra.
6. E5 render and bilingual comparison, every page of both PDFs.
7. E6 citations and prior art, bounded by reachable sources.
8. E7 release-package integrity, closing with a re-verification of the target hashes.

## Deviation from the reproduction protocol, and why

Step 8 prescribes `lake build PaperIII`. That was run first, and it is recorded in full. It
does **not** build the modules that step 9's eight queries import, so seven of the eight
queries failed. The auditor therefore additionally built the seven roots those queries import,
recorded separately. This is not a relaxation of the protocol: both builds started from an
absent project `.lake/build` and used the same verified dependency cache. The inconsistency
between steps 8 and 9 is itself recorded as `EXT-V13-007`, and its cause as `EXT-V13-001`.

Step 4 permits a directory junction to an auditor-controlled, independently verified package
cache. One was used: `.lake/packages` junctioned to a cache whose nine dependency revisions
were each verified by `git rev-parse HEAD` and `git status --porcelain` against the supplied
manifest. No author-built Paper III artifact was used, and the project `.lake/build` was proved
absent immediately before each build.

## Epistemic rules applied

- `#print axioms` was never treated as semantic conformance.
- No universal statement is reported as proved on the strength of finite testing.
- Compilation, semantic correspondence, axiom footprint and independent rederivation are
  reported as four separate statuses.
- Every auditor tool artifact discovered during the run is recorded rather than quietly fixed;
  four are listed in the report.
