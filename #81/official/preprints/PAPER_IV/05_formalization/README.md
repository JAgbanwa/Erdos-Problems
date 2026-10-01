# Formalization selected for Paper IV v1.22

## Main immutable source

- [Tree](lean_piv-v12-fb459343d234/)
- [Source ZIP](LEAN_SOURCE_piv-v12-fb459343d234.zip)
- [Source manifest](../03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json)

Identity: piv-v12-fb459343d234; 607 Lean modules, 615 manifest entries.
Source ZIP SHA-256:
cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6.

The external build verified 607 modules, 19 explicit targets and 224 export
checks. The final v1.22-r4 report revalidated that evidence by identity.
PaperIV is the mathematical aggregate; tools/audit_publication.py is the
serial auditing entry point. See [reproduction](../03_reproducibility/README.md).

## Separate bounded-gap annex

- [Annex sources](lean_v1.0_gap_annex/)
- [Annex ZIP](LEAN_BOUNDED_GAP_ANNEX_v1.0.zip)

The historical filename v1.0 identifies this unchanged annex, not a competing
Paper IV manuscript release. It contains 38 bounded-gap modules and uses a
recorded 50-module closure. Its ZIP hash is
2847a422865e06880d457ea806aae5b9f749d22359eff325349c09c01cb4837d.

No universal linear mixed gap follows from the conditional annex statements.
Their assumptions remain visible in the source and manuscript.

The old v0.8 source lives only in its superseded package. Other obsolete
formal trees and caches are not included. Existing software licenses remain
applicable. No dependency installation, theorem edit or build occurred
during this publication packaging.
