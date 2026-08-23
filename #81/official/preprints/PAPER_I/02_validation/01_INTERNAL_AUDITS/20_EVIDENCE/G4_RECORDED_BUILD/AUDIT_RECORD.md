# G4 RECORDED BUILD — Paper I v1.3 audit record

**Verdict:** `PASS_RECORDED_BUILD`

The frozen evidence records `EXIT_CODE=0` and `Build completed successfully
(8034 jobs).` The 15-surface axiom gate records `EXIT_CODE=0`, includes
`PaperI.assembly_sharp` and `PaperI.Split.residual_duality`, and reports only
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or project axiom is
reported. Source/package manifests and the archive sidecar verify.

The external v1.2 clean-room audit independently rebuilt these exact archive
bytes successfully. Under the agreed internal protocol, no `lake build` or
Lean command was run for v1.3 because the formal archive SHA-256 remains
`0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`.

