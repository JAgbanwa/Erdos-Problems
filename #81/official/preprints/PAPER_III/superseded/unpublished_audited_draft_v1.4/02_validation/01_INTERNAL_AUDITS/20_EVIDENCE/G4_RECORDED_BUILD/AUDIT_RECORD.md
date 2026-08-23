# G4 RECORDED-BUILD — audit record

**Verdict:** `PASS_RECORDED_BUILD`.

The audit did not rebuild Lean. It reviewed the sealed record of the exact target command:
exit 0, 8,719 successful jobs, Lean 4.28.0, and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Eight axiom-query files exited zero; every
queried declaration reports exactly the allowed footprint set `{propext, Classical.choice,
Quot.sound}`. There is no active `sorry` warning or `native_decide` use.

Two project axioms remain in unimported archived comparison modules. They are disclosed,
absent from all canonical footprints, and therefore outside the release proof closure. The
interrupted stage-one wrapper is retained only as diagnostic evidence and is not counted as a
successful build.
