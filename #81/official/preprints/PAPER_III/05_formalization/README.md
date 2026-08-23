# Formalization — Paper III v1.5 release package

`lean_v1.4_freeze/` is the immutable source-only formal snapshot carried by the v1.5
preprint.
Its archive is `PAPER_III_lean_v1.4_freeze.zip`, SHA-256
`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

The freeze contains 704 Lean files and a 707-entry source manifest. It is pinned to Lean
4.28.0 and Mathlib v4.28.0 commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The aggregate `PaperIII` root imports the
final theorem and `PublicAPI`; canonical model bridges and all manuscript-facing theorem
surfaces are covered by the directed axiom gate.

The preserved evidence includes a resumed author build, a later uninterrupted clean author
run and an independent uninterrupted external clean-room reproduction. The independent run
compiled the aggregate public root in 8,455 jobs and the query roots in 8,444 jobs and
confirmed the directed axiom surfaces. The v1.5 residual does not rebuild Lean because no
formal byte changed; it verifies that claim by cryptographic comparison with the audited
v1.4 package.

The v1.4 archive is the only formal target in the active package and the only archive named
by the v1.5 manuscript. Earlier unpublished targets remain under `superseded/`.
