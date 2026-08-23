# Formalization — Paper III v1.4

`lean_v1.4_freeze/` is the immutable source-only formal snapshot for this audit target.
Its archive is `PAPER_III_lean_v1.4_freeze.zip`, SHA-256
`79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.

The freeze contains 704 Lean files and a 707-entry source manifest. It is pinned to Lean
4.28.0 and Mathlib v4.28.0 commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The aggregate `PaperIII` root imports the
final theorem and `PublicAPI`; canonical model bridges and all manuscript-facing theorem
surfaces are covered by the directed axiom gate.

The recorded author build is `PASS_CLEAN_ORIGIN_RESUMED`. The source tree was clean at
origin, but the build resumed after an application restart. Independent uninterrupted
clean-room reproduction remains mandatory for external audit and public release.

The v1.3 freeze remains preserved in the separate v1.3 package. The editable candidate and
transfer kit were removed after their 707 source entries were verified identical to this
freeze. The v1.4 archive is the only formal target in this package and the only one named by
the v1.4 manuscript.
