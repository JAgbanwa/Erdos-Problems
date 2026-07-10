# Gate logs

Formal-verification gate outputs for `PaperII.theorem_1_2` at commit `5f2d448`.

- `lake_build.log` — `lake build` completes successfully, `sorry`-free (8057 jobs).
- `print_axioms.log` — `#print axioms PaperII.theorem_1_2` =
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no project-specific axiom),
  with the full theorem statement (hypotheses = standard `IsChordal`).

Provenance: these logs were produced by the **independent** AI adversarial audit
(`PAPER-II-EXT-AUDIT-001`), which re-elaborated the proof in its own environment —
i.e. they are a third-party reproduction, not the development build. Residual noted
by the auditor: the rebuild used the project's pinned Mathlib cache (not from-scratch).
See `../../../02_validation/02_IA_ADVERSARI