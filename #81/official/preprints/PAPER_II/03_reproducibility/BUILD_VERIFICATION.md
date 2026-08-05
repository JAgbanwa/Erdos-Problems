# Build verification -- formal certificate

From `05_formalization/lean`:

```bash
lake build
lake env lean --run /dev/stdin <<'EOF'
import PaperII
#print axioms PaperII.theorem_1_2
EOF
```

Expected results (recorded in `gate_logs/`):

- `lake build` completes successfully, `sorry`-free.
- `#print axioms PaperII.theorem_1_2` ->
  `[propext, Classical.choice, Quot.sound]` -- no `sorryAx`, no project-specific
  axiom.

**Independent reproduction (recommended).** Running the two commands above in a
clean environment that did not produce the proof provides third-party
confirmation of the certificate. This step is recommended before any
peer-review or publication claim and is currently pending.

## Computational audits
Each folder in `02_validation/PAPER_II_AUDIT/<section>/` contains a script and a
`requirements.txt`; run the script to recompute that section's claims and compare
against the rec