# G4 RECORDED-BUILD -- Paper I audit record

**Verdict:** `PASS`

The frozen evidence records `EXIT_CODE=0` and `Build completed successfully
(8034 jobs).` The corrective axiom gate records `EXIT_CODE=0` for 15 declarations,
including `PaperI.assembly_sharp` and `PaperI.Split.residual_duality`. The
headline theorem and admitted interfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; `sorryAx` and project axioms are absent
from the axiom report. The escape-hatch record classifies raw textual matches
as comments/report labels.

The source and package manifests and archive sidecar were recomputed and match.
Per protocol v1.3, no `lake build` or Lean command was executed in this audit.
Fresh reconstruction remains an external-audit gate.
