/-
# Re-export module.

`BKLO/MainRepaired.lean` imports `BKLO.VortexMain`, but no such file was present in the project as
delivered, so nothing in `BKLO` compiled.  The module is restored here as a re-export of
`BKLO/Main.lean`, which is what `BKLO/MainRepaired.lean` needs from it (the §11 assembly
`BKLO.triangle_decomposition_of_inputs` and everything it imports).
-/
import BKLO.Main
