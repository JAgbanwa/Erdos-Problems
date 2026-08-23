# Changelog — v1.1.5 to v1.1.6 near-final editorial

**Baseline:** `Papers_I_II_III_v1.1.5_near_final_editorial`  
**Output:** `Papers_I_II_III_v1.1.6_near_final_editorial`

## Scope

This update is editorial only. No theorem statement, definition, constant, displayed equation, proof step, or Lean source was changed.

## Paper III change

The Paper III manuscript now aligns the Lean-dependency narrative in Section 11.6 with the actual axiom footprint of the exposed sparse Lean node:

- the exposed node `E_8` is described as depending on `AX1 + AX2`;
- the very-sparse core lemma remains `AX2`-only;
- the section now states explicitly that the regime labels summarize the mathematical architecture rather than the transitive dependency of each exposed Lean node.

This resolves the only minor observation from the v1.1.5 adversarial report without touching the mathematics.

## Carry-forward material

- Paper I is carried forward unchanged from v1.1.5.
- Paper II is carried forward unchanged from v1.1.5.
- The frozen Lean archives and their SHA-256 values are unchanged.

## Verdict

`EDITORIALLY_READY_FOR_DELTA_AUDIT`
