# R2 -- exact mathematical regression

**Verdict:** `PASS`

The existing Paper II internal regression program was rerun against the
unchanged English Markdown anchor
`7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882`.
It completed with exit code 0 and checked:

- 195 complete-split LP instances;
- exact integer maximization through 5,000 vertices;
- 6,667 argmax and level-set checks;
- 139 non-isomorphic graph-atlas cases through six vertices;
- 931 vertex-copy nonedge pairs;
- 22 terminal-property graphs.

No discrepancy was found. These bounded computations are regression evidence,
not proof premises. The stronger external exhaustive falsification and Lean
reproduction remain preserved under their original hashes.
