# R4 -- formal evidence reuse

**Verdict:** `PASS_RECORDED_AND_EXTERNAL_REUSE`  
**Lean executed in this internal residual audit:** no

The formal archive remains byte-identical to the externally reproduced v1.2
archive:

`ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895`.

The previous external clean-room record and its three raw logs were copied into
`results/` for direct inspection. They record:

- `lake update` and cache retrieval without a changed dependency pin;
- exit-zero build, `Build completed successfully (8063 jobs)`;
- exit-zero theorem-level axiom query over 16 declarations;
- footprints restricted to `[propext, Classical.choice, Quot.sound]`, with the
  two documented smaller footprints `[propext, Quot.sound]`;
- no `sorryAx` and no project mathematical axiom.

This gate checks recorded evidence and byte identity only. It does not claim a
new Lean run and does not replace the prior external reproduction.
