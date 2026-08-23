# R4 formal evidence reuse

**Verdict:** `PASS_RECORDED_AND_EXTERNAL_REUSE`  
**Lean executed in this audit:** no

The formal archive remains SHA-256
`0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a`.
Recorded evidence reports build exit 0 and “Build completed successfully (8034
jobs).” The axiom gate exits 0 and directly covers
`PaperI.Split.paperI_main_sharp`, `PaperI.paperI_main`,
`PaperI.assembly_sharp` and `PaperI.Split.residual_duality`, with footprint
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The external v1.3 audit proved this archive byte-identical to its clean-room
rebuild. This internal gate reviews and preserves that evidence without
recompilation.

