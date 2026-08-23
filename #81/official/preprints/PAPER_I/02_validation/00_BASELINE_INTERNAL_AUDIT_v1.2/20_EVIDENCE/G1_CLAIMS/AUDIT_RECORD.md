# G1 CLAIMS -- Paper I audit record

**Verdict:** `PASS_AFTER_CORRECTION`

The audit checked Theorem 1.1, Lemma 3.1, Lemma 5.1, Proposition B.1, the final
assembly in Section 8, the complete-split benchmark, the scope exclusions, and
the formalization-status language against the English authority, Spanish
translation, claim map, calculation surfaces, and frozen Lean sources.

## Finding and correction

`P1-IA-001` (`MAJOR`, resolved in the package baseline): `CLAIM_MAP.md` had
identified the corrected final assembly with a weaker companion declaration.
The map now points to `PaperI.assembly_sharp` and
`PaperI.Split.paperI_main_sharp`, which are the v1.2 `n/2` surfaces. No theorem
or proof text changed.

The v1.2 audit additionally checked the exact archive name/hash, the four
headline axiom-query namespaces, and the corrected tightness wording.

All quantifiers, assumptions, constants, inequality directions, exceptional
branches, and scope limitations are consistent after the correction.
