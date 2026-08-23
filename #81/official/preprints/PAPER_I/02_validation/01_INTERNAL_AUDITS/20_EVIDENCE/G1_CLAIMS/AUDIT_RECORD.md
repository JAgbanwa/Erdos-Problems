# G1 CLAIMS — Paper I v1.3 audit record

**Verdict:** `PASS_AFTER_CORRECTION`

The audit checked Theorem 1.1, Lemma 3.1, Lemma 5.1, Proposition B.1, the
Section 8 assembly, the complete-split benchmark, scope limitations and
formalization-status language across English, Spanish, LaTeX, PDF, the claim
map and frozen Lean sources.

All eight external findings are resolved in the manuscript layer: duplicated
Spanish passages were removed; the integrity baseline was replaced; the
derivation of (4.7) now states `z=x` and accounts for every edge of `H`; the
Appendix A.2 formula is restricted to `o>=3`; “sharp” is explicitly limited to
the quadratic coefficient; the CEO primary scan is cited; the Schrijver
reference is chapter-level; and the unused repository citation was removed.

During this rerun, `P1-IA-V13-001` (`MINOR`) found one residual stale reference
to “Corollary 7.1g” in the formalization-status paragraph. It was corrected to
the chapter-level source in EN/ES Markdown and LaTeX, the PDFs were rebuilt,
and the full downstream checks were rerun. No theorem, hypothesis, constant or
proof step changed. Quantifiers, assumptions, inequality directions,
exceptional branches and scope limitations now match.
