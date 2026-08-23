# Protocol — Paper III v1.5 external adversarial residual audit

Run: `run_2026-08-23_v1.5_residual`.

Commissioned by `EXTERNAL_RESIDUAL_AUDIT_REQUEST_v1.5.md`, SHA-256
`75c82bd4cbb027408218bcc8e758ebc96b70c9fb0297544ba6f7394a76f1931c`, delivered with
`PAPER_III_v1.5_EXTERNAL_RESIDUAL_AUDIT_INSTRUCTIONS.zip`
(`e6a1445330ff8d602313fd2e7e6bdf00d1fba0ce2be052b23e1174c0e49f225c`).

## Standing

This auditor performed the v1.4 external residual audit and the v1.4 external challenger
review, and raised `EXT-V14C-N02` and `EXT-V14C-N03` — the two clarifications this release
implements. Reviewing the fixes to one's own findings is a continuation of the same external
mandate, not a second opinion on it; that limit is declared in the report. Consistent with the
request, `PASS` is not conditioned on commissioning another reviewer.

The author's internal `PASS` and the internal residual and semantic-integrity reports were
treated as maps of risk, never as proof authority. Every declared hash was recomputed. Every
gate conclusion in this report rests on evidence produced in this run or on byte identity
proved in this run.

## Method by gate

- **E0** intake: recompute the six manuscript hashes, the Lean ZIP, the sidecar and the six
  preserved authorities; confirm only v1.5 artifacts are active and v1.4 is preserved.
- **E1** delta: independent diff in both languages, checked twice over — structural invariance
  of formulas, tags, theorem/heading order and citations as *ordered sequences*, and
  containment of every changed hunk in the declared delta set, located by section. Then
  `EXT-V14C-N02` and `EXT-V14C-N03` reviewed as mathematics: is each inserted sentence true,
  correctly placed, sufficient for the gap it closes, and free of new claims.
- **E2** carried forward on that evidence, per the request's own instruction not to repeat the
  Sections 4–9 rederivation for ceremony.
- **E3** formal identity by byte proof: manifest counts, archive-vs-manifest by exact key,
  source-only, comparison against the preserved v1.4 freeze, aggregate root and canonical
  surfaces, eight axiom-query logs. Additionally, the four factual claims v1.5 newly makes
  about the external Lean reproduction were verified against the sealed external logs.
- **E4** no Lean rebuild, as requested; carried forward only after E3 and after the prior
  sealed packages re-verified.
- **E5** bilingual loss/duplication in both directions; N02/N03 propagation through
  Markdown -> TeX -> PDF in both languages; render QA including an auditor rebuild of both
  PDFs from the delivered TeX, page-by-page text comparison, raster margin scan of every page,
  and visual inspection of the title, Theorem 2.2 and Appendix D pages at 130 dpi.
- **E6** prior-art regression: bibliography and citation sequence identity against the audited
  v1.4, retention of the bounded negative statement, and absence of any absolute priority
  claim.
- **E7** release surfaces: presence, mutual consistency, quoted-hash resolution, local link
  resolution, HTML scope and disclosure, first-public-preprint framing, and preservation of
  the v1.4 evidence. Plus a sweep for generically-named stale copies of version-specific
  evidence.

## Auditor tool corrections made during the run

Five of this run's initial signals were defects in the auditor's own instruments, each fixed
and recorded rather than filed as findings against the target:

1. package-manifest entries paired to archive members by path suffix, which mis-paired
   `BKLO/Absorber.lean` with `Ax2/PartB/BKLO/Absorber.lean`; exact-key comparison gives 751/751;
2. delta hunks classified line by line, so the "before" side of a declared change looked
   undeclared; classification is per hunk;
3. theorem blocks counted by leading keyword, giving EN=34 ES=36 purely from Spanish word
   order ("Packing-form corollaries" / "Corolarios en forma de empaquetamiento");
4. `\b1\.5\b`, which never matches inside "v1.5" because `v` and `1` are both word characters;
5. a Spanish disclaimer pattern requiring "revisión por pares" where the text reads "revisión
   humana por pares"; and the PDF probe for the kernel-perfect sentence, which failed because
   inline `\(D\)` renders to an astral-plane glyph that pdftotext emits as replacement bytes.
