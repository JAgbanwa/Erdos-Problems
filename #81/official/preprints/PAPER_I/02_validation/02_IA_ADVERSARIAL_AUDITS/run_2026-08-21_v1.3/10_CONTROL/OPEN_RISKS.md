# Open risks and residuals — Paper I v1.3 residual re-audit

**Verdict:** `PASS_WITH_RESIDUALS`. Nothing here is claim-critical.

## Correctable in the target — these are what hold the verdict below a plain PASS

| ID | Severity | What | Fix |
|---|---|---|---|
| `RES-V13-001` | MINOR | `tmp/internal_report_v1.3/` holds three LaTeX build artifacts inside the sealed package; the `.log` and `.pdf` are byte-identical duplicates of files already correctly placed under `02_validation/01_INTERNAL_AUDITS/10_REPORT/` | delete the `tmp/` subtree and reseal |
| `RES-V13-002` | MINOR | `CHANGELOG_v1.3.md` line 10 names `PaperI.Split.assembly_sharp` and `PaperI.residual_duality`; the real declarations are `PaperI.assembly_sharp` and `PaperI.Split.residual_duality`. The manuscript's Appendix C has them right | correct the two names in the changelog |

Doing both would make a plain `PASS` available on a new target hash.

## Not correctable by editing the target

| Risk | Status |
|---|---|
| `RES-V13-004` (NOTE): the cited `ordman.net` URL serves an expired certificate, so a reader following reference [2] hits a warning | accessibility only; the `3/16` constant itself is now **verified** with a pinpoint |
| `erdosproblems.com` returns HTTP 403 to this auditor, so the official problem page was never read directly | the open status is corroborated by the verified primary source [1] |
| novelty | **not re-searched in this run.** This is a residual re-audit; the v1.2 Gate K conclusion was an evidence-bounded negative result and remains exactly that |
| the delivered PDFs were not independently recompiled from the delivered TeX | producer strings and source-to-PDF text tracking checked instead |
| six project Lean modules outside the eight built targets were never compiled | no verdict from any run |
| adequacy of the bespoke `PaperI.Split` structure as a model of every split graph | judged faithful by inspection; not formalized in the artifact |

## Risks specific to this run's configuration

- **The auditor is reviewing corrections to its own findings.** Inherent to a residual
  re-audit, disclosed in the declaration, not mitigated.
- **No adversarial challenger was run for v1.3.** In the v1.2 run the challenger found four
  of the five Spanish duplications that the primary auditor's display-math-only diff had
  missed. That safeguard is absent here; the duplication re-check was therefore made
  general and mechanical rather than phrase-targeted, which is a partial substitute at best.
- **Control 6 rests on owner-supplied evidence**, verified by the auditor but not
  independently retrieved.

## What would raise confidence most

1. Delete `tmp/`, fix the two changelog names, reseal — then a plain `PASS` is reachable.
2. Run an independent challenger, ideally a different model family, against v1.3.
3. Obtain specialist confirmation of novelty, which no run has provided.
