# Auditor declaration - final package-residual re-audit, Paper I v1.3

**Specification:** `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:** `93cf8e6a06cd47189e98a4939145b21a32a283956c172a2791812a4df5a87484`
**Run:** `run_2026-08-21_v1.3_pkgfix`

| Item | Value |
|---|---|
| Auditor | Claude, operating as an AI auditor under this specification |
| Provider / model | Anthropic, Claude Opus 5, `claude-opus-5` |
| Service date | 2026-08-21 |
| Operator | The repository owner |
| Independence configuration | Primary auditor only. **No adversarial challenger was run** for this run or for the preceding v1.3 run. |

## Conflicts and limitations, stated plainly

1. **Self-review.** This auditor produced the two MINOR findings being verified closed
   here, and the external report that preceded them. That is inherent to a residual
   re-audit and is disclosed rather than mitigated.
2. **No challenger.** The v1.2 run's challenger found four Spanish duplications the
   primary auditor had missed. That safeguard is absent from this run. The controls here
   were therefore made mechanical and exhaustive over all 308 files rather than targeted.
3. **Gate H and the mathematical, bilingual, citation and artifact regressions are
   reused**, not rerun, under the byte-identity rule the specification sets out. Byte
   identity was re-established in this run (32 of 32 archive members).
4. This audit is **not human peer review** and does **not** prove global novelty.

## Environment

Windows 11 (10.0.26200), Intel Core i7-1255U, 10 cores / 12 logical, 15.7 GB RAM.
Python 3.14.4; Poppler 24.04.0; MiKTeX 25.12 with LuaLaTeX; pandoc 3.9.0.2.
No external solver was used. **No random seeds anywhere.**
Deep package paths were reached through short directory junctions, because Windows
MAX_PATH silently truncates directory walks at this nesting depth.

## Unavailable capabilities

`ordman.net` (expired certificate), `erdosproblems.com` (HTTP 403), `web.archive.org`
(unreachable from this environment), and no institutional bibliographic database. The
delivered PDFs were not independently recompiled.

## Non-mutation

The target was not modified. The Lean archive was re-extracted into a scratch directory
for the byte-identity check and its hash re-verified afterwards as unchanged.
