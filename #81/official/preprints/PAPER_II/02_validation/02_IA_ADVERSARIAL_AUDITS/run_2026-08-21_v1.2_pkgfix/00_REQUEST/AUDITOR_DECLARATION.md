# Auditor declaration - PAPER_II v1.2 pkgfix

**Specification:** `FINAL_RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:** `2eadd655d6dd9f1d96127c979ba43a0b2d251da7478cd84ba4bb1868e38cb683`
**Run:** `run_2026-08-21_v1.2_pkgfix`

| Item | Value |
|---|---|
| Auditor | Claude, operating as an AI auditor under this specification |
| Provider / model | Anthropic, Claude Opus 5, `claude-opus-5` |
| Service date | 2026-08-21 |
| Operator | The repository owner |
| Independence configuration | Primary auditor only. **No adversarial challenger**, in this run or in the prior Paper II external run. |

## Conflicts and limitations, stated plainly

1. **Self-review.** This auditor produced `EXT-PII-M-001`, the finding verified closed here,
   and the external report that preceded it. Inherent to a residual re-audit; disclosed.
2. **Never challenged.** Paper II has been audited only by a single reasoning context across
   both runs. On Paper I an adversarial challenger found four Spanish duplications this
   auditor's own diff had missed, so the absence is material and not a formality.
3. **Reuse.** The mathematical, formal, citation, novelty, bilingual, duplicate and
   rendered-PDF gates were **not rerun**. They are reused under the byte-identity rule the
   specification sets out, after all nine protected anchors were confirmed to match.
4. One gate could be cross-checked against independent artifacts and was: the internal R4
   gate's copied logs were compared by SHA-256 against this auditor's own external logs and
   are byte-identical.
5. This audit is **not human peer review** and does **not** prove global novelty.

## Environment

Windows 11 (10.0.26200), Intel Core i7-1255U, 10 cores / 12 logical, 15.7 GB RAM.
Python 3.14.4; Poppler 24.04.0; MiKTeX 25.12 with LuaLaTeX; pandoc 3.9.0.2. No external
solver. **No random seeds anywhere.** Deep package paths were reached through short
directory junctions because Windows MAX_PATH silently truncates directory walks at this
nesting depth.

## Unavailable capabilities

`erdosproblems.com` (HTTP 403 on every path). No institutional bibliographic database. The
delivered PDFs were not independently recompiled.

## Non-mutation

The target was not modified. No Lean build was run; no target file was written, moved or
deleted by this auditor.
