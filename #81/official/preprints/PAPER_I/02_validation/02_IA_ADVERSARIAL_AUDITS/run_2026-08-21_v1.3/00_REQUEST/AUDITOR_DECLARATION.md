# Auditor declaration — residual re-audit, Paper I v1.3

**Specification:** `RESIDUAL_AUDIT_REQUEST_SPEC.md`
**Specification SHA-256:** `e8d92cf5fffbc55b02eada99e4e446207752dbe28f1b8492195838b123d85435`
**Run:** `run_2026-08-21_v1.3`
**Audit class:** external residual adversarial re-audit

## Identity

| Item | Value |
|---|---|
| Auditor | Claude, operating as an AI auditor under this specification |
| Provider / model | Anthropic, Claude Opus 5, `claude-opus-5` |
| Service date | 2026-08-21 |
| Operator | The repository owner (`jtraverso@ccs.cl`) |
| Prior involvement | **Yes, and material.** The same auditor produced the external v1.2 report whose findings this run validates. That is inherent to a residual re-audit and is disclosed rather than mitigated: the auditor is checking corrections to its own findings. An independent second opinion on the corrections would be stronger. |
| Independence configuration | Primary auditor only. The v1.2 run additionally used an adversarial challenger of the same model family; **no challenger was run for v1.3.** |

## Conflicts and limitations, stated plainly

1. **Self-review of own findings.** See above.
2. **No challenger for this run**, so the v1.2 configuration's main strength — a second
   context that found four Spanish duplications the primary auditor had missed — is absent
   here. The duplication re-check was instead made general and mechanical (every long unit
   compared against every other, plus page-image comparison) precisely to compensate.
3. **Owner-supplied evidence.** The Chen–Erdős–Ordman scan that closes control 6 was
   supplied by the owner after four auditor retrieval routes failed. The auditor verified
   the file itself by rendering and reading it, but did not obtain it independently. Labelled
   as such throughout.
4. **Gate H reused, not rerun**, under the byte-identity rule of specification Section 5.
5. This audit is **not human peer review** and does **not** prove global novelty.

## Environment

Windows 11 (10.0.26200), Intel Core i7-1255U, 10 cores / 12 logical, 15.7 GB RAM, x86_64.
Python 3.14.4 with `sympy` 1.14.0 and `Pillow` 12.2.0; Poppler 24.04.0; MiKTeX 25.12 with
LuaLaTeX; pandoc 3.9.0.2; Git 2.54.0.windows.1. No external LP/ILP solver: every linear
program was solved by exact-rational code written for this audit. **No random seeds were
used anywhere.**

Reused Gate H toolchain: Lean 4.28.0, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`;
Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

Disclosed environment notes: `git config --global core.longpaths true` remains set from the
v1.2 run; the deep package paths were accessed through short directory junctions because
Windows `MAX_PATH` silently truncates directory walks at this nesting depth.

## Unavailable capabilities

- `ordman.net` serves an expired certificate and redirects `http` to `https`; the auditor
  could not retrieve the cited scan (resolved by owner supply — see above).
- `erdosproblems.com` returns HTTP 403 to this auditor.
- `web.archive.org` is not reachable from this environment.
- No institutional bibliographic database (MathSciNet, zbMATH).
- The delivered PDFs were not independently recompiled from the delivered TeX.

## Timestamps

Specification received and hash-verified, anchors verified, and input freeze sealed on
2026-08-21 before any substantive analysis. Audit end recorded in
`30_REPORT/FINAL_AUDIT_SUMMARY.json`.
