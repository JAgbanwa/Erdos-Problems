# Auditor declaration

**Protocol:** `EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1`
**Protocol SHA-256:** `8ba029f443297927c9a5101b0a349bd33e3772587e56d32cbb70145de24ae505`
(recomputed by the auditor and matching the supplied sidecar
`EXTERNAL_AI_ADVERSARIAL_AUDIT_INSTRUCTIONS_v1.1.md.sha256` exactly)
**Run identifier:** `run_2026-08-21_v1.2`
**Audit class:** `EXTERNAL_AI_ADVERSARIAL`

## Identity and independence

| Item | Value |
|---|---|
| Auditor | Claude (Anthropic), operating as an AI auditor under this protocol |
| Provider | Anthropic |
| Model | Claude Opus 5 |
| Exact model identifier | `claude-opus-5` |
| Service date | 2026-08-21 |
| Reasoning configuration | Interactive agent session (Claude Code), extended tool use; no fine-tuning or retrieval augmentation specific to this project |
| Operator | The repository owner (`jtraverso@ccs.cl`), who launched both reasoning contexts |
| Organization | None independent of the project owner |
| Prior involvement with the project | The same operator previously ran a **suspended, unsealed** audit of the earlier `preprint_draft_v1.1` target under protocol v1.0. That run was closed without a verdict. Per protocol Section 4.1, **no conclusion from it was carried forward**; every regression control and every mathematical claim was re-established from scratch against the v1.2 bytes in this run. |
| Internal reports hidden during the independent first pass | **Yes.** Neither reasoning context read `02_validation/00_BASELINE_INTERNAL_AUDIT_v1.1/`, `02_validation/01_INTERNAL_AUDITS/`, nor any prior `02_IA_ADVERSARIAL_AUDITS/` content before producing its own claim map, attack plan and computational results. Author-side material inspected afterwards is labelled `AUTHOR_SIDE_COMPARISON` where cited. |

## Independence configuration (protocol Section 3.1)

Two isolated reasoning contexts were used:

- **Primary auditor** — claim map, analytic rederivation, formal reproduction,
  computational attacks, citation and prior-art work.
- **Adversarial challenger** — received only the immutable target and this protocol,
  and was instructed to produce its own attack plan, kill switches, claim map and
  findings before any reconciliation, and never to request the primary auditor's
  conclusions.

**Disclosed limitations of this configuration, stated plainly:**

1. Both contexts are the **same model family** (Claude Opus 5). The protocol permits
   this only if disclosed; it is disclosed here. A different provider or model family
   would be stronger.
2. **The same operator launched both contexts.** Therefore "external" in this report
   means *separation from the authoring workflow*, **not** independent human peer
   review.
3. This audit is **not** human peer review and does **not** establish global novelty.

## Conflicts of interest

The operator is the author of the audited work. The auditor has no independent interest
in the outcome and was instructed to falsify rather than confirm. This structural
conflict is recorded because it cannot be eliminated by the auditor.

## Environment

| Item | Value |
|---|---|
| Operating system | Windows 11 Home Single Language, 10.0.26200 |
| Shell | Git Bash / MSYS2 (`MINGW64_NT-10.0-26200`, 3.6.7) and PowerShell 7 |
| CPU | 12th Gen Intel Core i7-1255U, 10 cores / 12 logical processors |
| Memory | 15.7 GB physical |
| Architecture | x86_64 |

## Tool versions

| Tool | Version |
|---|---|
| Lean (inside the clean room, as pinned by `lean-toolchain`) | **4.28.0**, `x86_64-w64-windows-gnu`, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` — matches the protocol's expected Lean commit |
| Lake (inside the clean room) | 5.0.0-src+7e01a1b |
| Mathlib (pinned in `lake-manifest.json`) | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` — matches the protocol's expected revision |
| Elan | 4.2.3 (b6cec7e10, 2026-06-08) |
| Lean (elan default *outside* any project) | 4.33.1 — recorded only to avoid confusion; **not** the toolchain used for any audit result |
| Git | 2.54.0.windows.1 |
| Python | 3.14.4 (CPython) — all exact-arithmetic work used `fractions.Fraction` |
| Pillow | 12.2.0 — used for rendered-page ink analysis |
| TeX | MiKTeX-pdfTeX 4.23 (MiKTeX 25.12) |
| Poppler | `pdftoppm` 24.04.0, with `pdfinfo` and `pdftotext` from the same distribution |
| Solvers | **None external.** All linear programs were solved by exact-rational code written for this audit (vertex enumeration for the 3-variable orbit program; a primal simplex with Bland's rule for the packing/cover LPs). No floating-point LP solver was used for any recorded result. |

## Randomness and determinism

**No random seeds were used anywhere in this audit.** Every computational result comes
from deterministic exhaustive enumeration or deterministic exact-arithmetic evaluation.
Where a domain could not be exhausted, the domain actually swept is recorded explicitly
in the relevant gate record.

## Disclosed environment changes and caches (protocol Section 3.3)

1. **`git config --global core.longpaths true`.** Previously unset at both global and
   system scope. Without it, Mathlib checkout fails on this Windows host. This is a
   change to the auditor's machine, not to the target.
2. **Short clean-room roots** `C:\erdos_audit\P1`, `...\PII`, `...\PIII`, as protocol
   Section 3.3 recommends for Windows.
3. **Shared network dependency cache** `~/.cache/mathlib`, populated by
   `lake exe cache get`. Protocol Section 3.3 permits a network dependency cache when
   disclosed. It contains only Mathlib dependency artifacts and **no compiled project
   module** of Paper I, II or III. Each paper has its own separate clean room and its
   own `.lake`; no build output was shared between papers.
4. Each Lean archive's SHA-256 was verified **before** extraction, and each extracted
   tree was confirmed to contain **no** inherited `.lake` and **no** `.olean` before any
   build step.

## Frozen inputs received

| Paper | EN Markdown SHA-256 | Lean archive SHA-256 | Internal-audit ZIP SHA-256 |
|---|---|---|---|
| I | `da7e48196a03a8698a9c5a503976b43780cb9e5309558f1b7d3e06b4af35ee9e` | `0181506408644fc1f8872d711de5a98a500f4052aa295bcd6f8c82776694fd3a` | `34d41bb9fec6fdc1adb6e544d7f5974438c7453ef7f7eb217f857489987d32e6` |
| II | `7215e14bbea8ab2bf208dcdd1efa050cd2b72c997eee2efe504a1e6817c68882` | `ee2d05cc40d943ca92f8f7bf3e5dd83c2692518ddea5e2ca4f7686ccb1ac3895` | `e6f625486db867582da72fff9e71fa0f600dcce40e43ef885ce01756282b24e2` |
| III | `d4ca630d0966928b5b4d71ba6afcd34043fc33507757e8a817e3f42f245c80a1` | `9bff12f0c8279ae4485de960c01be322a423d8fd2f17592ebb7327b2c890fcb8` | `a5963462cf5c06283420135dcd6925a89e98a487e0b60890ff491a2b4079ccf2` |

All nine anchors were recomputed from the delivered bytes and **all nine match**.

## Timestamps

| Event | UTC |
|---|---|
| Protocol v1.1 received and hash-verified | 2026-08-21T14:38Z (file mtime 10:38 local) |
| Gate G0 freeze sealed | 2026-08-21T14:45Z |
| Clean-room extraction, Paper I | 2026-08-21T14:52Z |
| `lake update` + `cache get`, Paper I | 2026-08-21T14:52Z – 15:05Z |
| Protocol Section 9.1 build command started, Paper I | 2026-08-21T15:05:13Z |
| Audit end | recorded in `FINAL_AUDIT_SUMMARY.json` at seal time |

Timezone of the host is reported by the shell as `HSP`; all audit timestamps in this
package are UTC.

## Unavailable capabilities (declared, not worked around)

- **erdosproblems.com is inaccessible to this auditor** — HTTP 403 on every path tried,
  so the official Erdős Problem #81 page was never read directly.
- **No institutional bibliographic database** (MathSciNet, zbMATH) and no
  citation-graph traversal tool were available, which materially limits Gate K.
- **Chen–Erdős–Ordman 1994** (World Scientific, Beijing 1993 proceedings) has no open
  full text; its `3/16` constant could not be confirmed from the primary source.
- **Schrijver 1986** was not available, so the pinpoint `Corollary 7.1g` is unverified.
- **No non-English literature search** was performed.
- **PDFs were not independently recompiled** from the delivered TeX.

Each of these appears again as an explicit limitation in the gate record it affects, and
as a residual in the final report. None was silently assumed to pass.
