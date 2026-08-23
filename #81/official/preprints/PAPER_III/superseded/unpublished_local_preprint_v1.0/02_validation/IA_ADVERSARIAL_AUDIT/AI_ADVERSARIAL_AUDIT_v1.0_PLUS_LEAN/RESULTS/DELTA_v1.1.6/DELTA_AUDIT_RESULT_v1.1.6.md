# Delta Audit Result — Paper III v1.1.6 (vs validated v1.1.5)

**Date:** 2026-07-28
**Auditor:** Claude Opus 4.8 (Anthropic), invoked via Claude Code
**Baseline:** v1.1.5 (audited PASS_WITH_OBSERVATIONS; sole open item = F-G05, minor/editorial)
**Request:** `DELTA_AUDIT_REQUEST_v1.1.6.md` — confirm the update is editorial-only and preserves the
established mathematical + Lean status.

---

## Delta Verdict: PASS

The v1.1.6 update is confirmed **editorial-only**, it **accurately resolves** the single open
observation F-G05, and it changes **nothing** in the mathematics or the Lean development. The
cumulative Paper III audit status is therefore upgraded:

> **Paper III global verdict: PASS** (was PASS_WITH_OBSERVATIONS in v1.1.5).

This verdict is *earned*, not granted: every "did-not-change" claim was independently checked by
byte-level diff and hash, and the new §11.6 text was checked against the axiom footprint I measured
directly in the main audit.

---

## What I verified (independently)

### 1. Full manuscript diff — only §11.6 wording + version header changed

`diff` of the two manuscripts (2175 → 2177 lines; evidence:
`evidence/manuscript_v115_to_v116.diff`, 20 lines) shows **exactly three** edits:

1. **Version header** (line 9): `v1.1.5 → v1.1.6`, "supersedes v1.1.5", "All v1.1.6 changes are
   editorial … unchanged relative to v1.1.5." (No mathematical content.)
2. **§11.6 dependency table, sparse-node row** (line 1839):
   - was: *"Lean freeze: proved, relative to `AX2`"*
   - now: *"Lean freeze: the exposed node `E_8` depends on `AX1` and `AX2`; the very-sparse core lemma
     is `AX2`-only"*
3. **New clarifying paragraph** (after the table): *"The regime labels above summarize the
   mathematical architecture rather than the transitive dependency of every exposed Lean node. In
   particular, the sparse argument is organized around the `AX2` decomposition input, but `E_8`
   dispatches an intermediate alpha-range through the bulk lemma `E_4_3` and therefore inherits `AX1`
   as well."*

No other line changed. In particular, **unchanged**: all theorem/corollary/lemma statements, all
definitions, all constants (`1/6`, `0.9+ε`, `p₀=37`, `p₀=2304`, `μ(α)` breakpoints, …), all displayed
identities, all proof steps, §2.4 (AX1/AX2 literature scope), and the Appendix-C computational claims.

Manuscript SHA-256 (evidence: `evidence/manuscript_sha256.txt`):
- v1.1.5 `7aaf03083ddf7731dcb2b1e849cdfac97fb1697df1650c49a56e8431ce1bcb0b`
- v1.1.6 `b54d0b79c2c2a4ff21a1fe16f388de771a261c51fab0f6cfceea53559102e55d`

### 2. The new §11.6 text is factually correct against the frozen Lean

The main audit measured, via `#print axioms`, that the exposed sparse node `PaperIII.E_8` depends on
`[propext, Classical.choice, PaperIII.AX1, PaperIII.AX2, Quot.sound]`, and that the divergence arises
because `E_8` routes the sub-range `α ∈ [1/12, 1/2]` through the bulk lemma `E_4_3` (AX1) while the
very-sparse core `E_8_very_sparse_packing_estimate` (range `12q < p`) is AX2-only. The v1.1.6 text
states exactly this. **The correction is accurate.** F-G05 (outcome had been REFUTED sub-claim,
severity minor) is now **RESOLVED**.

### 3. Lean source and frozen archive are byte-identical

No new Lean freeze was created (only `lean/` and `lean_v1.0_freeze/` exist). Seven load-bearing
source files were re-hashed and compared against the freeze's own `FREEZE_MANIFEST_SHA256.txt`
(evidence: `evidence/freeze_integrity.txt`) — **all 7 MATCH**:

| File | SHA-256 (actual = manifest) |
|---|---|
| `PaperIII/AX.lean` | `70aa59bb…f235a0` |
| `PaperIII/E_8.lean` | `363e2cf3…e13742` |
| `PaperIII/E_4_3.lean` | `d9aab180…12dde3f` |
| `PaperIII/Main.lean` | `bc82e100…3b5dd30` |
| `PaperIII/Prop_10_1.lean` | `346d1a22…4837a4` |
| `PaperIII/Duality.lean` | `153d6498…1711f02e` |
| `PaperIII/Defs.lean` | `ec6ffd4b…428c845` |

No `.lean` source file is newer than the manifest. Because the Lean is unchanged, **all axiom-gate
results and every CONFIRMED finding from the v1.1.5 audit carry over verbatim** — no rebuild needed.
The build (8060 jobs, 0 errors), the two-axiom footprint (`AX1`, `AX2` only), the zero
`sorry`/`admit`/`unsafe`, the closed corridor (`Prop_10_1_low/mid` + packing corollaries), and the
`Theorem_1_1 = AX1+AX2` footprint all remain valid.

### 4. Supporting documents consistent

The supplied `CHANGELOG_v1.1.5_to_v1.1.6.md` ("editorial only … no Lean source changed … frozen Lean
archives and SHA-256 unchanged") matches my independent diff and hash checks exactly.

---

## One transparency note (not a finding)

The two regime-summary sentences at lines 1820 and 1822 retain the architectural shorthand
"bulk–`AX1`, sparse–`AX2`, corridor–none" / "`AX2` for the sparse node." These are now **explicitly
defined as architectural summaries** by the newly added paragraph, which also gives the precise
per-node footprint (`E_8` = `AX1+AX2`). With the authoritative node-level table row corrected and the
disambiguating paragraph in place, the document is internally consistent and non-misleading. No
residual finding; an optional further tightening would be to echo "(node `E_8`: `AX1+AX2`)" inline at
line 1822, but this is not required for correctness.

The prior severity-`none` note F-B02 (AX1's cover-side statement bundles finite LP strong duality with
Haxell–Rödl, disclosed by the authors) was always informational and never blocking; it does not affect
the PASS.

---

## Bottom line

| Item | v1.1.5 | v1.1.6 |
|---|---|---|
| Theorem 1.1 / Corollary 1.2 sound, conditional on AX1+AX2 | ✔ | ✔ (unchanged) |
| AX1/AX2 faithful to literature, not overstated | ✔ | ✔ (unchanged) |
| Corridor genuinely unconditional (closed footprints) | ✔ | ✔ (unchanged) |
| §11.6 sparse-node dependency description matches Lean | ✗ **F-G05** (minor) | ✔ **resolved** |
| Global verdict | PASS_WITH_OBSERVATIONS | **PASS** |

The delta is editorial-only, correct, and complete. **Paper III v1.1.6: PASS.**
