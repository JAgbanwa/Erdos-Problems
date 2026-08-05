# Paper II — Official preprint release v1.0

**Title:** *Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs*  
**Author:** Juan Pablo Traverso Gianini  
**Release date:** 2026-07-10  
**Release status:** official preprint release  
**Peer-review status:** not externally peer-reviewed  
**Novelty status:** subject to specialist literature review

This directory is the canonical public package for Paper II, preprint v1.0.
Historical drafts, superseded proofs, private audit records, and materials from
the separate asymptotic clique-partition route (Erdős #81) are kept outside this
release directory.

## Main result

For every integer `n >= 1`, over chordal graphs on `n` vertices,

```
max ( |E(G)| - 2*tau3*(G) )  =  floor( (2n+1)^2 / 24 ),
```

with `tau3*` the fractional triangle-cover number, attained by a complete-split
graph `S_{p,q} = K_p join complement(K_q)`. The theorem is formally verified in
Lean 4 (see `05_formalization/`).

## Interactive explainer

A five-level bilingual (EN/ES) explainer of the theorem: [`PaperII_explained_4_levels.html`](PaperII_explained_4_levels.html) — [rendered preview](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/preprints/PAPER_II/PaperII_explained_4_levels.html).

## Directory structure

```text
01_manuscript/       Official PDF/TeX/Markdown, English and Spanish
02_validation/       Calculation ledger, internal audits (A-F), validation status
03_reproducibility/  Build instructions and environment notes
04_integrity/        Hashes, manifest, and provenance
05_formalization/    Verified Lean 4 formalization of Theorem 1.1 (sorry-free, axiom-clean)
```

## Canonical files

- `01_manuscript/PAPER_II_preprint_v1.0.pdf` (English); `..._es.pdf` (Spanish)
- `01_manuscript/PAPER_II_preprint_v1.0.tex` / `.md` (+ Spanish `_es`)
- `02_validation/PAPER_II_CALCULATION_LEDGER_v1.1.md`
- `05_formalization/lean/PaperII/Unconditional.lean` (Lean theorem `PaperII.theorem_1_2` = Theorem 1.1)
- `05_formalization/lean/gate_logs/` (`lake build` and `#print axioms` records)

## Formal-verification certificate

`PaperII.theorem_1_2` (Lean 4 / Mathlib v4.28.0, repository commit `5f2d448`) is
`sorry`-free; its only chordality hypothesis is the standard `IsChordal`
definition; and `#print axioms` reports exactly `[propext, Classical.choice,
Quot.sound]` -- no `sorryAx`, no project-specific axiom.

## Validation boundary

The result has received AI adversarial **internal** audit and machine-checked
formalization, and was approved for preprint release by the editor and
researcher. This does **not** constitute external peer review, journal
refereeing, or a specialist priority review. An independent AI adversarial audit (deep protocol) returned **PASS**
(`PAPER-II-EXT-AUDIT-001`; see `02_validation/02_IA_ADVERSARIAL_AUDITS/`), and it
re-elaborated the Lean build and `#print axioms` independently. This is an
intermediate assurance tier, not external human peer review.

## Integrity check

```bash
sha256sum -c 04_integrity/SHA256SUMS.txt
```

## Scope

Paper II proves the exact finite extremum of the fractional cover functional. It
does **not** prove an integral clique-partition bound and does **not** settle
Erdős Problem #81, which remains open via a separate asymptotic route.

## Li