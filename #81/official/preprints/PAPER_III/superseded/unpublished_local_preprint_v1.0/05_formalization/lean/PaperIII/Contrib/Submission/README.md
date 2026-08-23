# `Contrib/Submission/` — Mathlib submission package

Clean, **self-contained** Lean results (a by-product of the Paper III / Erdős #81
formalization) prepared for upstreaming to
[Mathlib](https://github.com/leanprover-community/mathlib4). Everything here is ready **up to
the point just before opening a PR**; the only remaining steps are external/human (see
`PR_DRAFTS.md`).

> The repository **root is the working area** (the full Paper III formalization, which uses
> in-repo *bridged* copies under `PaperIII/Contrib/`). This `Submission/` folder is the
> **clean, dependency-minimal version to send to Mathlib**: each `.lean` here imports
> **Mathlib only** (`import Mathlib`), lives in `namespace SimpleGraph`, uses a general vertex
> type, and follows Mathlib conventions.

## Contents of this folder

| File | Type | What it is |
|------|------|------------|
| `Dirac.lean` | Lean (478 lines) | **Dirac's theorem**: `SimpleGraph.IsHamiltonian_of_minDegree` — a finite simple graph on `n ≥ 3` vertices with `δ ≥ n/2` is Hamiltonian (rotation–extension). Self-contained, sorry-free, axioms `[propext, Classical.choice, Quot.sound]`. |
| `Matching.lean` | Lean (371 lines) | **Matching from min-degree**: `SimpleGraph.exists_isPerfectMatching_of_minDegree` (even `n`) + near-perfect odd-case variant, via Tutte. Self-contained, sorry-free, same axioms. |
| `README.md` | doc | This file — describes the folder and how to verify/submit. |
| `PR_DRAFTS.md` | doc | Ready-to-use Zulip announcements, PR titles/descriptions, and the remaining human PR-time steps (incl. CLA and `shake` import-minimization). |

*(Kept in sync with the folder — update this table if files are added/removed/renamed.)*

## Target locations in Mathlib

| Result | Target file (add the declaration there) |
|--------|------------------------------------------|
| `Dirac.lean` → `IsHamiltonian_of_minDegree` | `Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean` |
| `Matching.lean` → `exists_isPerfectMatching_of_minDegree` (+ odd case) | `Mathlib/Combinatorics/SimpleGraph/Matching.lean` |

Both are gaps in Mathlib `v4.28.0` (the `IsHamiltonian*` / `Subgraph.IsMatching` *definitions*
exist, but neither theorem does).

## How to verify each file

From the `lean/` project directory (with `lake exe cache get` done):
```bash
lake env lean PaperIII/Contrib/Submission/Dirac.lean
lake env lean PaperIII/Contrib/Submission/Matching.lean
```
Clean output (no `error`/`sorry`/warning) = verified. Both currently pass, and
`#print axioms` of each export = `[propext, Classical.choice, Quot.sound]`.

## Provenance / disclosure

Developed with **AI assistance** (the Aristotle prover), verified by Lean's kernel and
human-reviewed. Disclose in the PR; the submitting contributor takes responsibility.

## Before a PR (details in `PR_DRAFTS.md`)

Announce on Zulip → sign the **CLA** (a one-time Contributor License Agreement: a legal grant
letting Mathlib use your contribution under Apache-2.0, asserting you may license it; a GitHub
bot guides you on the first PR) → fork/branch → move each declaration into its target file and
run `lake exe shake` to minimize imports → open the two PRs with the drafted text.
